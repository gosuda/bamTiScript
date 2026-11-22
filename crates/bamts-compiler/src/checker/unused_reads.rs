//! Shared reference analysis for the unused-name diagnostics.
//!
//! A binding counts as read when the binder recorded a reference to it that
//! is neither a write-only assignment target nor textually inside the
//! binding's own declaration. Both the unused-import and the unused-local
//! checks share this query so they cannot disagree on what counts as a use.

use std::collections::{HashMap, HashSet};

use super::binder::{SemanticModel, SymbolId};
use super::diagnostic_messages::{Args, by_u32};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::source::TextRange;
use crate::syntax::{
    AssignmentTarget, ExportDeclaration, ExportDefaultValue, ExportNamedDeclaration, Expression,
    ForInitializer, MemberProperty, ModuleExportName, SourceFile, Statement, Stmt,
};

/// Recorded references grouped by symbol, with write-only occurrences
/// removed. Built once per source file and shared by every unused check.
pub(crate) struct FileReads {
    by_symbol: HashMap<SymbolId, Vec<TextRange>>,
}

/// Collects the readable references of one source file.
#[must_use]
pub(crate) fn file_reads(source: &SourceFile, model: &SemanticModel) -> FileReads {
    let writes = write_ranges(source.statements());
    let mut by_symbol: HashMap<SymbolId, Vec<TextRange>> = HashMap::new();
    for (range, symbol) in model.symbol_references() {
        let key = range_key(*range);
        if writes.contains(&key) {
            continue;
        }
        by_symbol.entry(*symbol).or_default().push(*range);
    }
    FileReads { by_symbol }
}

/// Whether any readable reference resolves to `symbol` outside `home`.
#[must_use]
pub(crate) fn is_symbol_read(reads: &FileReads, symbol: SymbolId, home: TextRange) -> bool {
    let Some(ranges) = reads.by_symbol.get(&symbol) else {
        return false;
    };
    ranges.iter().any(|range| !contains_range(home, *range))
}

/// Whether `outer` textually contains `inner`.
fn contains_range(home: TextRange, range: TextRange) -> bool {
    home.start().get() <= range.start().get() && range.end().get() <= home.end().get()
}

fn range_key(range: TextRange) -> (usize, usize) {
    (range.start().get(), range.end().get())
}

/// Maps each bound identifier's range to its symbol.
#[must_use]
pub(crate) fn binding_symbols(model: &SemanticModel) -> HashMap<(usize, usize), SymbolId> {
    let mut map = HashMap::new();
    for (index, symbol) in model.symbols().iter().enumerate() {
        let id = SymbolId::new(u32::try_from(index).expect("symbol count fits in u32"));
        let range = symbol.range();
        map.insert(range_key(range), id);
    }
    map
}

/// Local names a source-less `export` statement publishes, plus the default
/// and `export =` identifier forms the binder resolves as ordinary reads.
#[must_use]
pub(crate) fn exported_local_names(source: &SourceFile) -> HashSet<String> {
    let mut exported = HashSet::new();
    for statement in source.statements() {
        collect_export_names(source, statement, &mut exported);
    }
    exported
}

/// Whether a source-less `export {x}` (or `export default x` / `export = x`)
/// names this binding: the name is exported and module lookup finds it.
#[must_use]
pub(crate) fn is_exported_name(
    model: &SemanticModel,
    exported: &HashSet<String>,
    name: &str,
    symbol: SymbolId,
) -> bool {
    exported.contains(name) && model.lookup_value(model.module_scope(), name) == Some(symbol)
}

fn collect_export_names(source: &SourceFile, statement: &Stmt, exported: &mut HashSet<String>) {
    let Statement::Export(export) = statement.data() else {
        return;
    };
    match export {
        ExportDeclaration::Named(ExportNamedDeclaration::Specifiers {
            source: from,
            specifiers,
            ..
        }) => {
            if from.is_some() {
                return;
            }
            for specifier in specifiers {
                note_export_name(source, &specifier.data().local, exported);
            }
        }
        ExportDeclaration::Default(default) => match &default.value {
            ExportDefaultValue::Expression(expression) => {
                note_expression_name(source, expression, exported);
            }
            ExportDefaultValue::Function(_)
            | ExportDefaultValue::Class(_)
            | ExportDefaultValue::Interface(_)
            | ExportDefaultValue::Missing(_) => {}
        },
        ExportDeclaration::Assignment(expression) => {
            note_expression_name(source, expression, exported);
        }
        _ => {}
    }
}

fn note_export_name(source: &SourceFile, name: &ModuleExportName, exported: &mut HashSet<String>) {
    if let ModuleExportName::Identifier(identifier) = name {
        note_identifier_name(source, identifier, exported);
    }
}

fn note_expression_name(
    source: &SourceFile,
    expression: &crate::syntax::Expr,
    exported: &mut HashSet<String>,
) {
    if let Expression::Identifier(identifier) = expression.data() {
        note_identifier_name(source, identifier, exported);
    }
}

fn note_identifier_name(
    source: &SourceFile,
    identifier: &crate::syntax::IdentifierNode,
    exported: &mut HashSet<String>,
) {
    if let Some(name) = source.identifier_text(identifier.data().token()) {
        exported.insert(name.into_owned());
    }
}

/// Ranges written but never read: plain-`=` assignment targets and
/// `for`-head targets. Reads live at disjoint ranges, so excluding these
/// ranges from the reference set leaves every genuine read intact.
fn write_ranges(statements: &[Stmt]) -> HashSet<(usize, usize)> {
    let mut writes = HashSet::new();
    for statement in statements {
        scan_stmt_writes(statement, &mut writes);
    }
    writes
}

/// Scans the readable positions of a binding pattern for nested writes:
/// initializers and computed keys. The bound identifiers themselves are
/// declarations, not writes.
fn scan_pattern_reads(pattern: &crate::syntax::Pattern, writes: &mut HashSet<(usize, usize)>) {
    match pattern.data() {
        crate::syntax::BindingPattern::Identifier(_)
        | crate::syntax::BindingPattern::Missing(_) => {}
        crate::syntax::BindingPattern::Object(pattern) => {
            for property in &pattern.properties {
                if let crate::syntax::PropertyName::Computed(key) = &property.name {
                    scan_expr_writes(key, writes);
                }
                scan_pattern_reads(&property.binding, writes);
                if let Some(initializer) = property.initializer.as_deref() {
                    scan_expr_writes(initializer, writes);
                }
            }
        }
        crate::syntax::BindingPattern::Array(pattern) => {
            for element in &pattern.elements {
                if let crate::syntax::ArrayBindingElement::Binding(inner) = element {
                    scan_pattern_reads(inner, writes);
                }
            }
        }
        crate::syntax::BindingPattern::Rest(rest) => {
            scan_pattern_reads(&rest.argument, writes);
        }
        crate::syntax::BindingPattern::Assignment(assignment) => {
            scan_pattern_reads(&assignment.left, writes);
            scan_expr_writes(&assignment.right, writes);
        }
    }
}

fn insert_range(writes: &mut HashSet<(usize, usize)>, range: TextRange) {
    writes.insert(range_key(range));
}

fn scan_stmts_writes(statements: &[Stmt], writes: &mut HashSet<(usize, usize)>) {
    for statement in statements {
        scan_stmt_writes(statement, writes);
    }
}

fn scan_stmt_writes(statement: &Stmt, writes: &mut HashSet<(usize, usize)>) {
    match statement.data() {
        Statement::Expression(expression) => {
            scan_expr_writes(&expression.expression, writes);
        }
        Statement::Variable(declaration) => {
            for declarator in &declaration.declarations {
                scan_pattern_reads(&declarator.data().binding, writes);
                if let Some(initializer) = declarator.data().initializer.as_deref() {
                    scan_expr_writes(initializer, writes);
                }
            }
        }
        Statement::Function(function) => scan_function_writes(&function.function, writes),
        Statement::Class(class) => scan_class_writes(class, writes),
        Statement::Namespace(namespace) => {
            scan_stmts_writes(&namespace.body.data().statements, writes);
        }
        Statement::If(value) => {
            scan_expr_writes(&value.test, writes);
            scan_stmt_writes(&value.consequent, writes);
            if let Some(alternate) = value.alternate.as_deref() {
                scan_stmt_writes(alternate, writes);
            }
        }
        Statement::Switch(value) => {
            scan_expr_writes(&value.discriminant, writes);
            for case in &value.cases {
                if let Some(test) = case.data().test.as_deref() {
                    scan_expr_writes(test, writes);
                }
                scan_stmts_writes(&case.data().consequent, writes);
            }
        }
        Statement::For(value) => {
            match value.initializer.as_ref() {
                Some(ForInitializer::Variable(declaration)) => {
                    for declarator in &declaration.declarations {
                        scan_pattern_reads(&declarator.data().binding, writes);
                        if let Some(initializer) = declarator.data().initializer.as_deref() {
                            scan_expr_writes(initializer, writes);
                        }
                    }
                }
                Some(ForInitializer::Expression(expression)) => {
                    scan_expr_writes(expression, writes);
                }
                None => {}
            }
            if let Some(test) = value.test.as_deref() {
                scan_expr_writes(test, writes);
            }
            if let Some(update) = value.update.as_deref() {
                scan_expr_writes(update, writes);
            }
            scan_stmt_writes(&value.body, writes);
        }
        Statement::ForIn(value) => {
            scan_for_binding_writes(&value.binding, writes);
            scan_expr_writes(&value.object, writes);
            scan_stmt_writes(&value.body, writes);
        }
        Statement::ForOf(value) => {
            scan_for_binding_writes(&value.binding, writes);
            scan_expr_writes(&value.iterable, writes);
            scan_stmt_writes(&value.body, writes);
        }
        Statement::While(value) => {
            scan_expr_writes(&value.test, writes);
            scan_stmt_writes(&value.body, writes);
        }
        Statement::DoWhile(value) => {
            scan_stmt_writes(&value.body, writes);
            scan_expr_writes(&value.test, writes);
        }
        Statement::With(value) => {
            scan_expr_writes(&value.object, writes);
            scan_stmt_writes(&value.body, writes);
        }
        Statement::Try(value) => {
            scan_stmts_writes(&value.block.data().statements, writes);
            if let Some(handler) = value.handler.as_ref().map(|node| node.data()) {
                if let Some(binding) = handler.binding.as_ref() {
                    scan_pattern_reads(binding, writes);
                }
                scan_stmts_writes(&handler.body.data().statements, writes);
            }
            if let Some(finalizer) = value.finalizer.as_ref().map(|node| node.data()) {
                scan_stmts_writes(&finalizer.statements, writes);
            }
        }
        Statement::Labeled(value) => {
            scan_stmt_writes(&value.body, writes);
        }
        Statement::Return(value) => {
            if let Some(argument) = value.argument.as_deref() {
                scan_expr_writes(argument, writes);
            }
        }
        Statement::Throw(value) => {
            scan_expr_writes(&value.argument, writes);
        }
        Statement::Block(value) => {
            scan_stmts_writes(&value.data().statements, writes);
        }
        Statement::Export(export) => match export {
            ExportDeclaration::Named(ExportNamedDeclaration::Declaration(inner)) => {
                scan_stmt_writes(inner, writes);
            }
            ExportDeclaration::Default(default) => match &default.value {
                ExportDefaultValue::Function(function) => {
                    scan_function_writes(function, writes);
                }
                ExportDefaultValue::Expression(expression) => {
                    scan_expr_writes(expression, writes);
                }
                ExportDefaultValue::Class(class) => scan_class_writes(class, writes),
                ExportDefaultValue::Interface(_) | ExportDefaultValue::Missing(_) => {}
            },
            ExportDeclaration::Assignment(expression) => {
                scan_expr_writes(expression, writes);
            }
            _ => {}
        },
        Statement::Declare(_)
        | Statement::Import(_)
        | Statement::ImportEquals(_)
        | Statement::Interface(_)
        | Statement::TypeAlias(_)
        | Statement::Enum(_)
        | Statement::Debugger
        | Statement::Break(_)
        | Statement::Continue(_)
        | Statement::Empty
        | Statement::Missing(_) => {}
    }
}

fn scan_for_binding_writes(
    binding: &crate::syntax::ForBinding,
    writes: &mut HashSet<(usize, usize)>,
) {
    match binding {
        crate::syntax::ForBinding::Variable(declaration) => {
            for declarator in &declaration.declarations {
                scan_pattern_reads(&declarator.data().binding, writes);
                if let Some(initializer) = declarator.data().initializer.as_deref() {
                    scan_expr_writes(initializer, writes);
                }
            }
        }
        crate::syntax::ForBinding::Target(target) => {
            add_target_writes(target, writes);
            scan_target_reads(target, writes);
        }
    }
}

fn scan_expr_writes(expression: &crate::syntax::Expr, writes: &mut HashSet<(usize, usize)>) {
    match expression.data() {
        Expression::Assignment(assignment) => {
            if assignment.operator == crate::syntax::AssignmentOperator::Assign {
                add_target_writes(&assignment.left, writes);
            }
            scan_target_reads(&assignment.left, writes);
            scan_expr_writes(&assignment.right, writes);
        }
        Expression::Update(update) => {
            scan_target_reads(&update.argument, writes);
        }
        Expression::Binary(value) => {
            scan_expr_writes(&value.left, writes);
            scan_expr_writes(&value.right, writes);
        }
        Expression::Logical(value) => {
            scan_expr_writes(&value.left, writes);
            scan_expr_writes(&value.right, writes);
        }
        Expression::Conditional(value) => {
            scan_expr_writes(&value.test, writes);
            scan_expr_writes(&value.consequent, writes);
            scan_expr_writes(&value.alternate, writes);
        }
        Expression::Sequence(value) => {
            for inner in &value.expressions {
                scan_expr_writes(inner, writes);
            }
        }
        Expression::Parenthesized(inner) => {
            scan_expr_writes(inner, writes);
        }
        Expression::As(value) => {
            scan_expr_writes(&value.expression, writes);
        }
        Expression::Satisfies(value) => {
            scan_expr_writes(&value.expression, writes);
        }
        Expression::TypeAssertion(value) => {
            scan_expr_writes(&value.expression, writes);
        }
        Expression::NonNull(value) => {
            scan_expr_writes(&value.expression, writes);
        }
        Expression::Await(value) => {
            scan_expr_writes(&value.argument, writes);
        }
        Expression::Yield(value) => {
            if let Some(argument) = value.argument.as_deref() {
                scan_expr_writes(argument, writes);
            }
        }
        Expression::Unary(value) => {
            scan_expr_writes(&value.argument, writes);
        }
        Expression::Call(value) => {
            scan_expr_writes(&value.callee, writes);
            for argument in &value.arguments {
                match argument {
                    crate::syntax::CallArgument::Expression(inner) => {
                        scan_expr_writes(inner, writes);
                    }
                    crate::syntax::CallArgument::Spread(spread) => {
                        scan_expr_writes(&spread.argument, writes);
                    }
                    crate::syntax::CallArgument::Missing(_) => {}
                }
            }
        }
        Expression::Array(value) => {
            for element in &value.elements {
                match element {
                    crate::syntax::ArrayElement::Expression(inner) => {
                        scan_expr_writes(inner, writes);
                    }
                    crate::syntax::ArrayElement::Spread(spread) => {
                        scan_expr_writes(&spread.argument, writes);
                    }
                    crate::syntax::ArrayElement::Elision
                    | crate::syntax::ArrayElement::Missing(_) => {}
                }
            }
        }
        Expression::Member(value) => {
            scan_expr_writes(&value.object, writes);
            if let crate::syntax::MemberProperty::Computed(computed) = &value.property {
                scan_expr_writes(computed, writes);
            }
        }
        Expression::New(value) => {
            scan_expr_writes(&value.callee, writes);
            for argument in &value.arguments {
                match argument {
                    crate::syntax::CallArgument::Expression(inner) => {
                        scan_expr_writes(inner, writes);
                    }
                    crate::syntax::CallArgument::Spread(spread) => {
                        scan_expr_writes(&spread.argument, writes);
                    }
                    crate::syntax::CallArgument::Missing(_) => {}
                }
            }
        }
        Expression::Object(value) => {
            for member in &value.members {
                match member.data() {
                    crate::syntax::ObjectMember::Property(property) => {
                        if let crate::syntax::PropertyName::Computed(key) = &property.name {
                            scan_expr_writes(key, writes);
                        }
                        scan_expr_writes(&property.value, writes);
                    }
                    crate::syntax::ObjectMember::Method(method) => {
                        scan_function_writes(&method.function, writes);
                    }
                    crate::syntax::ObjectMember::Spread(spread) => {
                        scan_expr_writes(&spread.argument, writes);
                    }
                    crate::syntax::ObjectMember::Missing(_) => {}
                }
            }
        }
        Expression::Function(value) => {
            scan_function_writes(&value.function, writes);
        }
        Expression::Class(value) => {
            scan_class_writes(&value.class, writes);
        }
        Expression::Arrow(value) => {
            scan_function_like_writes(&value.parameters, Some(&value.body), writes);
        }
        Expression::Template(value) => {
            for inner in &value.expressions {
                scan_expr_writes(inner, writes);
            }
        }
        Expression::TaggedTemplate(value) => {
            scan_expr_writes(&value.tag, writes);
            for inner in &value.template.expressions {
                scan_expr_writes(inner, writes);
            }
        }
        Expression::Import(value) => {
            scan_expr_writes(&value.source, writes);
            if let Some(options) = value.options.as_deref() {
                scan_expr_writes(options, writes);
            }
        }
        Expression::JsxElement(value) => {
            for attribute in &value.opening.data().attributes {
                scan_jsx_attribute(attribute, writes);
            }
            scan_jsx_children(&value.children, writes);
        }
        Expression::JsxFragment(value) => {
            scan_jsx_children(&value.children, writes);
        }
        Expression::JsxSelfClosingElement(value) => {
            for attribute in &value.attributes {
                scan_jsx_attribute(attribute, writes);
            }
        }
        Expression::Identifier(_)
        | Expression::Literal(_)
        | Expression::This
        | Expression::Super
        | Expression::Meta(_)
        | Expression::Missing(_) => {}
    }
}

fn scan_jsx_children(children: &[crate::syntax::JsxChild], writes: &mut HashSet<(usize, usize)>) {
    for child in children {
        match child {
            crate::syntax::JsxChild::ExpressionContainer(container) => {
                if let Some(expression) = container.data().expression.as_deref() {
                    scan_expr_writes(expression, writes);
                }
            }
            crate::syntax::JsxChild::Spread(spread) => {
                scan_expr_writes(&spread.data().expression, writes);
            }
            crate::syntax::JsxChild::Element(expression) => {
                scan_expr_writes(expression, writes);
            }
            crate::syntax::JsxChild::Text(_) => {}
        }
    }
}

fn scan_jsx_attribute(
    attribute: &crate::syntax::JsxAttributeItem,
    writes: &mut HashSet<(usize, usize)>,
) {
    match attribute {
        crate::syntax::JsxAttributeItem::Attribute(attribute) => {
            if let Some(crate::syntax::JsxAttributeInitializer::Expression(container)) =
                attribute.data().initializer.as_ref()
                && let Some(expression) = container.data().expression.as_deref()
            {
                scan_expr_writes(expression, writes);
            }
        }
        crate::syntax::JsxAttributeItem::Spread(spread) => {
            scan_expr_writes(&spread.data().expression, writes);
        }
    }
}

fn scan_function_writes(
    function: &crate::syntax::FunctionLike,
    writes: &mut HashSet<(usize, usize)>,
) {
    for decorator in &function.decorators {
        scan_expr_writes(&decorator.data().expression, writes);
    }
    scan_function_like_writes(&function.parameters, function.body.as_ref(), writes);
}

fn scan_function_like_writes(
    parameters: &[crate::syntax::ParameterNode],
    body: Option<&crate::syntax::FunctionBody>,
    writes: &mut HashSet<(usize, usize)>,
) {
    for parameter in parameters {
        for decorator in &parameter.data().decorators {
            scan_expr_writes(&decorator.data().expression, writes);
        }
        scan_pattern_reads(&parameter.data().binding, writes);
        if let Some(initializer) = parameter.data().initializer.as_deref() {
            scan_expr_writes(initializer, writes);
        }
    }
    match body {
        Some(crate::syntax::FunctionBody::Block(block)) => {
            scan_stmts_writes(&block.data().statements, writes);
        }
        Some(crate::syntax::FunctionBody::Expression(expression)) => {
            scan_expr_writes(expression, writes);
        }
        Some(crate::syntax::FunctionBody::Missing(_)) | None => {}
    }
}

fn scan_class_writes(
    class: &crate::syntax::ClassDeclaration,
    writes: &mut HashSet<(usize, usize)>,
) {
    for decorator in &class.decorators {
        scan_expr_writes(&decorator.data().expression, writes);
    }
    if let Some(heritage) = class.extends.as_ref() {
        scan_expr_writes(&heritage.expression, writes);
    }
    for member in &class.members {
        match member.data() {
            crate::syntax::ClassMember::Constructor(constructor) => {
                for decorator in &constructor.decorators {
                    scan_expr_writes(&decorator.data().expression, writes);
                }
                scan_function_like_writes(&constructor.parameters, None, writes);
                scan_stmts_writes(&constructor.body.data().statements, writes);
            }
            crate::syntax::ClassMember::Method(method) => {
                if let crate::syntax::PropertyName::Computed(key) = &method.name {
                    scan_expr_writes(key, writes);
                }
                scan_function_writes(&method.function, writes);
            }
            crate::syntax::ClassMember::Property(property) => {
                for decorator in &property.decorators {
                    scan_expr_writes(&decorator.data().expression, writes);
                }
                if let crate::syntax::PropertyName::Computed(key) = &property.name {
                    scan_expr_writes(key, writes);
                }
                if let Some(initializer) = property.initializer.as_deref() {
                    scan_expr_writes(initializer, writes);
                }
            }
            crate::syntax::ClassMember::AutoAccessor(accessor) => {
                for decorator in &accessor.decorators {
                    scan_expr_writes(&decorator.data().expression, writes);
                }
                if let crate::syntax::PropertyName::Computed(key) = &accessor.name {
                    scan_expr_writes(key, writes);
                }
                if let Some(initializer) = accessor.initializer.as_deref() {
                    scan_expr_writes(initializer, writes);
                }
            }
            crate::syntax::ClassMember::StaticBlock(block) => {
                scan_stmts_writes(&block.data().statements, writes);
            }
            crate::syntax::ClassMember::IndexSignature(_)
            | crate::syntax::ClassMember::Missing(_)
            | crate::syntax::ClassMember::Semicolon => {}
        }
    }
}

/// Records the plain-`=` write ranges of one assignment target and scans the
/// readable positions nested inside it for further writes.
fn add_target_writes(
    target: &crate::syntax::AssignmentTargetNode,
    writes: &mut HashSet<(usize, usize)>,
) {
    match target.data() {
        AssignmentTarget::Identifier(identifier) => {
            insert_range(writes, identifier.range());
        }
        AssignmentTarget::Member(member) => {
            insert_range(writes, target.range());
            scan_expr_writes(&member.object, writes);
            if let MemberProperty::Computed(key) = &member.property {
                scan_expr_writes(key, writes);
            }
        }
        AssignmentTarget::Object(pattern) => {
            for property in &pattern.properties {
                if let crate::syntax::PropertyName::Computed(key) = &property.name {
                    scan_expr_writes(key, writes);
                }
                add_target_writes(&property.target, writes);
                if let Some(initializer) = property.initializer.as_deref() {
                    scan_expr_writes(initializer, writes);
                }
            }
        }
        AssignmentTarget::Array(pattern) => {
            for element in &pattern.elements {
                match element {
                    crate::syntax::AssignmentArrayElement::Target(inner)
                    | crate::syntax::AssignmentArrayElement::Rest(inner) => {
                        add_target_writes(inner, writes);
                    }
                    crate::syntax::AssignmentArrayElement::Elision
                    | crate::syntax::AssignmentArrayElement::Missing(_) => {}
                }
            }
        }
        AssignmentTarget::Invalid(_) | AssignmentTarget::Missing(_) => {}
    }
}

/// Scans the readable positions of an assignment target for nested writes.
/// The target root itself is a write and contributes no readable range here.
fn scan_target_reads(
    target: &crate::syntax::AssignmentTargetNode,
    writes: &mut HashSet<(usize, usize)>,
) {
    match target.data() {
        AssignmentTarget::Identifier(_) => {}
        AssignmentTarget::Member(member) => {
            scan_expr_writes(&member.object, writes);
            if let MemberProperty::Computed(key) = &member.property {
                scan_expr_writes(key, writes);
            }
        }
        AssignmentTarget::Object(pattern) => {
            for property in &pattern.properties {
                if let crate::syntax::PropertyName::Computed(key) = &property.name {
                    scan_expr_writes(key, writes);
                }
                scan_target_reads(&property.target, writes);
                if let Some(initializer) = property.initializer.as_deref() {
                    scan_expr_writes(initializer, writes);
                }
            }
        }
        AssignmentTarget::Array(pattern) => {
            for element in &pattern.elements {
                match element {
                    crate::syntax::AssignmentArrayElement::Target(inner)
                    | crate::syntax::AssignmentArrayElement::Rest(inner) => {
                        scan_target_reads(inner, writes);
                    }
                    crate::syntax::AssignmentArrayElement::Elision
                    | crate::syntax::AssignmentArrayElement::Missing(_) => {}
                }
            }
        }
        AssignmentTarget::Invalid(operand) => {
            scan_expr_writes(operand, writes);
        }
        AssignmentTarget::Missing(_) => {}
    }
}

/// TS6133 for an unused binding, reported at its name or pattern span.
#[must_use]
pub(crate) fn unused_diagnostic(source: &SourceFile, range: TextRange, name: &str) -> Diagnostic {
    let entry = by_u32(6133);
    let message = entry
        .and_then(|message| message.format(Args::new([name])).ok())
        .unwrap_or_else(|| format!("'{name}' is declared but its value is never read."));
    Diagnostic::error(
        entry.map_or(DiagnosticCode::new("6133"), |message| {
            message.diagnostic_code()
        }),
        source.source_id(),
        range,
        message,
    )
}

/// TS6192 for an import declaration whose every binding is unused.
#[must_use]
pub(crate) fn all_unused_diagnostic(source: &SourceFile, range: TextRange) -> Diagnostic {
    let entry = by_u32(6192);
    let message = entry
        .and_then(|message| message.format(Args::new([])).ok())
        .unwrap_or_else(|| "All imports in import declaration are unused.".to_owned());
    Diagnostic::error(
        entry.map_or(DiagnosticCode::new("6192"), |message| {
            message.diagnostic_code()
        }),
        source.source_id(),
        range,
        message,
    )
}

/// TS6198 for a destructuring pattern whose every element is unused.
#[must_use]
pub(crate) fn unused_elements_diagnostic(source: &SourceFile, range: TextRange) -> Diagnostic {
    let entry = by_u32(6198);
    let message = entry
        .and_then(|message| message.format(Args::new([])).ok())
        .unwrap_or_else(|| "All destructured elements are unused.".to_owned());
    Diagnostic::error(
        entry.map_or(DiagnosticCode::new("6198"), |message| {
            message.diagnostic_code()
        }),
        source.source_id(),
        range,
        message,
    )
}

/// TS6199 for a variable statement whose every declarator is unused.
#[must_use]
pub(crate) fn unused_variables_diagnostic(source: &SourceFile, range: TextRange) -> Diagnostic {
    let entry = by_u32(6199);
    let message = entry
        .and_then(|message| message.format(Args::new([])).ok())
        .unwrap_or_else(|| "All variables are unused.".to_owned());
    Diagnostic::error(
        entry.map_or(DiagnosticCode::new("6199"), |message| {
            message.diagnostic_code()
        }),
        source.source_id(),
        range,
        message,
    )
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::super::binder::bind_source;
    use super::super::unused_locals::{UnusedDiagnostics, unused_diagnostics};
    use crate::diagnostic::Diagnostic;
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

    fn codes(diagnostics: &[Diagnostic]) -> Vec<&str> {
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect()
    }

    fn messages(diagnostics: &[Diagnostic]) -> Vec<String> {
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.message().to_owned())
            .collect()
    }

    #[test]
    fn plain_assign_target_is_write_only() {
        let outcome = check("function f() { var x = 0; x = 1; return 0; }");
        assert_eq!(codes(&outcome.locals), ["6133", "6133"], "{outcome:?}");
        let texts = messages(&outcome.locals);
        assert!(texts.contains(&"'f' is declared but its value is never read.".to_owned()));
        assert!(texts.contains(&"'x' is declared but its value is never read.".to_owned()));
        assert!(outcome.params.is_empty(), "{outcome:?}");
    }

    #[test]
    fn destructuring_assignment_target_is_write_only() {
        let outcome = check("function f() { var x = 0; [x] = [1]; return 0; }");
        assert_eq!(codes(&outcome.locals), ["6133", "6133"], "{outcome:?}");
        let texts = messages(&outcome.locals);
        assert!(texts.contains(&"'x' is declared but its value is never read.".to_owned()));
        assert!(outcome.params.is_empty(), "{outcome:?}");
    }

    #[test]
    fn for_head_assignment_is_write_only() {
        let outcome = check("function f() { var x = 0; for (x = 0;;) { break; } return 0; }");
        assert_eq!(codes(&outcome.locals), ["6133", "6133"], "{outcome:?}");
        let texts = messages(&outcome.locals);
        assert!(texts.contains(&"'x' is declared but its value is never read.".to_owned()));
        assert!(outcome.params.is_empty(), "{outcome:?}");
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
    fn update_expression_counts_as_read() {
        let outcome = check("function f() { var x = 0; x++; return 1; }");
        assert_eq!(codes(&outcome.locals), ["6133"], "{outcome:?}");
        assert_eq!(
            outcome.locals[0].message(),
            "'f' is declared but its value is never read."
        );
        assert!(outcome.params.is_empty(), "{outcome:?}");
    }

    #[test]
    fn read_in_later_initializer_counts_as_read() {
        let outcome = check("function f() { var x = 1; var y = x; return y; }");
        assert_eq!(codes(&outcome.locals), ["6133"], "{outcome:?}");
        assert_eq!(
            outcome.locals[0].message(),
            "'f' is declared but its value is never read."
        );
        assert!(outcome.params.is_empty(), "{outcome:?}");
    }

    #[test]
    fn read_in_nested_function_counts_as_read() {
        let outcome = check("function f() { var x = 1; function g() { return x; } return g; }");
        assert_eq!(codes(&outcome.locals), ["6133"], "{outcome:?}");
        assert_eq!(
            outcome.locals[0].message(),
            "'f' is declared but its value is never read."
        );
        assert!(outcome.params.is_empty(), "{outcome:?}");
    }

    #[test]
    fn read_as_computed_key_counts_as_read() {
        let outcome = check("function f() { var x = 0; var y = { [x]: 1 }; return y; }");
        assert_eq!(codes(&outcome.locals), ["6133"], "{outcome:?}");
        assert_eq!(
            outcome.locals[0].message(),
            "'f' is declared but its value is never read."
        );
        assert!(outcome.params.is_empty(), "{outcome:?}");
    }

    #[test]
    fn write_inside_enum_initializer_counts_as_read() {
        let outcome = check("function f() { var x = 0; enum E { A = (x = 1) } return E; }");
        assert_eq!(codes(&outcome.locals), ["6133"], "{outcome:?}");
        assert_eq!(
            outcome.locals[0].message(),
            "'f' is declared but its value is never read."
        );
        assert!(outcome.params.is_empty(), "{outcome:?}");
    }
}
