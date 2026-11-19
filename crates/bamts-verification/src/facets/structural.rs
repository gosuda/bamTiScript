use std::{collections::BTreeSet, sync::Arc};

use bamts_compiler::parser;
use bamts_compiler::scanner;
use bamts_compiler::source::{ScriptKind, SourceId, SourceText, TextRange, Utf16Pos};
use bamts_compiler::syntax::{
    BindingPattern, ClassDeclaration, ClassMember, ClassMemberNode, ExportDeclaration,
    ExportDefaultValue, ExportNamedDeclaration, FunctionLike, FunctionType, IdentifierNode,
    InterfaceDeclaration, NamespaceName, Node, NumericLiteralNode, PropertyName, SourceFile,
    Statement, Stmt, StringLiteralNode, Ty, TypeArgumentList, TypeMember, TypeMemberNode, TypeNode,
    TypeParameterList, VariableDeclaration,
};

use super::{FacetVerdict, compare_structural};

/// Structural comparator for `.types` baselines.
pub fn compare_types(expected: &str, actual: &str) -> FacetVerdict {
    compare_structural("types", expected, actual, |text| {
        Ok(canonicalize_record_baseline(
            text,
            is_types_section,
            types_record,
        ))
    })
}

/// Structural comparator for `.symbols` baselines.
pub fn compare_symbols(expected: &str, actual: &str) -> FacetVerdict {
    compare_structural("symbols", expected, actual, |text| {
        Ok(canonicalize_record_baseline(
            text,
            is_symbols_section,
            symbols_record,
        ))
    })
}

/// Structural comparator for emitted `.d.ts` declaration baselines.
///
/// Both sides are parsed with the exact BAMTS parser and canonicalized from the
/// AST. A baseline that does not parse without recovery can never pass.
pub fn compare_dts(expected: &str, actual: &str) -> FacetVerdict {
    compare_structural("d.ts", expected, actual, canonicalize_dts)
}

/// Structural comparator for JSON source-map baselines.
///
/// JSON object-key order and insignificant whitespace do not carry map meaning;
/// array order and scalar values remain significant.
pub fn compare_source_map(expected: &str, actual: &str) -> FacetVerdict {
    compare_structural("source-map", expected, actual, canonicalize_json)
}

fn canonicalize_json(text: &str) -> Result<Vec<String>, ()> {
    let mut lines = Vec::new();
    for line in text.replace("\r\n", "\n").replace('\r', "\n").lines() {
        let trimmed = line.trim();
        // Visualization trailers and blank lines carry no map meaning.
        if trimmed.is_empty() || trimmed.starts_with("//// https://") {
            continue;
        }
        if let Some(name) = trimmed
            .strip_prefix("//// [")
            .and_then(|rest| rest.strip_suffix(']'))
        {
            lines.push(format!("//// [{name}]"));
            continue;
        }
        if !trimmed.starts_with('{') && !trimmed.starts_with('[') {
            lines.push(trimmed.to_owned());
            continue;
        }
        let mut value: serde_json::Value = serde_json::from_str(trimmed).map_err(|_| ())?;
        // Upstream's serializer always writes `sourceRoot` (empty when unset);
        // absent and empty carry the same map meaning, so normalize to absent.
        if let Some(map) = value.as_object_mut()
            && map.get("sourceRoot").and_then(serde_json::Value::as_str) == Some("")
        {
            map.remove("sourceRoot");
        }
        lines.push(serde_json::to_string(&value).map_err(|_| ())?);
    }
    Ok(lines)
}

/// Declared identity of one element in a declaration-set container.
///
/// Only a simple declared name is a provably distinct identity. Every other
/// shape (computed/string names, call/construct/index signatures, anonymous
/// declarations, augmentations) keeps source order because order is semantic
/// for overloads, merge groups, and ordered type members.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum DeclIdentity {
    Simple(String),
    Anonymous,
}

/// Sort declaration-set elements only when every element has a simple identity
/// and no two share a name. Any duplicate name (a merge group or overload set)
/// or anonymous identity keeps the full source order, because order is
/// semantic there. This is the one case where order is provably irrelevant.
fn sort_declaration_groups(items: &mut [(DeclIdentity, String)]) {
    if items.len() < 2 {
        return;
    }
    let mut names = BTreeSet::new();
    for (identity, _) in items.iter() {
        let DeclIdentity::Simple(name) = identity else {
            return;
        };
        names.insert(name.as_str());
    }
    if names.len() != items.len() {
        return;
    }
    items.sort_by(|left, right| left.0.cmp(&right.0));
}

/// Parses declaration text with the exact BAMTS parser, failing on any
/// recovery diagnostic so structurally invalid baselines can never pass.
fn parse_dts_source(text: &str) -> Result<SourceFile, ()> {
    let source = SourceText::new(text.to_owned()).map_err(|_| ())?;
    let scanned = scanner::scan(SourceId::new(0), ScriptKind::TypeScript, Arc::new(source));
    let parsed = parser::parse(scanned);
    if !parsed.diagnostics().is_empty() {
        return Err(());
    }
    Ok(parsed.into_parts().0)
}

fn canonicalize_dts(text: &str) -> Result<Vec<String>, ()> {
    let file = parse_dts_source(text)?;
    let mut canonical = triple_slash_directives(text);
    canonical.extend(canonical_statement_list(file.statements(), &file));
    Ok(canonical)
}

/// Semantic `/// <reference ... />` directives in source order. They are an
/// ordered prologue: reordering, changing, or removing one changes the
/// declaration program, so they must compare exactly. TypeScript honors them
/// only in the file prologue before any statement, and a directive inside a
/// block comment or string is inert, so collection stops at the first
/// non-comment, non-directive line and skips block-comment bodies.
fn triple_slash_directives(text: &str) -> Vec<String> {
    let mut directives = Vec::new();
    let mut in_block_comment = false;
    for line in text.lines() {
        let trimmed = line.trim_start_matches('\u{feff}').trim();
        if in_block_comment {
            if trimmed.contains("*/") {
                in_block_comment = false;
            }
            continue;
        }
        if trimmed.is_empty() {
            continue;
        }
        if is_semantic_triple_slash_directive(line.trim_start_matches('\u{feff}')) {
            directives.push(normalize_record_line(trimmed));
            continue;
        }
        if trimmed.starts_with("/*") {
            if !trimmed.contains("*/") {
                in_block_comment = true;
            }
            continue;
        }
        if trimmed.starts_with("//") {
            continue;
        }
        // First real statement ends the prologue.
        break;
    }
    directives
}

fn canonical_statement_list(statements: &[Stmt], file: &SourceFile) -> Vec<String> {
    let mut items: Vec<(DeclIdentity, String)> = statements
        .iter()
        .map(|statement| canonical_statement(statement, file))
        .collect();
    sort_declaration_groups(&mut items);
    items
        .into_iter()
        .map(|(_, raw)| normalize_block_lines(&strip_comments(&raw)))
        .collect()
}

fn canonical_statement(statement: &Stmt, file: &SourceFile) -> (DeclIdentity, String) {
    match statement.data() {
        Statement::Declare(inner) => {
            let (identity, inner_raw) = canonical_statement(inner, file);
            let head = slice_range(file, statement.range().start(), inner.range().start());
            let tail = slice_range(file, inner.range().end(), statement.range().end());
            (identity, assemble(&[head, inner_raw, tail]))
        }
        Statement::Export(export) => canonical_export(export, statement.range(), file),
        Statement::Namespace(namespace) => {
            let mut items: Vec<(DeclIdentity, String)> = namespace
                .body
                .data()
                .statements
                .iter()
                .map(|child| canonical_statement(child, file))
                .collect();
            sort_declaration_groups(&mut items);
            let raw: Vec<String> = items.into_iter().map(|(_, raw)| raw).collect();
            let identity = namespace_identity(&namespace.name, file);
            let body_statements = &namespace.body.data().statements;
            let body_range = namespace.body.range();
            let range = statement.range();
            if is_synthetic_dotted_body(body_statements, body_range) {
                // `namespace A.B { ... }` desugars to A with a synthetic body
                // whose node range begins at the dot. Canonicalize it into the
                // same shape as explicit `namespace A { namespace B { ... } }`
                // by dropping the dot from the head and the child's leading dot.
                let child_raw = raw
                    .first()
                    .map(|child| child.trim_start_matches('.').to_owned())
                    .unwrap_or_default();
                let head = slice_range(file, range.start(), body_range.start());
                let head = head
                    .trim_end_matches(['.', ' ', '\t', '\r', '\n'])
                    .to_owned();
                let tail = slice_range(file, body_range.end(), range.end());
                (
                    identity,
                    assemble(&[
                        head,
                        "{".to_owned(),
                        format!("namespace {child_raw}"),
                        "}".to_owned(),
                        tail,
                    ]),
                )
            } else {
                (
                    identity,
                    assemble_statement_container(file, range, body_range, body_statements, raw),
                )
            }
        }
        Statement::Interface(interface) => {
            let members = canonical_type_members(&interface.members, file);
            let identity = DeclIdentity::Simple(identifier_text(file, &interface.name));
            let head = declaration_head(
                file,
                statement.range(),
                &interface.members,
                interface_head_children(interface),
            );
            (
                identity,
                assemble_member_container(
                    file,
                    statement.range(),
                    &interface.members,
                    members,
                    head,
                ),
            )
        }
        Statement::Class(class) => {
            let identity = match &class.name {
                Some(name) => DeclIdentity::Simple(identifier_text(file, name)),
                None => DeclIdentity::Anonymous,
            };
            let members = canonical_class_members(&class.members, file);
            let head = declaration_head(
                file,
                statement.range(),
                &class.members,
                class_head_children(class),
            );
            (
                identity,
                assemble_member_container(file, statement.range(), &class.members, members, head),
            )
        }
        Statement::TypeAlias(alias) => {
            let mut children = type_parameter_children(alias.type_parameters.as_ref());
            children.push(&alias.type_node);
            (
                DeclIdentity::Simple(identifier_text(file, &alias.name)),
                rebuild_children(file, statement.range(), children),
            )
        }
        Statement::Variable(variable) => {
            let mut children: Vec<&Ty> = Vec::new();
            for declarator in &variable.declarations {
                if let Some(annotation) = &declarator.data().type_annotation {
                    children.push(&*annotation.data().type_node);
                }
            }
            (
                variable_identity(variable, file),
                rebuild_children(file, statement.range(), children),
            )
        }
        Statement::Function(function) => (
            function_identity(&function.function.name, file),
            rebuild_children(
                file,
                statement.range(),
                function_like_children(&function.function),
            ),
        ),
        Statement::Enum(enum_declaration) => (
            DeclIdentity::Simple(identifier_text(file, &enum_declaration.name)),
            slice_node(file, statement.range()),
        ),
        Statement::Import(import) => {
            let specifier = unquote(&module_specifier_text(file, &import.source));
            let identity = DeclIdentity::Simple(specifier.clone());
            let raw = replace_string_child(file, statement.range(), &import.source, &specifier);
            (identity, raw)
        }
        _ => (DeclIdentity::Anonymous, slice_node(file, statement.range())),
    }
}

/// True when a namespace body is the parser's synthetic dotted desugaring: a
/// single child whose range begins exactly at the body range (no braces).
fn is_synthetic_dotted_body(statements: &[Stmt], body_range: TextRange) -> bool {
    statements.len() == 1 && statements[0].range().start() == body_range.start()
}

/// Canonicalizes the head of a member-bearing declaration (type parameters,
/// heritage, implements) while the members themselves are handled separately.
fn declaration_head<T>(
    file: &SourceFile,
    range: TextRange,
    members: &[Node<T>],
    head_children: Vec<&Ty>,
) -> String {
    let Some(first) = members.first() else {
        return rebuild_children(file, range, head_children);
    };
    let head_range = TextRange::new(range.start(), first.range().start()).unwrap_or(range);
    if head_children.is_empty() {
        slice_range(file, head_range.start(), head_range.end())
    } else {
        rebuild_children(file, head_range, head_children)
    }
}

fn interface_head_children(interface: &InterfaceDeclaration) -> Vec<&Ty> {
    let mut children = type_parameter_children(interface.type_parameters.as_ref());
    for reference in &interface.extends {
        if let Some(arguments) = &reference.type_arguments {
            children.extend(arguments.arguments.iter());
        }
    }
    children
}

fn class_head_children(class: &ClassDeclaration) -> Vec<&Ty> {
    let mut children = type_parameter_children(class.type_parameters.as_ref());
    if let Some(heritage) = &class.extends
        && let Some(arguments) = &heritage.type_arguments
    {
        children.extend(arguments.arguments.iter());
    }
    for implemented in &class.implements {
        children.push(implemented);
    }
    children
}

fn canonical_export(
    export: &ExportDeclaration,
    range: TextRange,
    file: &SourceFile,
) -> (DeclIdentity, String) {
    match export {
        ExportDeclaration::Named(export_named) => match export_named {
            ExportNamedDeclaration::Declaration(inner) => {
                let (identity, inner_raw) = canonical_statement(inner, file);
                let head = slice_range(file, range.start(), inner.range().start());
                let tail = slice_range(file, inner.range().end(), range.end());
                (identity, assemble(&[head, inner_raw, tail]))
            }
            ExportNamedDeclaration::Specifiers { .. } => {
                (DeclIdentity::Anonymous, slice_node(file, range))
            }
        },
        ExportDeclaration::Default(default) => {
            let identity = match &default.value {
                ExportDefaultValue::Function(function) => function_identity(&function.name, file),
                ExportDefaultValue::Class(class) => match &class.name {
                    Some(name) => DeclIdentity::Simple(identifier_text(file, name)),
                    None => DeclIdentity::Anonymous,
                },
                ExportDefaultValue::Expression(_) | ExportDefaultValue::Missing(_) => {
                    DeclIdentity::Anonymous
                }
                ExportDefaultValue::Interface(interface) => {
                    DeclIdentity::Simple(identifier_text(file, &interface.name))
                }
            };
            (identity, slice_node(file, range))
        }
        ExportDeclaration::All(_) | ExportDeclaration::Assignment(_) => {
            (DeclIdentity::Anonymous, slice_node(file, range))
        }
    }
}

fn variable_identity(variable: &VariableDeclaration, file: &SourceFile) -> DeclIdentity {
    let Some(first) = variable.declarations.first() else {
        return DeclIdentity::Anonymous;
    };
    match first.data().binding.data() {
        BindingPattern::Identifier(identifier) => {
            DeclIdentity::Simple(identifier_text(file, identifier))
        }
        BindingPattern::Object(_)
        | BindingPattern::Array(_)
        | BindingPattern::Rest(_)
        | BindingPattern::Assignment(_)
        | BindingPattern::Missing(_) => DeclIdentity::Anonymous,
    }
}

fn function_identity(name: &Option<IdentifierNode>, file: &SourceFile) -> DeclIdentity {
    match name {
        Some(name) => DeclIdentity::Simple(identifier_text(file, name)),
        None => DeclIdentity::Anonymous,
    }
}

fn namespace_identity(name: &NamespaceName, file: &SourceFile) -> DeclIdentity {
    match name {
        NamespaceName::Identifier { name, .. } => DeclIdentity::Simple(identifier_text(file, name)),
        NamespaceName::StringLiteral(literal) => {
            // Distinct external modules are provably distinct identities; two
            // augmentations of the same module share one key and stay ordered.
            DeclIdentity::Simple(unquote(&module_specifier_text(file, literal)))
        }
        NamespaceName::Global { .. } => DeclIdentity::Anonymous,
    }
}

/// A member name is a simple identity when it is an identifier, string literal,
/// or numeric literal. Identifiers and string literals with the same text are
/// the same property key in TypeScript, so they share one merge group (order is
/// semantic across them).
fn property_identity(name: &PropertyName, file: &SourceFile) -> DeclIdentity {
    match name {
        PropertyName::Identifier(identifier) => {
            DeclIdentity::Simple(identifier_text(file, identifier))
        }
        PropertyName::String(literal) => {
            DeclIdentity::Simple(unquote(&module_specifier_text(file, literal)))
        }
        PropertyName::Number(literal) => DeclIdentity::Simple(numeric_text(file, literal)),
        PropertyName::Computed(_) | PropertyName::Private(_) | PropertyName::Missing(_) => {
            DeclIdentity::Anonymous
        }
    }
}

fn unquote(text: &str) -> String {
    let bytes = text.as_bytes();
    if bytes.len() >= 2 && matches!(bytes[0], b'"' | b'\'') && bytes[bytes.len() - 1] == bytes[0] {
        text[1..text.len() - 1].to_owned()
    } else {
        text.to_owned()
    }
}

fn identifier_text(file: &SourceFile, identifier: &IdentifierNode) -> String {
    file.token_text(identifier.data().token())
        .unwrap_or("")
        .to_owned()
}

fn numeric_text(file: &SourceFile, literal: &NumericLiteralNode) -> String {
    file.token_text(literal.data().token())
        .unwrap_or("")
        .to_owned()
}

fn module_specifier_text(file: &SourceFile, literal: &StringLiteralNode) -> String {
    file.token_text(literal.data().token())
        .unwrap_or("")
        .to_owned()
}

fn slice_node(file: &SourceFile, range: TextRange) -> String {
    slice_range(file, range.start(), range.end())
}

fn slice_range(file: &SourceFile, start: Utf16Pos, end: Utf16Pos) -> String {
    let source = file.source_text().as_str();
    let start = file.source_text().utf16_to_byte(start).unwrap_or(0);
    let end = file
        .source_text()
        .utf16_to_byte(end)
        .unwrap_or(source.len());
    source[start..end].to_owned()
}

fn assemble(parts: &[String]) -> String {
    parts.join("\n")
}

/// Assembles a statement whose body is a statement list (namespace/module/global
/// bodies). The body's own delimiters (`{`/`}` for real bodies, none for
/// synthetic dotted tails) come from source slices around the child ranges, so
/// the brace shape is preserved while sorted children keep their own text.
fn assemble_statement_container(
    file: &SourceFile,
    range: TextRange,
    body_range: TextRange,
    statements: &[Stmt],
    sorted_raw: Vec<String>,
) -> String {
    let head = slice_range(file, range.start(), body_range.start());
    let tail = slice_range(file, body_range.end(), range.end());
    if statements.is_empty() {
        let body = slice_range(file, body_range.start(), body_range.end());
        return assemble(&[head, body, tail]);
    }
    let first = statements[0].range().start();
    let last_end = statements[statements.len() - 1].range().end();
    let body_head = slice_range(file, body_range.start(), first);
    let body_tail = slice_range(file, last_end, body_range.end());
    let mut parts = vec![head, body_head];
    for (index, raw) in sorted_raw.iter().enumerate() {
        if index > 0 {
            parts.push("\n".to_owned());
        }
        parts.push(raw.clone());
    }
    parts.push(body_tail);
    if !tail.is_empty() {
        parts.push(tail);
    }
    assemble(&parts)
}

/// Assembles a node (interface/class/object type) whose members are sorted.
/// Inter-member separators (`;` and whitespace) are dropped because they are
/// irrelevant formatting; each member keeps its own canonical text.
fn assemble_member_container<T>(
    file: &SourceFile,
    range: TextRange,
    members: &[Node<T>],
    sorted_raw: Vec<String>,
    head: String,
) -> String {
    if members.is_empty() {
        return slice_node(file, range);
    }
    let last_end = members[members.len() - 1].range().end();
    let mut tail = slice_range(file, last_end, range.end());
    tail = trim_member_separators(&tail).to_owned();
    let mut parts = vec![head];
    for (index, raw) in sorted_raw.iter().enumerate() {
        if index > 0 {
            parts.push("\n".to_owned());
        }
        parts.push(trim_member_separators(raw).to_owned());
    }
    if !tail.is_empty() {
        parts.push(tail);
    }
    assemble(&parts)
}

fn trim_member_separators(text: &str) -> &str {
    text.trim()
        .trim_start_matches(';')
        .trim_end_matches(';')
        .trim()
}

fn canonical_type_members(members: &[TypeMemberNode], file: &SourceFile) -> Vec<String> {
    let mut items: Vec<(DeclIdentity, String)> = members
        .iter()
        .map(|member| canonical_type_member(member, file))
        .collect();
    sort_declaration_groups(&mut items);
    items.into_iter().map(|(_, raw)| raw).collect()
}

fn canonical_type_member(member: &TypeMemberNode, file: &SourceFile) -> (DeclIdentity, String) {
    let identity = match member.data() {
        TypeMember::Property(property) => property_identity(&property.name, file),
        TypeMember::Method(method) => property_identity(&method.name, file),
        TypeMember::Call(_)
        | TypeMember::Construct(_)
        | TypeMember::Index(_)
        | TypeMember::Missing(_) => DeclIdentity::Anonymous,
    };
    let raw = match member.data() {
        TypeMember::Property(property) => {
            let Some(annotation) = &property.type_annotation else {
                return (identity, slice_node(file, member.range()));
            };
            replace_type_child(file, member.range(), &annotation.data().type_node)
        }
        TypeMember::Method(method) => {
            function_type_children(file, member.range(), &method.function)
        }
        TypeMember::Call(call) => function_type_children(file, member.range(), &call.function),
        TypeMember::Construct(construct) => {
            function_type_children(file, member.range(), &construct.function.function)
        }
        TypeMember::Index(index) => {
            let mut children: Vec<&Ty> = index
                .parameters
                .iter()
                .map(|parameter| &*parameter.type_annotation.data().type_node)
                .collect();
            children.push(&*index.type_annotation.data().type_node);
            rebuild_children(file, member.range(), children)
        }
        TypeMember::Missing(_) => slice_node(file, member.range()),
    };
    (identity, raw)
}

fn canonical_class_members(members: &[ClassMemberNode], file: &SourceFile) -> Vec<String> {
    let mut items: Vec<(DeclIdentity, String)> = members
        .iter()
        .map(|member| canonical_class_member(member, file))
        .collect();
    sort_declaration_groups(&mut items);
    items.into_iter().map(|(_, raw)| raw).collect()
}

fn canonical_class_member(member: &ClassMemberNode, file: &SourceFile) -> (DeclIdentity, String) {
    let identity = match member.data() {
        ClassMember::Constructor(_)
        | ClassMember::StaticBlock(_)
        | ClassMember::IndexSignature(_)
        | ClassMember::Missing(_)
        | ClassMember::Semicolon => DeclIdentity::Anonymous,
        ClassMember::Method(method) => property_identity(&method.name, file),
        ClassMember::Property(property) => property_identity(&property.name, file),
        ClassMember::AutoAccessor(accessor) => property_identity(&accessor.name, file),
    };
    let raw = match member.data() {
        ClassMember::Method(method) => rebuild_children(
            file,
            member.range(),
            function_like_children(&method.function),
        ),
        ClassMember::Property(property) => {
            let Some(annotation) = &property.type_annotation else {
                return (identity, slice_node(file, member.range()));
            };
            replace_type_child(file, member.range(), &annotation.data().type_node)
        }
        ClassMember::AutoAccessor(accessor) => {
            let Some(annotation) = &accessor.type_annotation else {
                return (identity, slice_node(file, member.range()));
            };
            replace_type_child(file, member.range(), &annotation.data().type_node)
        }
        ClassMember::IndexSignature(index) => {
            let mut children: Vec<&Ty> = Vec::new();
            for parameter in &index.parameters {
                if let Some(annotation) = &parameter.data().type_annotation {
                    children.push(&*annotation.data().type_node);
                }
            }
            children.push(&*index.type_annotation.data().type_node);
            rebuild_children(file, member.range(), children)
        }
        ClassMember::Constructor(_)
        | ClassMember::StaticBlock(_)
        | ClassMember::Missing(_)
        | ClassMember::Semicolon => slice_node(file, member.range()),
    };
    (identity, raw)
}

/// Ordered type children of a function-like declaration: type-parameter
/// constraints/defaults, parameter annotations, then the return annotation.
fn function_like_children(function: &FunctionLike) -> Vec<&Ty> {
    let mut children = type_parameter_children(function.type_parameters.as_ref());
    for parameter in &function.parameters {
        if let Some(annotation) = &parameter.data().type_annotation {
            children.push(&*annotation.data().type_node);
        }
    }
    if let Some(return_type) = &function.return_type {
        children.push(&*return_type.data().type_node);
    }
    children
}

/// Replaces the single child type inside `range` with its canonical form so
/// nested object-type members canonicalize wherever they appear.
fn replace_type_child(file: &SourceFile, range: TextRange, child: &Ty) -> String {
    let head = slice_range(file, range.start(), child.range().start());
    let tail = slice_range(file, child.range().end(), range.end());
    assemble(&[head, canonical_type(child, file), tail])
}

/// Replaces a string-literal child with normalized (unquoted) text so quote
/// style is formatting-only.
fn replace_string_child(
    file: &SourceFile,
    range: TextRange,
    literal: &StringLiteralNode,
    replacement: &str,
) -> String {
    let head = slice_range(file, range.start(), literal.range().start());
    let tail = slice_range(file, literal.range().end(), range.end());
    assemble(&[head, replacement.to_owned(), tail])
}

/// Canonicalizes a type node: object-type member lists are grouped and sorted
/// by the declaration rule; every other AST `Vec` (union/intersection
/// constituents, tuple elements, parameters, type arguments, heritage, enum
/// members) keeps source order because order is semantic there.
fn canonical_type(ty: &Ty, file: &SourceFile) -> String {
    let range = ty.range();
    match ty.data() {
        TypeNode::Object(object) => {
            let members = canonical_type_members(&object.members, file);
            let head = declaration_head(file, range, &object.members, Vec::new());
            assemble_member_container(file, range, &object.members, members, head)
        }
        TypeNode::Union(types) => rebuild_children(file, range, types.iter().collect()),
        TypeNode::Intersection(types) => rebuild_children(file, range, types.iter().collect()),
        TypeNode::Array(inner) => rebuild_children(file, range, vec![&**inner]),
        TypeNode::Parenthesized(inner) => rebuild_children(file, range, vec![&**inner]),
        TypeNode::Tuple(tuple) => rebuild_children(
            file,
            range,
            tuple
                .elements
                .iter()
                .map(|element| &*element.type_node)
                .collect(),
        ),
        TypeNode::Function(function) => function_type_children(file, range, function),
        TypeNode::Constructor(construct) => {
            function_type_children(file, range, &construct.function)
        }
        TypeNode::Reference(reference) => {
            type_argument_children(file, range, reference.type_arguments.as_ref())
        }
        TypeNode::Query(query) => {
            type_argument_children(file, range, query.type_arguments.as_ref())
        }
        TypeNode::Operator { operand, .. } => rebuild_children(file, range, vec![&**operand]),
        TypeNode::IndexedAccess(access) => {
            rebuild_children(file, range, vec![&*access.object_type, &*access.index_type])
        }
        TypeNode::Conditional(conditional) => rebuild_children(
            file,
            range,
            vec![
                &*conditional.check_type,
                &*conditional.extends_type,
                &*conditional.true_type,
                &*conditional.false_type,
            ],
        ),
        TypeNode::Mapped(mapped) => {
            let mut children: Vec<&Ty> = Vec::new();
            if let Some(constraint) = &mapped.parameter.data().constraint {
                children.push(&**constraint);
            }
            if let Some(name) = &mapped.name_type {
                children.push(&**name);
            }
            if let Some(value) = &mapped.value_type {
                children.push(&**value);
            }
            rebuild_children(file, range, children)
        }
        TypeNode::Infer(infer) => match &infer.parameter.data().constraint {
            Some(constraint) => rebuild_children(file, range, vec![&**constraint]),
            None => slice_node(file, range),
        },
        TypeNode::Import(import) => {
            type_argument_children(file, range, import.type_arguments.as_ref())
        }
        TypeNode::TemplateLiteral(template) => {
            rebuild_children(file, range, template.types.iter().collect())
        }
        TypeNode::Predicate(predicate) => match &predicate.type_node {
            Some(inner) => rebuild_children(file, range, vec![&**inner]),
            None => slice_node(file, range),
        },
        TypeNode::Keyword(_) | TypeNode::Literal(_) | TypeNode::This | TypeNode::Missing(_) => {
            slice_node(file, range)
        }
    }
}

fn function_type_children(file: &SourceFile, range: TextRange, function: &FunctionType) -> String {
    let mut children: Vec<&Ty> = type_parameter_children(function.type_parameters.as_ref());
    children.extend(
        function
            .parameters
            .iter()
            .map(|parameter| &*parameter.type_annotation.data().type_node),
    );
    children.push(&*function.return_type);
    rebuild_children(file, range, children)
}

fn type_parameter_children(parameters: Option<&TypeParameterList>) -> Vec<&Ty> {
    let mut children = Vec::new();
    let Some(parameters) = parameters else {
        return children;
    };
    for parameter in &parameters.parameters {
        if let Some(constraint) = &parameter.data().constraint {
            children.push(&**constraint);
        }
        if let Some(default) = &parameter.data().default {
            children.push(&**default);
        }
    }
    children
}

fn type_argument_children(
    file: &SourceFile,
    range: TextRange,
    arguments: Option<&TypeArgumentList>,
) -> String {
    match arguments {
        Some(arguments) => rebuild_children(file, range, arguments.arguments.iter().collect()),
        None => slice_node(file, range),
    }
}

/// Rebuilds `range`'s source text with every child type replaced by its
/// canonical form, preserving ordered children and the gaps between them.
fn rebuild_children(file: &SourceFile, range: TextRange, children: Vec<&Ty>) -> String {
    if children.is_empty() {
        return slice_node(file, range);
    }
    let mut parts: Vec<String> = Vec::new();
    let mut cursor = range.start();
    for child in children {
        parts.push(slice_range(file, cursor, child.range().start()));
        parts.push(canonical_type(child, file));
        cursor = child.range().end();
    }
    parts.push(slice_range(file, cursor, range.end()));
    assemble(&parts)
}

/// One record in a structural baseline section, positioned by indentation.
struct BaselineRecord {
    identity: DeclIdentity,
    content: String,
    children: Vec<BaselineRecord>,
}

/// Canonicalizes a `.types`/`.symbols` baseline. Section headers stay in
/// source order. Within each section, records form an indentation tree whose
/// children are grouped and sorted only when every identity is a distinct
/// simple name; all other order is preserved.
fn canonicalize_record_baseline(
    text: &str,
    is_section_header: fn(&str) -> bool,
    record_of: fn(&str) -> Option<(usize, DeclIdentity, String)>,
) -> Vec<String> {
    let mut canonical: Vec<String> = Vec::new();
    let mut records: Vec<(usize, DeclIdentity, String)> = Vec::new();
    let flush = |canonical: &mut Vec<String>, records: &mut Vec<(usize, DeclIdentity, String)>| {
        let mut tree: Vec<(DeclIdentity, String)> = build_baseline_tree(records)
            .iter()
            .map(|node| (node.identity.clone(), canonical_baseline_node(node)))
            .collect();
        records.clear();
        sort_declaration_groups(&mut tree);
        for (_, content) in tree {
            canonical.push(content);
        }
    };
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if is_section_header(trimmed) {
            flush(&mut canonical, &mut records);
            canonical.push(normalize_record_line(trimmed));
        } else if let Some(record) = record_of(line) {
            records.push(record);
        } else {
            // An unrecognized display line acts as an order barrier.
            flush(&mut canonical, &mut records);
            canonical.push(normalize_record_line(trimmed));
        }
    }
    flush(&mut canonical, &mut records);
    canonical
}

fn build_baseline_tree(records: &[(usize, DeclIdentity, String)]) -> Vec<BaselineRecord> {
    struct Node {
        indent: usize,
        identity: DeclIdentity,
        content: String,
        parent: Option<usize>,
        children: Vec<usize>,
    }
    let mut nodes: Vec<Node> = Vec::new();
    let mut stack: Vec<usize> = Vec::new();
    for (indent, identity, content) in records {
        while stack
            .last()
            .is_some_and(|&top| nodes[top].indent >= *indent)
        {
            stack.pop();
        }
        let index = nodes.len();
        let parent = stack.last().copied();
        nodes.push(Node {
            indent: *indent,
            identity: identity.clone(),
            content: content.clone(),
            parent,
            children: Vec::new(),
        });
        if let Some(parent) = parent {
            nodes[parent].children.push(index);
        }
        stack.push(index);
    }
    fn convert(nodes: &[Node], index: usize) -> BaselineRecord {
        BaselineRecord {
            identity: nodes[index].identity.clone(),
            content: nodes[index].content.clone(),
            children: nodes[index]
                .children
                .iter()
                .map(|&child| convert(nodes, child))
                .collect(),
        }
    }
    (0..nodes.len())
        .filter(|&index| nodes[index].parent.is_none())
        .map(|index| convert(&nodes, index))
        .collect()
}

fn canonical_baseline_node(node: &BaselineRecord) -> String {
    let mut children: Vec<(DeclIdentity, String)> = node
        .children
        .iter()
        .map(|child| (child.identity.clone(), canonical_baseline_node(child)))
        .collect();
    sort_declaration_groups(&mut children);
    let mut out = normalize_record_line(&strip_comments(&node.content));
    for (_, child) in children {
        out.push('\n');
        out.push_str(&child);
    }
    out
}

fn is_types_section(line: &str) -> bool {
    let trimmed = line.trim();
    trimmed.starts_with("===") && trimmed.ends_with("===")
}

fn types_record(line: &str) -> Option<(usize, DeclIdentity, String)> {
    let trimmed = line.trim_start();
    let after_marker = trimmed.strip_prefix('>')?;
    let content = after_marker.trim_start();
    if content.is_empty() {
        return None;
    }
    // Indentation is the whitespace before `>` plus the whitespace after it, so
    // `>   memberA` nests under a `> type T = {` owner exactly like tsc emits.
    let indent = leading_indent(trimmed) + leading_indent(after_marker);
    Some((indent, types_record_identity(content), content.to_owned()))
}

/// The declared identity of a `.types` display record: the first identifier
/// after an optional declaration keyword, so `> var x: number` and
/// `> function f(...)` identify as `x` and `f` and overloads merge. A trailing
/// `:` is stripped so `x:` and `x :` formatting both identify as `x` and stay
/// one merge group.
fn types_record_identity(content: &str) -> DeclIdentity {
    let mut words = content.split_whitespace();
    let Some(first) = words.next() else {
        return DeclIdentity::Anonymous;
    };
    let name = if is_declaration_keyword(first) {
        words.next().unwrap_or("")
    } else {
        first
    };
    // Cut parameter lists so every overload of `f` identifies as `f` and stays
    // one source-ordered merge group: `f(a:` and `f(b:` both reduce to `f`.
    let name = name.split('(').next().unwrap_or("").trim_end_matches(':');
    if name.is_empty() {
        DeclIdentity::Anonymous
    } else {
        DeclIdentity::Simple(name.to_owned())
    }
}

fn is_declaration_keyword(word: &str) -> bool {
    matches!(
        word,
        "var"
            | "let"
            | "const"
            | "function"
            | "class"
            | "interface"
            | "type"
            | "enum"
            | "namespace"
            | "module"
            | "declare"
            | "export"
            | "default"
            | "abstract"
            | "async"
            | "readonly"
            | "static"
            | "get"
            | "set"
            | "accessor"
            | "new"
            | "method"
            | "property"
            | "constructor"
            | "import"
            | "from"
    )
}

fn is_symbols_section(line: &str) -> bool {
    let trimmed = line.trim();
    trimmed.starts_with('[') && trimmed.ends_with(']')
}

fn symbols_record(line: &str) -> Option<(usize, DeclIdentity, String)> {
    let indent = leading_indent(line);
    let content = line.trim_start();
    if content.starts_with('[') && content.ends_with(']') {
        return None;
    }
    let (name, _) = content.split_once(" : ")?;
    let name = name.trim();
    if name.is_empty() {
        return None;
    }
    Some((
        indent,
        DeclIdentity::Simple(name.to_owned()),
        content.to_owned(),
    ))
}

fn normalize_block_lines(text: &str) -> String {
    text.lines()
        .map(normalize_record_line)
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>()
        .join("\n")
}

fn normalize_record_line(line: &str) -> String {
    let mut output = String::new();
    let mut chars = line.char_indices().peekable();
    while let Some((start, ch)) = chars.next() {
        if ch.is_whitespace() {
            continue;
        }
        let end = if matches!(ch, '"' | '\'' | '`') {
            string_token_end(line, &mut chars, ch)
        } else if ch.is_ascii_digit() {
            number_token_end(line, &mut chars)
        } else if is_identifier_char(ch) {
            token_end(line, &mut chars, is_identifier_char)
        } else {
            punctuation_token_end(line, start, ch, &mut chars)
        };
        let token = &line[start..end];
        output.push_str(&token.len().to_string());
        output.push(':');
        output.push_str(token);
        output.push('|');
    }
    output
}

fn string_token_end(
    line: &str,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
    quote: char,
) -> usize {
    let mut escaped = false;
    for (index, ch) in chars.by_ref() {
        if escaped {
            escaped = false;
            continue;
        }
        if ch == '\\' {
            escaped = true;
        } else if ch == quote {
            return index + ch.len_utf8();
        }
    }
    line.len()
}

fn number_token_end(
    line: &str,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> usize {
    let mut end = line.len();
    let mut exponent = false;
    while let Some(&(index, ch)) = chars.peek() {
        let continues = ch.is_ascii_alphanumeric()
            || matches!(ch, '_' | '.')
            || (exponent && matches!(ch, '+' | '-'));
        if !continues {
            end = index;
            break;
        }
        exponent = matches!(ch, 'e' | 'E');
        chars.next();
    }
    end
}

fn punctuation_token_end(
    line: &str,
    start: usize,
    first: char,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> usize {
    // `>>`/`>>>` are deliberately absent: the parser splits them in type
    // context, so `A<B<C>>` and `A<B<C> >` are both valid and must normalize
    // to the same two `>` tokens. `>>=` stays compound because it only occurs
    // as a single operator in expressions.
    const COMPOUND: &[&str] = &[
        ">>>=", "===", "!==", "<<=", ">>=", "**=", "&&=", "||=", "??=", "...", "=>", "==", "!=",
        "<=", ">=", "++", "--", "&&", "||", "??", "?.", "**", "<<", "+=", "-=", "*=", "/=", "%=",
        "&=", "|=", "^=", "</", "/>",
    ];
    let remainder = &line[start..];
    let length = COMPOUND
        .iter()
        .find(|token| remainder.starts_with(**token))
        .map_or(first.len_utf8(), |token| token.len());
    let end = start + length;
    while chars.peek().is_some_and(|(index, _)| *index < end) {
        chars.next();
    }
    end
}

fn token_end(
    line: &str,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
    continues: fn(char) -> bool,
) -> usize {
    let mut end = line.len();
    while let Some(&(index, ch)) = chars.peek() {
        if !continues(ch) {
            end = index;
            break;
        }
        chars.next();
    }
    end
}

fn is_identifier_char(ch: char) -> bool {
    ch.is_alphanumeric() || matches!(ch, '_' | '$') || !ch.is_ascii()
}

fn leading_indent(line: &str) -> usize {
    line.chars()
        .take_while(|ch| *ch == ' ' || *ch == '\t')
        .map(|ch| if ch == '\t' { 4 } else { 1 })
        .sum()
}

fn strip_comments(text: &str) -> String {
    let mut output = String::with_capacity(text.len());
    let bytes = text.as_bytes();
    let mut index = 0;
    let mut in_line_comment = false;
    let mut in_block_comment = false;
    let mut in_string: Option<u8> = None;

    while index < bytes.len() {
        let byte = bytes[index];
        if in_line_comment {
            if byte == b'\n' {
                in_line_comment = false;
                output.push('\n');
            }
            index += 1;
            continue;
        }
        if in_block_comment {
            if byte == b'*' && index + 1 < bytes.len() && bytes[index + 1] == b'/' {
                in_block_comment = false;
                index += 2;
                continue;
            }
            if byte == b'\n' {
                output.push('\n');
            }
            index += 1;
            continue;
        }
        if let Some(quote) = in_string {
            output.push(byte as char);
            if byte == b'\\' && index + 1 < bytes.len() {
                output.push(bytes[index + 1] as char);
                index += 2;
                continue;
            }
            if byte == quote {
                in_string = None;
            }
            index += 1;
            continue;
        }

        if byte == b'"' || byte == b'\'' || byte == b'`' {
            in_string = Some(byte);
            output.push(byte as char);
            index += 1;
            continue;
        }
        if byte == b'/' && index + 1 < bytes.len() {
            match bytes[index + 1] {
                b'/' => {
                    // Every line comment is stripped, including triple-slash
                    // directives: only the file prologue carries semantic
                    // directives, and `triple_slash_directives` collects those
                    // from the raw text separately. A directive outside the
                    // prologue is inert and must not leak into the canonical
                    // form.
                    in_line_comment = true;
                    index += 2;
                    continue;
                }
                b'*' => {
                    in_block_comment = true;
                    index += 2;
                    continue;
                }
                _ => {}
            }
        }
        output.push(byte as char);
        index += 1;
    }

    output
}

fn is_semantic_triple_slash_directive(comment: &str) -> bool {
    let Some(reference) = comment
        .trim()
        .strip_prefix("///")
        .map(str::trim)
        .and_then(|body| body.strip_prefix("<reference"))
    else {
        return false;
    };
    if !reference.starts_with(char::is_whitespace) || !reference.trim_end().ends_with("/>") {
        return false;
    }
    ["path", "types", "lib", "no-default-lib"]
        .iter()
        .any(|attribute| {
            reference.match_indices(attribute).any(|(index, _)| {
                reference[..index]
                    .chars()
                    .next_back()
                    .is_some_and(char::is_whitespace)
                    && reference[index + attribute.len()..]
                        .trim_start()
                        .starts_with('=')
            })
        })
}
