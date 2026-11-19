use std::fmt::Write as _;

use super::binder::{FunctionSignature, ObjectType, PropertyType};
use super::{SemanticModel, SymbolId, Type, TypeId};
use crate::literal::number_value;
use bamts_bytecode::{EcmaString, format_number};
/// Renders an interned type as its canonical TypeScript display string.
#[must_use]
pub fn render_type(model: &SemanticModel, type_id: TypeId) -> String {
    let mut visiting_aliases = Vec::new();
    render_type_grouped(model, type_id, false, &mut visiting_aliases)
}

/// Renders an interned type as a declaration-emit string.
///
/// Like [`render_type`] but formats object types with multiple members across
/// multiple lines (indented by `indent` spaces), matching tsc's `.d.ts`
/// output for synthesized types. Single call/construct signatures keep the
/// inline arrow form.
#[must_use]
pub fn render_type_declaration(model: &SemanticModel, type_id: TypeId, indent: usize) -> String {
    let mut visiting_aliases = Vec::new();
    render_type_declaration_grouped(model, type_id, false, indent, &mut visiting_aliases)
}

/// An inline type rendering alongside the caret-blank spans inside it, in
/// byte offsets. Blanks mark printed text that reproduces a written type
/// annotation (a declared parameter, return, constraint, default, or member
/// type) or a function parameter name; everything else takes carets.
struct AnnotatedType {
    text: String,
    blanks: Vec<(usize, usize)>,
}

impl AnnotatedType {
    fn push(&mut self, text: &str) {
        self.text.push_str(text);
    }

    fn push_blank(&mut self, text: &str) {
        let start = self.text.len();
        self.text.push_str(text);
        self.blanks.push((start, self.text.len()));
    }
}

fn push_blank_rendered(
    out: &mut AnnotatedType,
    model: &SemanticModel,
    type_id: TypeId,
    group: bool,
    visiting_aliases: &mut Vec<SymbolId>,
) {
    let start = out.text.len();
    render_annotated_into(out, model, type_id, group, visiting_aliases);
    out.blanks.push((start, out.text.len()));
}

/// Renders an interned type as its canonical TypeScript display string and
/// yields the caret-blank spans for `.types` baselines.
#[must_use]
pub fn render_type_annotated(
    model: &SemanticModel,
    type_id: TypeId,
) -> (String, Vec<(usize, usize)>) {
    let mut out = AnnotatedType {
        text: String::new(),
        blanks: Vec::new(),
    };
    let mut visiting_aliases = Vec::new();
    render_annotated_into(&mut out, model, type_id, false, &mut visiting_aliases);
    (out.text, out.blanks)
}

fn render_type_grouped(
    model: &SemanticModel,
    type_id: TypeId,
    group: bool,
    visiting_aliases: &mut Vec<SymbolId>,
) -> String {
    let mut out = AnnotatedType {
        text: String::new(),
        blanks: Vec::new(),
    };
    render_annotated_into(&mut out, model, type_id, group, visiting_aliases);
    out.text
}

fn render_annotated_into(
    out: &mut AnnotatedType,
    model: &SemanticModel,
    type_id: TypeId,
    group: bool,
    visiting_aliases: &mut Vec<SymbolId>,
) {
    match model.types().get(type_id) {
        Type::Error | Type::Any => out.push("any"),
        Type::Unknown => out.push("unknown"),
        Type::Never => out.push("never"),
        Type::Void => out.push("void"),
        Type::Null => out.push("null"),
        Type::Undefined => out.push("undefined"),
        Type::Boolean => out.push("boolean"),
        Type::Number => out.push("number"),
        Type::BigInt => out.push("bigint"),
        Type::String => out.push("string"),
        Type::Symbol => out.push("symbol"),
        Type::Object => out.push("object"),
        Type::BooleanLiteral(value) => out.push(if *value { "true" } else { "false" }),
        Type::NumberLiteral(text) => out.push(&render_number_literal(text)),
        Type::BigIntLiteral(text) => out.push(text),
        Type::StringLiteral(text) => out.push(&render_string_literal(text)),
        Type::Array(element) => {
            render_annotated_into(out, model, *element, true, visiting_aliases);
            out.push("[]");
        }
        Type::Tuple(shape) => {
            out.push("[");
            let mut first = true;
            for (index, element) in shape.prefix.iter().enumerate() {
                if !first {
                    out.push(", ");
                }
                first = false;
                let optional = index >= usize::try_from(shape.required).expect("tuple length fits");
                render_annotated_into(out, model, *element, optional, visiting_aliases);
                if optional {
                    out.push("?");
                }
            }
            if let Some(rest) = shape.rest {
                if !first {
                    out.push(", ");
                }
                first = false;
                out.push("...");
                render_annotated_into(out, model, rest, true, visiting_aliases);
                out.push("[]");
            }
            for element in shape.suffix.iter() {
                if !first {
                    out.push(", ");
                }
                first = false;
                render_annotated_into(out, model, *element, false, visiting_aliases);
            }
            out.push("]");
        }
        Type::Union(members) => {
            if group {
                out.push("(");
            }
            join_annotated(out, model, members, true, " | ", visiting_aliases);
            if group {
                out.push(")");
            }
        }
        Type::Intersection(members) => {
            if group {
                out.push("(");
            }
            join_annotated(out, model, members, true, " & ", visiting_aliases);
            if group {
                out.push(")");
            }
        }
        Type::Function(signature) => {
            if group {
                out.push("(");
            }
            render_signature_into(out, model, signature, " => ", visiting_aliases);
            if group {
                out.push(")");
            }
        }
        Type::ObjectType(object) => render_object_into(out, model, object, visiting_aliases),
        Type::AppliedClass { symbol, arguments } => {
            let name = model.symbol(*symbol).name();
            if arguments.is_empty() {
                out.push(name);
            } else {
                out.push(name);
                out.push("<");
                join_annotated(out, model, arguments, false, ", ", visiting_aliases);
                out.push(">");
            }
        }
        Type::AppliedAlias { symbol, arguments } => {
            if arguments.is_empty()
                && model.types().has_alias(*symbol)
                && model.types().alias_type_parameters(*symbol).is_empty()
            {
                out.push(model.symbol(*symbol).name());
                return;
            }
            // A reference whose target mentions its type parameters keeps its
            // written `Name<args>` form (tsc prints `Pair<string>`, never
            // `[string, string]`); a reference whose target ignores them
            // (e.g. `type Strange<T> = string`) renders as its view, which
            // tsc prints as `string`. Baseline proof:
            // `genericTypeAliases.types` rows `>tree : Tree<number>`,
            // `>ls : Lazy<string>`, `>x : Foo<string>` against `>s : string`.
            let aligned = !arguments.is_empty()
                && arguments.len() == model.types().alias_type_parameters(*symbol).len();
            if aligned
                && !visiting_aliases.contains(symbol)
                && model.types().alias_target_uses_parameters(*symbol)
            {
                out.push(model.symbol(*symbol).name());
                out.push("<");
                join_annotated(out, model, arguments, false, ", ", visiting_aliases);
                out.push(">");
            } else if !visiting_aliases.contains(symbol)
                && let Some(view) = model.types().applied_alias_view(type_id)
            {
                visiting_aliases.push(*symbol);
                render_annotated_into(out, model, view, group, visiting_aliases);
                visiting_aliases.pop();
            } else {
                let name = model.symbol(*symbol).name();
                if arguments.is_empty() {
                    out.push(name);
                } else {
                    out.push(name);
                    out.push("<");
                    join_annotated(out, model, arguments, false, ", ", visiting_aliases);
                    out.push(">");
                }
            }
        }
        Type::TypeQuery {
            name, arguments, ..
        } => {
            if group {
                out.push("(");
            }
            out.push("typeof ");
            out.push(name);
            if !arguments.is_empty() {
                out.push("<");
                for (index, argument) in arguments.iter().enumerate() {
                    if index > 0 {
                        out.push(", ");
                    }
                    render_annotated_into(out, model, *argument, false, visiting_aliases);
                }
                out.push(">");
            }
            if group {
                out.push(")");
            }
        }
        Type::Keyof(operand) => {
            if group {
                out.push("(");
            }
            out.push("keyof ");
            render_annotated_into(out, model, *operand, true, visiting_aliases);
            if group {
                out.push(")");
            }
        }
        Type::IndexedAccess { object, index } => {
            render_annotated_into(out, model, *object, true, visiting_aliases);
            out.push("[");
            render_annotated_into(out, model, *index, false, visiting_aliases);
            out.push("]");
        }
        Type::Record { key, value } => {
            out.push("Record<");
            render_annotated_into(out, model, *key, false, visiting_aliases);
            out.push(", ");
            render_annotated_into(out, model, *value, false, visiting_aliases);
            out.push(">");
        }
        Type::This { .. } => out.push("this"),
        Type::EnumMember {
            enum_symbol,
            member_symbol,
            ..
        } => {
            let enum_name = model.symbol(*enum_symbol).name();
            let member_name = model.symbol(*member_symbol).name();
            out.push(&format!("{enum_name}.{member_name}"));
        }
        Type::Named(symbol) | Type::NumericEnum(symbol) => {
            out.push(model.symbol(*symbol).name());
        }
        Type::ConstructorType {
            symbol, arguments, ..
        } => {
            let name = model.symbol(*symbol).name();
            if arguments.is_empty() {
                out.push(&format!("typeof {name}"));
            } else {
                out.push(&format!("typeof {name}<"));
                join_annotated(out, model, arguments, false, ", ", visiting_aliases);
                out.push(">");
            }
        }
    }
}

fn join_annotated(
    out: &mut AnnotatedType,
    model: &SemanticModel,
    members: &[TypeId],
    group: bool,
    separator: &str,
    visiting_aliases: &mut Vec<SymbolId>,
) {
    for (index, member) in members.iter().enumerate() {
        if index > 0 {
            out.push(separator);
        }
        render_annotated_into(out, model, *member, group, visiting_aliases);
    }
}

fn render_type_declaration_grouped(
    model: &SemanticModel,
    type_id: TypeId,
    group: bool,
    indent: usize,
    visiting_aliases: &mut Vec<SymbolId>,
) -> String {
    match model.types().get(type_id) {
        Type::ObjectType(object) => {
            render_object_type_declaration(model, object, indent, visiting_aliases)
        }
        Type::Function(signature) => {
            let body =
                render_signature_declaration(model, signature, " => ", indent, visiting_aliases);
            if group { format!("({body})") } else { body }
        }
        Type::Union(members) => {
            let body = members
                .iter()
                .map(|member| {
                    render_type_declaration_grouped(model, *member, true, indent, visiting_aliases)
                })
                .collect::<Vec<_>>()
                .join(" | ");
            if group { format!("({body})") } else { body }
        }
        Type::Intersection(members) => {
            let body = members
                .iter()
                .map(|member| {
                    render_type_declaration_grouped(model, *member, true, indent, visiting_aliases)
                })
                .collect::<Vec<_>>()
                .join(" & ");
            if group { format!("({body})") } else { body }
        }
        Type::Array(element) => format!(
            "{}[]",
            render_type_declaration_grouped(model, *element, true, indent, visiting_aliases)
        ),
        Type::Tuple(shape) => {
            let mut elements = Vec::with_capacity(
                shape.prefix.len() + usize::from(shape.rest.is_some()) + shape.suffix.len(),
            );
            elements.extend(shape.prefix.iter().enumerate().map(|(index, element)| {
                let optional = index >= usize::try_from(shape.required).expect("tuple length fits");
                let rendered = render_type_declaration_grouped(
                    model,
                    *element,
                    optional,
                    indent,
                    visiting_aliases,
                );
                if optional {
                    format!("{rendered}?")
                } else {
                    rendered
                }
            }));
            if let Some(rest) = shape.rest {
                elements.push(format!(
                    "...{}[]",
                    render_type_declaration_grouped(model, rest, true, indent, visiting_aliases)
                ));
            }
            elements.extend(shape.suffix.iter().map(|element| {
                render_type_declaration_grouped(model, *element, false, indent, visiting_aliases)
            }));
            format!("[{}]", elements.join(", "))
        }
        // For all other type kinds, delegate to the inline renderer.
        _ => render_type_grouped(model, type_id, group, visiting_aliases),
    }
}

fn render_signature_declaration(
    model: &SemanticModel,
    signature: &FunctionSignature,
    return_separator: &str,
    indent: usize,
    visiting_aliases: &mut Vec<SymbolId>,
) -> String {
    let type_params = if signature.type_parameters().is_empty() {
        String::new()
    } else {
        let names = signature
            .type_parameters()
            .iter()
            .zip(signature.type_parameter_bounds())
            .map(|(symbol, bounds)| {
                let mut rendered = model.symbol(*symbol).name().to_owned();
                if let Some(constraint) = bounds.constraint() {
                    rendered.push_str(" extends ");
                    rendered.push_str(&render_type_declaration_grouped(
                        model,
                        constraint,
                        false,
                        indent,
                        visiting_aliases,
                    ));
                }
                if let Some(default) = bounds.default() {
                    rendered.push_str(" = ");
                    rendered.push_str(&render_type_declaration_grouped(
                        model,
                        default,
                        false,
                        indent,
                        visiting_aliases,
                    ));
                }
                rendered
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!("<{names}>")
    };
    let params = signature
        .parameters()
        .iter()
        .map(|param| {
            format!(
                "{}{}{}: {}",
                if param.rest() { "..." } else { "" },
                param.name(),
                if param.optional() { "?" } else { "" },
                render_type_declaration_grouped(
                    model,
                    param.type_id(),
                    false,
                    indent,
                    visiting_aliases
                )
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    let displayed_return = signature
        .declared_return()
        .unwrap_or(signature.return_type());
    format!(
        "{type_params}({params}){return_separator}{}",
        render_type_declaration_grouped(model, displayed_return, false, indent, visiting_aliases)
    )
}

fn render_object_type_declaration(
    model: &SemanticModel,
    object: &ObjectType,
    indent: usize,
    visiting_aliases: &mut Vec<SymbolId>,
) -> String {
    // Single call/construct signature with no properties or index signatures
    // stays inline (arrow form), matching tsc's declaration output.
    if object.properties.is_empty()
        && object.index_signatures.is_empty()
        && object.call_signatures.len() + object.construct_signatures.len() == 1
    {
        if let Some(signature) = object.call_signatures.first() {
            return render_signature_declaration(
                model,
                signature,
                " => ",
                indent,
                visiting_aliases,
            );
        }
        if let Some(entry) = object.construct_signatures.first() {
            return format!(
                "{}new {}",
                if entry.is_abstract { "abstract " } else { "" },
                render_signature_declaration(
                    model,
                    &entry.signature,
                    " => ",
                    indent,
                    visiting_aliases
                )
            );
        }
    }

    let inner_indent = indent + 4;
    let pad = " ".repeat(inner_indent);
    let close_pad = " ".repeat(indent);

    let mut members = Vec::with_capacity(
        object.call_signatures.len()
            + object.construct_signatures.len()
            + object.index_signatures.len()
            + object.properties.len(),
    );
    members.extend(object.call_signatures.iter().map(|signature| {
        render_signature_declaration(model, signature, ": ", inner_indent, visiting_aliases)
    }));
    members.extend(object.construct_signatures.iter().map(|entry| {
        format!(
            "{}new {}",
            if entry.is_abstract { "abstract " } else { "" },
            render_signature_declaration(
                model,
                &entry.signature,
                ": ",
                inner_indent,
                visiting_aliases
            )
        )
    }));
    members.extend(object.index_signatures.iter().map(|signature| {
        let parameters = signature
            .parameters
            .iter()
            .map(|parameter| {
                format!(
                    "{}: {}",
                    parameter.name(),
                    render_type_declaration_grouped(
                        model,
                        parameter.type_id(),
                        false,
                        inner_indent,
                        visiting_aliases
                    )
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "{}[{parameters}]: {}",
            if signature.readonly { "readonly " } else { "" },
            render_type_declaration_grouped(
                model,
                signature.value_type,
                false,
                inner_indent,
                visiting_aliases
            )
        )
    }));
    members.extend(object.properties.iter().map(|property| {
        render_property_declaration(model, property, inner_indent, visiting_aliases)
    }));
    if members.is_empty() {
        "{}".to_owned()
    } else {
        let body = members
            .iter()
            .map(|m| format!("{pad}{m};"))
            .collect::<Vec<_>>()
            .join("\n");
        format!("{{\n{body}\n{close_pad}}}")
    }
}

fn render_signature_into(
    out: &mut AnnotatedType,
    model: &SemanticModel,
    signature: &FunctionSignature,
    return_separator: &str,
    visiting_aliases: &mut Vec<SymbolId>,
) {
    if !signature.type_parameters().is_empty() {
        out.push("<");
        for (index, (symbol, bounds)) in signature
            .type_parameters()
            .iter()
            .zip(signature.type_parameter_bounds())
            .enumerate()
        {
            if index > 0 {
                out.push(", ");
            }
            out.push_blank(model.symbol(*symbol).name());
            if let Some(constraint) = bounds.constraint() {
                out.push(" extends ");
                push_blank_rendered(out, model, constraint, false, visiting_aliases);
            }
            if let Some(default) = bounds.default() {
                out.push(" = ");
                push_blank_rendered(out, model, default, false, visiting_aliases);
            }
        }
        out.push(">");
    }
    out.push("(");
    for (index, parameter) in signature.parameters().iter().enumerate() {
        if index > 0 {
            out.push(", ");
        }
        if parameter.rest() {
            out.push("...");
        }
        out.push_blank(parameter.name());
        if parameter.optional() {
            out.push("?");
        }
        out.push(": ");
        if parameter.declared() {
            push_blank_rendered(out, model, parameter.type_id(), false, visiting_aliases);
        } else {
            render_annotated_into(out, model, parameter.type_id(), false, visiting_aliases);
        }
    }
    out.push(")");
    out.push(return_separator);
    let displayed = signature
        .declared_return()
        .unwrap_or(signature.return_type());
    if signature.declared_return().is_some() {
        push_blank_rendered(out, model, displayed, false, visiting_aliases);
    } else {
        render_annotated_into(out, model, displayed, false, visiting_aliases);
    }
}

fn render_object_into(
    out: &mut AnnotatedType,
    model: &SemanticModel,
    object: &ObjectType,
    visiting_aliases: &mut Vec<SymbolId>,
) {
    if object.properties.is_empty()
        && object.index_signatures.is_empty()
        && object.call_signatures.len() + object.construct_signatures.len() == 1
    {
        if let Some(signature) = object.call_signatures.first() {
            render_signature_into(out, model, signature, " => ", visiting_aliases);
            return;
        }
        if let Some(entry) = object.construct_signatures.first() {
            if entry.is_abstract {
                out.push("abstract ");
            }
            out.push("new ");
            render_signature_into(out, model, &entry.signature, " => ", visiting_aliases);
            return;
        }
    }

    let start = out.text.len();
    out.push("{ ");
    let mut first = true;
    for signature in &object.call_signatures {
        if !first {
            out.push("; ");
        }
        first = false;
        render_signature_into(out, model, signature, ": ", visiting_aliases);
    }
    for entry in &object.construct_signatures {
        if !first {
            out.push("; ");
        }
        first = false;
        if entry.is_abstract {
            out.push("abstract ");
        }
        out.push("new ");
        render_signature_into(out, model, &entry.signature, ": ", visiting_aliases);
    }
    for signature in &object.index_signatures {
        if !first {
            out.push("; ");
        }
        first = false;
        if signature.readonly {
            out.push("readonly ");
        }
        out.push("[");
        for (index, parameter) in signature.parameters.iter().enumerate() {
            if index > 0 {
                out.push(", ");
            }
            out.push_blank(parameter.name());
            out.push(": ");
            render_annotated_into(out, model, parameter.type_id(), false, visiting_aliases);
        }
        out.push("]: ");
        render_annotated_into(out, model, signature.value_type, false, visiting_aliases);
    }
    for property in &object.properties {
        if !first {
            out.push("; ");
        }
        first = false;
        render_property_into(out, model, property, visiting_aliases);
    }
    if first {
        out.text.truncate(start);
        out.push("{}");
    } else {
        out.push("; }");
    }
}

/// Normalizes a numeric lexeme to tsc's canonical display form.
///
/// tsc renders number literal types via `ts.numberToString`, which parses
/// the value and emits the shortest decimal representation. Hex/octal/binary
/// prefixes, trailing `.0`, and integer-valued exponents all collapse to
/// the plain integer. A bare `0x` (no digits) is `NaN` in JS but tsc treats
/// it as `0` in the type position.
///
/// Baseline proof: `tests/baselines/reference/numericLiteralTypes1.types`
/// rows `>A2 : 1` (source `1.0`), `>A3 : 1` (source `1e0`), `>A4 : 1`
/// (source `10e-1`).
/// Counterexample checked: `tests/baselines/reference/literalTypes1.types`
/// row `>c2 : 100` (source `100`), confirming plain integers pass through.
fn render_number_literal(text: &str) -> String {
    match number_value(text) {
        Some(value) if value.is_finite() => {
            if value == 0.0 {
                "0".to_owned()
            } else if value == value.trunc() && value.abs() < 1e21 {
                format!("{value:.0}")
            } else {
                format_number(value)
            }
        }
        _ => text.to_owned(),
    }
}

/// Renders one property of an object type, choosing method shorthand
/// (`name(params): ret`) or property form (`name: type`) to match tsc.
///
/// tsc distinguishes method declarations (`method() { }`) from function-
/// expression properties (`prop: () => void`). Methods use the
/// `name(params): ret` shorthand; properties use `name: type`.
///
/// Baseline proof: `tests/baselines/reference/objectSpreadWithinMethodWithinObjectWithSpread.types`
/// row `>a : { prop(): { metadata: number; }; }` — `prop` is a method
/// shorthand, rendered with `()` not `: () =>`.
/// Counterexample checked: same baseline row `>p1 : () => void` inside the
/// object — `p1` is a function-expression property, rendered as `name: type`.
fn render_property_into(
    out: &mut AnnotatedType,
    model: &SemanticModel,
    property: &PropertyType,
    visiting_aliases: &mut Vec<SymbolId>,
) {
    if property.readonly() {
        out.push("readonly ");
    }
    out.push(property.name());
    if property.optional() {
        out.push("?");
    }
    if property.is_method()
        && let Type::Function(signature) = model.types().get(property.type_id())
    {
        render_signature_into(out, model, signature, ": ", visiting_aliases);
    } else {
        out.push(": ");
        if property.declared() {
            push_blank_rendered(out, model, property.type_id(), false, visiting_aliases);
        } else {
            render_annotated_into(out, model, property.type_id(), false, visiting_aliases);
        }
    }
}
#[cfg(test)]
fn render_signature(
    model: &SemanticModel,
    signature: &FunctionSignature,
    return_separator: &str,
    visiting_aliases: &mut Vec<SymbolId>,
) -> String {
    let mut out = AnnotatedType {
        text: String::new(),
        blanks: Vec::new(),
    };
    render_signature_into(
        &mut out,
        model,
        signature,
        return_separator,
        visiting_aliases,
    );
    out.text
}

/// Declaration-emit variant of [`render_property_into`], using the declaration
/// renderer for nested types and passing the indent context.
fn render_property_declaration(
    model: &SemanticModel,
    property: &PropertyType,
    indent: usize,
    visiting_aliases: &mut Vec<SymbolId>,
) -> String {
    let prefix = if property.readonly() { "readonly " } else { "" };
    let optional = if property.optional() { "?" } else { "" };
    if property.is_method()
        && let Type::Function(signature) = model.types().get(property.type_id())
    {
        let body = render_signature_declaration(model, signature, ": ", indent, visiting_aliases);
        format!("{prefix}{}{optional}{body}", property.name())
    } else {
        format!(
            "{prefix}{}{optional}: {}",
            property.name(),
            render_type_declaration_grouped(
                model,
                property.type_id(),
                false,
                indent,
                visiting_aliases
            )
        )
    }
}

fn render_string_literal(value: &EcmaString) -> String {
    let mut out = String::with_capacity(value.len_units() + 2);
    out.push('"');
    for (_, code_point) in value.code_points() {
        match char::from_u32(code_point) {
            Some('"') => out.push_str("\\\""),
            Some('\\') => out.push_str("\\\\"),
            Some('\n') => out.push_str("\\n"),
            Some('\t') => out.push_str("\\t"),
            Some('\r') => out.push_str("\\r"),
            Some('\u{0008}') => out.push_str("\\b"),
            Some('\u{000C}') => out.push_str("\\f"),
            Some('\u{000B}') => out.push_str("\\v"),
            Some(character) if character.is_control() && code_point < 0x20 => {
                write!(out, "\\u{code_point:04X}").expect("writing to String cannot fail");
            }
            Some('\u{2028}' | '\u{2029}') => {
                write!(out, "\\u{code_point:04X}").expect("writing to String cannot fail");
            }
            Some(character) => out.push(character),
            None => {
                write!(out, "\\u{code_point:04X}").expect("writing to String cannot fail");
            }
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::{
        render_signature, render_signature_declaration, render_string_literal, render_type,
        render_type_annotated, render_type_declaration, render_type_grouped,
    };
    use bamts_bytecode::EcmaString;
    use std::sync::Arc;

    use crate::checker::binder::Type;
    use crate::checker::{SemanticModel, TypeId, check};
    use crate::parser;
    use crate::scanner;
    use crate::source::{ScriptKind, SourceId, SourceText};

    #[test]
    fn string_literals_preserve_controls_and_unpaired_surrogates() {
        assert_eq!(
            render_string_literal(&EcmaString::encode("a\n\"b")),
            "\"a\\n\\\"b\""
        );
        assert_eq!(
            render_string_literal(&EcmaString::from_units(&[0xD800])),
            "\"\\uD800\""
        );
    }

    /// Parses and checks one TypeScript source, returning the source text and
    /// the resulting semantic model.
    fn check_text(
        text: &'static str,
    ) -> (Arc<SourceText>, crate::checker::Recovered<SemanticModel>) {
        let source_text = Arc::new(SourceText::new(text).expect("test source fits"));
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::clone(&source_text),
        ));
        let checked = check(&parsed);
        (source_text, checked)
    }

    /// Returns the recorded type of the typed expression whose source slice is
    /// exactly `needle`, searched from byte offset `from`. Test sources are
    /// ASCII, so byte offsets and UTF-16 offsets coincide.
    fn typed_expression_of(
        model: &SemanticModel,
        source: &SourceText,
        needle: &str,
        from: usize,
    ) -> TypeId {
        let start = source.as_str()[from..]
            .find(needle)
            .expect("needle is present")
            + from;
        let end = start + needle.len();
        let matches: Vec<TypeId> = model
            .typed_expressions()
            .iter()
            .filter(|(range, _)| range.start().get() == start && range.end().get() == end)
            .map(|(_, type_id)| *type_id)
            .collect();
        let [type_id] = matches.as_slice() else {
            panic!("expected exactly one typed expression for {needle:?}");
        };
        *type_id
    }

    #[test]
    fn array_concat_member_renders_the_library_overload_pair() {
        // Upstream baseline: tests/baselines/reference/concatTuples.types
        // (sha256 d5e672ec6281c8d0409d3b809a4cd56882631d4030a282a4bf1e2af635337140),
        // row `>ijs.concat : {...}`.
        let text = "let ijs: [number, number][] = [[1, 2]];\nijs = ijs.concat([[3, 4], [5, 6]]);\n";
        let (source, checked) = check_text(text);
        let model = checked.product();
        let type_id = typed_expression_of(model, &source, "ijs.concat", 0);
        assert_eq!(
            render_type(model, type_id),
            "{ (...items: ConcatArray<[number, number]>[]): [number, number][]; \
             (...items: (ConcatArray<[number, number]> | [number, number])[]): [number, number][]; }"
        );
    }

    #[test]
    fn declaration_only_construct_signature_renders_new_arrow() {
        // Upstream baseline:
        // tests/baselines/reference/comparisonOperatorWithNoRelationshipObjectsOnConstructorSignature.types
        // (sha256 caaad48f518da3a8b3c6dcf3d0d94661099a825ac8db65c85dc13ec7379dcd92),
        // row `>b4 : new () => C`.
        let text = "class C { }\ndeclare var b4: { new (): C };\nlet x = b4;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();
        let type_id = typed_expression_of(model, &source, "b4", text.find("let x").unwrap());
        assert_eq!(render_type(model, type_id), "new () => C");
    }

    #[test]
    fn object_types_render_call_construct_index_and_readonly_members() {
        let text = "class Local { }\ninterface Mixed {\n    readonly id: number;\n    [key: string]: unknown;\n    (a: string): void;\n    new (): Local;\n}\ndeclare var mixed: Mixed;\nlet z = mixed;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();
        let type_id = typed_expression_of(model, &source, "mixed", text.find("let z").unwrap());
        assert_eq!(
            render_type(model, type_id),
            "{ (a: string): void; new (): Local; [key: string]: unknown; readonly id: number; }"
        );
    }

    #[test]
    fn method_shorthand_renders_as_call_not_arrow() {
        // Upstream baseline:
        // tests/baselines/reference/objectSpreadWithinMethodWithinObjectWithSpread.types
        // row `>a : { prop(): { metadata: number; }; }` — method shorthand
        // `prop()` renders with `()` not `: () =>`.
        // Counterexample checked:
        // tests/baselines/reference/superInObjectLiterals_ES5(target=es2015).types
        // row `>obj : { ... p1: () => void; ... }` — function-expression
        // properties keep `name: () => type` form.
        let text =
            "interface I { prop(): { metadata: number; }; }\ndeclare var a: I;\nlet z = a;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();
        let type_id = typed_expression_of(model, &source, "a", text.find("let z").unwrap());
        assert_eq!(
            render_type(model, type_id),
            "{ prop(): { metadata: number; }; }"
        );
    }

    #[test]
    fn number_literal_normalizes_hex_and_decimal_forms() {
        // Upstream baseline:
        // tests/baselines/reference/numericLiteralTypes1.types
        // rows `>A2 : 1` (source `1.0`), `>A3 : 1` (source `1e0`),
        // `>A4 : 1` (source `10e-1`) — all normalize to `1`.
        // Counterexample checked:
        // tests/baselines/reference/scannerS7.8.3_A6.1_T1.types
        // row `>0x : 0` — bare `0x` normalizes to `0`.
        // `const` preserves the literal type (unlike `let` which widens).
        let text = "const a = 1.0;\nconst b = 1e0;\nconst c = 10e-1;\nlet z = a;\nlet y = b;\nlet w = c;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();
        let a = typed_expression_of(model, &source, "a", text.find("let z").unwrap());
        assert_eq!(render_type(model, a), "1");
        let b = typed_expression_of(model, &source, "b", text.find("let y").unwrap());
        assert_eq!(render_type(model, b), "1");
        let c = typed_expression_of(model, &source, "c", text.find("let w").unwrap());
        assert_eq!(render_type(model, c), "1");
    }

    #[test]
    fn number_literals_use_exponent_form_like_tsc() {
        let text = "const aa = 0.0000001;\nconst bb = 1e21;\nconst cc = 1e-9;\nconst dd = 1e25;\nconst ee = 0.000001;\nconst ff = 1e20;\nconst gg = 1e-3;\nconst hh = 1.5;\nlet z1 = aa;\nlet z2 = bb;\nlet z3 = cc;\nlet z4 = dd;\nlet z5 = ee;\nlet z6 = ff;\nlet z7 = gg;\nlet z8 = hh;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();
        let aa = typed_expression_of(model, &source, "aa", text.find("let z1").unwrap());
        assert_eq!(render_type(model, aa), "1e-7");
        let bb = typed_expression_of(model, &source, "bb", text.find("let z2").unwrap());
        assert_eq!(render_type(model, bb), "1e+21");
        let cc = typed_expression_of(model, &source, "cc", text.find("let z3").unwrap());
        assert_eq!(render_type(model, cc), "1e-9");
        let dd = typed_expression_of(model, &source, "dd", text.find("let z4").unwrap());
        assert_eq!(render_type(model, dd), "1e+25");
        let ee = typed_expression_of(model, &source, "ee", text.find("let z5").unwrap());
        assert_eq!(render_type(model, ee), "0.000001");
        let ff = typed_expression_of(model, &source, "ff", text.find("let z6").unwrap());
        assert_eq!(render_type(model, ff), "100000000000000000000");
        let gg = typed_expression_of(model, &source, "gg", text.find("let z7").unwrap());
        assert_eq!(render_type(model, gg), "0.001");
        let hh = typed_expression_of(model, &source, "hh", text.find("let z8").unwrap());
        assert_eq!(render_type(model, hh), "1.5");
    }

    /// The renderer reads `declared_return` before the semantic `return_type`,
    /// so two signatures with the same semantic return can render differently
    /// based on their written annotations. This hand-built test uses model-owned
    /// TypeIds from bound signatures and only mutates local clones, never the
    /// semantic model's private type table.
    #[test]
    fn declared_return_preferred_over_return_type_in_signature_renderer() {
        let text = "declare var u: number | undefined;\n\
                    declare var f: () => number;\n\
                    let z = f;\n\
                    let w = u;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let f_id = typed_expression_of(model, &source, "f", text.find("let z").unwrap());
        let u_id = typed_expression_of(model, &source, "u", text.find("let w").unwrap());

        let Type::Function(base) = model.types().get(f_id).clone() else {
            panic!("f should be a function type");
        };
        assert_eq!(base.return_type(), base.declared_return().unwrap());

        let mut with_alias = base.clone();
        with_alias.declared_return = Some(u_id);
        assert_eq!(
            render_signature(model, &with_alias, " => ", &mut Vec::new()),
            "() => number | undefined"
        );
        assert_eq!(
            render_signature_declaration(model, &with_alias, " => ", 0, &mut Vec::new()),
            "() => number | undefined"
        );

        assert_eq!(
            render_signature(model, &base, " => ", &mut Vec::new()),
            "() => number"
        );
    }

    /// Methods render the written `declared_return`, not the semantic
    /// `return_type`. We hand-build a same-semantic pair by attaching `n`'s
    /// written return annotation to `m`'s signature; both have semantic
    /// `number` (m directly, n after T4a nonull projection), but the renderer
    /// shows the declared `number | undefined` for the clone.
    #[test]
    fn interface_method_displays_declared_return_not_semantic() {
        let text = "declare var o: { n(x: string): number | undefined; m(x: string): number; };\n\
                    let z = o;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let o_id = typed_expression_of(model, &source, "o", text.find("let z").unwrap());
        let Type::ObjectType(object) = model.types().get(o_id).clone() else {
            panic!("o should be an object type");
        };

        let n_property = object
            .properties
            .iter()
            .find(|p| p.name() == "n")
            .expect("n method");
        let m_property = object
            .properties
            .iter()
            .find(|p| p.name() == "m")
            .expect("m method");

        let Type::Function(n_sig) = model.types().get(n_property.type_id()).clone() else {
            panic!("n should be a method");
        };
        let Type::Function(base) = model.types().get(m_property.type_id()).clone() else {
            panic!("m should be a method");
        };

        assert_eq!(
            render_signature(model, &base, ": ", &mut Vec::new()),
            "(x: string): number"
        );

        let mut with_declared = base.clone();
        with_declared.declared_return = n_sig.declared_return();
        assert_eq!(
            render_signature(model, &with_declared, ": ", &mut Vec::new()),
            "(x: string): number | undefined"
        );
    }

    /// Call expressions resolve to the semantic `return_type`, never to the
    /// written `declared_return`. Pre-T4a the two are the same; after T4a
    /// projection this test guards that callers still see the projected
    /// semantic return while display remains on declared_return.
    #[test]
    fn call_result_type_uses_semantic_return_not_declared() {
        let text = "declare var f: () => number | undefined;\n\
                    let x = f();\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let from = text.find("let x").unwrap();
        let f_id = typed_expression_of(model, &source, "f", from);
        let x_id = typed_expression_of(model, &source, "f()", from);

        let Type::Function(signature) = model.types().get(f_id).clone() else {
            panic!("f should be a function type");
        };

        assert_eq!(x_id, signature.return_type());
    }

    /// Explicitly-written intersection call signatures keep the ` & ` separator
    /// and per-member parentheses after the declared_return renderer change.
    #[test]
    fn explicit_intersection_call_signatures_keep_ampersand_separator() {
        let text = "declare var f: ((x: number) => number) & ((x: string) => string);\n\
                    let z = f;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let z_id = typed_expression_of(model, &source, "f", text.find("let z").unwrap());
        assert_eq!(
            render_type(model, z_id),
            "((x: number) => number) & ((x: string) => string)"
        );
    }

    /// A registered alias that declares no type parameters renders as its
    /// written name, never as its structural view.
    ///
    /// `type R = { x: R }` interns the recursive occurrence as
    /// `AppliedAlias(R, [])` and the table eagerly materializes that head's
    /// view, so the renderer must not let the cached view reach the output.
    /// The two legs below are the two ways the old renderer could disagree
    /// with itself: consulting the cached view, and taking the name path the
    /// recursion guard (or an absent view) forces. They must now agree.
    #[test]
    fn zero_parameter_alias_head_renders_its_name_regardless_of_view_state() {
        let text = "type R = { x: R };\n\
                    declare var v: R;\n\
                    let z = v;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let v_id = typed_expression_of(model, &source, "v", text.find("let z").unwrap());
        let view_id = model
            .types()
            .applied_alias_view(v_id)
            .expect("R's semantic view is materialized");
        let Type::ObjectType(object) = model.types().get(view_id).clone() else {
            panic!("R's semantic view should be an object type");
        };
        let head = object
            .properties
            .iter()
            .find(|property| property.name() == "x")
            .expect("x property")
            .type_id();

        let Type::AppliedAlias { symbol, arguments } = model.types().get(head).clone() else {
            panic!("R's recursive occurrence should be an AppliedAlias head");
        };
        assert!(arguments.is_empty(), "R declares no type parameters");
        assert!(model.types().has_alias(symbol));
        assert!(model.types().alias_type_parameters(symbol).is_empty());
        // The discriminating cache state: the head's structural view really is
        // materialized, so a view-first renderer would expand it here.
        assert!(model.types().applied_alias_view(head).is_some());

        assert_eq!(render_type(model, head), "R");
        assert_eq!(render_type_declaration(model, head, 0), "R");
        // The name path — what an uncached view produces — agrees exactly.
        assert_eq!(
            render_type_grouped(model, head, false, &mut vec![symbol]),
            "R"
        );
        // A consumer reaching the head through the object keeps the name
        // instead of inlining the cached view.
        assert_eq!(render_type(model, view_id), "{ x: R; }");
        assert_eq!(render_type(model, v_id), "R");
    }

    /// A parameterized alias whose target mentions its type parameters keeps
    /// its written `Name<args>` form. Upstream baseline:
    /// `genericTypeAliases.types` rows `>tree : Tree<number>`,
    /// `>ls : Lazy<string>`, `>x : Foo<string>`, `>zz : Box<WinCondition>`.
    #[test]
    fn parameterized_alias_reference_keeps_written_name() {
        let text = "type Pair<T> = [T, T];\n\
                    declare var p: Pair<string>;\n\
                    let z = p;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let p_id = typed_expression_of(model, &source, "p", text.find("let z").unwrap());
        assert_eq!(render_type(model, p_id), "Pair<string>");
        assert_eq!(render_type_declaration(model, p_id, 0), "Pair<string>");
    }

    /// A parameterized alias whose target ignores its type parameters renders
    /// as its view. Upstream baseline: `genericTypeAliases.types` row
    /// `>s : string` for `var s: Strange<number>` with
    /// `type Strange<T> = string`.
    #[test]
    fn alias_ignoring_its_parameters_renders_its_view() {
        let text = "type Strange<T> = string;\n\
                    declare var s: Strange<number>;\n\
                    let z = s;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let s_id = typed_expression_of(model, &source, "s", text.find("let z").unwrap());
        assert_eq!(render_type(model, s_id), "string");
    }

    /// A parameterized alias that uses its parameter only inside `Record`
    /// keeps its written `Name<args>` form. tsc prints `R<number>`, never
    /// the expanded `Record<string, number>`.
    #[test]
    fn record_alias_using_parameter_only_inside_record_keeps_written_name() {
        let text = "type R<T> = Record<string, T>;\n\
                    declare var r: R<number>;\n\
                    let z = r;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let r_id = typed_expression_of(model, &source, "r", text.find("let z").unwrap());
        assert_eq!(render_type(model, r_id), "R<number>");
        assert_eq!(render_type_declaration(model, r_id, 0), "R<number>");
    }

    /// A parameterized alias that uses its parameter only in a function
    /// return keeps its written `Name<args>` form. tsc prints `F<number>`.
    #[test]
    fn function_alias_using_parameter_only_in_return_keeps_written_name() {
        let text = "type F<T> = () => T;\n\
                    declare var f: F<number>;\n\
                    let z = f;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let f_id = typed_expression_of(model, &source, "f", text.find("let z").unwrap());
        assert_eq!(render_type(model, f_id), "F<number>");
        assert_eq!(render_type_declaration(model, f_id, 0), "F<number>");
    }

    /// A `keyof` alias never keeps its written name, even for an unresolved
    /// parameter. tsc prints `<T>(x: keyof T) => void`, never `K<T>`.
    #[test]
    fn keyof_alias_with_unresolved_parameter_renders_keyof_form() {
        let text = "type K<T> = keyof T;\n\
                    declare function f<T>(x: K<T>): void;\n\
                    let g = f;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let f_id = typed_expression_of(model, &source, "f", text.find("let g").unwrap());
        assert_eq!(render_type(model, f_id), "<T>(x: keyof T) => void");
    }

    /// A resolved `keyof` alias expands to the evaluated key union.
    /// Upstream baseline: `keyofAndIndexedAccess.types` row
    /// `>K21 : string | number` for `type K21 = KeyOf<Dictionary<Shape>>`.
    /// (`declare const` avoids the mutable-binding widening of literal
    /// constituents, which tsc does not perform on annotated declarations.)
    #[test]
    fn keyof_alias_over_object_literal_expands_to_key_union() {
        let text = "type K<T> = keyof T;\n\
                    declare const k: K<{ a: number; b: string }>;\n\
                    let out = k;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let k_id = typed_expression_of(model, &source, "k", text.find("let out").unwrap());
        assert_eq!(render_type(model, k_id), "\"a\" | \"b\"");
    }

    /// An indexed-access alias keeps its written name while the access
    /// cannot resolve. Upstream baseline: `computedPropertyNamesContextualType6_ES5.types`
    /// rows `>foo : <T>(obj: I<T>) => T` and `>obj : I<T>`.
    #[test]
    fn indexed_alias_with_unresolved_parameter_keeps_written_name() {
        let text = "type G<T extends { a: number }> = T[\"a\"];\n\
                    declare function h<U extends { a: number }>(y: G<U>): void;\n\
                    let go = h;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let h_id = typed_expression_of(model, &source, "h", text.find("let go").unwrap());
        assert_eq!(
            render_type(model, h_id),
            "<U extends { a: number; }>(y: G<U>) => void"
        );
    }

    /// A mention that passes through a nested alias counts only when the
    /// nested alias observes that argument: `Wrap<T> = Strange<T>` ignores
    /// `T`, so tsc prints `Wrap<number>` as `string`.
    #[test]
    fn nested_alias_ignoring_argument_expands_to_view() {
        let text = "type Strange<T> = string;\n\
                    type Wrap<T> = Strange<T>;\n\
                    declare var w: Wrap<number>;\n\
                    let out = w;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let w_id = typed_expression_of(model, &source, "w", text.find("let out").unwrap());
        assert_eq!(render_type(model, w_id), "string");
    }

    /// The same nesting keeps its written name when the inner alias observes
    /// the argument: `Wrap2<T> = Pair<T>` prints as `Wrap2<number>`.
    #[test]
    fn nested_alias_using_argument_through_inner_alias_keeps_written_name() {
        let text = "type Pair<T> = [T, T];\n\
                    type Wrap2<T> = Pair<T>;\n\
                    declare var w: Wrap2<number>;\n\
                    let out = w;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let w_id = typed_expression_of(model, &source, "w", text.find("let out").unwrap());
        assert_eq!(render_type(model, w_id), "Wrap2<number>");
        assert_eq!(render_type_declaration(model, w_id, 0), "Wrap2<number>");
    }

    /// A `typeof` query renders its written spelling for nominal operands and
    /// resolves plain variables to their target. Upstream baselines:
    /// `castTest.types` row `>Point : typeof Point`,
    /// `FunctionAndModuleWithSameNameAndCommonRoot.types` rows
    /// `>A.Point : typeof A.Point` and `>A : typeof A`.
    #[test]
    fn typeof_query_renders_written_name() {
        let text = "class Point { x: number }\n\
                    declare var p: typeof Point;\n\
                    let z = p;\n\
                    namespace A { export class Q { x: number } }\n\
                    declare var q: typeof A.Q;\n\
                    let w = q;\n\
                    declare var foo: { a: number };\n\
                    declare var v: typeof foo;\n\
                    let u = v;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let p_id = typed_expression_of(model, &source, "p", text.find("let z").unwrap());
        assert_eq!(render_type(model, p_id), "typeof Point");
        let q_id = typed_expression_of(model, &source, "q", text.find("let w").unwrap());
        assert_eq!(render_type(model, q_id), "typeof A.Q");
        let v_id = typed_expression_of(model, &source, "v", text.find("let u").unwrap());
        assert_eq!(render_type(model, v_id), "{ a: number; }");
    }

    /// `render_type_annotated` blanks the spans that reproduce written
    /// annotations: parameter names always, declared parameter and return
    /// types only when written. `function f(a: string): void` renders
    /// `(a: string) => void` with blanks over `a`, `string`, and `void`.
    #[test]
    fn annotated_signature_blanks_names_and_written_spans() {
        let text = "function f(a: string): void {}\nlet g = f;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let f_id = typed_expression_of(model, &source, "f", text.find("let g").unwrap());
        let (rendered, blanks) = render_type_annotated(model, f_id);
        assert_eq!(rendered, "(a: string) => void");
        assert_eq!(blanks, vec![(1, 2), (4, 10), (15, 19)]);
    }

    /// Inferred spans take carets: only the parameter name is blank in
    /// `(a: any) => void` for `function g(a) {}`.
    #[test]
    fn inferred_signature_blanks_only_parameter_name() {
        let text = "function g(a) {}\nlet h = g;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let g_id = typed_expression_of(model, &source, "g", text.find("let h").unwrap());
        let (rendered, blanks) = render_type_annotated(model, g_id);
        assert_eq!(rendered, "(a: any) => void");
        assert_eq!(blanks, vec![(1, 2)]);
    }

    /// A declared object member type is blank while its surroundings take
    /// carets: `{ foo: string; }` blanks only `string`.
    #[test]
    fn annotated_object_member_blanks_only_member_type() {
        let text = "var n: { foo: string } = { foo: \"x\" };\nlet m = n;\n";
        let (source, checked) = check_text(text);
        let model = checked.product();

        let n_id = typed_expression_of(model, &source, "n", text.find("let m").unwrap());
        let (rendered, blanks) = render_type_annotated(model, n_id);
        assert_eq!(rendered, "{ foo: string; }");
        assert_eq!(blanks, vec![(7, 13)]);
    }
}
