//! `emitDecoratorMetadata` metadata: the `__metadata("design:*", T)` elements
//! a decorated member's `__decorate` array carries.
//!
//! Each annotation serializes to one runtime expression per the baselines:
//! intrinsic kinds wrap to their constructor (`String`, `Number`, `Boolean`,
//! `BigInt`, `Symbol`), arrays and tuples to `Array`, function and constructor
//! types to `Function`, everything else unresolved to `Object`, `void`,
//! `undefined`, `null`, and `never` to `void 0`, and a named type to the
//! emitted reference for its declaration. A union folds its constituents:
//! shared kind wins, mixed kinds fall to `Object`, a lone survivor serializes
//! in full, and a union of nothing serializes to `void 0`.

use crate::checker::{SymbolKind, Type, TypeId};
use crate::source::TextRange;
use crate::syntax::*;

use super::Rewriter;
use super::helpers::HelperKind;

/// Which declaration asks for metadata: a decorated member, or the class's
/// constructor parameters riding the class `__decorate` call.
pub(super) enum MetadataSubject {
    Property(Option<Ty>),
    Method {
        parameters: Vec<ParameterNode>,
        return_type: Option<Ty>,
        is_async: bool,
    },
    Accessor {
        getter_return: Option<Ty>,
        setter_parameters: Vec<ParameterNode>,
    },
    ConstructorParameters(Vec<ParameterNode>),
}

/// The intrinsic family a union constituent belongs to. `Absent` covers
/// `null` and `undefined`, which `strictNullChecks` removes from unions;
/// `Nothing` covers `never`, which vanishes everywhere.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum IntrinsicKind {
    String,
    Number,
    Boolean,
    BigInt,
    Symbol,
    Other,
    Absent,
    Nothing,
}

impl MetadataSubject {
    /// The pair view of the accessor `accessor`: what its getter returns and
    /// what its setter takes, collected from every member sharing the name.
    pub(super) fn accessor(
        rewriter: &Rewriter<'_>,
        accessor: &MethodDeclaration,
        members: &[ClassMemberNode],
    ) -> Self {
        let mut getter_return = None;
        let mut setter_parameters = Vec::new();
        if let Some(name) = rewriter.property_name_text(&accessor.name) {
            for member in members {
                let ClassMember::Method(method) = member.data() else {
                    continue;
                };
                let Some(member_name) = rewriter.property_name_text(&method.name) else {
                    continue;
                };
                if member_name != name {
                    continue;
                }
                match method.modifier {
                    PropertyModifier::Get => {
                        getter_return = method
                            .function
                            .return_type
                            .as_ref()
                            .map(|annotation| (*annotation.data().type_node).clone());
                    }
                    PropertyModifier::Set => setter_parameters = method.function.parameters.clone(),
                    PropertyModifier::None => {}
                }
            }
        }
        Self::Accessor {
            getter_return,
            setter_parameters,
        }
    }
}

impl Rewriter<'_> {
    /// The `__metadata` elements one decorated declaration carries.
    pub(super) fn decorator_metadata(
        &mut self,
        subject: MetadataSubject,
        range: TextRange,
    ) -> Vec<Expr> {
        if !self.options.emit_decorator_metadata {
            return Vec::new();
        }
        match subject {
            MetadataSubject::Property(annotation) => {
                let design = self.design_type(annotation.as_ref(), range);
                vec![self.metadata_element("design:type", design, range)]
            }
            MetadataSubject::Method {
                parameters,
                return_type,
                is_async,
            } => {
                let design = self.ident_expr("Function");
                let parameters_element = self.parameter_types(&parameters, range);
                let return_element = self.method_return_type(return_type.as_ref(), is_async, range);
                vec![
                    self.metadata_element("design:type", design, range),
                    self.metadata_element("design:paramtypes", parameters_element, range),
                    self.metadata_element("design:returntype", return_element, range),
                ]
            }
            MetadataSubject::Accessor {
                getter_return,
                setter_parameters,
            } => {
                let design =
                    self.accessor_design_type(getter_return.as_ref(), &setter_parameters, range);
                let parameters_element = self.parameter_types(&setter_parameters, range);
                vec![
                    self.metadata_element("design:type", design, range),
                    self.metadata_element("design:paramtypes", parameters_element, range),
                ]
            }
            MetadataSubject::ConstructorParameters(parameters) => {
                let parameters_element = self.parameter_types(&parameters, range);
                vec![self.metadata_element("design:paramtypes", parameters_element, range)]
            }
        }
    }

    /// `__metadata("key", value)`.
    fn metadata_element(&mut self, key: &str, value: Expr, range: TextRange) -> Expr {
        let callee = self.helper_ident(HelperKind::Metadata);
        let literal = self.string_literal(key);
        let key = self.node(range, Expression::Literal(Literal::String(literal)));
        self.call_expression(range, callee, vec![key, value])
    }

    /// What an accessor's `design:type` reads: the getter's return annotation,
    /// else the setter's first parameter annotation, else `Object`.
    fn accessor_design_type(
        &mut self,
        getter_return: Option<&Ty>,
        setter_parameters: &[ParameterNode],
        range: TextRange,
    ) -> Expr {
        if let Some(annotation) = getter_return {
            return self.design_type(Some(annotation), range);
        }
        let setter = setter_parameters
            .iter()
            .find(|parameter| !self.is_this_parameter(parameter));
        match setter.and_then(|parameter| parameter.data().type_annotation.as_ref()) {
            Some(annotation) => {
                let annotation = (*annotation.data().type_node).clone();
                self.design_type(Some(&annotation), range)
            }
            None => self.ident_expr("Object"),
        }
    }

    /// What a method's `design:returntype` reads: the annotation, else
    /// `Promise` for an async method, else `void 0`.
    fn method_return_type(
        &mut self,
        return_type: Option<&Ty>,
        is_async: bool,
        range: TextRange,
    ) -> Expr {
        match (return_type, is_async) {
            (Some(annotation), _) => self.design_type(Some(annotation), range),
            (None, true) => self.ident_expr("Promise"),
            (None, false) => self.void_zero(range),
        }
    }

    /// `[T1, T2]`, one entry per parameter, `this` parameters skipped.
    fn parameter_types(&mut self, parameters: &[ParameterNode], range: TextRange) -> Expr {
        let named: Vec<&ParameterNode> = parameters
            .iter()
            .filter(|parameter| !self.is_this_parameter(parameter))
            .collect();
        let elements = named
            .into_iter()
            .map(|parameter| {
                ArrayElement::Expression(Box::new(self.parameter_type(parameter, range)))
            })
            .collect();
        self.node(range, Expression::Array(ArrayLiteral { elements }))
    }

    /// A rest parameter reports its array element's kind; every other
    /// parameter reports its annotation, or `Object` when it has none.
    fn parameter_type(&mut self, parameter: &ParameterNode, range: TextRange) -> Expr {
        let annotation = parameter
            .data()
            .type_annotation
            .as_ref()
            .map(|annotation| (*annotation.data().type_node).clone());
        let is_rest = matches!(parameter.data().binding.data(), BindingPattern::Rest(_));
        let annotation = if is_rest {
            annotation.map(|annotation| match annotation.data() {
                TypeNode::Array(element) => (**element).clone(),
                TypeNode::Operator {
                    operator: TypeOperator::Readonly,
                    operand,
                } => match operand.data() {
                    TypeNode::Array(element) => (**element).clone(),
                    _ => annotation,
                },
                _ => annotation,
            })
        } else {
            annotation
        };
        self.design_type(annotation.as_ref(), range)
    }

    /// Whether the parameter binds `this`, which carries no runtime argument.
    fn is_this_parameter(&self, parameter: &ParameterNode) -> bool {
        match parameter.data().binding.data() {
            BindingPattern::Identifier(ident) => {
                self.identifier_name(ident).as_deref() == Some("this")
            }
            _ => false,
        }
    }

    /// The runtime expression one type annotation serializes to.
    fn design_type(&mut self, annotation: Option<&Ty>, range: TextRange) -> Expr {
        if let Some(resolved) = self.resolved_design_type(annotation) {
            let union = match self.model.map(|model| model.types().get(resolved)) {
                Some(Type::Union(constituents)) => Some(constituents.clone()),
                _ => None,
            };
            if let Some(constituents) = union {
                return self.union_design_resolved(&constituents, range);
            }
            return self.type_wrapper(resolved, range);
        }
        let Some(annotation) = annotation else {
            return self.ident_expr("Object");
        };
        match annotation.data() {
            TypeNode::Keyword(keyword) => self.keyword_design(*keyword, range),
            TypeNode::Literal(literal) => self.literal_design(literal, range),
            TypeNode::Reference(reference) => self.reference_design(reference, range),
            TypeNode::Query(query) => {
                let reference = TypeReference {
                    name: query.name.clone(),
                    type_arguments: None,
                };
                self.reference_design(&reference, range)
            }
            TypeNode::Union(constituents) => {
                let constituents: Vec<&Ty> = constituents.iter().collect();
                self.union_design(&constituents, range)
            }
            TypeNode::Conditional(conditional) => {
                let constituents = vec![&*conditional.true_type, &*conditional.false_type];
                self.union_design(&constituents, range)
            }
            TypeNode::Array(_) | TypeNode::Tuple(_) => self.ident_expr("Array"),
            TypeNode::Function(_) | TypeNode::Constructor(_) => self.ident_expr("Function"),
            TypeNode::TemplateLiteral(_) => self.ident_expr("String"),
            TypeNode::Parenthesized(inner) => self.design_type(Some(inner), range),
            TypeNode::Operator { operator, operand } => match operator {
                TypeOperator::Readonly => self.design_type(Some(operand), range),
                TypeOperator::Unique => self.ident_expr("Symbol"),
                TypeOperator::Keyof => self.ident_expr("Object"),
            },
            _ => self.ident_expr("Object"),
        }
    }

    /// The checker's resolved type for one annotation, when recorded.
    fn resolved_design_type(&mut self, annotation: Option<&Ty>) -> Option<TypeId> {
        let annotation = annotation?;
        let model = self.model?;
        model.resolved_type(annotation.id())
    }

    /// The runtime expression one resolved non-union type serializes to.
    fn type_wrapper(&mut self, resolved: TypeId, range: TextRange) -> Expr {
        match self.resolved_kind(resolved) {
            IntrinsicKind::String => self.ident_expr("String"),
            IntrinsicKind::Number => self.ident_expr("Number"),
            IntrinsicKind::Boolean => self.ident_expr("Boolean"),
            IntrinsicKind::BigInt => self.ident_expr("BigInt"),
            IntrinsicKind::Symbol => self.ident_expr("Symbol"),
            IntrinsicKind::Absent | IntrinsicKind::Nothing => self.void_zero(range),
            IntrinsicKind::Other => self.resolved_reference(resolved),
        }
    }

    /// The emitted reference a resolved named type reads, or `Object` when
    /// the name has no runtime form.
    fn resolved_reference(&mut self, resolved: TypeId) -> Expr {
        let Some(model) = self.model else {
            return self.ident_expr("Object");
        };
        let symbol = match model.types().get(resolved) {
            Type::Named(symbol) => *symbol,
            Type::AppliedClass { symbol, .. } => *symbol,
            Type::AppliedAlias { symbol, .. } => *symbol,
            Type::ConstructorType { symbol, .. } => *symbol,
            Type::NumericEnum(symbol) => *symbol,
            Type::EnumMember { member_symbol, .. } => *member_symbol,
            _ => return self.ident_expr("Object"),
        };
        match model.symbol(symbol).kind() {
            SymbolKind::Enum => self.ident_expr("Number"),
            SymbolKind::EnumMember => match model.types().get(resolved) {
                Type::EnumMember {
                    string_value: Some(_),
                    ..
                } => self.ident_expr("String"),
                _ => self.ident_expr("Number"),
            },
            SymbolKind::Class | SymbolKind::Namespace => {
                let name = model.symbol(symbol).name().to_owned();
                if model.scope(model.module_scope()).value(&name).is_some() {
                    self.ident_expr(&name)
                } else {
                    self.ident_expr("Function")
                }
            }
            SymbolKind::IntrinsicType | SymbolKind::IntrinsicValue => {
                self.ident_expr(model.symbol(symbol).name())
            }
            _ => self.ident_expr("Object"),
        }
    }

    /// Which intrinsic family a resolved type belongs to.
    fn resolved_kind(&self, resolved: TypeId) -> IntrinsicKind {
        let Some(model) = self.model else {
            return IntrinsicKind::Other;
        };
        match model.types().get(resolved) {
            Type::String | Type::StringLiteral(_) => IntrinsicKind::String,
            Type::Number | Type::NumberLiteral(_) => IntrinsicKind::Number,
            Type::Boolean | Type::BooleanLiteral(_) => IntrinsicKind::Boolean,
            Type::BigInt | Type::BigIntLiteral(_) => IntrinsicKind::BigInt,
            Type::Symbol => IntrinsicKind::Symbol,
            Type::Void | Type::Undefined | Type::Null => IntrinsicKind::Absent,
            Type::Never => IntrinsicKind::Nothing,
            Type::NumericEnum(_) => IntrinsicKind::Number,
            Type::EnumMember {
                string_value: Some(_),
                ..
            } => IntrinsicKind::String,
            Type::EnumMember { .. } => IntrinsicKind::Number,
            Type::Union(constituents) => {
                let mut kinds = constituents.iter().map(|id| self.resolved_kind(*id));
                let Some(first) = kinds.next() else {
                    return IntrinsicKind::Nothing;
                };
                if kinds.all(|kind| kind == first) {
                    first
                } else {
                    IntrinsicKind::Other
                }
            }
            Type::Named(symbol) => match model.symbol(*symbol).kind() {
                SymbolKind::Enum | SymbolKind::EnumMember => IntrinsicKind::Number,
                SymbolKind::IntrinsicType | SymbolKind::IntrinsicValue => {
                    match model.symbol(*symbol).name() {
                        "string" => IntrinsicKind::String,
                        "number" => IntrinsicKind::Number,
                        "boolean" => IntrinsicKind::Boolean,
                        "bigint" => IntrinsicKind::BigInt,
                        "symbol" => IntrinsicKind::Symbol,
                        "void" | "undefined" | "null" => IntrinsicKind::Absent,
                        _ => IntrinsicKind::Other,
                    }
                }
                _ => IntrinsicKind::Other,
            },
            _ => IntrinsicKind::Other,
        }
    }

    /// The wrapper expression one resolved union folds to: strict mode drops
    /// `never`, loose mode also drops `null` and `undefined`, a lone survivor
    /// serializes in full, a shared kind wins, and mixed kinds fall to `Object`.
    fn union_design_resolved(&mut self, constituents: &[TypeId], range: TextRange) -> Expr {
        let nothing = IntrinsicKind::Nothing;
        let classified: Vec<(TypeId, IntrinsicKind)> = constituents
            .iter()
            .map(|id| (*id, self.resolved_kind(*id)))
            .collect();
        let kept: Vec<(TypeId, IntrinsicKind)> = if self.options.strict_null_checks {
            classified
                .into_iter()
                .filter(|(_, kind)| *kind != nothing)
                .collect()
        } else {
            classified
                .into_iter()
                .filter(|(_, kind)| !matches!(kind, IntrinsicKind::Absent | IntrinsicKind::Nothing))
                .collect()
        };
        let Some(first) = kept.first() else {
            return self.void_zero(range);
        };
        if kept.len() == 1 {
            return self.type_wrapper(first.0, range);
        }
        if kept.iter().all(|(_, kind)| *kind == first.1) {
            return self.kind_wrapper(first.1);
        }
        self.ident_expr("Object")
    }

    /// The symbol a type-position name resolves to, from the module scope
    /// outward through the global scope's type and value planes.
    fn lookup_symbol(&self, name: &str) -> Option<crate::checker::SymbolId> {
        let model = self.model?;
        let mut scope = Some(model.module_scope());
        while let Some(id) = scope {
            let scope_ref = model.scope(id);
            if let Some(symbol) = scope_ref.type_binding(name) {
                return Some(symbol);
            }
            scope = scope_ref.parent();
        }
        let mut scope = Some(model.module_scope());
        while let Some(id) = scope {
            let scope_ref = model.scope(id);
            if let Some(symbol) = scope_ref.value(name) {
                return Some(symbol);
            }
            scope = scope_ref.parent();
        }
        None
    }
    /// The wrapper one keyword serializes to.
    fn keyword_design(&mut self, keyword: KeywordType, range: TextRange) -> Expr {
        match keyword {
            KeywordType::Boolean => self.ident_expr("Boolean"),
            KeywordType::Number => self.ident_expr("Number"),
            KeywordType::BigInt => self.ident_expr("BigInt"),
            KeywordType::String => self.ident_expr("String"),
            KeywordType::Symbol => self.ident_expr("Symbol"),
            KeywordType::Never | KeywordType::Void | KeywordType::Undefined | KeywordType::Null => {
                self.void_zero(range)
            }
            _ => self.ident_expr("Object"),
        }
    }

    /// The wrapper one literal serializes to.
    fn literal_design(&mut self, literal: &TypeLiteral, range: TextRange) -> Expr {
        match literal {
            TypeLiteral::String(_) => self.ident_expr("String"),
            TypeLiteral::Number(_) | TypeLiteral::Unary { .. } => self.ident_expr("Number"),
            TypeLiteral::BigInt(_) => self.ident_expr("BigInt"),
            TypeLiteral::Boolean(_) => self.ident_expr("Boolean"),
            TypeLiteral::Null(_) => self.void_zero(range),
        }
    }

    /// The runtime expression one named type serializes to.
    fn reference_design(&mut self, reference: &TypeReference, range: TextRange) -> Expr {
        let Some(leftmost) = Self::entity_leftmost(&reference.name) else {
            return self.ident_expr("Object");
        };
        let Some(name) = self.identifier_name(leftmost) else {
            return self.ident_expr("Object");
        };
        let Some(model) = self.model else {
            return self.ident_expr("Object");
        };
        let Some(symbol) = model
            .reference(leftmost.id())
            .or_else(|| self.lookup_symbol(&name))
        else {
            return self.ident_expr("Object");
        };
        match model.symbol(symbol).kind() {
            SymbolKind::TypeParameter
            | SymbolKind::TypeAlias
            | SymbolKind::Interface
            | SymbolKind::IntrinsicType => self.ident_expr("Object"),
            SymbolKind::Enum | SymbolKind::EnumMember => self.ident_expr("Number"),
            SymbolKind::Class | SymbolKind::Namespace => {
                if model.scope(model.module_scope()).value(&name).is_some() {
                    self.entity_reference(&reference.name, range)
                } else {
                    self.ident_expr("Function")
                }
            }
            SymbolKind::Import => {
                if model.scope(model.module_scope()).value(&name).is_some() {
                    self.entity_reference(&reference.name, range)
                } else {
                    self.ident_expr("Object")
                }
            }
            _ => self.entity_reference(&reference.name, range),
        }
    }

    /// The emitted reference for an entity name: its leftmost binding reads
    /// the module value form, the remaining segments read members off it.
    fn entity_reference(&mut self, name: &EntityName, range: TextRange) -> Expr {
        match name {
            EntityName::Identifier(ident) => {
                let Some(name) = self.identifier_name(ident) else {
                    return self.ident_expr("Object");
                };
                self.cjs_local_value(&name, range)
            }
            EntityName::Qualified { left, right } => {
                let object = self.entity_reference(left, range);
                let Some(property) = self.identifier_name(right) else {
                    return self.ident_expr("Object");
                };
                self.member_access(object, &property, range)
            }
            EntityName::Missing(_) => self.ident_expr("Object"),
        }
    }

    /// The leftmost identifier of an entity name.
    fn entity_leftmost(name: &EntityName) -> Option<&IdentifierNode> {
        let mut current = name;
        loop {
            match current {
                EntityName::Identifier(ident) => return Some(ident),
                EntityName::Qualified { left, .. } => current = left,
                EntityName::Missing(_) => return None,
            }
        }
    }

    /// The wrapper one union folds to: a shared intrinsic kind wins, mixed
    /// kinds fall to `Object`, and nothing left falls to `void 0`.
    fn union_design(&mut self, constituents: &[&Ty], range: TextRange) -> Expr {
        if self.options.strict_null_checks {
            let kinds: Vec<IntrinsicKind> = constituents
                .iter()
                .map(|constituent| self.classify(constituent))
                .filter(|kind| *kind != IntrinsicKind::Nothing)
                .collect();
            let Some(first) = kinds.first() else {
                return self.void_zero(range);
            };
            if kinds.iter().all(|kind| kind == first) {
                return self.kind_wrapper(*first);
            }
            return self.ident_expr("Object");
        }
        let kept: Vec<&Ty> = constituents
            .iter()
            .copied()
            .filter(|constituent| {
                !matches!(
                    self.classify(constituent),
                    IntrinsicKind::Absent | IntrinsicKind::Nothing
                )
            })
            .collect();
        let Some(first) = kept.first() else {
            return self.void_zero(range);
        };
        if kept.len() == 1 {
            return self.design_type(Some(first), range);
        }
        let first_kind = self.classify(first);
        if kept
            .iter()
            .all(|constituent| self.classify(constituent) == first_kind)
        {
            return self.kind_wrapper(first_kind);
        }
        self.ident_expr("Object")
    }

    /// The constructor one intrinsic kind reads.
    fn kind_wrapper(&mut self, kind: IntrinsicKind) -> Expr {
        match kind {
            IntrinsicKind::String => self.ident_expr("String"),
            IntrinsicKind::Number => self.ident_expr("Number"),
            IntrinsicKind::Boolean => self.ident_expr("Boolean"),
            IntrinsicKind::BigInt => self.ident_expr("BigInt"),
            IntrinsicKind::Symbol => self.ident_expr("Symbol"),
            _ => self.ident_expr("Object"),
        }
    }

    /// Which intrinsic family one union constituent belongs to.
    fn classify(&self, annotation: &Ty) -> IntrinsicKind {
        match annotation.data() {
            TypeNode::Keyword(keyword) => match keyword {
                KeywordType::String => IntrinsicKind::String,
                KeywordType::Number => IntrinsicKind::Number,
                KeywordType::Boolean => IntrinsicKind::Boolean,
                KeywordType::BigInt => IntrinsicKind::BigInt,
                KeywordType::Symbol => IntrinsicKind::Symbol,
                KeywordType::Never => IntrinsicKind::Nothing,
                KeywordType::Void | KeywordType::Undefined | KeywordType::Null => {
                    IntrinsicKind::Absent
                }
                _ => IntrinsicKind::Other,
            },
            TypeNode::Literal(literal) => match literal {
                TypeLiteral::String(_) => IntrinsicKind::String,
                TypeLiteral::Number(_) | TypeLiteral::Unary { .. } => IntrinsicKind::Number,
                TypeLiteral::BigInt(_) => IntrinsicKind::BigInt,
                TypeLiteral::Boolean(_) => IntrinsicKind::Boolean,
                TypeLiteral::Null(_) => IntrinsicKind::Absent,
            },
            TypeNode::TemplateLiteral(_) => IntrinsicKind::String,
            TypeNode::Reference(reference) => {
                let Some(leftmost) = Self::entity_leftmost(&reference.name) else {
                    return IntrinsicKind::Other;
                };
                let Some(name) = self.identifier_name(leftmost) else {
                    return IntrinsicKind::Other;
                };
                let names_enum = self.model.and_then(|model| {
                    let symbol = model
                        .reference(leftmost.id())
                        .or_else(|| self.lookup_symbol(&name))?;
                    Some(matches!(
                        model.symbol(symbol).kind(),
                        SymbolKind::Enum | SymbolKind::EnumMember
                    ))
                });
                if names_enum == Some(true) {
                    IntrinsicKind::Number
                } else {
                    IntrinsicKind::Other
                }
            }
            TypeNode::Conditional(conditional) => {
                let true_kind = self.classify(&conditional.true_type);
                let false_kind = self.classify(&conditional.false_type);
                if true_kind == false_kind {
                    true_kind
                } else {
                    IntrinsicKind::Other
                }
            }
            TypeNode::Parenthesized(inner) => self.classify(inner),
            TypeNode::Operator { operator, operand } => match operator {
                TypeOperator::Readonly => self.classify(operand),
                TypeOperator::Unique => IntrinsicKind::Symbol,
                TypeOperator::Keyof => IntrinsicKind::Other,
            },
            _ => IntrinsicKind::Other,
        }
    }

    /// The authored text of a property name, when it names a binding.
    pub(super) fn property_name_text(&self, name: &PropertyName) -> Option<String> {
        match name {
            PropertyName::Identifier(ident) => self.identifier_name(ident),
            PropertyName::String(literal) => {
                let quoted = self.token_text(literal.data().token());
                let inner = quoted.trim_matches(['"', '\'']);
                Some(inner.to_owned())
            }
            PropertyName::Number(literal) => {
                Some(self.token_text(literal.data().token()).to_owned())
            }
            PropertyName::Private(_) | PropertyName::Computed(_) | PropertyName::Missing(_) => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::diagnostic::Recovered;
    use crate::emitter::{EmitFileNames, EmitOptions};
    use crate::parser;
    use crate::scanner;
    use crate::source::{ScriptKind, SourceId, SourceText};
    use std::sync::Arc;

    use super::super::emit_transformed;

    fn parse(source: &str) -> crate::syntax::SourceFile {
        parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(source).expect("test source fits the per-file source budget")),
        ))
        .into_product()
    }

    fn metadata_code(source: &str) -> String {
        let options = EmitOptions {
            experimental_decorators: true,
            emit_decorator_metadata: true,
            ..EmitOptions::default()
        };
        let output = emit_transformed(
            &parse(source),
            crate::checker::check(&Recovered::clean(parse(source))).product(),
            &options.transform_view(),
            &EmitFileNames::default(),
        );
        output
            .javascript
            .as_ref()
            .expect("JavaScript output")
            .code
            .to_owned()
    }

    #[test]
    fn a_property_annotation_wraps_to_its_intrinsic_constructor() {
        let code = metadata_code(
            "declare function PropDeco(target: Object, propKey: string | symbol): void;\nclass Foo {\n    @PropDeco\n    foo: string;\n}\n",
        );
        assert!(
            code.contains("__metadata(\"design:type\", String)"),
            "{code}"
        );
    }

    #[test]
    fn a_mixed_union_folds_to_object_and_a_shared_union_wraps() {
        let code = metadata_code(
            "declare function PropDeco(target: Object, propKey: string | symbol): void;\nclass Foo {\n    @PropDeco\n    a: \"foo\" | number;\n    @PropDeco\n    b: \"foo\" | \"bar\";\n}\n",
        );
        assert!(
            code.contains("__metadata(\"design:type\", Object)"),
            "{code}"
        );
        assert!(
            code.contains("__metadata(\"design:type\", String)"),
            "{code}"
        );
    }

    #[test]
    fn an_enum_member_type_reads_number() {
        let code = metadata_code(
            "declare function PropDeco(target: Object, propKey: string | symbol): void;\nenum E { A, B }\nclass Foo {\n    @PropDeco\n    a: E.A;\n}\n",
        );
        assert!(
            code.contains("__metadata(\"design:type\", Number)"),
            "{code}"
        );
    }

    #[test]
    fn a_method_reads_function_its_parameters_and_its_return() {
        let code = metadata_code(
            "declare var decorator: any;\nclass Foo {\n    @decorator\n    method(x: string): number {\n        return 0;\n    }\n}\n",
        );
        assert!(
            code.contains("__metadata(\"design:type\", Function)"),
            "{code}"
        );
        assert!(
            code.contains("__metadata(\"design:paramtypes\", [String])"),
            "{code}"
        );
        assert!(
            code.contains("__metadata(\"design:returntype\", Number)"),
            "{code}"
        );
    }

    #[test]
    fn an_accessor_reads_its_setter_for_type_and_parameters() {
        let code = metadata_code(
            "declare var decorator: any;\nclass Foo {\n    @decorator\n    set x(value: number) { }\n}\n",
        );
        assert!(
            code.contains("__metadata(\"design:type\", Number)"),
            "{code}"
        );
        assert!(
            code.contains("__metadata(\"design:paramtypes\", [Number])"),
            "{code}"
        );
    }

    #[test]
    fn a_class_constructor_rides_the_class_decoration() {
        let code = metadata_code(
            "declare var decorator: any;\n@decorator\nclass Foo {\n    constructor(x: string) { }\n}\n",
        );
        assert!(
            code.contains("__metadata(\"design:paramtypes\", [String])"),
            "{code}"
        );
    }

    #[test]
    fn a_class_without_a_constructor_carries_no_parameter_metadata() {
        let code = metadata_code("declare var decorator: any;\n@decorator\nclass Foo {\n}\n");
        assert!(!code.contains("__metadata"), "{code}");
    }

    #[test]
    fn a_rest_parameter_reports_its_element_type() {
        let code = metadata_code(
            "declare var decorator: any;\nclass Foo {\n    @decorator\n    method(...args: string[]) { }\n}\n",
        );
        assert!(
            code.contains("__metadata(\"design:paramtypes\", [String])"),
            "{code}"
        );
    }

    #[test]
    fn a_type_parameter_reads_object() {
        let code = metadata_code(
            "declare var decorator: any;\nclass Foo<T> {\n    @decorator\n    member: T;\n}\n",
        );
        assert!(
            code.contains("__metadata(\"design:type\", Object)"),
            "{code}"
        );
    }

    #[test]
    fn a_local_class_reference_reads_its_identifier() {
        let code = metadata_code(
            "declare var decorator: any;\nclass A { }\nclass Foo {\n    @decorator\n    x: A = new A();\n}\n",
        );
        assert!(code.contains("__metadata(\"design:type\", A)"), "{code}");
    }

    #[test]
    fn an_async_method_without_annotation_reads_promise() {
        let code = metadata_code(
            "declare var decorator: any;\nclass Foo {\n    @decorator\n    async foo() { }\n}\n",
        );
        assert!(
            code.contains("__metadata(\"design:returntype\", Promise)"),
            "{code}"
        );
    }
}
