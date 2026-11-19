//! Semantic evaluation for conditional, infer, template-literal, and mapped types.
//!
//! Syntax nodes are resolved into the canonical [`TypeTable`] before entering this
//! module. Evaluation interns only canonical checker types; no parallel type graph
//! or permissive recovery type is introduced here.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use super::{
    binder::{FunctionParameter, FunctionSignature},
    inference::{InferenceProvenance, InferredTypeArgument, InferredTypeArguments},
};
use crate::{
    checker::{PropertyType, SymbolId, Type, TypeId, TypeTable},
    syntax::MappedModifier,
};

/// Default cap for a template-literal cross product or mapped property set.
pub const DEFAULT_EXPANSION_LIMIT: usize = 1_000;

/// A failed advanced-type evaluation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConditionalTypeError {
    ExpansionLimitExceeded { limit: usize },
    NoCommonContravariantCandidate,
    UnsupportedTemplatePlaceholder(TypeId),
    MappedKeyIsNotPropertyKey(TypeId),
    StructuralDepthExceeded { limit: usize },
}

/// Variance position occupied by an `infer` variable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InferPosition {
    Covariant,
    Contravariant,
}

impl InferPosition {
    fn inverted(self) -> Self {
        match self {
            Self::Covariant => Self::Contravariant,
            Self::Contravariant => Self::Covariant,
        }
    }
}

/// A resolved extends-pattern containing zero or more `infer` captures.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InferPattern {
    Exact(TypeId),
    Capture(SymbolId),
    Array(Box<Self>),
    Object(Box<[(Box<str>, Self)]>),
    Function {
        parameters: Box<[Self]>,
        return_type: Box<Self>,
    },
    Template(TemplateInferPattern),
}

/// One placeholder in a template extends-pattern.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TemplateInferSpan {
    Capture(SymbolId),
    Exact(TypeId),
}

/// A template extends-pattern such as `` `${infer Head}-${infer Tail}` ``.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TemplateInferPattern {
    pub head: Box<str>,
    /// Each placeholder is followed by its literal delimiter.
    pub spans: Box<[(TemplateInferSpan, Box<str>)]>,
}

/// A semantic conditional type ready for evaluation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConditionalType {
    pub check_type: TypeId,
    pub extends_pattern: InferPattern,
    pub true_type: TypeId,
    pub false_type: TypeId,
    /// True only when the source check was a naked type parameter.
    pub distributive: bool,
}

/// One semantic template-literal type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TemplateLiteralType {
    pub head: Box<str>,
    /// Each placeholder is followed by its literal tail.
    pub spans: Box<[(TypeId, Box<str>)]>,
}

/// One mapped-type evaluation request.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MappedType {
    /// Object supplying preserved optional/readonly modifiers, when homomorphic.
    pub source: Option<TypeId>,
    pub keys: TypeId,
    pub parameter: SymbolId,
    pub name_type: Option<TypeId>,
    pub value_type: TypeId,
    pub optional_modifier: MappedModifier,
    pub readonly_modifier: MappedModifier,
    /// Canonical readonly facts for `source`; `PropertyType` itself has no
    /// readonly bit, so the mapped result carries these facts separately too.
    pub source_readonly: BTreeSet<Box<str>>,
}

/// The canonical object type plus readonly facts not represented in `TypeTable`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MappedTypeResult {
    pub type_id: TypeId,
    pub readonly_properties: BTreeSet<Box<str>>,
}

#[derive(Clone, Debug)]
struct CaptureCandidate {
    position: InferPosition,
    type_id: TypeId,
}

/// Stateful evaluator. The only mutable graph is the canonical type table.
pub struct ConditionalTypeEvaluator<'table> {
    types: &'table mut TypeTable,
    expansion_limit: usize,
    depth_limit: usize,
}

impl<'table> ConditionalTypeEvaluator<'table> {
    #[must_use]
    pub fn new(types: &'table mut TypeTable) -> Self {
        Self::with_limits(types, DEFAULT_EXPANSION_LIMIT, 100)
    }

    #[must_use]
    pub fn with_limits(
        types: &'table mut TypeTable,
        expansion_limit: usize,
        depth_limit: usize,
    ) -> Self {
        Self {
            types,
            expansion_limit,
            depth_limit,
        }
    }

    /// Evaluates a conditional type, distributing only a naked check type.
    pub fn evaluate_conditional(
        &mut self,
        conditional: &ConditionalType,
    ) -> Result<TypeId, ConditionalTypeError> {
        if matches!(self.types.get(conditional.check_type), Type::Never) && conditional.distributive
        {
            return Ok(self.types.never());
        }
        let members = match self.types.get(conditional.check_type) {
            Type::Union(members) if conditional.distributive => members.clone(),
            _ => vec![conditional.check_type],
        };
        let mut results = Vec::with_capacity(members.len());
        for member in members {
            let mut captures = BTreeMap::<SymbolId, Vec<CaptureCandidate>>::new();
            let selected = if self.match_pattern(
                member,
                &conditional.extends_pattern,
                InferPosition::Covariant,
                &mut captures,
                0,
            )? {
                let substitutions = self.resolve_captures(captures)?;
                self.substitute(conditional.true_type, &substitutions, 0)?
            } else {
                conditional.false_type
            };
            results.push(selected);
        }
        let result = self.types.union(&results);
        self.check_type_depth(result, 0, &mut HashSet::new())?;
        Ok(result)
    }

    /// Evaluates a template-literal type, including finite union cross products.
    pub fn evaluate_template_literal(
        &mut self,
        template: &TemplateLiteralType,
    ) -> Result<TypeId, ConditionalTypeError> {
        let mut products = vec![template.head.to_string()];
        for (placeholder, tail) in &template.spans {
            let Some(values) = self.template_values(*placeholder)? else {
                return Ok(self.types.string());
            };
            let next_len = products.len().saturating_mul(values.len());
            if next_len > self.expansion_limit {
                return Err(ConditionalTypeError::ExpansionLimitExceeded {
                    limit: self.expansion_limit,
                });
            }
            let mut next = Vec::with_capacity(next_len);
            for prefix in &products {
                for value in &values {
                    let mut expanded =
                        String::with_capacity(prefix.len() + value.len() + tail.len());
                    expanded.push_str(prefix);
                    expanded.push_str(value);
                    expanded.push_str(tail);
                    next.push(expanded);
                }
            }
            products = next;
        }
        let literals = products
            .iter()
            .map(|product| self.types.string_literal(product))
            .collect::<Vec<_>>();
        Ok(self.types.union(&literals))
    }

    /// Evaluates a mapped type, including key remapping and `+`/`-` modifiers.
    pub fn evaluate_mapped_type(
        &mut self,
        mapped: &MappedType,
    ) -> Result<MappedTypeResult, ConditionalTypeError> {
        let keys = self.literal_keys(mapped.keys)?;
        if keys.len() > self.expansion_limit {
            return Err(ConditionalTypeError::ExpansionLimitExceeded {
                limit: self.expansion_limit,
            });
        }
        let source_properties = mapped
            .source
            .and_then(|source| match self.types.get(source) {
                Type::ObjectType(object) => Some(object.properties().to_vec()),
                _ => None,
            })
            .unwrap_or_default();

        let mut properties = Vec::new();
        let mut generated_names = 0usize;
        let mut readonly_properties = BTreeSet::new();
        for key in keys {
            let key_type = self.types.string_literal(&key);
            let substitutions = BTreeMap::from([(mapped.parameter, key_type)]);
            let names = if let Some(name_type) = mapped.name_type {
                let remapped = self.substitute(name_type, &substitutions, 0)?;
                self.literal_keys(remapped)?
            } else {
                vec![key.clone()]
            };
            generated_names = generated_names.saturating_add(names.len());
            if generated_names > self.expansion_limit {
                return Err(ConditionalTypeError::ExpansionLimitExceeded {
                    limit: self.expansion_limit,
                });
            }
            let value_type = self.substitute(mapped.value_type, &substitutions, 0)?;
            let source_property = source_properties
                .iter()
                .find(|property| property.name() == key);
            let optional = match mapped.optional_modifier {
                MappedModifier::Preserve => source_property.is_some_and(PropertyType::optional),
                MappedModifier::Add => true,
                MappedModifier::Remove => false,
            };
            let readonly = match mapped.readonly_modifier {
                MappedModifier::Preserve => mapped.source_readonly.contains(key.as_str()),
                MappedModifier::Add => true,
                MappedModifier::Remove => false,
            };
            for name in names {
                if readonly {
                    readonly_properties.insert(name.clone().into_boxed_str());
                }
                if let Some(index) = properties
                    .iter()
                    .position(|property: &PropertyType| property.name() == name)
                {
                    let existing = &properties[index];
                    let merged_type = self.types.union(&[existing.type_id(), value_type]);
                    properties[index] =
                        PropertyType::new(name, existing.optional() || optional, merged_type);
                } else {
                    properties.push(PropertyType::new(name, optional, value_type));
                }
            }
        }
        Ok(MappedTypeResult {
            type_id: self.types.object_type(properties),
            readonly_properties,
        })
    }

    /// Computes canonical string-literal keys for an object type.
    pub fn keyof(&mut self, object: TypeId) -> Result<TypeId, ConditionalTypeError> {
        let keys = self.key_names(object, 0)?;
        let literals = keys
            .iter()
            .map(|key| self.types.string_literal(key))
            .collect::<Vec<_>>();
        Ok(self.types.union(&literals))
    }

    fn key_names(
        &self,
        object: TypeId,
        depth: usize,
    ) -> Result<BTreeSet<Box<str>>, ConditionalTypeError> {
        self.check_depth(depth)?;
        match self.types.get(object) {
            Type::ObjectType(object) => Ok(object
                .properties()
                .iter()
                .map(|property| Box::<str>::from(property.name()))
                .collect()),
            Type::Union(members) => {
                let Some((first, rest)) = members.split_first() else {
                    return Ok(BTreeSet::new());
                };
                let mut keys = self.key_names(*first, depth + 1)?;
                for member in rest {
                    let member_keys = self.key_names(*member, depth + 1)?;
                    keys.retain(|key| member_keys.contains(key));
                }
                Ok(keys)
            }
            Type::Array(_) => Ok(BTreeSet::from([Box::<str>::from("length")])),
            Type::Any | Type::Unknown | Type::Object => Ok(BTreeSet::new()),
            _ => Ok(BTreeSet::new()),
        }
    }

    fn match_pattern(
        &mut self,
        candidate: TypeId,
        pattern: &InferPattern,
        position: InferPosition,
        captures: &mut BTreeMap<SymbolId, Vec<CaptureCandidate>>,
        depth: usize,
    ) -> Result<bool, ConditionalTypeError> {
        self.check_depth(depth)?;
        match pattern {
            InferPattern::Exact(expected) => Ok(self.types.assignable(candidate, *expected)),
            InferPattern::Capture(symbol) => {
                captures.entry(*symbol).or_default().push(CaptureCandidate {
                    position,
                    type_id: candidate,
                });
                Ok(true)
            }
            InferPattern::Array(element_pattern) => {
                let Type::Array(element) = self.types.get(candidate) else {
                    return Ok(false);
                };
                let element = *element;
                self.match_pattern(element, element_pattern, position, captures, depth + 1)
            }
            InferPattern::Object(pattern_properties) => {
                let Type::ObjectType(candidate_properties) = self.types.get(candidate).clone()
                else {
                    return Ok(false);
                };
                for (name, property_pattern) in pattern_properties {
                    let Some(property) = candidate_properties
                        .properties()
                        .iter()
                        .find(|property| property.name() == name.as_ref())
                    else {
                        return Ok(false);
                    };
                    if !self.match_pattern(
                        property.type_id(),
                        property_pattern,
                        position,
                        captures,
                        depth + 1,
                    )? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            InferPattern::Function {
                parameters,
                return_type,
            } => {
                let Type::Function(signature) = self.types.get(candidate).clone() else {
                    return Ok(false);
                };
                if signature.parameters().len() != parameters.len() {
                    return Ok(false);
                }
                for (parameter, parameter_pattern) in signature.parameters().iter().zip(parameters)
                {
                    if !self.match_pattern(
                        parameter.type_id(),
                        parameter_pattern,
                        position.inverted(),
                        captures,
                        depth + 1,
                    )? {
                        return Ok(false);
                    }
                }
                self.match_pattern(
                    signature.return_type(),
                    return_type,
                    position,
                    captures,
                    depth + 1,
                )
            }
            InferPattern::Template(template) => {
                let Type::StringLiteral(text) = self.types.get(candidate) else {
                    return Ok(false);
                };
                let text = text
                    .to_utf8_strict()
                    .map_err(|_| ConditionalTypeError::UnsupportedTemplatePlaceholder(candidate))?;
                let Some(values) = match_template(&text, template) else {
                    return Ok(false);
                };
                for ((span, _), value) in template.spans.iter().zip(values) {
                    match span {
                        TemplateInferSpan::Capture(symbol) => {
                            let type_id = self.types.string_literal(value);
                            captures
                                .entry(*symbol)
                                .or_default()
                                .push(CaptureCandidate { position, type_id });
                        }
                        TemplateInferSpan::Exact(expected) => {
                            if !template_segment_matches(self.types, value, *expected) {
                                return Ok(false);
                            }
                        }
                    }
                }
                Ok(true)
            }
        }
    }

    fn resolve_captures(
        &mut self,
        captures: BTreeMap<SymbolId, Vec<CaptureCandidate>>,
    ) -> Result<BTreeMap<SymbolId, TypeId>, ConditionalTypeError> {
        let mut resolved = BTreeMap::new();
        for (symbol, candidates) in captures {
            let has_contravariant = candidates
                .iter()
                .any(|candidate| candidate.position == InferPosition::Contravariant);
            let type_id = if has_contravariant {
                let contravariant = candidates
                    .iter()
                    .filter(|candidate| candidate.position == InferPosition::Contravariant)
                    .map(|candidate| candidate.type_id)
                    .collect::<Vec<_>>();
                contravariant
                    .iter()
                    .copied()
                    .find(|candidate| {
                        contravariant
                            .iter()
                            .all(|other| self.types.assignable(*candidate, *other))
                    })
                    .ok_or(ConditionalTypeError::NoCommonContravariantCandidate)?
            } else {
                let covariant = candidates
                    .iter()
                    .map(|candidate| candidate.type_id)
                    .collect::<Vec<_>>();
                self.types.union(&covariant)
            };
            resolved.insert(symbol, type_id);
        }
        Ok(resolved)
    }

    fn substitute(
        &mut self,
        type_id: TypeId,
        substitutions: &BTreeMap<SymbolId, TypeId>,
        depth: usize,
    ) -> Result<TypeId, ConditionalTypeError> {
        self.check_depth(depth)?;
        let inferred = substitutions
            .iter()
            .map(|(&symbol, &type_id)| {
                InferredTypeArgument::new(symbol, type_id, InferenceProvenance::Inferred)
            })
            .collect();
        let instantiated = InferredTypeArguments::new(inferred).instantiate(self.types, type_id);
        self.check_type_depth(instantiated, depth, &mut HashSet::new())?;
        Ok(instantiated)
    }

    fn check_type_depth(
        &self,
        type_id: TypeId,
        depth: usize,
        visiting: &mut HashSet<TypeId>,
    ) -> Result<(), ConditionalTypeError> {
        self.check_depth(depth)?;
        if !visiting.insert(type_id) {
            return Ok(());
        }

        let child_depth = depth.saturating_add(1);
        let result = match self.types.get(type_id).clone() {
            Type::Array(element) | Type::Keyof(element) => {
                self.check_type_depth(element, child_depth, visiting)
            }
            Type::Tuple(shape) => shape
                .prefix
                .into_iter()
                .chain(shape.rest)
                .chain(shape.suffix)
                .try_for_each(|element| self.check_type_depth(element, child_depth, visiting)),
            Type::Union(members) | Type::Intersection(members) => members
                .into_iter()
                .try_for_each(|member| self.check_type_depth(member, child_depth, visiting)),
            Type::ObjectType(object) => {
                let mut children = object
                    .properties
                    .into_iter()
                    .map(|property| property.type_id())
                    .chain(object.generator_return)
                    .chain(object.iterator_property.map(|property| property.type_id()))
                    .chain(
                        object
                            .async_iterator_property
                            .map(|property| property.type_id()),
                    )
                    .collect::<Vec<_>>();
                for signature in object.call_signatures {
                    Self::signature_children(&signature, &mut children);
                }
                for entry in object.construct_signatures {
                    Self::signature_children(&entry.signature, &mut children);
                }
                for signature in object.index_signatures {
                    children.extend(
                        signature
                            .parameters
                            .into_iter()
                            .map(|parameter| parameter.type_id()),
                    );
                    children.push(signature.value_type);
                }
                children
                    .into_iter()
                    .try_for_each(|child| self.check_type_depth(child, child_depth, visiting))
            }
            Type::Function(signature) => {
                let mut children = Vec::new();
                Self::signature_children(&signature, &mut children);
                children
                    .into_iter()
                    .try_for_each(|child| self.check_type_depth(child, child_depth, visiting))
            }
            Type::AppliedClass { arguments, .. } | Type::AppliedAlias { arguments, .. } => {
                arguments
                    .into_iter()
                    .try_for_each(|argument| self.check_type_depth(argument, child_depth, visiting))
            }
            Type::ConstructorType {
                arguments,
                structural,
                ..
            } => arguments
                .into_iter()
                .try_for_each(|argument| self.check_type_depth(argument, child_depth, visiting))
                .and_then(|()| self.check_type_depth(structural, child_depth, visiting)),
            Type::TypeQuery {
                arguments, target, ..
            } => arguments
                .into_iter()
                .try_for_each(|argument| self.check_type_depth(argument, child_depth, visiting))
                .and_then(|()| self.check_type_depth(target, child_depth, visiting)),
            Type::IndexedAccess { object, index } => self
                .check_type_depth(object, child_depth, visiting)
                .and_then(|()| self.check_type_depth(index, child_depth, visiting)),
            Type::Record { key, value } => self
                .check_type_depth(key, child_depth, visiting)
                .and_then(|()| self.check_type_depth(value, child_depth, visiting)),
            Type::This { constraint, .. } => {
                self.check_type_depth(constraint, child_depth, visiting)
            }
            Type::Error
            | Type::Any
            | Type::Unknown
            | Type::Never
            | Type::Void
            | Type::Null
            | Type::Undefined
            | Type::Boolean
            | Type::Number
            | Type::BigInt
            | Type::String
            | Type::Symbol
            | Type::Object
            | Type::BooleanLiteral(_)
            | Type::NumberLiteral(_)
            | Type::StringLiteral(_)
            | Type::BigIntLiteral(_)
            | Type::Named(_)
            | Type::NumericEnum(_)
            | Type::EnumMember { .. } => Ok(()),
        };
        visiting.remove(&type_id);
        result
    }

    fn signature_children(signature: &FunctionSignature, children: &mut Vec<TypeId>) {
        children.extend(
            signature
                .type_parameter_bounds()
                .iter()
                .flat_map(|bounds| [bounds.constraint(), bounds.default()])
                .flatten(),
        );
        children.extend(
            signature
                .parameters()
                .iter()
                .map(FunctionParameter::type_id),
        );
        children.push(signature.return_type());
    }
    fn literal_keys(&self, type_id: TypeId) -> Result<Vec<String>, ConditionalTypeError> {
        match self.types.get(type_id) {
            Type::StringLiteral(value) => value
                .to_utf8_strict()
                .map(|value| vec![value])
                .map_err(|_| ConditionalTypeError::UnsupportedTemplatePlaceholder(type_id)),
            Type::Union(members) => {
                let mut keys = Vec::new();
                for member in members {
                    keys.extend(self.literal_keys(*member)?);
                }
                keys.sort();
                keys.dedup();
                Ok(keys)
            }
            Type::Never
            | Type::Any
            | Type::Unknown
            | Type::Error
            | Type::Named(_)
            | Type::String
            | Type::Number
            | Type::BigInt
            | Type::Boolean
            | Type::Symbol => Ok(Vec::new()),
            _ => Err(ConditionalTypeError::MappedKeyIsNotPropertyKey(type_id)),
        }
    }

    fn template_values(
        &self,
        type_id: TypeId,
    ) -> Result<Option<Vec<String>>, ConditionalTypeError> {
        match self.types.get(type_id) {
            Type::StringLiteral(value) => value
                .to_utf8_strict()
                .map(|value| Some(vec![value]))
                .map_err(|_| ConditionalTypeError::UnsupportedTemplatePlaceholder(type_id)),
            Type::NumberLiteral(value) => Ok(Some(vec![value.to_string()])),
            Type::BigIntLiteral(value) => Ok(Some(vec![value.trim_end_matches('n').to_owned()])),
            Type::BooleanLiteral(value) => Ok(Some(vec![value.to_string()])),
            Type::Null => Ok(Some(vec!["null".to_owned()])),
            Type::Undefined => Ok(Some(vec!["undefined".to_owned()])),
            Type::String
            | Type::Number
            | Type::BigInt
            | Type::Boolean
            | Type::Any
            | Type::Unknown
            | Type::Error
            | Type::Named(_) => Ok(None),
            Type::Union(members) => {
                let mut values = Vec::new();
                for member in members {
                    let Some(member_values) = self.template_values(*member)? else {
                        return Ok(None);
                    };
                    values.extend(member_values);
                }
                values.sort();
                values.dedup();
                Ok(Some(values))
            }
            _ => Err(ConditionalTypeError::UnsupportedTemplatePlaceholder(
                type_id,
            )),
        }
    }

    fn check_depth(&self, depth: usize) -> Result<(), ConditionalTypeError> {
        if depth > self.depth_limit {
            Err(ConditionalTypeError::StructuralDepthExceeded {
                limit: self.depth_limit,
            })
        } else {
            Ok(())
        }
    }
}

fn template_segment_matches(types: &TypeTable, value: &str, expected: TypeId) -> bool {
    match types.get(expected) {
        Type::Any | Type::Unknown | Type::Error | Type::Named(_) | Type::String => true,
        Type::Never => false,
        Type::StringLiteral(expected) => {
            expected.as_units().iter().copied().eq(value.encode_utf16())
        }
        Type::Number => value.parse::<f64>().is_ok(),
        Type::NumberLiteral(expected) => value
            .parse::<f64>()
            .ok()
            .zip(expected.parse::<f64>().ok())
            .is_some_and(|(value, expected)| value == expected),
        Type::BigInt => {
            let digits = value.strip_prefix('-').unwrap_or(value);
            !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit())
        }
        Type::BigIntLiteral(expected) => value == expected.as_ref(),
        Type::Boolean => matches!(value, "true" | "false"),
        Type::BooleanLiteral(expected) => value == expected.to_string(),
        Type::Union(members) => members
            .iter()
            .any(|member| template_segment_matches(types, value, *member)),
        _ => false,
    }
}

fn match_template<'text>(
    text: &'text str,
    pattern: &TemplateInferPattern,
) -> Option<Vec<&'text str>> {
    let mut remaining = text.strip_prefix(pattern.head.as_ref())?;
    let mut captures = Vec::with_capacity(pattern.spans.len());
    for (index, (_, delimiter)) in pattern.spans.iter().enumerate() {
        if delimiter.is_empty() && index + 1 == pattern.spans.len() {
            captures.push(remaining);
            remaining = "";
            continue;
        }
        let boundary = remaining.find(delimiter.as_ref())?;
        captures.push(&remaining[..boundary]);
        remaining = &remaining[boundary + delimiter.len()..];
    }
    remaining.is_empty().then_some(captures)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn naked_conditional_distributes_and_infers_independently() {
        let mut types = TypeTable::new();
        let infer = SymbolId::new(1);
        let infer_type = types.named(infer);
        let number_array = types.array(types.number());
        let string_array = types.array(types.string());
        let check = types.union(&[number_array, string_array, types.boolean()]);
        let conditional = ConditionalType {
            check_type: check,
            extends_pattern: InferPattern::Array(Box::new(InferPattern::Capture(infer))),
            true_type: infer_type,
            false_type: types.never(),
            distributive: true,
        };
        let mut evaluator = ConditionalTypeEvaluator::new(&mut types);
        let result = evaluator.evaluate_conditional(&conditional).unwrap();
        let expected = evaluator
            .types
            .union(&[evaluator.types.number(), evaluator.types.string()]);
        assert_eq!(result, expected);
    }

    #[test]
    fn wrapped_conditional_does_not_distribute() {
        let mut types = TypeTable::new();
        let check = types.union(&[types.number(), types.string()]);
        let conditional = ConditionalType {
            check_type: check,
            extends_pattern: InferPattern::Exact(types.number()),
            true_type: types.boolean_literal(true),
            false_type: types.boolean_literal(false),
            distributive: false,
        };
        let mut evaluator = ConditionalTypeEvaluator::new(&mut types);
        let expected = evaluator.types.boolean_literal(false);
        assert_eq!(evaluator.evaluate_conditional(&conditional), Ok(expected));
    }

    #[test]
    fn template_literals_form_a_finite_cross_product() {
        let mut types = TypeTable::new();
        let get = types.string_literal("get");
        let set = types.string_literal("set");
        let method = types.union(&[get, set]);
        let user = types.string_literal("User");
        let post = types.string_literal("Post");
        let resource = types.union(&[user, post]);
        let template = TemplateLiteralType {
            head: "".into(),
            spans: vec![(method, "".into()), (resource, "".into())].into(),
        };
        let mut evaluator = ConditionalTypeEvaluator::new(&mut types);
        let result = evaluator.evaluate_template_literal(&template).unwrap();
        let expected_members = ["getUser", "getPost", "setUser", "setPost"]
            .map(|value| evaluator.types.string_literal(value));
        let expected = evaluator.types.union(&expected_members);
        assert_eq!(result, expected);
    }

    #[test]
    fn template_infer_captures_delimited_segments() {
        let mut types = TypeTable::new();
        let head = SymbolId::new(1);
        let tail = SymbolId::new(2);
        let head_type = types.named(head);
        let candidate = types.string_literal("left-right");
        let conditional = ConditionalType {
            check_type: candidate,
            extends_pattern: InferPattern::Template(TemplateInferPattern {
                head: "".into(),
                spans: vec![
                    (TemplateInferSpan::Capture(head), "-".into()),
                    (TemplateInferSpan::Capture(tail), "".into()),
                ]
                .into(),
            }),
            true_type: head_type,
            false_type: types.never(),
            distributive: false,
        };
        let mut evaluator = ConditionalTypeEvaluator::new(&mut types);
        let expected = evaluator.types.string_literal("left");
        assert_eq!(evaluator.evaluate_conditional(&conditional), Ok(expected));
    }

    #[test]
    fn mapped_type_remaps_keys_and_applies_modifiers() {
        let mut types = TypeTable::new();
        let parameter = SymbolId::new(1);
        let parameter_type = types.named(parameter);
        let source = types.object_type(vec![
            PropertyType::new("x", true, types.number()),
            PropertyType::new("y", false, types.string()),
        ]);
        let x = types.string_literal("x");
        let y = types.string_literal("y");
        let keys = types.union(&[x, y]);
        let mapped = MappedType {
            source: Some(source),
            keys,
            parameter,
            name_type: Some(parameter_type),
            value_type: types.boolean(),
            optional_modifier: MappedModifier::Remove,
            readonly_modifier: MappedModifier::Add,
            source_readonly: BTreeSet::new(),
        };
        let mut evaluator = ConditionalTypeEvaluator::new(&mut types);
        let result = evaluator.evaluate_mapped_type(&mapped).unwrap();
        let expected = evaluator.types.object_type(vec![
            PropertyType::new("x", false, evaluator.types.boolean()),
            PropertyType::new("y", false, evaluator.types.boolean()),
        ]);
        assert_eq!(result.type_id, expected);
        assert_eq!(
            result.readonly_properties,
            BTreeSet::from([Box::<str>::from("x"), Box::<str>::from("y")])
        );
    }

    #[test]
    fn mapped_type_unions_values_when_remapped_keys_collide() {
        let mut types = TypeTable::new();
        let parameter = SymbolId::new(1);
        let parameter_type = types.named(parameter);
        let a = types.string_literal("a");
        let b = types.string_literal("b");
        let keys = types.union(&[a, b]);
        let remapped_name = types.string_literal("combined");
        let mapped = MappedType {
            source: None,
            keys,
            parameter,
            name_type: Some(remapped_name),
            value_type: parameter_type,
            optional_modifier: MappedModifier::Preserve,
            readonly_modifier: MappedModifier::Preserve,
            source_readonly: BTreeSet::new(),
        };
        let mut evaluator = ConditionalTypeEvaluator::new(&mut types);
        let result = evaluator.evaluate_mapped_type(&mapped).unwrap();
        let value_type = evaluator.types.union(&[a, b]);
        let expected = evaluator
            .types
            .object_type(vec![PropertyType::new("combined", false, value_type)]);
        assert_eq!(result.type_id, expected);
    }

    #[test]
    fn keyof_union_is_the_intersection_of_member_keys() {
        let mut types = TypeTable::new();
        let first = types.object_type(vec![
            PropertyType::new("shared", false, types.number()),
            PropertyType::new("first", false, types.number()),
        ]);
        let second = types.object_type(vec![
            PropertyType::new("shared", false, types.string()),
            PropertyType::new("second", false, types.string()),
        ]);
        let union = types.union(&[first, second]);
        let mut evaluator = ConditionalTypeEvaluator::new(&mut types);
        let result = evaluator.keyof(union).unwrap();
        let expected = evaluator.types.string_literal("shared");
        assert_eq!(result, expected);
    }

    #[test]
    fn mapped_remapping_expansion_limit_fails_closed() {
        let mut types = TypeTable::new();
        let parameter = SymbolId::new(1);
        let a = types.string_literal("a");
        let b = types.string_literal("b");
        let keys = types.union(&[a, b]);
        let x = types.string_literal("x");
        let y = types.string_literal("y");
        let names = types.union(&[x, y]);
        let mapped = MappedType {
            source: None,
            keys,
            parameter,
            name_type: Some(names),
            value_type: types.number(),
            optional_modifier: MappedModifier::Preserve,
            readonly_modifier: MappedModifier::Preserve,
            source_readonly: BTreeSet::new(),
        };
        let mut evaluator = ConditionalTypeEvaluator::with_limits(&mut types, 3, 100);
        assert_eq!(
            evaluator.evaluate_mapped_type(&mapped),
            Err(ConditionalTypeError::ExpansionLimitExceeded { limit: 3 })
        );
    }

    #[test]
    fn expansion_limit_fails_closed() {
        let mut types = TypeTable::new();
        let a = types.string_literal("a");
        let b = types.string_literal("b");
        let values = types.union(&[a, b]);
        let template = TemplateLiteralType {
            head: "".into(),
            spans: vec![(values, "".into()), (values, "".into())].into(),
        };
        let mut evaluator = ConditionalTypeEvaluator::with_limits(&mut types, 3, 100);
        assert_eq!(
            evaluator.evaluate_template_literal(&template),
            Err(ConditionalTypeError::ExpansionLimitExceeded { limit: 3 })
        );
    }

    #[test]
    fn recursive_substitution_obeys_the_structural_depth_limit() {
        let mut types = TypeTable::new();
        let parameter = SymbolId::new(1);
        let mut nested = types.named(parameter);
        for _ in 0..4 {
            nested = types.array(nested);
        }
        let conditional = ConditionalType {
            check_type: types.number(),
            extends_pattern: InferPattern::Capture(parameter),
            true_type: nested,
            false_type: types.never(),
            distributive: false,
        };
        let mut evaluator = ConditionalTypeEvaluator::with_limits(&mut types, 100, 2);
        assert_eq!(
            evaluator.evaluate_conditional(&conditional),
            Err(ConditionalTypeError::StructuralDepthExceeded { limit: 2 })
        );
    }

    #[test]
    fn selected_result_depth_is_checked_before_union_normalization() {
        let mut types = TypeTable::new();
        let number = types.number();
        let string = types.string();
        let check_type = types.union(&[number, string]);
        let mut nested = number;
        for _ in 0..4 {
            nested = types.array(nested);
        }
        let conditional = ConditionalType {
            check_type,
            extends_pattern: InferPattern::Exact(number),
            true_type: nested,
            false_type: types.any(),
            distributive: true,
        };
        let mut evaluator = ConditionalTypeEvaluator::with_limits(&mut types, 100, 2);
        assert_eq!(
            evaluator.evaluate_conditional(&conditional),
            Err(ConditionalTypeError::StructuralDepthExceeded { limit: 2 })
        );
    }

    #[test]
    fn distributed_union_layer_obeys_the_structural_depth_limit() {
        let mut types = TypeTable::new();
        let number = types.number();
        let string = types.string();
        let check_type = types.union(&[number, string]);
        let mut true_type = number;
        let mut false_type = string;
        for _ in 0..2 {
            true_type = types.array(true_type);
            false_type = types.array(false_type);
        }
        let conditional = ConditionalType {
            check_type,
            extends_pattern: InferPattern::Exact(number),
            true_type,
            false_type,
            distributive: true,
        };
        let mut evaluator = ConditionalTypeEvaluator::with_limits(&mut types, 100, 2);
        assert_eq!(
            evaluator.evaluate_conditional(&conditional),
            Err(ConditionalTypeError::StructuralDepthExceeded { limit: 2 })
        );
    }
}
