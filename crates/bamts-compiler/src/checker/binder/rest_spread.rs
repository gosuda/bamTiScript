use std::borrow::Cow;

use super::{Binder, ObjectType, PropertyType, Type, TypeId};
use crate::syntax::Accessibility;

impl<'src> Binder<'src> {
    pub(super) fn is_spread_excluded(property: &PropertyType) -> bool {
        property.access() != Accessibility::Public
            || (property.declaring_class().is_some()
                && (property.is_method() || property.accessor()))
    }

    /// Computes the type an object-pattern rest element binds from `source`
    /// after removing `excluded` sibling names. Class prototype members and
    /// non-public members never spread, mirroring the object-literal spread
    /// rule above. Sources that do not resolve to a concrete object shape
    /// pass through unchanged.
    pub(super) fn rest_spread_source(&mut self, source: TypeId, excluded: &[String]) -> TypeId {
        let mut view = self
            .types
            .prepare_applied_alias_view(source)
            .unwrap_or(source);
        if let Type::Named(symbol) = self.types.get(view).clone() {
            if let Some(constraint) = self.types.type_parameter_constraint(symbol) {
                if constraint != view {
                    view = constraint;
                }
            } else {
                let resolved = self.resolve_named_type_symbol(symbol);
                if resolved != view {
                    view = resolved;
                }
            }
        }
        if let Type::This { constraint, .. } = self.types.get(view).clone() {
            view = constraint;
        }
        view = self.types.prepare_applied_class_view(view).unwrap_or(view);
        if let Type::Union(members) = self.types.get(view).clone() {
            let mut rests = Vec::with_capacity(members.len());
            for member in members {
                if matches!(self.types.get(member), Type::Null | Type::Undefined) {
                    continue;
                }
                rests.push(self.rest_spread_source(member, excluded));
            }
            if rests.is_empty() {
                return self.types.object_type_with_members(ObjectType {
                    properties: Vec::new(),
                    call_signatures: Vec::new(),
                    call_candidate_order: Vec::new(),
                    construct_signatures: Vec::new(),
                    index_signatures: Vec::new(),
                    generator_return: None,
                    iterator_property: None,
                    async_iterator_property: None,
                });
            }
            if rests.len() == 1 {
                return rests[0];
            }
            return self.types.union(&rests);
        }
        let (structural, statics) = match self.types.get(view).clone() {
            Type::ConstructorType { structural, .. } => (structural, true),
            _ => (view, false),
        };
        let Some(object) = self.types.current_object_view(structural) else {
            return source;
        };
        if matches!(&object, Cow::Borrowed(_))
            && excluded.is_empty()
            && !object.properties.iter().any(Self::is_spread_excluded)
            && !statics
        {
            return source;
        }
        let mut object = object.into_owned();
        object.properties.retain(|property| {
            if excluded.iter().any(|name| name.as_str() == property.name()) {
                return false;
            }
            if statics {
                property.access() == Accessibility::Public
            } else {
                !Self::is_spread_excluded(property)
            }
        });
        self.types.object_type_with_members(object)
    }
}
