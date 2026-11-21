use super::{Binder, ScopeId, SymbolId, SymbolKind, Type, TypeId};
use crate::checker::{PROPERTY_DOES_NOT_EXIST, PROPERTY_DOES_NOT_EXIST_MESSAGE};
use crate::syntax::{Expr, MemberProperty};
use bamts_bytecode::EcmaString;

impl<'src> Binder<'src> {
    /// Types a `#name` member access. Undeclared private names report the
    /// missing-property diagnostic, matching the authority treatment of
    /// `#bar` on `any` and every `#name` on `never`. Declared names keep
    /// the established silent `any` read.
    pub(super) fn type_of_private_member(
        &mut self,
        object: &'src Expr,
        property: &'src MemberProperty,
        scope: ScopeId,
    ) -> (TypeId, bool) {
        let MemberProperty::Private(identifier) = property else {
            return (self.types.any(), false);
        };
        let object_type = self.legacy_type_of_expr(object, scope);
        if matches!(self.types.get(object_type), Type::Never) {
            self.emit(
                PROPERTY_DOES_NOT_EXIST,
                identifier.range(),
                PROPERTY_DOES_NOT_EXIST_MESSAGE,
            );
            return (self.types.error_type(), false);
        }
        if matches!(self.types.get(object_type), Type::Any | Type::Unknown) {
            let declared = self
                .member_symbol_name(property)
                .is_some_and(|name| self.private_name_declared(&name));
            if !declared {
                self.emit(
                    PROPERTY_DOES_NOT_EXIST,
                    identifier.range(),
                    PROPERTY_DOES_NOT_EXIST_MESSAGE,
                );
                return (self.types.error_type(), false);
            }
            return (self.types.any(), false);
        }
        if self
            .private_member_owner(object, object_type)
            .is_some_and(|owner| {
                self.member_symbol(owner, &self.private_member_key(property))
                    .is_some()
            })
        {
            return (self.types.any(), false);
        }
        self.emit(
            PROPERTY_DOES_NOT_EXIST,
            identifier.range(),
            PROPERTY_DOES_NOT_EXIST_MESSAGE,
        );
        (self.types.error_type(), false)
    }

    /// The `#`-prefixed lookup key for a private member reference, or an
    /// empty key when the property is not a private name.
    pub(super) fn private_member_key(&self, property: &MemberProperty) -> EcmaString {
        self.member_symbol_name(property).unwrap_or_default()
    }

    /// Whether `#name` is declared in any class member scope in the program.
    /// Undeclared names cannot resolve on `any` receivers either.
    pub(super) fn private_name_declared(&self, name: &EcmaString) -> bool {
        let key = name.to_utf8_lossy();
        self.declared_private_names.contains(&*key)
    }

    /// The class that owns `#name` lookup for this receiver, when the
    /// receiver denotes a class instance, static side, or `this`.
    pub(super) fn private_member_owner(
        &self,
        object: &'src Expr,
        object_type: TypeId,
    ) -> Option<SymbolId> {
        if let Some(symbol) = self.resolved_expression_reference(object)
            && self.symbols[symbol.get() as usize].kind == SymbolKind::Class
        {
            return Some(symbol);
        }
        match self.types.get(object_type).clone() {
            Type::AppliedClass { symbol, .. } => Some(symbol),
            Type::ConstructorType { symbol, .. } => Some(symbol),
            Type::This { owner, .. } => Some(owner),
            _ => None,
        }
    }
}
