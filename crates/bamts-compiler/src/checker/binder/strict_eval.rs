use super::{Binder, ScopeId, ScopeKind, SymbolKind};
use crate::checker::diagnostic_messages::{Args, by_u32};
use crate::checker::{
    EVAL_OR_ARGUMENTS_IN_CLASS, EVAL_OR_ARGUMENTS_IN_MODULE, EVAL_OR_ARGUMENTS_IN_STRICT_MODE,
};
use crate::diagnostic::DiagnosticCode;
use crate::source::TextRange;
use crate::syntax::{Ty, TypeMember, TypeNode};

impl<'src> Binder<'src> {
    pub(super) fn scope_enclosed_in_class(&self, scope: ScopeId) -> bool {
        let mut current = Some(scope);
        while let Some(id) = current {
            let candidate = &self.scopes[id.0 as usize];
            if candidate.kind == ScopeKind::Class {
                let interface_owned = candidate.owner.is_some_and(|owner| {
                    self.symbols[owner.get() as usize].kind == SymbolKind::Interface
                });
                if !interface_owned {
                    return true;
                }
            }
            current = candidate.parent;
        }
        false
    }

    pub(super) fn strict_eval_or_arguments_code(
        &self,
        scope: ScopeId,
    ) -> Option<(DiagnosticCode, u32)> {
        if self.ambient_binding
            || self.ambient_stack.last().copied().unwrap_or(false)
            || self.is_declaration_file
        {
            return None;
        }
        if !self.scopes[scope.0 as usize].is_strict() && !self.file_has_dynamic_import {
            return None;
        }
        if self.scope_enclosed_in_class(scope) {
            return Some((EVAL_OR_ARGUMENTS_IN_CLASS, 1210));
        }
        if self.is_module {
            return Some((EVAL_OR_ARGUMENTS_IN_MODULE, 1215));
        }
        Some((EVAL_OR_ARGUMENTS_IN_STRICT_MODE, 1100))
    }

    pub(super) fn emit_strict_eval_or_arguments(
        &mut self,
        name: &str,
        scope: ScopeId,
        range: TextRange,
    ) {
        if range.start().get() == range.end().get() {
            return;
        }
        if !matches!(name, "eval" | "arguments") {
            return;
        }
        let Some((code, numeric)) = self.strict_eval_or_arguments_code(scope) else {
            return;
        };
        if !self.strict_eval_reported.insert(range) {
            return;
        }
        let message = by_u32(numeric)
            .and_then(|entry| entry.format(Args::new([name])).ok())
            .unwrap_or_else(|| format!("Invalid use of '{name}' in strict mode."));
        self.emit_with_message(code, range, message);
    }

    pub(super) fn check_function_type_parameters(
        &mut self,
        parameters: &[crate::syntax::FunctionTypeParameter],
        scope: ScopeId,
    ) {
        for parameter in parameters {
            let name = self.identifier_text(&parameter.name);
            if name.as_ref() == "this" {
                continue;
            }
            self.emit_strict_eval_or_arguments(name.as_ref(), scope, parameter.name.range());
        }
    }

    pub(super) fn check_type_member_eval_or_arguments(
        &mut self,
        member: &'src crate::syntax::TypeMemberNode,
        scope: ScopeId,
        stack: &mut Vec<&'src Ty>,
    ) {
        match member.data() {
            TypeMember::Call(call) => {
                self.check_function_type_parameters(&call.function.parameters, scope);
                stack.push(&call.function.return_type);
            }
            TypeMember::Construct(construct) => {
                self.check_function_type_parameters(&construct.function.function.parameters, scope);
                stack.push(&construct.function.function.return_type);
            }
            TypeMember::Method(method) => {
                self.check_function_type_parameters(&method.function.parameters, scope);
                stack.push(&method.function.return_type);
            }
            TypeMember::Property(property) => {
                if let Some(annotation) = &property.type_annotation {
                    stack.push(&annotation.data().type_node);
                }
            }
            TypeMember::Index(index) => {
                stack.push(&index.type_annotation.data().type_node);
                for parameter in &index.parameters {
                    stack.push(&parameter.type_annotation.data().type_node);
                }
            }
            TypeMember::Missing(_) => {}
        }
    }

    pub(super) fn check_single_type_node_eval_or_arguments(
        &mut self,
        node: &'src Ty,
        scope: ScopeId,
        stack: &mut Vec<&'src Ty>,
    ) {
        match node.data() {
            TypeNode::Function(function) => {
                self.check_function_type_parameters(&function.parameters, scope);
                stack.push(&function.return_type);
            }
            TypeNode::Constructor(constructor) => {
                self.check_function_type_parameters(&constructor.function.parameters, scope);
                stack.push(&constructor.function.return_type);
            }
            TypeNode::Object(object) => {
                for member in &object.members {
                    self.check_type_member_eval_or_arguments(member, scope, stack);
                }
            }
            TypeNode::Parenthesized(inner) => stack.push(inner),
            TypeNode::Union(members) | TypeNode::Intersection(members) => stack.extend(members),
            _ => {}
        }
    }

    pub(super) fn check_type_node_eval_or_arguments(&mut self, node: &'src Ty, scope: ScopeId) {
        let mut stack = vec![node];
        while let Some(current) = stack.pop() {
            self.check_single_type_node_eval_or_arguments(current, scope, &mut stack);
        }
    }
}
