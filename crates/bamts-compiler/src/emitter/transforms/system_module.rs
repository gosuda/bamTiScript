//! System.register: the module body inside a factory that receives the export
//! function and the module context.
//!
//! `System.register([deps], function (exports_1, context_1) { ... })` lists the
//! dependencies up front; the setters the loader runs first assign each import
//! local, and `execute` runs the body. Every `var` of the module scope hoists
//! to the factory level, exported functions hoist above `return`, and each
//! value an export publishes goes out through `exports_1(name, value)`.

use std::collections::{BTreeSet, HashSet};

use crate::checker::{SemanticModel, SymbolId, SymbolKind};
use crate::emitter::{ModuleWrapper, temp_names::TempNames};
use crate::source::TextRange;
use crate::syntax::*;

use super::namespaces::{
    ContainerBinding, ExportSink, alias_target_bears_value, is_qualified_alias,
};
use super::{
    CaptureScope, CjsPlan, RequireNames, Rewriter, collect_target_identifiers,
    declared_binding_names, exported_locals, identifier_text, is_identifier_name,
    is_type_only_export, module_export_text, module_specifier, quote_module_specifier,
    quote_string,
};

/// One action a dependency's setter performs, in statement order.
pub(super) enum SetterAction {
    /// `local = param;`
    Assign(String),
    /// `exportStar_1(param);`
    Star,
    /// `exports_1({ "a": param["a"] });` for `export {a as b} from`.
    Object(Vec<(String, String)>),
    /// `exports_1("ns", param);` for `export * as ns from`.
    NamespaceObject(String),
}

/// One module the factory depends on.
pub(super) struct SystemDependency {
    pub(super) specifier: String,
    /// A module-level name no setter assigns, which still names the parameter:
    /// the implicit local of a star export.
    pub(super) implicit: Option<String>,
    pub(super) actions: Vec<SetterAction>,
}

/// Per-file System lowering plan built before the rewrite walk.
#[derive(Default)]
pub(super) struct SystemPlan {
    /// The `amd-module` directive's name, which becomes the first argument.
    pub(super) module_name: Option<String>,
    pub(super) dependencies: Vec<SystemDependency>,
    /// Factory-level `var` names in statement order: authored bindings and
    /// temporary placeholders, which the factory line resolves like the body.
    pub(super) hoisted: Vec<String>,
    /// Every name the module exports, in first-export order.
    pub(super) export_names: Vec<String>,
    /// The module has an `export * from`, so it carries `exportStar_1`.
    pub(super) star: bool,
    /// Module-scope symbols whose re-export calls live in an import's group.
    pub(super) reexported: BTreeSet<SymbolId>,
    /// The setter-assigned local of each import statement, hoisted when the
    /// walk reaches that statement.
    pub(super) import_locals: Vec<(NodeId, String)>,
}

impl SystemPlan {
    pub(super) fn dependency(&mut self, specifier: &str) -> &mut SystemDependency {
        if let Some(index) = self
            .dependencies
            .iter()
            .position(|dependency| dependency.specifier == specifier)
        {
            return &mut self.dependencies[index];
        }
        self.dependencies.push(SystemDependency {
            specifier: specifier.to_owned(),
            implicit: None,
            actions: Vec::new(),
        });
        let index = self.dependencies.len() - 1;
        &mut self.dependencies[index]
    }

    pub(super) fn export_name(&mut self, name: &str) {
        if !self.export_names.iter().any(|existing| existing == name) {
            self.export_names.push(name.to_owned());
        }
    }

    pub(super) fn hoist(&mut self, name: &str) {
        if !self.hoisted.iter().any(|existing| existing == name) {
            self.hoisted.push(name.to_owned());
        }
    }

    /// Adds a setter action for the module `source` names. A dependency no
    /// import assigns still needs a name for its setter parameter.
    fn setter_action(
        &mut self,
        file: &SourceFile,
        source: &StringLiteralNode,
        names: &mut RequireNames,
        action: SetterAction,
    ) {
        let module = module_specifier(file, source);
        let dependency = self.dependency(&quote_module_specifier(&module));
        if dependency.actions.is_empty() && dependency.implicit.is_none() {
            dependency.implicit = Some(names.allocate(&module));
        }
        dependency.actions.push(action);
    }

    /// Hoists `name` at `index`, ahead of names hoisted later; returns the
    /// index the next name takes.
    fn hoist_at(&mut self, index: usize, name: &str) -> usize {
        if self.hoisted.iter().any(|existing| existing == name) {
            return index;
        }
        let index = index.min(self.hoisted.len());
        self.hoisted.insert(index, name.to_owned());
        index + 1
    }

    /// The wrapper around a rewritten module body: the hoisted declarations
    /// print between the factory lines and the `return`.
    pub(super) fn wrapper<'a>(
        &self,
        reserved: &HashSet<String>,
        hoisted: &'a [Stmt],
    ) -> ModuleWrapper<'a> {
        let mut hoisted_texts = self.hoisted.clone();
        for name in resolve_factory_temps(&self.hoisted, reserved) {
            if let Some(slot) = hoisted_texts
                .iter_mut()
                .find(|text| TempNames::is_placeholder(text))
            {
                *slot = name;
            }
        }
        ModuleWrapper {
            head: self.register_head(),
            inner: self.factory_inner(&hoisted_texts),
            hoisted: (!hoisted.is_empty()).then_some(hoisted),
            mid: self.factory_mid(),
            tail: Self::factory_tail(),
            body_indent: 2,
        }
    }

    /// `System.register(["a", "b"], function (exports_1, context_1) {`
    fn register_head(&self) -> String {
        let quoted: Vec<String> = self
            .dependencies
            .iter()
            .map(|dependency| dependency.specifier.clone())
            .collect();
        let name = self
            .module_name
            .as_ref()
            .map(|name| format!("\"{name}\", "))
            .unwrap_or_default();
        format!(
            "System.register({name}[{}], function (exports_1, context_1) {{",
            quoted.join(", ")
        )
    }

    /// The factory lines above the hoisted function declarations.
    fn factory_inner(&self, hoisted: &[String]) -> String {
        let mut lines: Vec<String> = vec![String::from("\"use strict\";")];
        if !hoisted.is_empty() {
            lines.push(format!("var {};", hoisted.join(", ")));
        }
        lines.push(String::from(
            "var __moduleName = context_1 && context_1.id;",
        ));
        lines.join("\n")
    }

    /// The `exportedNames_1` table and the `exportStar_1` function of a module
    /// with a star export. They follow the hoisted function declarations.
    fn star_lines(&self) -> Vec<String> {
        if !self.star {
            return Vec::new();
        }
        let mut lines = Vec::new();
        let guard = if self.export_names.is_empty() {
            ""
        } else {
            lines.push(String::from("var exportedNames_1 = {"));
            let last = self.export_names.len() - 1;
            for (index, name) in self.export_names.iter().enumerate() {
                let comma = if index == last { "" } else { "," };
                lines.push(format!("    \"{name}\": true{comma}"));
            }
            lines.push(String::from("};"));
            " && !exportedNames_1.hasOwnProperty(n)"
        };
        lines.push(String::from("function exportStar_1(m) {"));
        lines.push(String::from("    var exports = {};"));
        lines.push(String::from("    for (var n in m) {"));
        lines.push(format!(
            "        if (n !== \"default\"{guard}) exports[n] = m[n];"
        ));
        lines.push(String::from("    }"));
        lines.push(String::from("    exports_1(exports);"));
        lines.push(String::from("}"));
        lines
    }

    /// `return { ... }` with the setters and the open `execute` body.
    fn factory_mid(&self) -> String {
        let mut lines = self.star_lines();
        lines.push(String::from("return {"));
        if self.dependencies.is_empty() {
            lines.push(String::from("    setters: [],"));
        } else {
            lines.push(String::from("    setters: ["));
            let last = self.dependencies.len() - 1;
            for (index, dependency) in self.dependencies.iter().enumerate() {
                lines.extend(self.setter_lines(dependency));
                lines.push(String::from(if index == last {
                    "        }"
                } else {
                    "        },"
                }));
            }
            lines.push(String::from("    ],"));
        }
        lines.push(String::from("    execute: function () {"));
        lines.join("\n")
    }

    fn setter_lines(&self, dependency: &SystemDependency) -> Vec<String> {
        let assigned = dependency.actions.iter().find_map(|action| match action {
            SetterAction::Assign(local) => Some(local),
            _ => None,
        });
        let param = assigned
            .or(dependency.implicit.as_ref())
            .map_or_else(|| String::from("_1"), |local| format!("{local}_1"));
        let mut lines = vec![format!("        function ({param}) {{")];
        for action in &dependency.actions {
            match action {
                SetterAction::Assign(local) => {
                    lines.push(format!("            {local} = {param};"));
                }
                SetterAction::Star => {
                    lines.push(format!("            exportStar_1({param});"));
                }
                SetterAction::Object(pairs) => {
                    lines.push(String::from("            exports_1({"));
                    for (index, (exported, imported)) in pairs.iter().enumerate() {
                        let comma = if index + 1 == pairs.len() { "" } else { "," };
                        lines.push(format!(
                            "                \"{exported}\": {param}[\"{imported}\"]{comma}"
                        ));
                    }
                    lines.push(String::from("            });"));
                }
                SetterAction::NamespaceObject(name) => {
                    lines.push(format!("            exports_1(\"{name}\", {param});"));
                }
            }
        }
        lines
    }

    /// The lines that close `execute`, the return object, and the register
    /// call. They print at the left margin, so they carry their indentation.
    fn factory_tail() -> String {
        String::from("        }\n    };\n});")
    }
}

/// The placeholder names of the factory var line, resolved the way the body
/// resolves them: in print order, skipping names the program writes.
fn resolve_factory_temps(hoisted: &[String], reserved: &HashSet<String>) -> Vec<String> {
    let placeholders: Vec<&String> = hoisted
        .iter()
        .filter(|name| TempNames::is_placeholder(name))
        .collect();
    let mut temps = TempNames::new(reserved.clone());
    placeholders
        .iter()
        .map(|placeholder| temps.resolve(placeholder))
        .collect()
}
/// One module read off a setter parameter: `param`, or `param.name`.
fn import_read(root: &str, property: Option<&str>) -> String {
    match property {
        None | Some("") => root.to_owned(),
        Some(property) if is_identifier_name(property) => format!("{root}.{property}"),
        Some(property) => format!("{root}[{}]", quote_string(property)),
    }
}

/// Registers an import statement's dependency and its setter assignment.
pub(super) fn register_import(plan: &mut CjsPlan, statement: NodeId, specifier: &str, local: &str) {
    let Some(system) = plan.system.as_mut() else {
        return;
    };
    let dependency = system.dependency(specifier);
    dependency
        .actions
        .push(SetterAction::Assign(local.to_owned()));
    system.import_locals.push((statement, local.to_owned()));
}

/// Plans one export statement: the names the module exports, and the setter
/// actions of an export that reads another module.
pub(super) fn plan_export(
    file: &SourceFile,
    export: &ExportDeclaration,
    names: &mut RequireNames,
    plan: &mut CjsPlan,
) {
    let Some(system) = plan.system.as_mut() else {
        return;
    };
    match export {
        ExportDeclaration::All(all) if !all.type_only => {
            let exported = all
                .exported
                .as_ref()
                .map(|name| module_export_text(file, name));
            let action = match exported {
                Some(name) => {
                    system.export_name(&name);
                    SetterAction::NamespaceObject(name)
                }
                None => {
                    system.star = true;
                    SetterAction::Star
                }
            };
            system.setter_action(file, &all.source, names, action);
        }
        ExportDeclaration::Named(ExportNamedDeclaration::Specifiers {
            type_only: false,
            specifiers,
            source,
            ..
        }) => {
            let pairs: Vec<(String, String)> = specifiers
                .iter()
                .map(|specifier| specifier.data())
                .filter(|specifier| matches!(specifier.mode, ExportSpecifierMode::Value))
                .map(|specifier| {
                    (
                        module_export_text(file, &specifier.exported),
                        module_export_text(file, &specifier.local),
                    )
                })
                .collect();
            for (exported, _) in &pairs {
                system.export_name(exported);
            }
            if let Some(source) = source {
                system.setter_action(file, source, names, SetterAction::Object(pairs));
            }
        }
        ExportDeclaration::Named(ExportNamedDeclaration::Declaration(inner)) => {
            let declared = match inner.data() {
                Statement::Function(declaration) => declaration.function.name.as_ref(),
                Statement::Class(class) => class.name.as_ref(),
                _ => None,
            };
            if let Some(name) = declared {
                system.export_name(&identifier_text(file, name));
            }
            for name in declared_binding_names(file, inner) {
                system.export_name(&name);
            }
        }
        _ => {}
    }
}

/// Re-exports an import binding: an export call in the import's group under
/// System, the caller's line under CommonJS.
pub(super) fn publish_import_reexport(
    plan: &mut CjsPlan,
    exported: &str,
    root: &str,
    property: Option<&str>,
    commonjs: String,
) {
    let line = match plan.system.as_mut() {
        Some(system) => {
            system.export_name(exported);
            format!(
                "exports_1(\"{exported}\", {});",
                import_read(root, property)
            )
        }
        None => commonjs,
    };
    plan.requires.push(line);
}

/// Records that a module-scope symbol's re-export call already lives in an
/// import group, so the specifier statement does not publish it again.
pub(super) fn mark_reexported(plan: &mut CjsPlan, symbol: SymbolId) {
    if let Some(system) = plan.system.as_mut() {
        system.reexported.insert(symbol);
    }
}

/// Whether re-exporting a named import binding publishes nothing because the
/// binding names only a type. Import-type and erased locals arrive in
/// `type_imports`, same-file type-only declarations answer through the
/// semantic model, and a resolved target answers by its kind: an interface
/// or type alias carries no value unless a same-named value declaration
/// shares its scope. Every other target kind carries a value, and an
/// unresolved target publishes, as the import may carry a value. The first
/// two facts are the ones the CommonJS export specifiers consult in
/// `exports_only_a_type`; the kind rule is the one `promise_names_a_value`
/// applies to annotation symbols. Registration still runs for such a
/// binding, so the specifier statement keeps skipping the name.
pub(super) fn import_reexport_is_type_only(
    model: &SemanticModel,
    target: Option<SymbolId>,
    local: &str,
    type_imports: &BTreeSet<String>,
) -> bool {
    if type_imports.contains(local) || is_type_only_export(model, local) {
        return true;
    }
    target.is_some_and(|target| {
        let declared = model.symbol(target);
        match declared.kind() {
            SymbolKind::Interface | SymbolKind::TypeAlias => model
                .lookup_value(declared.scope(), declared.name())
                .is_none(),
            _ => false,
        }
    })
}

impl Rewriter<'_> {
    pub(super) fn system_active(&self) -> bool {
        self.cjs.as_ref().is_some_and(|plan| plan.system.is_some())
    }

    /// The statement list being rewritten is the module's own.
    pub(super) fn system_module_level(&self) -> bool {
        self.declared_names.len() == 1
    }

    /// The text of an identifier, wherever its range points.
    pub(super) fn bank_text(&self, token: &Token) -> String {
        let range = token.range();
        self.bank
            .names
            .iter()
            .find(|(_, candidate)| **candidate == range)
            .map(|(text, _)| text.clone())
            .unwrap_or_else(|| self.token_text(token).to_owned())
    }

    /// `exports_1("name", value)`.
    pub(super) fn system_export_call_value(
        &mut self,
        name: &str,
        value: Expr,
        range: TextRange,
    ) -> Expr {
        let callee = self.ident_expr("exports_1");
        let literal = self.string_literal(name);
        let name_expr = self.syn_node(range, Expression::Literal(Literal::String(literal)));
        self.call_expression(range, callee, vec![name_expr, value])
    }

    /// `exports_1("name", local);`
    fn system_export_call(&mut self, name: &str, local: &str, range: TextRange) -> Stmt {
        let value = self.ident_expr(local);
        let call = self.system_export_call_value(name, value, range);
        self.expression_statement(call, range)
    }

    fn system_hoist(&mut self, name: &str) {
        if let Some(plan) = self.cjs.as_mut().and_then(|plan| plan.system.as_mut()) {
            plan.hoist(name);
        }
    }

    fn system_mut(&mut self) -> Option<&mut SystemPlan> {
        self.cjs.as_mut().and_then(|plan| plan.system.as_mut())
    }

    /// A module-level write the module exports, wrapped so the export function
    /// observes it. The forms match the CommonJS write publishing; only the
    /// wrap differs.
    pub(super) fn system_wrap_writes(&mut self, source: &Expr, rewritten: Expr) -> Expr {
        let range = source.range();
        let (Some(plan), Some(model)) = (&self.cjs, self.model) else {
            return rewritten;
        };
        let mut identifiers = Vec::new();
        match source.data() {
            Expression::Assignment(assignment) => {
                collect_target_identifiers(&assignment.left, &mut identifiers);
            }
            Expression::Update(update) => match update.argument.data() {
                AssignmentTarget::Identifier(identifier) => identifiers.push(identifier),
                _ => return rewritten,
            },
            _ => return rewritten,
        }
        let Some((names, local)) = identifiers.into_iter().find_map(|identifier| {
            let symbol = model.reference(identifier.id())?;
            let names = plan.live_locals.get(&symbol).cloned()?;
            Some((names, self.token_text(identifier.data().token()).to_owned()))
        }) else {
            return rewritten;
        };
        let postfix = matches!(source.data(), Expression::Update(update) if !update.prefix);
        let mut wrapped = if postfix {
            let current = self.ident_expr(&local);
            let sequence = self.sequence(vec![rewritten, current], range);
            self.syn_node(range, Expression::Parenthesized(Box::new(sequence)))
        } else {
            rewritten
        };
        for name in names {
            wrapped = self.system_export_call_value(&name, wrapped, range);
        }
        wrapped
    }

    /// The export calls a specifier statement publishes for what a statement
    /// just declared. A binding without an initializer publishes nothing.
    pub(super) fn system_publish_declared(&mut self, statement: &Stmt) -> Vec<Stmt> {
        let Some(pairs) = self
            .cjs
            .as_mut()
            .and_then(|plan| plan.declared_exports.remove(&statement.id()))
        else {
            return Vec::new();
        };
        let range = statement.range();
        let initialized: BTreeSet<String> = match statement.data() {
            Statement::Variable(declaration) => declaration
                .declarations
                .iter()
                .filter(|declarator| declarator.data().initializer.is_some())
                .filter_map(|declarator| match declarator.data().binding.data() {
                    BindingPattern::Identifier(ident) => {
                        Some(self.token_text(ident.data().token()).to_owned())
                    }
                    _ => None,
                })
                .collect(),
            Statement::ImportEquals(_) => BTreeSet::new(),
            _ => match statement.data() {
                Statement::Class(class) => class
                    .name
                    .iter()
                    .map(|ident| self.token_text(ident.data().token()).to_owned())
                    .collect(),
                _ => BTreeSet::new(),
            },
        };
        pairs
            .into_iter()
            .filter(|(_, local)| {
                !matches!(statement.data(), Statement::Variable(_)) || initialized.contains(local)
            })
            .map(|(exported, local)| self.system_export_call(&exported, &local, range))
            .collect()
    }

    fn system_hoist_import_local(&mut self, statement: NodeId) {
        let Some(system) = self.system_mut() else {
            return;
        };
        let locals: Vec<String> = system
            .import_locals
            .iter()
            .filter(|(id, _)| *id == statement)
            .map(|(_, local)| local.clone())
            .collect();
        for local in locals {
            system.hoist(&local);
        }
    }

    /// A namespace or enum declares its container with a bare `var`; under
    /// System the name hoists to the factory instead.
    fn system_hoist_bare_declarations(&mut self, statements: &mut Vec<Stmt>) {
        let mut names = Vec::new();
        statements.retain(|statement| {
            let Statement::Variable(declaration) = statement.data() else {
                return true;
            };
            let mut bare = Vec::new();
            for declarator in &declaration.declarations {
                let data = declarator.data();
                let BindingPattern::Identifier(ident) = data.binding.data() else {
                    return true;
                };
                if data.initializer.is_some() {
                    return true;
                }
                bare.push(ident.clone());
            }
            names.extend(bare);
            false
        });
        for ident in names {
            let name = self.bank_text(ident.data().token());
            self.system_hoist(&name);
        }
    }

    /// The module root: statement order drives the factory var line, and the
    /// hoisted function declarations print above `return`.
    pub(super) fn rewrite_root_statements_system(
        &mut self,
        statements: &[Stmt],
        range: TextRange,
    ) -> Vec<Stmt> {
        self.expression_temp_scopes.push(Vec::new());
        self.capture_scopes.push(CaptureScope::default());
        self.declared_names.push(BTreeSet::new());
        let mut body = Vec::new();
        for statement in statements {
            self.record_declaration(statement);
            self.system_hoist_import_local(statement.id());
            let mark = self.system_hoisted_len();
            let temp_start = self.expression_temp_scopes.last().map_or(0, Vec::len);
            let mut rewritten = self.rewrite_statement(statement);
            if matches!(
                statement.data(),
                Statement::Namespace(_) | Statement::Enum(_)
            ) {
                self.system_hoist_bare_declarations(&mut rewritten);
            }
            body.extend(rewritten);
            body.extend(self.system_publish_declared(statement));
            self.system_hoist_statement_temps(temp_start, mark);
        }
        self.declared_names.pop();
        self.expression_temp_scopes.pop();
        let captures = self.capture_scopes.pop().unwrap_or_default();
        for declaration in self.capture_declarations(captures, range) {
            let Statement::Variable(declaration) = declaration.data() else {
                continue;
            };
            for declarator in &declaration.declarations {
                let data = declarator.data();
                let BindingPattern::Identifier(ident) = data.binding.data() else {
                    continue;
                };
                let name = self.bank_text(ident.data().token());
                self.system_hoist(&name);
                let Some(initializer) = data.initializer.as_deref() else {
                    continue;
                };
                let value = self.rewrite_expr(initializer);
                body.push(self.system_plain_assignment(&name, value, range));
            }
        }
        body
    }

    fn system_hoisted_len(&self) -> usize {
        self.cjs
            .as_ref()
            .and_then(|plan| plan.system.as_ref())
            .map_or(0, |system| system.hoisted.len())
    }

    /// Hoists the temporaries a statement drew ahead of the names it declared.
    fn system_hoist_statement_temps(&mut self, temp_start: usize, mark: usize) {
        let temps = self
            .expression_temp_scopes
            .last()
            .cloned()
            .unwrap_or_default();
        let mut index = mark;
        for temp in &temps[temp_start.min(temps.len())..] {
            let name = self.bank_text(temp.data().token());
            if let Some(system) = self.system_mut() {
                index = system.hoist_at(index, &name);
            }
        }
    }

    /// `name = value;` for a hoisted System binding.
    pub(super) fn system_plain_assignment(
        &mut self,
        name: &str,
        value: Expr,
        range: TextRange,
    ) -> Stmt {
        let local = self.ident(name);
        let left = self.syn_node(range, AssignmentTarget::Identifier(local));
        let assignment = self.assignment(left, value, range);
        self.expression_statement(assignment, range)
    }

    /// A module-level `var`/`let`/`const`: the names hoist, and each
    /// initializer becomes an execute assignment.
    pub(super) fn system_variable_statement(
        &mut self,
        statement: &Stmt,
        declaration: &VariableDeclaration,
    ) -> Vec<Stmt> {
        let range = statement.range();
        for name in declared_binding_names(self.file, statement) {
            self.system_hoist(&name);
        }
        let mut expressions = Vec::new();
        for declarator in &declaration.declarations {
            let data = declarator.data();
            let Some(initializer) = data.initializer.as_deref() else {
                continue;
            };
            let value = self.rewrite_expr(initializer);
            match data.binding.data() {
                BindingPattern::Identifier(ident) => {
                    let name = self.token_text(ident.data().token()).to_owned();
                    let local = self.ident(&name);
                    let left = self.syn_node(range, AssignmentTarget::Identifier(local));
                    expressions.push(self.assignment(left, value, range));
                }
                BindingPattern::Object(_) | BindingPattern::Array(_) => self.flatten_export(
                    &data.binding,
                    value,
                    &ExportSink::PlainLocal,
                    &mut expressions,
                ),
                _ => {}
            }
        }
        match expressions.len() {
            0 => Vec::new(),
            1 => vec![self.expression_statement(expressions.remove(0), range)],
            _ => {
                let sequence = self.sequence(expressions, range);
                vec![self.expression_statement(sequence, range)]
            }
        }
    }

    /// `export var/let/const`: each initializer assignment goes out through
    /// the export function.
    fn system_exported_variable_declaration(
        &mut self,
        statement: &Stmt,
        declaration: &VariableDeclaration,
    ) -> Vec<Stmt> {
        let range = statement.range();
        for name in declared_binding_names(self.file, statement) {
            self.system_hoist(&name);
        }
        let mut expressions = Vec::new();
        for declarator in &declaration.declarations {
            let data = declarator.data();
            let Some(initializer) = data.initializer.as_deref() else {
                continue;
            };
            let value = self.rewrite_expr(initializer);
            self.flatten_export(
                &data.binding,
                value,
                &ExportSink::SystemExport,
                &mut expressions,
            );
        }
        match expressions.len() {
            0 => Vec::new(),
            1 => vec![self.expression_statement(expressions.remove(0), range)],
            _ => {
                let sequence = self.sequence(expressions, range);
                vec![self.expression_statement(sequence, range)]
            }
        }
    }

    /// `export` of a module-level declaration.
    pub(super) fn system_export_declaration(
        &mut self,
        statement: &Stmt,
        inner: &Stmt,
    ) -> Vec<Stmt> {
        let range = statement.range();
        match inner.data() {
            Statement::Function(function) => {
                self.system_hoist_function(range, &function.function, None)
            }
            Statement::Class(class) => self.system_export_class(range, class, None),
            Statement::Variable(declaration) => {
                self.system_exported_variable_declaration(inner, declaration)
            }
            Statement::Namespace(namespace) => {
                self.system_export_container_namespace(inner, namespace, range)
            }
            Statement::Enum(declaration) => {
                if declaration.is_const {
                    return Vec::new();
                }
                self.system_export_container_enum(inner, declaration, range)
            }
            Statement::ImportEquals(import) if is_qualified_alias(import) => {
                self.system_alias_statement(statement, import)
            }
            Statement::ImportEquals(_) => Vec::new(),
            Statement::Interface(_) | Statement::TypeAlias(_) => Vec::new(),
            _ => vec![statement.clone()],
        }
    }

    /// An exported function: the declaration hoists above `return` with its
    /// export call, unless only a type spells it.
    fn system_hoist_function(
        &mut self,
        range: TextRange,
        function: &FunctionLike,
        exported: Option<&str>,
    ) -> Vec<Stmt> {
        let authored = function
            .name
            .as_ref()
            .map(|ident| self.token_text(ident.data().token()).to_owned());
        if let Some(name) = &authored
            && self.exports_only_a_type(name)
        {
            return Vec::new();
        }
        let mut function = function.clone();
        if function.name.is_none() {
            function.name = Some(self.ident("default_1"));
        }
        let function = self.rewrite_function_like(&function, range);
        let statement = self.node(range, Statement::Function(FunctionDeclaration { function }));
        let name = match statement.data() {
            Statement::Function(declaration) => declaration
                .function
                .name
                .as_ref()
                .map(|ident| self.bank_text(ident.data().token()))
                .unwrap_or_default(),
            _ => String::new(),
        };
        self.system_hoisted.push(statement);
        let call = self.system_export_call(exported.unwrap_or(&name), &name, range);
        self.system_hoisted.push(call);
        Vec::new()
    }

    /// A module-level function declaration hoists above `return`; a bodyless
    /// overload has nothing to hoist.
    pub(super) fn system_module_function(
        &mut self,
        range: TextRange,
        function: &FunctionLike,
    ) -> Vec<Stmt> {
        if function.body.is_none() {
            return Vec::new();
        }
        let local = function
            .name
            .as_ref()
            .map(|ident| self.token_text(ident.data().token()).to_owned());
        let function = self.rewrite_function_like(function, range);
        let statement = self.node(range, Statement::Function(FunctionDeclaration { function }));
        self.system_hoisted.push(statement);
        let exported = local
            .as_ref()
            .and_then(|local| exported_locals(self.file).remove(local))
            .unwrap_or_default();
        for name in exported {
            let call = self.system_export_call(&name, local.as_deref().unwrap_or_default(), range);
            self.system_hoisted.push(call);
        }
        Vec::new()
    }

    /// `export class C {}` and `export default class`: the class runs in
    /// `execute` and the export call follows it.
    fn system_export_class(
        &mut self,
        range: TextRange,
        class: &ClassDeclaration,
        exported: Option<&str>,
    ) -> Vec<Stmt> {
        let name = class.name.as_ref().map_or_else(
            || String::from("default_1"),
            |ident| self.token_text(ident.data().token()).to_owned(),
        );
        let class = class.clone();
        self.system_hoist(&name);
        let statement = self.node(range, Statement::Class(class));
        let Statement::Class(class) = statement.data() else {
            return vec![statement.clone()];
        };
        let rewritten = self.rewrite_class_statement(&statement, class);
        let mut out = Vec::new();
        for statement in rewritten {
            let range = statement.range();
            match statement.into_data() {
                Statement::Class(class) => {
                    let local = class
                        .name
                        .as_ref()
                        .map(|ident| self.bank_text(ident.data().token()))
                        .unwrap_or_else(|| String::from("default_1"));
                    let value = self.syn_node(range, Expression::Class(ClassExpression { class }));
                    out.push(self.system_plain_assignment(&local, value, range));
                    let exported = exported.unwrap_or(&local).to_owned();
                    out.push(self.system_export_call(&exported, &local, range));
                }
                other => out.push(self.node(range, other)),
            }
        }
        out
    }

    fn system_export_container_namespace(
        &mut self,
        statement: &Stmt,
        namespace: &NamespaceDeclaration,
        range: TextRange,
    ) -> Vec<Stmt> {
        let Some(plan) = self
            .model
            .and_then(|model| model.namespace_facts().declaration(statement.id()))
        else {
            return vec![statement.clone()];
        };
        let NamespaceName::Identifier { name, .. } = &namespace.name else {
            return vec![statement.clone()];
        };
        if !plan.is_value_bearing() {
            return vec![statement.clone()];
        }
        let Some(local) = self.identifier_name(name) else {
            return vec![statement.clone()];
        };
        self.system_hoist(&local);
        let parameter = self.namespace_parameter(&local, namespace.body.range());
        let body = self.lower_namespace_body(namespace, plan.container(), &parameter);
        let argument = self.container_argument(&local, &ContainerBinding::System, range);
        vec![self.container_call(&parameter, body, argument, range)]
    }

    fn system_export_container_enum(
        &mut self,
        statement: &Stmt,
        declaration: &EnumDeclaration,
        range: TextRange,
    ) -> Vec<Stmt> {
        let Some(plan) = self
            .model
            .and_then(|model| model.enum_facts().declaration(statement.id()))
            .filter(|plan| plan.members().len() == declaration.members.len())
        else {
            return vec![statement.clone()];
        };
        let Some(local) = self
            .identifier_name(&declaration.name)
            .filter(|local| !local.is_empty())
        else {
            return vec![statement.clone()];
        };
        self.system_hoist(&local);
        let body = declaration
            .members
            .iter()
            .zip(plan.members())
            .filter_map(|(member, plan)| self.enum_member_statement(&local, member, plan))
            .collect();
        let argument = self.container_argument(&local, &ContainerBinding::System, range);
        vec![self.container_call(&local, body, argument, range)]
    }

    /// `export { a, b as c };` of the module's own names. A specifier whose
    /// local an import group re-exports has its call there; a local whose
    /// declaration runs in `execute` has its call on that declaration; a
    /// setter-assigned local gets its call here; a valueless local publishes
    /// nothing.
    pub(super) fn system_export_specifiers(
        &mut self,
        specifiers: &[ExportSpecifierNode],
    ) -> Vec<Stmt> {
        let mut out = Vec::new();
        for specifier in specifiers {
            let specifier = specifier.data();
            if matches!(specifier.mode, ExportSpecifierMode::TypeOnly) {
                continue;
            }
            let ModuleExportName::Identifier(local) = &specifier.local else {
                continue;
            };
            let local_range = local.range();
            let local_text = self.token_text(local.data().token()).to_owned();
            let exported = module_export_text(self.file, &specifier.exported);
            if self.exports_only_a_type(&local_text) {
                continue;
            }
            let Some(symbol) = self
                .model
                .and_then(|model| model.scope(model.module_scope()).value(&local_text))
            else {
                continue;
            };
            let reexported = self
                .cjs
                .as_ref()
                .and_then(|plan| plan.system.as_ref())
                .is_some_and(|system| system.reexported.contains(&symbol));
            let declares_value = self.system_local_declares_value(&local_text);
            let setter_assigned = self.system_local_is_setter_assigned(&local_text, symbol);
            if reexported || declares_value || !setter_assigned {
                continue;
            }
            out.push(self.system_export_call(&exported, &local_text, local_range));
        }
        out
    }

    /// Whether the module level declares `local` with an initializer or as a
    /// qualified alias, so its execute statement carries the export calls.
    fn system_local_declares_value(&self, local: &str) -> bool {
        self.file
            .statements()
            .iter()
            .any(|statement| match statement.data() {
                Statement::Variable(declaration) => {
                    declaration.declarations.iter().any(|declarator| {
                        let data = declarator.data();
                        matches!(
                            data.binding.data(),
                            BindingPattern::Identifier(ident)
                                if self.token_text(ident.data().token()) == local
                        ) && data.initializer.is_some()
                    })
                }
                Statement::ImportEquals(import) => {
                    is_qualified_alias(import)
                        && self.token_text(import.local.data().token()) == local
                }
                _ => false,
            })
    }

    /// Whether `local` is a System setter target: a require alias or a
    /// namespace import the setter assigns.
    fn system_local_is_setter_assigned(&self, local: &str, symbol: SymbolId) -> bool {
        let Some(plan) = self.cjs.as_ref() else {
            return false;
        };
        if let Some(reference) = plan.imports.get(&symbol) {
            return reference.property.is_none();
        }
        self.file.statements().iter().any(|statement| {
            matches!(
                statement.data(),
                Statement::ImportEquals(import)
                    if !import.is_type_only
                        && matches!(import.reference, ExternalModuleReference::Require(_))
                        && self.token_text(import.local.data().token()) == local
            )
        })
    }

    /// `export default`: a function hoists with its call; a class or
    /// expression runs in `execute`.
    pub(super) fn system_default_export(
        &mut self,
        default: &ExportDefaultDeclaration,
        range: TextRange,
    ) -> Vec<Stmt> {
        match &default.value {
            ExportDefaultValue::Function(function) => {
                self.system_hoist_function(range, function, Some("default"))
            }
            ExportDefaultValue::Class(class) => {
                self.system_export_class(range, class, Some("default"))
            }
            ExportDefaultValue::Expression(value) => {
                if let Expression::Identifier(identifier) = value.data()
                    && self.exports_only_a_type(self.token_text(identifier.data().token()))
                {
                    return Vec::new();
                }
                let value = self.rewrite_expr(value);
                let call = self.system_export_call_value("default", value, range);
                vec![self.expression_statement(call, range)]
            }
            ExportDefaultValue::Interface(_) | ExportDefaultValue::Missing(_) => Vec::new(),
        }
    }

    /// `import x = require("m")` and `import a = N.b`: the name hoists and the
    /// setter or the execute assignment fills it. A require alias's statement
    /// goes away; the setter takes its place.
    pub(super) fn system_alias_statement(
        &mut self,
        statement: &Stmt,
        import: &ImportEqualsDeclaration,
    ) -> Vec<Stmt> {
        if import.is_type_only || !matches!(import.reference, ExternalModuleReference::Qualified(_))
        {
            return Vec::new();
        }
        let exported = exported_locals(self.file)
            .remove(self.token_text(import.local.data().token()))
            .filter(|_| alias_target_bears_value(self.model, statement))
            .unwrap_or_default();
        if exported.is_empty() && !self.alias_is_read(statement) {
            return Vec::new();
        }
        let range = statement.range();
        let Some(local) = self.identifier_name(&import.local) else {
            return vec![statement.clone()];
        };
        let ExternalModuleReference::Qualified(name) = &import.reference else {
            return Vec::new();
        };
        let Some(value) = self.entity_expression(name, range) else {
            return vec![statement.clone()];
        };
        self.system_hoist(&local);
        let mut out = vec![self.system_plain_assignment(&local, value, range)];
        for name in exported {
            out.push(self.system_export_call(&name, &local, range));
        }
        out
    }
}
