//! Immutable TypeScript namespace facts derived from one completed checker pass.

use std::collections::HashMap;

use bamts_bytecode::EcmaString;

use crate::checker::{ScopeId, SemanticModel, SymbolId};
use crate::syntax::{
    BindingPattern, ExportDeclaration, ExportNamedDeclaration, NamespaceDeclaration, NamespaceName,
    NodeId, Statement, VariableDeclaration,
};

/// The checked meaning of all namespace declarations in one source file.
#[derive(Clone, Debug)]
pub struct NamespaceFacts {
    symbols: Vec<crate::checker::Symbol>,
    declaration_symbols: HashMap<NodeId, SymbolId>,
    declarations: HashMap<NodeId, NamespacePlan>,
    merged_declarations: HashMap<SymbolId, Box<[NodeId]>>,
    member_uses: HashMap<NodeId, NamespaceMemberUse>,
    qualified_type_paths: HashMap<NodeId, Box<[SymbolId]>>,
    qualified_import_paths: HashMap<NodeId, Box<[SymbolId]>>,
    /// Built from the per-plan export lists so `exports_for_member_declaration`
    /// is linear in the number of matching exports.
    exports_by_declaration: HashMap<NodeId, Vec<(NodeId, u32)>>,
}

impl NamespaceFacts {
    /// Creates deliberately unchecked empty facts.
    #[must_use]
    pub(crate) fn unchecked() -> Self {
        Self {
            symbols: Vec::new(),
            declaration_symbols: HashMap::new(),
            declarations: HashMap::new(),
            merged_declarations: HashMap::new(),
            member_uses: HashMap::new(),
            qualified_type_paths: HashMap::new(),
            qualified_import_paths: HashMap::new(),
            exports_by_declaration: HashMap::new(),
        }
    }

    #[must_use]
    pub(crate) fn symbols(&self) -> &[crate::checker::Symbol] {
        &self.symbols
    }

    #[must_use]
    pub(crate) fn declaration_symbol(&self, declaration: NodeId) -> Option<SymbolId> {
        self.declaration_symbols.get(&declaration).copied()
    }

    #[must_use]
    pub(crate) fn declaration(&self, declaration: NodeId) -> Option<&NamespacePlan> {
        self.declarations.get(&declaration)
    }

    /// Runtime exports whose declaring statement is `declaration` (the inner
    /// `var`/`function`/`class`/`enum` statement under `export`, not the
    /// enclosing namespace declaration).
    #[must_use]
    pub(crate) fn exports_for_member_declaration(
        &self,
        declaration: NodeId,
    ) -> Vec<(SymbolId, &NamespaceExport)> {
        let Some(positions) = self.exports_by_declaration.get(&declaration) else {
            return Vec::new();
        };
        positions
            .iter()
            .map(|(plan_id, index)| {
                let plan = self
                    .declarations
                    .get(plan_id)
                    .expect("export index entry must resolve to a built plan");
                (plan.container, &plan.exports[*index as usize])
            })
            .collect()
    }

    #[must_use]
    pub(crate) fn merged_declarations(&self, symbol: SymbolId) -> &[NodeId] {
        self.merged_declarations
            .get(&symbol)
            .map_or(&[], Box::as_ref)
    }

    #[must_use]
    pub(crate) fn member_use(&self, reference: NodeId) -> Option<&NamespaceMemberUse> {
        self.member_uses.get(&reference)
    }

    #[allow(dead_code)] // exercised by checker unit tests
    #[allow(dead_code)] // exercised by checker unit tests
    #[must_use]
    pub(crate) fn qualified_type_path(&self, reference: NodeId) -> Option<&[SymbolId]> {
        self.qualified_type_paths.get(&reference).map(Box::as_ref)
    }

    /// Returns the checker-resolved SymbolId path for a qualified `import X = A.B`.
    #[must_use]
    pub(crate) fn qualified_import_path(&self, declaration: NodeId) -> Option<&[SymbolId]> {
        self.qualified_import_paths
            .get(&declaration)
            .map(Box::as_ref)
    }

    pub(crate) fn set_qualified_import_paths(&mut self, paths: HashMap<NodeId, Box<[SymbolId]>>) {
        self.qualified_import_paths = paths;
    }
}

/// One declaration block's checked runtime plan.
#[derive(Clone, Debug)]
pub struct NamespacePlan {
    container: SymbolId,
    acquisition: ContainerAcquisition,
    exports: Box<[NamespaceExport]>,
    is_value_bearing: bool,
}

impl NamespacePlan {
    #[allow(dead_code)] // exercised by checker unit tests
    #[must_use]
    pub(crate) const fn container(&self) -> SymbolId {
        self.container
    }

    #[must_use]
    pub(crate) const fn acquisition(&self) -> ContainerAcquisition {
        self.acquisition
    }

    #[allow(dead_code)] // exercised by checker unit tests
    #[must_use]
    pub(crate) fn exports(&self) -> &[NamespaceExport] {
        &self.exports
    }

    #[must_use]
    pub(crate) const fn is_value_bearing(&self) -> bool {
        self.is_value_bearing
    }
}

/// How a namespace declaration obtains its runtime container.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ContainerAcquisition {
    Binding,
    Member { parent: SymbolId },
}

/// One source-ordered runtime export.
#[derive(Clone, Debug)]
pub struct NamespaceExport {
    name: EcmaString,
    #[allow(dead_code)] // mirrored into ExportIdentity; read via storage() in tests
    storage: ExportStorage,
    declaration: NodeId,
}

impl NamespaceExport {
    #[must_use]
    pub(crate) fn name(&self) -> &EcmaString {
        &self.name
    }

    #[allow(dead_code)] // exercised by checker unit tests
    #[must_use]
    pub(crate) const fn storage(&self) -> ExportStorage {
        self.storage
    }
}

/// Whether an exported declaration is represented only by a property or also
/// by a local binding in its declaring namespace block.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExportStorage {
    Property,
    LocalAndProperty,
}

/// A direct identifier use resolved through a namespace export scope.
#[derive(Clone, Debug)]
pub struct NamespaceMemberUse {
    container: SymbolId,
    name: EcmaString,
}

impl NamespaceMemberUse {
    #[must_use]
    pub(crate) const fn container(&self) -> SymbolId {
        self.container
    }

    #[must_use]
    pub(crate) fn name(&self) -> &EcmaString {
        &self.name
    }
}

/// Checker-owned declaration input. Source references live only until facts
/// are built; [`NamespaceFacts`] itself owns no syntax.
pub(crate) struct NamespaceDeclarationBinding<'src> {
    pub(crate) declaration: &'src NamespaceDeclaration,
    pub(crate) declaration_id: NodeId,
    pub(crate) symbol: SymbolId,
    pub(crate) export_scope: ScopeId,
    pub(crate) parent: Option<SymbolId>,
    pub(crate) ambient: bool,
}

#[derive(Clone)]
struct ExportIdentity {
    container: SymbolId,
    name: EcmaString,
    storage: ExportStorage,
    declaration_block: NodeId,
}

/// Builds namespace facts after binding and reference resolution.
pub(crate) fn build(
    model: &SemanticModel,
    source: &crate::syntax::SourceFile,
    bindings: &[NamespaceDeclarationBinding<'_>],
    reference_blocks: &HashMap<NodeId, NodeId>,
    qualified_type_paths: HashMap<NodeId, Box<[SymbolId]>>,
) -> NamespaceFacts {
    let mut facts = NamespaceFacts::unchecked();
    facts.symbols = model.symbols().to_vec();
    facts.qualified_type_paths = qualified_type_paths;

    let mut by_declaration = HashMap::new();
    let mut merged_declarations: HashMap<SymbolId, Vec<NodeId>> = HashMap::new();
    for binding in bindings {
        facts
            .declaration_symbols
            .insert(binding.declaration_id, binding.symbol);
        by_declaration.insert(binding.declaration_id, binding);
        merged_declarations
            .entry(binding.symbol)
            .or_default()
            .push(binding.declaration_id);
    }
    facts.merged_declarations = merged_declarations
        .into_iter()
        .map(|(symbol, declarations)| (symbol, declarations.into_boxed_slice()))
        .collect();

    let mut export_identities: HashMap<SymbolId, Vec<ExportIdentity>> = HashMap::new();
    for binding in bindings {
        let is_value_bearing = namespace_is_value_bearing(binding, &by_declaration);
        let mut exports = Vec::new();
        if is_value_bearing {
            for statement in &binding.declaration.body.data().statements {
                collect_runtime_exports(
                    statement,
                    binding,
                    model,
                    source,
                    &by_declaration,
                    &mut exports,
                    &mut export_identities,
                );
            }
        }
        facts.declarations.insert(
            binding.declaration_id,
            NamespacePlan {
                container: binding.symbol,
                acquisition: binding
                    .parent
                    .map_or(ContainerAcquisition::Binding, |parent| {
                        ContainerAcquisition::Member { parent }
                    }),
                exports: exports.into_boxed_slice(),
                is_value_bearing,
            },
        );
    }

    for (&reference, &declaration_block) in reference_blocks {
        let Some(symbol) = model.reference(reference) else {
            continue;
        };
        let Some(exports) = export_identities.get(&symbol) else {
            continue;
        };
        let selected = exports.iter().find(|export| {
            export.storage == ExportStorage::Property
                || export.declaration_block != declaration_block
        });
        let Some(export) = selected else {
            continue;
        };
        facts.member_uses.insert(
            reference,
            NamespaceMemberUse {
                container: export.container,
                name: export.name.clone(),
            },
        );
    }
    // Build an export-by-declaration index once, in the same plan-iteration
    // order as the original full scan, so the lookup order is preserved and
    // each query is proportional to its number of matches.
    let mut exports_by_declaration: HashMap<NodeId, Vec<(NodeId, u32)>> = HashMap::new();
    for (plan_id, plan) in &facts.declarations {
        for (i, export) in plan.exports.iter().enumerate() {
            exports_by_declaration
                .entry(export.declaration)
                .or_default()
                .push((*plan_id, i as u32));
        }
    }
    facts.exports_by_declaration = exports_by_declaration;

    facts
}

fn collect_runtime_exports(
    statement: &crate::syntax::Stmt,
    binding: &NamespaceDeclarationBinding<'_>,
    model: &SemanticModel,
    source: &crate::syntax::SourceFile,
    by_declaration: &HashMap<NodeId, &NamespaceDeclarationBinding<'_>>,
    exports: &mut Vec<NamespaceExport>,
    identities: &mut HashMap<SymbolId, Vec<ExportIdentity>>,
) {
    let declaration = match statement.data() {
        Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(inner))) => {
            inner.as_ref()
        }
        Statement::Namespace(_)
            if by_declaration
                .get(&statement.id())
                .is_some_and(|child| child.parent == Some(binding.symbol)) =>
        {
            statement
        }
        _ => return,
    };

    match declaration.data() {
        Statement::Variable(variable) => {
            collect_variable_exports(variable, |identifier| {
                add_identifier_export(
                    identifier,
                    ExportStorage::Property,
                    declaration.id(),
                    binding,
                    model,
                    source,
                    exports,
                    identities,
                );
            });
        }
        Statement::Function(function) => {
            if let Some(name) = &function.function.name {
                add_identifier_export(
                    name,
                    ExportStorage::LocalAndProperty,
                    declaration.id(),
                    binding,
                    model,
                    source,
                    exports,
                    identities,
                );
            }
        }
        Statement::Class(class) => {
            if let Some(name) = &class.name {
                add_identifier_export(
                    name,
                    ExportStorage::LocalAndProperty,
                    declaration.id(),
                    binding,
                    model,
                    source,
                    exports,
                    identities,
                );
            }
        }
        Statement::Enum(enum_declaration) if !enum_declaration.is_const => add_identifier_export(
            &enum_declaration.name,
            ExportStorage::LocalAndProperty,
            declaration.id(),
            binding,
            model,
            source,
            exports,
            identities,
        ),
        Statement::Namespace(namespace)
            if matches!(namespace.name, NamespaceName::Identifier { .. })
                && by_declaration.get(&declaration.id()).is_some_and(|child| {
                    !child.ambient && namespace_is_value_bearing(child, by_declaration)
                }) =>
        {
            add_identifier_export(
                namespace
                    .name
                    .as_identifier()
                    .expect("guarded identifier name"),
                ExportStorage::LocalAndProperty,
                declaration.id(),
                binding,
                model,
                source,
                exports,
                identities,
            );
        }
        _ => {}
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "identifier export recording shares the namespace build tables"
)]
fn add_identifier_export(
    identifier: &crate::syntax::IdentifierNode,
    storage: ExportStorage,
    declaration: NodeId,
    binding: &NamespaceDeclarationBinding<'_>,
    model: &SemanticModel,
    source: &crate::syntax::SourceFile,
    exports: &mut Vec<NamespaceExport>,
    identities: &mut HashMap<SymbolId, Vec<ExportIdentity>>,
) {
    let Some(name) = source.identifier_text(identifier.data().token()) else {
        return;
    };
    add_export(
        name.as_ref(),
        storage,
        declaration,
        binding,
        model,
        exports,
        identities,
    );
}

fn add_export(
    name: &str,
    storage: ExportStorage,
    declaration: NodeId,
    binding: &NamespaceDeclarationBinding<'_>,
    model: &SemanticModel,
    exports: &mut Vec<NamespaceExport>,
    identities: &mut HashMap<SymbolId, Vec<ExportIdentity>>,
) {
    let Some(symbol) = model.scope(binding.export_scope).value(name) else {
        return;
    };
    let name = EcmaString::encode(name);
    exports.push(NamespaceExport {
        name: name.clone(),
        storage,
        declaration,
    });
    identities.entry(symbol).or_default().push(ExportIdentity {
        container: binding.symbol,
        name,
        storage,
        declaration_block: binding.declaration_id,
    });
}

fn collect_variable_exports(
    variable: &VariableDeclaration,
    mut add: impl FnMut(&crate::syntax::IdentifierNode),
) {
    fn visit(
        pattern: &crate::syntax::Pattern,
        add: &mut impl FnMut(&crate::syntax::IdentifierNode),
    ) {
        match pattern.data() {
            BindingPattern::Identifier(identifier) => add(identifier),
            BindingPattern::Object(object) => {
                for property in &object.properties {
                    visit(&property.binding, add);
                }
            }
            BindingPattern::Array(array) => {
                for element in &array.elements {
                    if let crate::syntax::ArrayBindingElement::Binding(inner) = element {
                        visit(inner, add);
                    }
                }
            }
            BindingPattern::Rest(rest) => visit(&rest.argument, add),
            BindingPattern::Assignment(assignment) => visit(&assignment.left, add),
            BindingPattern::Missing(_) => {}
        }
    }

    for declarator in &variable.declarations {
        visit(&declarator.data().binding, &mut add);
    }
}

fn namespace_is_value_bearing(
    binding: &NamespaceDeclarationBinding<'_>,
    by_declaration: &HashMap<NodeId, &NamespaceDeclarationBinding<'_>>,
) -> bool {
    matches!(binding.declaration.name, NamespaceName::Identifier { .. })
        && !binding.ambient
        && binding
            .declaration
            .body
            .data()
            .statements
            .iter()
            .any(|statement| statement_is_value_bearing(statement, by_declaration))
}

fn statement_is_value_bearing(
    statement: &crate::syntax::Stmt,
    by_declaration: &HashMap<NodeId, &NamespaceDeclarationBinding<'_>>,
) -> bool {
    match statement.data() {
        Statement::Interface(_) | Statement::TypeAlias(_) => false,
        Statement::Enum(declaration) => !declaration.is_const,
        Statement::Namespace(_) => by_declaration
            .get(&statement.id())
            .is_some_and(|binding| namespace_is_value_bearing(binding, by_declaration)),
        Statement::Declare(_) => false,
        // An alias holds a value only once it is published on the container.
        Statement::ImportEquals(_) => false,
        Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(inner))) => {
            matches!(inner.data(), Statement::ImportEquals(_))
                || statement_is_value_bearing(inner, by_declaration)
        }
        Statement::Empty => false,
        _ => true,
    }
}
