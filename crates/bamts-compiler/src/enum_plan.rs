//! Immutable TypeScript enum facts derived from one completed checker pass.

use std::collections::{HashMap, HashSet};

use bamts_bytecode::{EcmaString, EcmaStringBuilder, NumberBits, format_number};

use crate::checker::{EnumBindingView, SemanticModel, Symbol, SymbolId, SymbolKind};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::literal::{cook_escapes, number_value, string_value};
use crate::source::{SourceId, TextRange};
use crate::syntax::{
    BinaryOperator, EnumDeclaration, Expr, Expression, Literal, MemberProperty, NodeId,
    PropertyName, Statement, Stmt, TokenKind, UnaryOperator,
};

pub const INVALID_ENUM_MEMBER_NAME: DiagnosticCode = DiagnosticCode::new("BAMTS-C005");
pub const ENUM_AUTO_INITIALIZER_REQUIRED: DiagnosticCode = DiagnosticCode::new("BAMTS-C006");
pub const CONST_OR_AMBIENT_ENUM_NONCONSTANT: DiagnosticCode = DiagnosticCode::new("BAMTS-C007");
pub const CONST_ENUM_NONFINITE: DiagnosticCode = DiagnosticCode::new("BAMTS-C008");
pub const ENUM_SELF_OR_FORWARD_REFERENCE: DiagnosticCode = DiagnosticCode::new("BAMTS-C009");
pub const MIXED_ENUM_CONSTNESS: DiagnosticCode = DiagnosticCode::new("BAMTS-C010");
pub const MERGED_ENUM_MULTIPLE_AUTO_FIRST: DiagnosticCode = DiagnosticCode::new("BAMTS-C011");
pub const ENUM_ARITHMETIC_LEFT_NOT_NUMBER: DiagnosticCode = DiagnosticCode::new("BAMTS-C042");
pub const ENUM_ARITHMETIC_RIGHT_NOT_NUMBER: DiagnosticCode = DiagnosticCode::new("BAMTS-C043");

const INVALID_NAME_MESSAGE: &str =
    "An enum member name must be an identifier, string literal, or numeric literal.";
const AUTO_INITIALIZER_MESSAGE: &str =
    "Enum member must have initializer because the preceding value is not a number.";
const CONST_OR_AMBIENT_MESSAGE: &str =
    "Const or ambient enum member initializer must be a constant expression.";
const NONFINITE_MESSAGE: &str = "Const enum member initializer cannot evaluate to NaN or Infinity.";
const SELF_OR_FORWARD_MESSAGE: &str =
    "Enum member initializer cannot reference itself or a later member.";
const MIXED_CONSTNESS_MESSAGE: &str = "All declarations of a merged enum must agree on constness.";
const MULTIPLE_AUTO_FIRST_MESSAGE: &str =
    "Only one declaration of a merged enum may omit its first member initializer.";
const ENUM_ARITHMETIC_LEFT_NOT_NUMBER_MESSAGE: &str = "The left-hand side of an arithmetic operation must be of type 'any', 'number', 'bigint' or an enum type.";
const ENUM_ARITHMETIC_RIGHT_NOT_NUMBER_MESSAGE: &str = "The right-hand side of an arithmetic operation must be of type 'any', 'number', 'bigint' or an enum type.";

/// The checked meaning of all enum declarations in one source file.
#[derive(Clone, Debug)]
pub struct EnumFacts {
    declaration_symbols: HashMap<NodeId, SymbolId>,
    member_symbols: HashMap<NodeId, SymbolId>,
    declarations: HashMap<NodeId, EnumPlan>,
    const_uses: HashMap<NodeId, EnumScalar>,
    member_uses: HashMap<NodeId, EnumMemberUse>,
    const_enum_members: HashMap<SymbolId, ConstEnumMembers>,
    imported_member_uses: HashMap<NodeId, ImportedEnumMemberUse>,
    local_member_targets: HashMap<NodeId, SymbolId>,
    imported_member_targets: HashSet<NodeId>,
    const_enum_member_targets: HashSet<NodeId>,
    elided_import_specifiers: HashSet<NodeId>,
}

impl EnumFacts {
    /// Creates deliberately unchecked empty facts.
    ///
    /// This is only for callers that intentionally bypass semantic checking;
    /// normal compilation must use checker-produced facts.  There is no
    /// `Default` implementation so that bypass remains visible at the callsite.
    #[must_use]
    pub(crate) fn unchecked() -> Self {
        Self {
            declaration_symbols: HashMap::new(),
            member_symbols: HashMap::new(),
            declarations: HashMap::new(),
            const_uses: HashMap::new(),
            member_uses: HashMap::new(),
            const_enum_members: HashMap::new(),
            imported_member_uses: HashMap::new(),
            local_member_targets: HashMap::new(),
            imported_member_targets: HashSet::new(),
            const_enum_member_targets: HashSet::new(),
            elided_import_specifiers: HashSet::new(),
        }
    }

    #[must_use]
    pub(crate) fn declaration_symbol(&self, declaration: NodeId) -> Option<SymbolId> {
        self.declaration_symbols.get(&declaration).copied()
    }

    #[must_use]
    pub(crate) fn declaration(&self, declaration: NodeId) -> Option<&EnumPlan> {
        self.declarations.get(&declaration)
    }

    #[must_use]
    pub(crate) fn member_symbol(&self, member: NodeId) -> Option<SymbolId> {
        self.member_symbols.get(&member).copied()
    }

    #[must_use]
    pub(crate) fn const_use(&self, reference: NodeId) -> Option<&EnumScalar> {
        self.const_uses.get(&reference)
    }

    #[must_use]
    pub(crate) fn member_use(&self, reference: NodeId) -> Option<&EnumMemberUse> {
        self.member_uses.get(&reference)
    }

    pub(crate) fn member_uses(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.member_uses.keys().copied()
    }

    #[must_use]
    pub(crate) fn const_enum_members(&self, symbol: SymbolId) -> Option<&ConstEnumMembers> {
        self.const_enum_members.get(&symbol)
    }

    pub(crate) fn imported_member_uses(
        &self,
    ) -> impl Iterator<Item = (NodeId, &ImportedEnumMemberUse)> + '_ {
        self.imported_member_uses
            .iter()
            .map(|(&node, site)| (node, site))
    }

    pub(crate) fn local_member_targets(&self) -> impl Iterator<Item = (NodeId, SymbolId)> + '_ {
        self.local_member_targets
            .iter()
            .map(|(&target, &symbol)| (target, symbol))
    }

    pub(crate) fn imported_member_targets(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.imported_member_targets.iter().copied()
    }

    #[must_use]
    pub(crate) fn is_imported_member_target(&self, target: NodeId) -> bool {
        self.imported_member_targets.contains(&target)
    }

    #[must_use]
    pub(crate) fn is_const_enum_member_target(&self, target: NodeId) -> bool {
        self.const_enum_member_targets.contains(&target)
    }

    pub(crate) fn add_import_const_enum_member_target(&mut self, target: NodeId) {
        self.const_enum_member_targets.insert(target);
    }

    #[must_use]
    pub(crate) fn is_elided_import_specifier(&self, specifier: NodeId) -> bool {
        self.elided_import_specifiers.contains(&specifier)
    }

    pub(crate) fn add_import_const_use(&mut self, member: NodeId, value: EnumScalar) {
        self.const_uses.insert(member, value);
    }

    pub(crate) fn elide_import_specifier(&mut self, specifier: NodeId) {
        self.elided_import_specifiers.insert(specifier);
    }
}

/// One declaration's ordered enum members.
#[derive(Clone, Debug)]
pub struct EnumPlan {
    members: Box<[EnumMemberPlan]>,
}

impl EnumPlan {
    #[must_use]
    pub(crate) fn members(&self) -> &[EnumMemberPlan] {
        &self.members
    }
}

/// One source member's checked meaning.
#[derive(Clone, Debug)]
pub enum EnumMemberPlan {
    Valid {
        name: EcmaString,
        value: EnumValue,
        reverse: bool,
    },
    Invalid,
}

impl EnumMemberPlan {
    #[must_use]
    pub(crate) fn name(&self) -> Option<&EcmaString> {
        match self {
            Self::Valid { name, .. } => Some(name),
            Self::Invalid => None,
        }
    }

    #[must_use]
    pub(crate) fn value(&self) -> Option<&EnumValue> {
        match self {
            Self::Valid { value, .. } => Some(value),
            Self::Invalid => None,
        }
    }

    #[must_use]
    pub(crate) fn reverse(&self) -> bool {
        matches!(self, Self::Valid { reverse: true, .. })
    }
}

/// An enum member either has a compile-time scalar or must execute its source initializer.
#[derive(Clone, Debug)]
pub enum EnumValue {
    Constant(EnumScalar),
    Runtime,
}

impl EnumValue {
    #[must_use]
    pub(crate) fn constant(&self) -> Option<&EnumScalar> {
        match self {
            Self::Constant(value) => Some(value),
            Self::Runtime => None,
        }
    }
}

/// A compile-time enum scalar, represented without lossy Rust conversions.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum EnumScalar {
    Number(NumberBits),
    String(EcmaString),
}

impl EnumScalar {
    #[must_use]
    pub(crate) fn number(&self) -> Option<NumberBits> {
        match self {
            Self::Number(value) => Some(*value),
            Self::String(_) => None,
        }
    }
}

/// A direct identifier use of an enum member, resolved by symbol identity.
#[derive(Clone, Debug)]
pub struct EnumMemberUse {
    enum_symbol: SymbolId,
    name: EcmaString,
}

impl EnumMemberUse {
    #[must_use]
    pub(crate) const fn enum_symbol(&self) -> SymbolId {
        self.enum_symbol
    }

    #[must_use]
    pub(crate) fn name(&self) -> &EcmaString {
        &self.name
    }
}

/// An already-evaluated constant-member table for one local const enum.
#[derive(Clone, Debug)]
pub(crate) struct ConstEnumMembers {
    members: HashMap<EcmaString, ConstEnumMember>,
}

impl ConstEnumMembers {
    #[must_use]
    pub(crate) fn member(&self, name: &EcmaString) -> Option<&ConstEnumMember> {
        self.members.get(name)
    }
}

/// The checked constness of a member exported from a const enum.
#[derive(Clone, Debug)]
pub(crate) enum ConstEnumMember {
    Constant(EnumScalar),
    Nonconstant,
    Pending,
}

/// A linked imported const-enum member's current fixed-point value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ImportedConstEnumValue {
    Constant(EnumScalar),
    Nonconstant,
    NotConst,
    Unresolved,
    Ambiguous,
    Cycle,
    Pending,
}

/// An imported-member expression candidate recorded during local reference resolution.
#[derive(Clone, Debug)]
pub(crate) struct ImportedEnumMemberUse {
    base: ImportedEnumMemberBase,
    name: EcmaString,
    range: TextRange,
}

impl ImportedEnumMemberUse {
    #[must_use]
    pub(crate) const fn new(
        base: ImportedEnumMemberBase,
        name: EcmaString,
        range: TextRange,
    ) -> Self {
        Self { base, name, range }
    }

    #[must_use]
    pub(crate) const fn base(&self) -> ImportedEnumMemberBase {
        self.base
    }

    #[must_use]
    pub(crate) fn name(&self) -> &EcmaString {
        &self.name
    }

    #[must_use]
    pub(crate) const fn range(&self) -> TextRange {
        self.range
    }
}

/// The resolved import identity at the base of an imported member expression.
#[derive(Clone, Copy, Debug)]
pub(crate) enum ImportedEnumMemberBase {
    Import(SymbolId),
    /// The outer `Expr` node of a preceding member access. Its result may be an
    /// enum object, a namespace, or a scalar; program linking must classify it
    /// before resolving another member.
    MemberResult(NodeId),
}

/// Checker-owned binding input.  It deliberately borrows syntax only while
/// facts are built; the returned facts contain no source references.
pub(crate) struct EnumDeclarationBinding<'src> {
    pub(crate) declaration: &'src EnumDeclaration,
    pub(crate) declaration_id: NodeId,
    pub(crate) symbol: SymbolId,
    pub(crate) ambient: bool,
}

/// Cooks one valid enum member property name exactly once during binding.
#[must_use]
pub(crate) fn cook_member_name(
    source: &crate::syntax::SourceFile,
    name: &PropertyName,
) -> Option<EcmaString> {
    match name {
        PropertyName::Identifier(identifier) => source
            .identifier_text(identifier.data().token())
            .map(|name| EcmaString::encode(name.as_ref())),
        PropertyName::String(string) => source
            .token_text(string.data().token())
            .and_then(string_value),
        PropertyName::Number(number) => source
            .token_text(number.data().token())
            .and_then(number_value)
            .map(|value| EcmaString::encode(&format_number(value))),
        PropertyName::Private(_) | PropertyName::Computed(_) | PropertyName::Missing(_) => None,
    }
}

#[derive(Clone)]
struct MemberEntry<'src> {
    enum_symbol: SymbolId,
    name: EcmaString,
    initializer: Option<&'src Expr>,
    range: TextRange,
    ordinal: usize,
    syntactically_string: bool,
}

#[derive(Clone)]
enum Evaluated {
    Constant(EnumScalar),
    Runtime,
    Invalid,
    Deferred,
    ImportedInvalid,
}

/// Minimal lexical read view needed by enum scalar evaluation: reference
/// resolution by node, symbol kind/name lookup for the NaN/Infinity
/// intrinsics, and the resolved-reference sweep for const uses.  Implemented
/// by the typed [`SemanticModel`] and by the bootstrap [`EnumBindingView`],
/// so one evaluator serves both without a dummy model.
pub(crate) trait EnumLexicalView {
    /// Symbol a reference resolved to (identifier or alias node).
    fn enum_reference(&self, node: NodeId) -> Option<SymbolId>;

    /// Bound symbol by identity (used only for the NaN/Infinity intrinsics).
    fn enum_symbol(&self, id: SymbolId) -> &Symbol;

    /// Every resolved reference by node, for the const-use sweep.
    fn enum_references(&self) -> impl Iterator<Item = (NodeId, SymbolId)> + '_;
}

impl EnumLexicalView for SemanticModel {
    fn enum_reference(&self, node: NodeId) -> Option<SymbolId> {
        self.reference(node)
    }

    fn enum_symbol(&self, id: SymbolId) -> &Symbol {
        self.symbol(id)
    }

    fn enum_references(&self) -> impl Iterator<Item = (NodeId, SymbolId)> + '_ {
        self.references()
    }
}

impl EnumLexicalView for EnumBindingView<'_> {
    fn enum_reference(&self, node: NodeId) -> Option<SymbolId> {
        self.references
            .get(&node)
            .or_else(|| self.reference_aliases.get(&node))
            .copied()
    }

    fn enum_symbol(&self, id: SymbolId) -> &Symbol {
        &self.symbols[id.get() as usize]
    }

    fn enum_references(&self) -> impl Iterator<Item = (NodeId, SymbolId)> + '_ {
        self.references
            .iter()
            .map(|(&node, &symbol)| (node, symbol))
    }
}

/// Builds checked enum facts after binding and reference resolution.
#[expect(
    clippy::too_many_arguments,
    reason = "enum fact construction takes the full checker binding/use tables"
)]
pub(crate) fn build(
    model: &SemanticModel,
    source: &crate::syntax::SourceFile,
    source_id: SourceId,
    bindings: &[EnumDeclarationBinding<'_>],
    member_symbols: &HashMap<NodeId, SymbolId>,
    member_names: &HashMap<NodeId, EcmaString>,
    direct_member_uses: &HashSet<NodeId>,
    local_member_targets: &HashMap<NodeId, SymbolId>,
    imported_member_uses: &HashMap<NodeId, ImportedEnumMemberUse>,
    imported_member_targets: &HashSet<NodeId>,
) -> (EnumFacts, Vec<Diagnostic>) {
    build_with_imports(
        model,
        source,
        source_id,
        bindings,
        member_symbols,
        member_names,
        direct_member_uses,
        local_member_targets,
        imported_member_uses,
        imported_member_targets,
        &HashMap::new(),
    )
}

/// Builds checked enum facts from the typed semantic model.
#[expect(
    clippy::too_many_arguments,
    reason = "enum fact construction with imports takes the full checker binding/use tables"
)]
pub(crate) fn build_with_imports(
    model: &SemanticModel,
    source: &crate::syntax::SourceFile,
    source_id: SourceId,
    bindings: &[EnumDeclarationBinding<'_>],
    member_symbols: &HashMap<NodeId, SymbolId>,
    member_names: &HashMap<NodeId, EcmaString>,
    direct_member_uses: &HashSet<NodeId>,
    local_member_targets: &HashMap<NodeId, SymbolId>,
    imported_member_uses: &HashMap<NodeId, ImportedEnumMemberUse>,
    imported_member_targets: &HashSet<NodeId>,
    imported_values: &HashMap<NodeId, ImportedConstEnumValue>,
) -> (EnumFacts, Vec<Diagnostic>) {
    build_with_imports_view(
        model,
        source,
        source_id,
        bindings,
        member_symbols,
        member_names,
        direct_member_uses,
        local_member_targets,
        imported_member_uses,
        imported_member_targets,
        imported_values,
    )
}

/// Builds checked enum facts from a retained lexical binder's view before any
/// typed checking, e.g. `build_with_imports_from_inventory(
/// &binder.enum_binding_view(), ...)`.  Shares the evaluator with
/// [`build_with_imports`]; no dummy model is constructed.  The returned facts
/// carry the final local const-enum member scalars in `const_enum_members`,
/// which the cross-file fixed point reads to populate the next round's
/// `imported_values` until no member stays `Pending`.
#[expect(
    clippy::too_many_arguments,
    reason = "inventory entry mirrors build_with_imports"
)]
pub(crate) fn build_with_imports_from_inventory<V: EnumLexicalView + ?Sized>(
    view: &V,
    source: &crate::syntax::SourceFile,
    source_id: SourceId,
    bindings: &[EnumDeclarationBinding<'_>],
    member_symbols: &HashMap<NodeId, SymbolId>,
    member_names: &HashMap<NodeId, EcmaString>,
    direct_member_uses: &HashSet<NodeId>,
    local_member_targets: &HashMap<NodeId, SymbolId>,
    imported_member_uses: &HashMap<NodeId, ImportedEnumMemberUse>,
    imported_member_targets: &HashSet<NodeId>,
    imported_values: &HashMap<NodeId, ImportedConstEnumValue>,
) -> (EnumFacts, Vec<Diagnostic>) {
    build_with_imports_view(
        view,
        source,
        source_id,
        bindings,
        member_symbols,
        member_names,
        direct_member_uses,
        local_member_targets,
        imported_member_uses,
        imported_member_targets,
        imported_values,
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "enum fact construction with imports takes the full checker binding/use tables"
)]
fn build_with_imports_view<V: EnumLexicalView + ?Sized>(
    view: &V,
    source: &crate::syntax::SourceFile,
    source_id: SourceId,
    bindings: &[EnumDeclarationBinding<'_>],
    member_symbols: &HashMap<NodeId, SymbolId>,
    member_names: &HashMap<NodeId, EcmaString>,
    direct_member_uses: &HashSet<NodeId>,
    local_member_targets: &HashMap<NodeId, SymbolId>,
    imported_member_uses: &HashMap<NodeId, ImportedEnumMemberUse>,
    imported_member_targets: &HashSet<NodeId>,
    imported_values: &HashMap<NodeId, ImportedConstEnumValue>,
) -> (EnumFacts, Vec<Diagnostic>) {
    let mut facts = EnumFacts::unchecked();
    facts.member_symbols = member_symbols.clone();
    facts.imported_member_uses = imported_member_uses.clone();
    facts.local_member_targets = local_member_targets.clone();
    facts.imported_member_targets = imported_member_targets.clone();
    let mut diagnostics = Vec::new();
    let mut groups: HashMap<SymbolId, Vec<&EnumDeclarationBinding<'_>>> = HashMap::new();
    for binding in bindings {
        facts
            .declaration_symbols
            .insert(binding.declaration_id, binding.symbol);
        groups.entry(binding.symbol).or_default().push(binding);
    }

    let mut entries = Vec::new();
    let mut names_by_enum: HashMap<SymbolId, HashMap<EcmaString, SymbolId>> = HashMap::new();
    let mut symbol_to_entry = HashMap::new();
    let mut seen_names: HashMap<SymbolId, HashSet<EcmaString>> = HashMap::new();
    let mut declarations_with_duplicate_members = HashSet::new();
    for binding in bindings {
        for member in &binding.declaration.members {
            let member_id = member.id();
            let Some(name) = member_names.get(&member_id).cloned() else {
                diagnostics.push(error(
                    source_id,
                    INVALID_ENUM_MEMBER_NAME,
                    member.range(),
                    INVALID_NAME_MESSAGE,
                ));
                continue;
            };
            let symbol = member_symbols[&member_id];
            let duplicate = !seen_names
                .entry(binding.symbol)
                .or_default()
                .insert(name.clone());
            if duplicate {
                declarations_with_duplicate_members.insert(member_id);
                continue;
            }
            names_by_enum
                .entry(binding.symbol)
                .or_default()
                .insert(name.clone(), symbol);
            let ordinal = entries.len();
            symbol_to_entry.insert(symbol, ordinal);
            let initializer = member.data().initializer.as_deref();
            entries.push(MemberEntry {
                enum_symbol: binding.symbol,
                name,
                initializer,
                range: member.range(),
                ordinal,
                syntactically_string: initializer.is_some_and(is_syntactically_string),
            });
        }
    }

    let mut const_enums = HashSet::new();
    for (symbol, declarations) in &groups {
        let any_const = declarations
            .iter()
            .any(|binding| binding.declaration.is_const);
        let all_const = declarations
            .iter()
            .all(|binding| binding.declaration.is_const);
        if any_const && !all_const {
            for binding in declarations {
                diagnostics.push(error(
                    source_id,
                    MIXED_ENUM_CONSTNESS,
                    binding.declaration.name.range(),
                    MIXED_CONSTNESS_MESSAGE,
                ));
            }
        }
        if all_const {
            const_enums.insert(*symbol);
        }
        let omitted_first: Vec<_> = declarations
            .iter()
            .filter_map(|binding| {
                binding
                    .declaration
                    .members
                    .first()
                    .filter(|member| member.data().initializer.is_none())
            })
            .collect();
        for member in omitted_first.into_iter().skip(1) {
            diagnostics.push(error(
                source_id,
                MERGED_ENUM_MULTIPLE_AUTO_FIRST,
                member.range(),
                MULTIPLE_AUTO_FIRST_MESSAGE,
            ));
        }
    }

    let mut values = HashMap::new();
    let mut plans: HashMap<NodeId, Vec<EnumMemberPlan>> = bindings
        .iter()
        .map(|binding| {
            (
                binding.declaration_id,
                Vec::with_capacity(binding.declaration.members.len()),
            )
        })
        .collect();
    for binding in bindings {
        let const_enum = const_enums.contains(&binding.symbol);
        let mut auto = Some(0.0_f64);
        for member in &binding.declaration.members {
            let member_id = member.id();
            let mut deferred = false;
            let mut imported_invalid = false;
            let plan = if declarations_with_duplicate_members.contains(&member_id)
                || !member_names.contains_key(&member_id)
            {
                EnumMemberPlan::Invalid
            } else {
                let entry = &entries[*symbol_to_entry
                    .get(&member_symbols[&member_id])
                    .expect("bound enum member has an entry")];
                let evaluated = match entry.initializer {
                    Some(initializer) => evaluate(
                        initializer,
                        entry,
                        view,
                        source,
                        &entries,
                        &symbol_to_entry,
                        &names_by_enum,
                        &values,
                        imported_member_uses,
                        imported_values,
                        source_id,
                        &mut diagnostics,
                    ),
                    None if binding.ambient && !const_enum => Evaluated::Runtime,
                    None => match auto {
                        Some(value) => Evaluated::Constant(number(value)),
                        None => {
                            diagnostics.push(error(
                                source_id,
                                ENUM_AUTO_INITIALIZER_REQUIRED,
                                entry.range,
                                AUTO_INITIALIZER_MESSAGE,
                            ));
                            Evaluated::Invalid
                        }
                    },
                };
                deferred = matches!(evaluated, Evaluated::Deferred);
                imported_invalid = matches!(evaluated, Evaluated::ImportedInvalid);
                match evaluated {
                    Evaluated::Constant(value)
                        if (const_enum || binding.ambient) && is_nonfinite(&value) =>
                    {
                        diagnostics.push(error(
                            source_id,
                            CONST_ENUM_NONFINITE,
                            entry.range,
                            NONFINITE_MESSAGE,
                        ));
                        EnumMemberPlan::Invalid
                    }
                    Evaluated::Constant(value) => EnumMemberPlan::Valid {
                        name: entry.name.clone(),
                        reverse: !matches!(&value, EnumScalar::String(_))
                            && !entry.syntactically_string,
                        value: EnumValue::Constant(value),
                    },
                    Evaluated::Runtime
                        if const_enum || (binding.ambient && entry.initializer.is_some()) =>
                    {
                        diagnostics.push(error(
                            source_id,
                            CONST_OR_AMBIENT_ENUM_NONCONSTANT,
                            entry.range,
                            CONST_OR_AMBIENT_MESSAGE,
                        ));
                        EnumMemberPlan::Invalid
                    }
                    Evaluated::Runtime => EnumMemberPlan::Valid {
                        name: entry.name.clone(),
                        value: EnumValue::Runtime,
                        reverse: !entry.syntactically_string,
                    },
                    Evaluated::Deferred | Evaluated::ImportedInvalid
                        if const_enum || binding.ambient =>
                    {
                        EnumMemberPlan::Invalid
                    }
                    Evaluated::Deferred | Evaluated::ImportedInvalid => EnumMemberPlan::Valid {
                        name: entry.name.clone(),
                        value: EnumValue::Runtime,
                        reverse: !entry.syntactically_string,
                    },
                    Evaluated::Invalid => EnumMemberPlan::Invalid,
                }
            };
            if let Some(symbol) = member_symbols.get(&member_id).copied() {
                match &plan {
                    EnumMemberPlan::Valid {
                        value: EnumValue::Constant(value),
                        ..
                    } => {
                        values.insert(symbol, Evaluated::Constant(value.clone()));
                        auto = value.number().map(|value| value.to_f64() + 1.0);
                    }
                    EnumMemberPlan::Valid {
                        value: EnumValue::Runtime,
                        ..
                    } => {
                        values.insert(symbol, Evaluated::Runtime);
                        auto = None;
                    }
                    EnumMemberPlan::Invalid => {
                        values.insert(
                            symbol,
                            if deferred {
                                Evaluated::Deferred
                            } else if imported_invalid {
                                Evaluated::ImportedInvalid
                            } else {
                                Evaluated::Invalid
                            },
                        );
                        auto = None;
                    }
                }
            } else {
                auto = None;
            }
            plans
                .get_mut(&binding.declaration_id)
                .expect("every enum declaration has a plan")
                .push(plan);
        }
    }

    for binding in bindings {
        if !const_enums.contains(&binding.symbol) {
            continue;
        }
        let members = facts
            .const_enum_members
            .entry(binding.symbol)
            .or_insert_with(|| ConstEnumMembers {
                members: HashMap::new(),
            });
        for member in &binding.declaration.members {
            let Some(name) = member_names.get(&member.id()).cloned() else {
                continue;
            };
            let value = member_symbols
                .get(&member.id())
                .and_then(|symbol| values.get(symbol));
            let value = match value {
                Some(Evaluated::Constant(value)) => ConstEnumMember::Constant(value.clone()),
                Some(Evaluated::Deferred) => ConstEnumMember::Pending,
                _ => ConstEnumMember::Nonconstant,
            };
            members.members.insert(name, value);
        }
    }

    for (&target, &symbol) in local_member_targets {
        if const_enums.contains(&symbol) {
            facts.const_enum_member_targets.insert(target);
        }
    }

    for (declaration, members) in plans {
        facts.declarations.insert(
            declaration,
            EnumPlan {
                members: members.into_boxed_slice(),
            },
        );
    }
    for reference in direct_member_uses {
        let Some(symbol) = view.enum_reference(*reference) else {
            continue;
        };
        let Some(index) = symbol_to_entry.get(&symbol) else {
            continue;
        };
        let entry = &entries[*index];
        facts.member_uses.insert(
            *reference,
            EnumMemberUse {
                enum_symbol: entry.enum_symbol,
                name: entry.name.clone(),
            },
        );
        if const_enums.contains(&entry.enum_symbol)
            && let Some(Evaluated::Constant(value)) = values.get(&symbol)
        {
            facts.const_uses.insert(*reference, value.clone());
        }
    }
    for (reference, symbol) in view.enum_references() {
        let Some(index) = symbol_to_entry.get(&symbol) else {
            continue;
        };
        let entry = &entries[*index];
        if !const_enums.contains(&entry.enum_symbol) {
            continue;
        }
        if let Some(Evaluated::Constant(value)) = values.get(&symbol) {
            facts.const_uses.insert(reference, value.clone());
        }
    }
    for reference in imported_member_uses.keys() {
        if let Some(ImportedConstEnumValue::Constant(value)) = imported_values.get(reference) {
            facts.const_uses.insert(*reference, value.clone());
        }
        if imported_member_targets.contains(reference)
            && matches!(
                imported_values.get(reference),
                Some(
                    ImportedConstEnumValue::Constant(_)
                        | ImportedConstEnumValue::Nonconstant
                        | ImportedConstEnumValue::Cycle,
                )
            )
        {
            facts.const_enum_member_targets.insert(*reference);
        }
    }
    (facts, diagnostics)
}

#[expect(
    clippy::too_many_arguments,
    reason = "const-enum expression evaluation needs the member tables and import value maps"
)]
fn evaluate<V: EnumLexicalView + ?Sized>(
    expression: &Expr,
    current: &MemberEntry<'_>,
    view: &V,
    source: &crate::syntax::SourceFile,
    entries: &[MemberEntry<'_>],
    symbol_to_entry: &HashMap<SymbolId, usize>,
    names_by_enum: &HashMap<SymbolId, HashMap<EcmaString, SymbolId>>,
    values: &HashMap<SymbolId, Evaluated>,
    imported_member_uses: &HashMap<NodeId, ImportedEnumMemberUse>,
    imported_values: &HashMap<NodeId, ImportedConstEnumValue>,
    source_id: SourceId,
    diagnostics: &mut Vec<Diagnostic>,
) -> Evaluated {
    let expression = unwrap_transparent_expression(expression);
    if imported_member_uses.contains_key(&expression.id()) {
        return match imported_values.get(&expression.id()) {
            Some(ImportedConstEnumValue::Constant(value)) => Evaluated::Constant(value.clone()),
            Some(ImportedConstEnumValue::NotConst) => Evaluated::Runtime,
            Some(
                ImportedConstEnumValue::Nonconstant
                | ImportedConstEnumValue::Unresolved
                | ImportedConstEnumValue::Ambiguous
                | ImportedConstEnumValue::Cycle,
            ) => Evaluated::ImportedInvalid,
            Some(ImportedConstEnumValue::Pending) | None => Evaluated::Deferred,
        };
    }
    match expression.data() {
        Expression::Literal(Literal::Number(number_literal)) => source
            .token_text(number_literal.data().token())
            .and_then(number_value)
            .map(number)
            .map(Evaluated::Constant)
            .unwrap_or(Evaluated::Runtime),
        Expression::Literal(Literal::String(string_literal)) => source
            .token_text(string_literal.data().token())
            .and_then(string_value)
            .map(EnumScalar::String)
            .map(Evaluated::Constant)
            .unwrap_or(Evaluated::Runtime),
        Expression::Template(template) if template.expressions.is_empty() => {
            let [element] = template.elements.as_slice() else {
                return Evaluated::Runtime;
            };
            let token = element.data().token();
            if token.kind() != TokenKind::NoSubstitutionTemplate {
                return Evaluated::Runtime;
            }
            source
                .token_text(token)
                .and_then(|text| text.strip_prefix('`')?.strip_suffix('`'))
                .map(cook_escapes)
                .map(EnumScalar::String)
                .map(Evaluated::Constant)
                .unwrap_or(Evaluated::Runtime)
        }
        Expression::Identifier(_) => {
            let Some(symbol) = view.enum_reference(expression.id()) else {
                return Evaluated::Runtime;
            };
            if matches!(view.enum_symbol(symbol).kind(), SymbolKind::IntrinsicValue)
                && matches!(view.enum_symbol(symbol).name(), "NaN" | "Infinity")
            {
                return Evaluated::Constant(number(if view.enum_symbol(symbol).name() == "NaN" {
                    f64::NAN
                } else {
                    f64::INFINITY
                }));
            }
            enum_member_value(
                symbol,
                expression.range(),
                current,
                entries,
                symbol_to_entry,
                values,
                source_id,
                diagnostics,
            )
        }
        Expression::Member(member) if !member.optional => {
            let Some(enum_symbol) = view.enum_reference(member.object.id()) else {
                return Evaluated::Runtime;
            };
            let Some(name) = cook_member_property_name(source, &member.property) else {
                return Evaluated::Runtime;
            };
            let Some(symbol) = names_by_enum
                .get(&enum_symbol)
                .and_then(|members| members.get(&name))
                .copied()
            else {
                return Evaluated::Runtime;
            };
            enum_member_value(
                symbol,
                expression.range(),
                current,
                entries,
                symbol_to_entry,
                values,
                source_id,
                diagnostics,
            )
        }
        Expression::Unary(unary) => match evaluate(
            &unary.argument,
            current,
            view,
            source,
            entries,
            symbol_to_entry,
            names_by_enum,
            values,
            imported_member_uses,
            imported_values,
            source_id,
            diagnostics,
        ) {
            Evaluated::Constant(EnumScalar::Number(value)) => {
                let value = value.to_f64();
                match unary.operator {
                    UnaryOperator::Plus => Evaluated::Constant(number(value)),
                    UnaryOperator::Minus => Evaluated::Constant(number(-value)),
                    UnaryOperator::BitNot => Evaluated::Constant(number(f64::from(!to_i32(value)))),
                    _ => Evaluated::Runtime,
                }
            }
            Evaluated::Deferred | Evaluated::ImportedInvalid
                if !matches!(
                    unary.operator,
                    UnaryOperator::Plus | UnaryOperator::Minus | UnaryOperator::BitNot
                ) =>
            {
                // The operator itself is nonconstant, independent of its operand.
                Evaluated::Runtime
            }
            other => other,
        },
        Expression::Binary(binary) => {
            let left = evaluate(
                &binary.left,
                current,
                view,
                source,
                entries,
                symbol_to_entry,
                names_by_enum,
                values,
                imported_member_uses,
                imported_values,
                source_id,
                diagnostics,
            );
            let right = evaluate(
                &binary.right,
                current,
                view,
                source,
                entries,
                symbol_to_entry,
                names_by_enum,
                values,
                imported_member_uses,
                imported_values,
                source_id,
                diagnostics,
            );
            // `+` is the only binary operator that accepts string operands;
            // `-`, `*`, etc. require numeric/bigint/enum operands.
            if matches!(
                binary.operator,
                BinaryOperator::Subtract
                    | BinaryOperator::Multiply
                    | BinaryOperator::Divide
                    | BinaryOperator::Remainder
                    | BinaryOperator::Exponentiate
                    | BinaryOperator::LeftShift
                    | BinaryOperator::SignedRightShift
                    | BinaryOperator::UnsignedRightShift
                    | BinaryOperator::BitAnd
                    | BinaryOperator::BitOr
                    | BinaryOperator::BitXor
            ) {
                let left_error = matches!(left, Evaluated::Constant(EnumScalar::String(_)));
                let right_error = matches!(right, Evaluated::Constant(EnumScalar::String(_)));
                if left_error {
                    diagnostics.push(error(
                        source_id,
                        ENUM_ARITHMETIC_LEFT_NOT_NUMBER,
                        binary.left.range(),
                        ENUM_ARITHMETIC_LEFT_NOT_NUMBER_MESSAGE,
                    ));
                }
                if right_error {
                    diagnostics.push(error(
                        source_id,
                        ENUM_ARITHMETIC_RIGHT_NOT_NUMBER,
                        binary.right.range(),
                        ENUM_ARITHMETIC_RIGHT_NOT_NUMBER_MESSAGE,
                    ));
                }
                if left_error || right_error {
                    return Evaluated::Invalid;
                }
            }
            binary_value(binary.operator, left, right)
        }
        _ => Evaluated::Runtime,
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "enum member value lookup threads entry tables and diagnostics together"
)]
fn enum_member_value(
    symbol: SymbolId,
    range: TextRange,
    current: &MemberEntry<'_>,
    entries: &[MemberEntry<'_>],
    symbol_to_entry: &HashMap<SymbolId, usize>,
    values: &HashMap<SymbolId, Evaluated>,
    source_id: SourceId,
    diagnostics: &mut Vec<Diagnostic>,
) -> Evaluated {
    let Some(index) = symbol_to_entry.get(&symbol) else {
        return Evaluated::Runtime;
    };
    let target = &entries[*index];
    if target.enum_symbol == current.enum_symbol && target.ordinal >= current.ordinal {
        diagnostics.push(error(
            source_id,
            ENUM_SELF_OR_FORWARD_REFERENCE,
            range,
            SELF_OR_FORWARD_MESSAGE,
        ));
        return Evaluated::Invalid;
    }
    values.get(&symbol).cloned().unwrap_or(Evaluated::Runtime)
}

fn binary_value(operator: BinaryOperator, left: Evaluated, right: Evaluated) -> Evaluated {
    match (left, right) {
        (Evaluated::Invalid, _) | (_, Evaluated::Invalid) => Evaluated::Invalid,
        (Evaluated::Deferred | Evaluated::ImportedInvalid, _)
        | (_, Evaluated::Deferred | Evaluated::ImportedInvalid)
            if !matches!(
                operator,
                BinaryOperator::Add
                    | BinaryOperator::Subtract
                    | BinaryOperator::Multiply
                    | BinaryOperator::Divide
                    | BinaryOperator::Remainder
                    | BinaryOperator::Exponentiate
                    | BinaryOperator::LeftShift
                    | BinaryOperator::SignedRightShift
                    | BinaryOperator::UnsignedRightShift
                    | BinaryOperator::BitAnd
                    | BinaryOperator::BitOr
                    | BinaryOperator::BitXor
            ) =>
        {
            // An unsupported operator is a local C007 cause, not an imported one.
            Evaluated::Runtime
        }
        (Evaluated::ImportedInvalid, _) | (_, Evaluated::ImportedInvalid) => Evaluated::Invalid,
        (Evaluated::Runtime, _) | (_, Evaluated::Runtime) => Evaluated::Runtime,
        (Evaluated::Deferred, _) | (_, Evaluated::Deferred) => Evaluated::Deferred,
        (
            Evaluated::Constant(EnumScalar::String(left)),
            Evaluated::Constant(EnumScalar::String(right)),
        ) if operator == BinaryOperator::Add => {
            let mut output = EcmaStringBuilder::with_capacity(left.len_units() + right.len_units());
            for unit in left.as_units().iter().chain(right.as_units()) {
                output.push_unit(*unit);
            }
            Evaluated::Constant(EnumScalar::String(output.finish()))
        }
        (
            Evaluated::Constant(EnumScalar::Number(left)),
            Evaluated::Constant(EnumScalar::Number(right)),
        ) => {
            let left = left.to_f64();
            let right = right.to_f64();
            let value = match operator {
                BinaryOperator::Add => left + right,
                BinaryOperator::Subtract => left - right,
                BinaryOperator::Multiply => left * right,
                BinaryOperator::Divide => left / right,
                BinaryOperator::Remainder => left % right,
                BinaryOperator::Exponentiate => left.powf(right),
                BinaryOperator::LeftShift => {
                    f64::from(to_i32(left).wrapping_shl(to_u32(right) & 31))
                }
                BinaryOperator::SignedRightShift => f64::from(to_i32(left) >> (to_u32(right) & 31)),
                BinaryOperator::UnsignedRightShift => {
                    f64::from(to_u32(left) >> (to_u32(right) & 31))
                }
                BinaryOperator::BitAnd => f64::from(to_i32(left) & to_i32(right)),
                BinaryOperator::BitOr => f64::from(to_i32(left) | to_i32(right)),
                BinaryOperator::BitXor => f64::from(to_i32(left) ^ to_i32(right)),
                _ => return Evaluated::Runtime,
            };
            Evaluated::Constant(number(value))
        }
        _ => Evaluated::Runtime,
    }
}

pub(crate) fn cook_member_property_name(
    source: &crate::syntax::SourceFile,
    property: &MemberProperty,
) -> Option<EcmaString> {
    match property {
        MemberProperty::Named(identifier) => source
            .identifier_text(identifier.data().token())
            .map(|name| EcmaString::encode(name.as_ref())),
        MemberProperty::Computed(expression) => match expression.data() {
            Expression::Literal(Literal::String(string)) => source
                .token_text(string.data().token())
                .and_then(string_value),
            Expression::Literal(Literal::Number(number)) => source
                .token_text(number.data().token())
                .and_then(number_value)
                .map(|value| EcmaString::encode(&format_number(value))),
            _ => None,
        },
        MemberProperty::Private(_) => None,
    }
}

fn unwrap_transparent_expression(expression: &Expr) -> &Expr {
    match expression.data() {
        Expression::Parenthesized(inner) => unwrap_transparent_expression(inner),
        Expression::As(as_expression) => unwrap_transparent_expression(&as_expression.expression),
        Expression::Satisfies(satisfies) => unwrap_transparent_expression(&satisfies.expression),
        Expression::TypeAssertion(assertion) => {
            unwrap_transparent_expression(&assertion.expression)
        }
        Expression::NonNull(non_null) => unwrap_transparent_expression(&non_null.expression),
        _ => expression,
    }
}

fn is_syntactically_string(expression: &Expr) -> bool {
    match unwrap_transparent_expression(expression).data() {
        Expression::Literal(Literal::String(_)) | Expression::Template(_) => true,
        Expression::Binary(binary) if binary.operator == BinaryOperator::Add => {
            is_syntactically_string(&binary.left) || is_syntactically_string(&binary.right)
        }
        _ => false,
    }
}

fn number(value: f64) -> EnumScalar {
    EnumScalar::Number(NumberBits::from_f64(value))
}

fn is_nonfinite(value: &EnumScalar) -> bool {
    value
        .number()
        .is_some_and(|value| !value.to_f64().is_finite())
}

fn to_i32(value: f64) -> i32 {
    to_u32(value) as i32
}

fn to_u32(value: f64) -> u32 {
    if !value.is_finite() || value == 0.0 {
        return 0;
    }
    let integer = value.trunc();
    let modulo = integer.rem_euclid(4_294_967_296.0);
    modulo as u32
}

fn error(
    source: SourceId,
    code: DiagnosticCode,
    range: TextRange,
    message: &'static str,
) -> Diagnostic {
    Diagnostic::error(code, source, range, message)
}

/// Returns an enum declaration and the identity that enum facts use, unwrapping
/// declaration-file `declare` wrappers.
pub(crate) fn enum_declaration(statement: &Stmt) -> Option<(&EnumDeclaration, NodeId)> {
    let mut statement = statement;
    while let Statement::Declare(inner) = statement.data() {
        statement = inner.as_ref();
    }
    let Statement::Enum(declaration) = statement.data() else {
        return None;
    };
    Some((declaration, statement.id()))
}

#[cfg(test)]
mod tests {
    use super::{ENUM_ARITHMETIC_LEFT_NOT_NUMBER, ENUM_ARITHMETIC_RIGHT_NOT_NUMBER};
    use super::{cook_member_name, cook_member_property_name};
    use crate::checker::{SemanticModel, check};
    use crate::diagnostic::Recovered;
    use crate::source::{ScriptKind, SourceId, SourceText};
    use crate::syntax::{Expression, MemberProperty, SourceFile, Statement};
    use crate::{parser, scanner};
    use std::sync::Arc;

    fn check_text(text: &str) -> Recovered<SemanticModel> {
        let source = Arc::new(SourceText::new(text).expect("test source fits the per-file budget"));
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source,
        ));
        check(&parsed)
    }

    fn arithmetic_codes(result: &Recovered<SemanticModel>) -> Vec<&'static str> {
        result
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .filter(|code| {
                *code == ENUM_ARITHMETIC_LEFT_NOT_NUMBER.as_str()
                    || *code == ENUM_ARITHMETIC_RIGHT_NOT_NUMBER.as_str()
            })
            .collect()
    }

    #[test]
    fn relational_operator_with_string_operand_does_not_trigger_arithmetic_diagnostic() {
        // `<` is relational, not arithmetic — a string operand is legal, so
        // C042/C043 must not fire even though the operand is a string constant.
        let checked = check_text(r#"enum E { A = "x" < "y" }"#);
        assert!(
            arithmetic_codes(&checked).is_empty(),
            "relational operator should not trigger C042/C043: {:?}",
            arithmetic_codes(&checked)
        );
    }

    #[test]
    fn arithmetic_operator_with_string_operand_still_triggers_diagnostic() {
        // `-` is arithmetic — a string left operand is invalid, so C042 fires.
        let checked = check_text(r#"enum E { A = "x" - 1 }"#);
        assert_eq!(
            arithmetic_codes(&checked),
            [ENUM_ARITHMETIC_LEFT_NOT_NUMBER.as_str()]
        );
    }
    fn source_text(text: &str) -> SourceFile {
        let source = Arc::new(SourceText::new(text).expect("test source fits the per-file budget"));
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source,
        ));
        assert!(
            parsed.diagnostics().is_empty(),
            "test source should parse cleanly: {:?}",
            parsed.diagnostics()
        );
        parsed.into_product()
    }

    fn member_properties(source: &SourceFile) -> Vec<&MemberProperty> {
        let mut properties = Vec::new();
        for statement in source.statements() {
            let Statement::Expression(statement) = statement.data() else {
                continue;
            };
            let Expression::Member(member) = statement.expression.data() else {
                continue;
            };
            properties.push(&member.property);
        }
        properties
    }

    #[test]
    fn computed_numeric_member_property_name_normalizes_equivalent_spellings() {
        // Decimal, exponent, separator, and hexadecimal spellings of the same
        // numeric value must resolve to the same enum member name so computed
        // access like `E[1e3]` finds the member declared as `1000`.
        let source = source_text("o[1e3]; o[1_000]; o[0x3e8]; o[1000];");
        let properties = member_properties(&source);
        assert_eq!(properties.len(), 4, "expected four member expressions");
        let names: Vec<_> = properties
            .iter()
            .map(|property| cook_member_property_name(&source, property))
            .collect();
        let first = names[0]
            .as_ref()
            .expect("first access should produce a name");
        for name in &names[1..] {
            assert_eq!(
                name.as_ref().map(|n| n.to_utf8_lossy()),
                Some(first.to_utf8_lossy()),
                "all equivalent numeric spellings must normalize to the same member name"
            );
        }
        assert_eq!(first.to_utf8_lossy(), "1000");
    }

    #[test]
    fn exponent_boundary_numeric_names_use_ecmascript_format() {
        let source = source_text("enum E { 1e21, 1e-7 }\no[1e21]; o[1e-7];");
        let Statement::Enum(declaration) = source.statements()[0].data() else {
            panic!("first statement should be an enum declaration");
        };
        let declared: Vec<String> = declaration
            .members
            .iter()
            .map(|member| {
                cook_member_name(&source, &member.data().name)
                    .expect("numeric enum member should have a cooked name")
                    .to_utf8_lossy()
            })
            .collect();
        assert_eq!(declared, ["1e+21", "1e-7"]);

        let accessed: Vec<String> = member_properties(&source)
            .into_iter()
            .map(|property| {
                cook_member_property_name(&source, property)
                    .expect("computed numeric access should have a cooked name")
                    .to_utf8_lossy()
            })
            .collect();
        assert_eq!(accessed, ["1e+21", "1e-7"]);
    }
}
