use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
    sync::Arc,
};

use crate::checker::binder::{PropertyAnchor, PropertyAnchorKind, PropertyId};
use crate::{
    checker::{SymbolId, SymbolKind, render_type},
    diagnostic::DiagnosticSeverity,
    scanner,
    source::{ScriptKind, SourceId, SourceText, TextRange, Utf16Pos},
    syntax::{Token, TokenKind, VariableKind},
};

use super::{DocumentSnapshot, ServiceError, ServiceState, filesystem::FileSystem};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Completion {
    pub name: String,
    pub kind: SymbolKind,
    pub replacement: TextRange,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Location {
    pub path: PathBuf,
    pub range: TextRange,
    /// Whether this location is the symbol's declaration rather than a use.
    pub is_declaration: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DocumentEdit {
    pub path: PathBuf,
    pub range: TextRange,
    pub replacement: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RenameEdit {
    pub edits: Vec<DocumentEdit>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RenameResult {
    pub symbol: String,
    pub edit: RenameEdit,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DiagnosticEntry {
    pub path: PathBuf,
    pub range: TextRange,
    pub code: &'static str,
    pub severity: DiagnosticSeverity,
    pub message: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum QuickInfoKind {
    Symbol(SymbolKind),
    Property,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QuickInfo {
    pub name: String,
    pub kind: QuickInfoKind,
    pub type_display: String,
    pub range: TextRange,
}

impl QuickInfo {
    #[must_use]
    pub fn display(&self) -> String {
        let kind = match self.kind {
            QuickInfoKind::Symbol(SymbolKind::Variable(VariableKind::Const)) => "const",
            QuickInfoKind::Symbol(SymbolKind::Variable(VariableKind::Let)) => "let",
            QuickInfoKind::Symbol(SymbolKind::Variable(VariableKind::Var)) => "var",
            QuickInfoKind::Symbol(SymbolKind::Variable(VariableKind::Using)) => "using",
            QuickInfoKind::Symbol(SymbolKind::Variable(VariableKind::AwaitUsing)) => "await using",
            QuickInfoKind::Symbol(SymbolKind::Function) => "function",
            QuickInfoKind::Symbol(SymbolKind::Class) => "class",
            QuickInfoKind::Symbol(SymbolKind::Interface) => "interface",
            QuickInfoKind::Symbol(SymbolKind::TypeAlias) => "type",
            QuickInfoKind::Symbol(SymbolKind::Enum) => "enum",
            QuickInfoKind::Symbol(SymbolKind::EnumMember) => "enum member",
            QuickInfoKind::Symbol(SymbolKind::Parameter) => "parameter",
            QuickInfoKind::Symbol(SymbolKind::TypeParameter) => "type parameter",
            QuickInfoKind::Symbol(SymbolKind::Import) => "alias",
            QuickInfoKind::Symbol(SymbolKind::Namespace) => "namespace",
            QuickInfoKind::Symbol(SymbolKind::IntrinsicValue | SymbolKind::IntrinsicType) => {
                "symbol"
            }
            QuickInfoKind::Property => "property",
        };
        format!("{kind} {}: {}", self.name, self.type_display)
    }
}

impl<F: FileSystem> ServiceState<F> {
    pub fn completions(
        &mut self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
    ) -> Result<Vec<Completion>, ServiceError> {
        let document = self.ensure_document(path.as_ref())?;
        validate_position(&document, position)?;
        let (prefix, replacement) = completion_prefix(&document, position);
        let mut seen = BTreeSet::new();
        let mut completions = document
            .semantic()
            .symbols()
            .iter()
            .filter(|symbol| symbol.name().starts_with(prefix.as_str()))
            .filter(|symbol| seen.insert(symbol.name().to_owned()))
            .map(|symbol| Completion {
                name: symbol.name().to_owned(),
                kind: symbol.kind(),
                replacement,
            })
            .collect::<Vec<_>>();
        completions.sort_by(|left, right| left.name.cmp(&right.name));
        Ok(completions)
    }

    pub fn definition(
        &mut self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
    ) -> Result<Option<Location>, ServiceError> {
        let document = self.ensure_document(path.as_ref())?;
        let Some(symbol) = symbol_at(&document, position)? else {
            return Ok(property_definition_location(&document, position));
        };
        Ok(Some(Location {
            path: document.path().to_path_buf(),
            range: document.semantic().symbol(symbol).range(),
            is_declaration: true,
        }))
    }

    pub fn quick_info(
        &mut self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
    ) -> Result<Option<QuickInfo>, ServiceError> {
        let document = self.ensure_document(path.as_ref())?;
        let symbol = symbol_at(&document, position)?;
        let Some(token) = token_at(&document, position) else {
            return Ok(None);
        };
        let Some(symbol) = symbol else {
            return Ok(property_quick_info(&document, token));
        };
        let model = document.semantic();
        let target = model.symbol(symbol);
        let type_id = model.symbol_type(symbol);
        if matches!(model.types().get(type_id), crate::checker::Type::Error) {
            return Ok(None);
        }
        Ok(Some(QuickInfo {
            name: target.name().to_owned(),
            kind: QuickInfoKind::Symbol(target.kind()),
            type_display: render_type(model, type_id),
            range: token.range(),
        }))
    }

    pub fn references(
        &mut self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
    ) -> Result<Vec<Location>, ServiceError> {
        let document = self.ensure_document(path.as_ref())?;
        let Some(symbol) = symbol_at(&document, position)? else {
            let Some(property_id) = property_anchor_at(&document, position) else {
                return Ok(Vec::new());
            };
            return Ok(property_reference_locations(&document, property_id));
        };
        Ok(reference_locations(&document, symbol))
    }

    pub fn rename(
        &mut self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
        new_name: &str,
    ) -> Result<RenameResult, ServiceError> {
        if !is_rename_identifier(new_name) {
            return Err(ServiceError::InvalidRename(format!(
                "rename target is not an identifier: {new_name}"
            )));
        }
        let document = self.ensure_document(path.as_ref())?;
        if let Some(property_id) = property_anchor_at(&document, position) {
            return rename_property(&document, property_id, new_name);
        }
        let symbol = symbol_at(&document, position)?.ok_or(ServiceError::RenameUnavailable)?;
        let target = document.semantic().symbol(symbol);
        let old_name = target.name();
        if document
            .semantic()
            .symbols()
            .iter()
            .enumerate()
            .any(|(index, candidate)| {
                index != symbol_index(symbol)
                    && candidate.scope() == target.scope()
                    && candidate.name() == new_name
            })
        {
            return Err(ServiceError::InvalidRename(format!(
                "rename would conflict with existing symbol `{new_name}`"
            )));
        }
        let edits = reference_locations(&document, symbol)
            .into_iter()
            .map(|location| DocumentEdit {
                path: location.path,
                range: location.range,
                replacement: new_name.to_owned(),
            })
            .collect();
        Ok(RenameResult {
            symbol: old_name.to_owned(),
            edit: RenameEdit { edits },
        })
    }

    pub fn diagnostics(
        &mut self,
        path: impl AsRef<Path>,
    ) -> Result<Vec<DiagnosticEntry>, ServiceError> {
        let document = self.ensure_document(path.as_ref())?;
        Ok(document
            .diagnostics()
            .iter()
            .map(|diagnostic| DiagnosticEntry {
                path: document.path().to_path_buf(),
                range: diagnostic.range(),
                code: diagnostic.code().as_str(),
                severity: diagnostic.severity(),
                message: diagnostic.message().to_owned(),
            })
            .collect())
    }
}

fn validate_position(document: &DocumentSnapshot, position: Utf16Pos) -> Result<(), ServiceError> {
    document
        .source()
        .source_text()
        .utf16_to_byte(position)
        .map(|_| ())
        .map_err(|_| ServiceError::InvalidPosition {
            path: document.path().to_path_buf(),
            offset: position.get(),
        })
}

fn completion_prefix(document: &DocumentSnapshot, position: Utf16Pos) -> (String, TextRange) {
    let Some(token) = token_at(document, position) else {
        return (
            String::new(),
            TextRange::new(position, position).expect("ordered empty range"),
        );
    };
    if identifier_text(document, token).is_none() {
        return (
            String::new(),
            TextRange::new(position, position).expect("ordered empty range"),
        );
    }
    if position < token.range().start() || position > token.range().end() {
        return (
            String::new(),
            TextRange::new(position, position).expect("ordered empty range"),
        );
    }
    let end = document
        .source()
        .source_text()
        .utf16_to_byte(position)
        .expect("position validated");
    let start = document
        .source()
        .source_text()
        .utf16_to_byte(token.range().start())
        .expect("token boundary");
    let prefix = document.source().source_text().as_str()[start..end].to_owned();
    (prefix, token.range())
}

fn symbol_at(
    document: &DocumentSnapshot,
    position: Utf16Pos,
) -> Result<Option<SymbolId>, ServiceError> {
    validate_position(document, position)?;
    let Some(token) = token_at(document, position) else {
        return Ok(None);
    };
    if identifier_text(document, token).is_none() {
        return Ok(None);
    }
    let model = document.semantic();

    if let Some((index, _)) = model
        .symbols()
        .iter()
        .enumerate()
        .find(|(_, symbol)| symbol.range() == token.range())
    {
        let index = u32::try_from(index).expect("symbol table exceeds u32");
        return Ok(Some(SymbolId::new(index)));
    }

    Ok(model
        .symbol_references()
        .iter()
        .find_map(|(range, symbol)| (*range == token.range()).then_some(*symbol)))
}

fn reference_locations(document: &DocumentSnapshot, symbol: SymbolId) -> Vec<Location> {
    let model = document.semantic();
    let mut ranges = Vec::with_capacity(model.symbol_references().len() + 1);
    ranges.push((model.symbol(symbol).range(), true));
    ranges.extend(
        model
            .symbol_references()
            .iter()
            .filter_map(|(range, target)| (*target == symbol).then_some((*range, false))),
    );
    ranges.sort_by_key(|(range, _)| (range.start(), range.end()));
    ranges.dedup();
    ranges
        .into_iter()
        .map(|(range, is_declaration)| Location {
            path: document.path().to_path_buf(),
            range,
            is_declaration,
        })
        .collect()
}

fn property_quick_info(document: &DocumentSnapshot, token: &Token) -> Option<QuickInfo> {
    let tokens = document.source().tokens();
    let index = tokens
        .iter()
        .position(|candidate| candidate.range() == token.range())?;
    let previous = index.checked_sub(1).and_then(|index| tokens.get(index))?;
    if !matches!(previous.kind(), TokenKind::Dot | TokenKind::QuestionDot) {
        return None;
    }

    let model = document.semantic();
    let (_, type_id) = model
        .typed_expressions()
        .iter()
        .filter(|(range, _)| {
            range.start() < token.range().start() && range.end() == token.range().end()
        })
        .min_by_key(|(range, _)| range.len())?;
    if matches!(model.types().get(*type_id), crate::checker::Type::Error) {
        return None;
    }
    Some(QuickInfo {
        name: identifier_text(document, token)?,
        kind: QuickInfoKind::Property,
        type_display: render_type(model, *type_id),
        range: token.range(),
    })
}

/// Finds the property anchor at `position`. The anchor's bare range either
/// equals the token range (identifier keys) or sits strictly inside it
/// (string-literal keys whose interior is the bare span).
fn property_anchor_at(document: &DocumentSnapshot, position: Utf16Pos) -> Option<PropertyId> {
    let token = token_at(document, position)?;
    let model = document.semantic();
    let token_range = token.range();
    model
        .property_anchors()
        .iter()
        .find(|anchor| {
            anchor.range == token_range
                || (token_range.start() < anchor.range.start()
                    && anchor.range.end() < token_range.end())
        })
        .map(|anchor| anchor.property_id)
}

/// Resolves the property identity anchored at `position` to its declaration
/// location. Returns `None` when no anchor sits at the position or the
/// identity has no recorded declaration anchor.
fn property_definition_location(
    document: &DocumentSnapshot,
    position: Utf16Pos,
) -> Option<Location> {
    let property_id = property_anchor_at(document, position)?;
    let model = document.semantic();
    let anchor = model
        .property_anchors()
        .iter()
        .filter(|anchor| anchor.property_id == property_id)
        .find(|anchor| anchor.declaration)?;
    Some(Location {
        path: document.path().to_path_buf(),
        range: anchor.range,
        is_declaration: true,
    })
}

/// Collects every anchored occurrence of a property identity, ordered like
/// symbol reference locations, with declaration flags preserved for
/// `includeDeclaration` filtering.
fn property_reference_locations(
    document: &DocumentSnapshot,
    property_id: PropertyId,
) -> Vec<Location> {
    let model = document.semantic();
    let mut ranges = model
        .property_anchors()
        .iter()
        .filter(|anchor| anchor.property_id == property_id)
        .map(|anchor| (anchor.range, anchor.declaration))
        .collect::<Vec<_>>();
    ranges.sort_by_key(|(range, _)| (range.start(), range.end()));
    ranges.dedup();
    ranges
        .into_iter()
        .map(|(range, is_declaration)| Location {
            path: document.path().to_path_buf(),
            range,
            is_declaration,
        })
        .collect()
}

/// Builds the rename edit set for a property identity. Owner-local collision
/// checks, completeness guards, and shorthand expansion all resolve here.
fn rename_property(
    document: &DocumentSnapshot,
    property_id: PropertyId,
    new_name: &str,
) -> Result<RenameResult, ServiceError> {
    let model = document.semantic();
    let site = model
        .property_site(property_id)
        .ok_or(ServiceError::RenameUnavailable)?;
    let old_name = site.name.to_string();
    if model
        .property_sites()
        .iter()
        .any(|other| other.owner == site.owner && other.name.as_ref() == new_name)
    {
        return Err(ServiceError::InvalidRename(format!(
            "rename would conflict with existing property `{new_name}`"
        )));
    }
    let anchors: Vec<&PropertyAnchor> = model
        .property_anchors()
        .iter()
        .filter(|anchor| anchor.property_id == property_id)
        .collect();
    if !anchors.iter().any(|anchor| anchor.declaration) {
        return Err(ServiceError::RenameUnavailable);
    }
    let edits = anchors
        .iter()
        .map(|anchor| {
            let replacement = match anchor.kind {
                PropertyAnchorKind::Plain => new_name.to_owned(),
                PropertyAnchorKind::Shorthand => format!("{new_name}: {old_name}"),
            };
            DocumentEdit {
                path: document.path().to_path_buf(),
                range: anchor.range,
                replacement,
            }
        })
        .collect();
    Ok(RenameResult {
        symbol: old_name,
        edit: RenameEdit { edits },
    })
}

fn token_at(document: &DocumentSnapshot, position: Utf16Pos) -> Option<&Token> {
    let tokens = document.source().tokens();
    tokens
        .iter()
        .find(|token| {
            !token.is_missing()
                && token.range().start() < position
                && position < token.range().end()
        })
        .or_else(|| {
            tokens.iter().find(|token| {
                !token.is_missing()
                    && token.range().start() == position
                    && identifier_text(document, token).is_some()
            })
        })
        .or_else(|| {
            tokens.iter().find(|token| {
                !token.is_missing()
                    && token.range().end() == position
                    && identifier_text(document, token).is_some()
            })
        })
        .or_else(|| {
            tokens.iter().find(|token| {
                !token.is_missing()
                    && token.range().start() <= position
                    && position <= token.range().end()
            })
        })
}

fn identifier_text<'a>(document: &'a DocumentSnapshot, token: &'a Token) -> Option<String> {
    let text = document.source().identifier_text(token)?.into_owned();
    is_identifier(&text).then_some(text)
}

fn is_identifier(text: &str) -> bool {
    let mut characters = text.chars();
    let Some(first) = characters.next() else {
        return false;
    };
    (first == '_' || first == '$' || first.is_alphabetic())
        && characters
            .all(|character| character == '_' || character == '$' || character.is_alphanumeric())
}

fn is_rename_identifier(text: &str) -> bool {
    if text.is_empty() {
        return false;
    }
    let Ok(source) = SourceText::new(text) else {
        return false;
    };
    let scanned = scanner::scan(
        SourceId::new(u32::MAX),
        ScriptKind::TypeScript,
        Arc::new(source),
    );
    scanned.diagnostics().is_empty()
        && matches!(scanned.product().tokens(), [token] if token.kind() == TokenKind::Identifier)
}

const fn symbol_index(symbol: SymbolId) -> usize {
    symbol.get() as usize
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        time::{SystemTime, UNIX_EPOCH},
    };

    use super::*;
    use crate::service::{ServiceError, ServiceState, filesystem::OsFileSystem};

    fn state(source: &str) -> (PathBuf, ServiceState<OsFileSystem>) {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "bamts-language-service-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&root).expect("create root");
        let mut state = ServiceState::new(OsFileSystem::new(&root).expect("filesystem"));
        state.open("a.ts", source, 1).expect("open");
        (root, state)
    }

    #[test]
    fn completion_navigation_references_and_rename_share_checker_snapshot() {
        let (root, mut state) = state("const answer = 1;\nans\nanswer;\n");
        let completions = state
            .completions("a.ts", Utf16Pos::new(21))
            .expect("completions");
        assert_eq!(
            completions
                .iter()
                .map(|item| item.name.as_str())
                .collect::<Vec<_>>(),
            ["answer"]
        );

        let definition = state
            .definition("a.ts", Utf16Pos::new(28))
            .expect("definition")
            .expect("symbol");
        assert_eq!(definition.range.start(), Utf16Pos::new(6));
        let references = state
            .references("a.ts", Utf16Pos::new(28))
            .expect("references");
        assert_eq!(references.len(), 2);
        let rename = state
            .rename("a.ts", Utf16Pos::new(28), "result")
            .expect("rename");
        assert_eq!(rename.edit.edits.len(), 2);
        assert!(
            rename
                .edit
                .edits
                .iter()
                .all(|edit| edit.replacement == "result")
        );
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn rename_ignores_unrelated_nested_shadowing_declarations() {
        let (root, mut state) =
            state("const outer = 1; { const replacement = 2; replacement; } outer;");
        let rename = state
            .rename("a.ts", Utf16Pos::new(58), "replacement")
            .expect("nested declaration is outside the target scope");
        assert_eq!(rename.edit.edits.len(), 2);
        assert!(
            rename
                .edit
                .edits
                .iter()
                .all(|edit| edit.replacement == "replacement")
        );
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn diagnostics_and_failure_paths_are_public_data() {
        let (root, mut state) = state("const value: number = 'wrong';");
        assert!(
            state
                .diagnostics("a.ts")
                .expect("diagnostics")
                .iter()
                .any(|item| item.code == "BAMTS-C004")
        );
        assert!(matches!(
            state.definition("a.ts", Utf16Pos::new(10_000)),
            Err(ServiceError::InvalidPosition { .. })
        ));
        assert!(matches!(
            state.rename("a.ts", Utf16Pos::new(6), "not-valid!"),
            Err(ServiceError::InvalidRename(_))
        ));
        fs::remove_dir_all(root).expect("remove root");
    }
    #[test]
    fn quick_info_renders_primitives_functions_and_unions() {
        let (root, mut state) = state(
            "const value: number = 1;\nfunction greet(name: string): string { return name; }\nconst choice: number | string = value;\n",
        );
        let value = state
            .quick_info("a.ts", Utf16Pos::new(6))
            .expect("quick info")
            .expect("value");
        assert_eq!(value.type_display, "number");
        assert_eq!(value.display(), "const value: number");
        let function = state
            .quick_info("a.ts", Utf16Pos::new(34))
            .expect("quick info")
            .expect("function");
        assert_eq!(function.type_display, "(name: string) => string");
        assert_eq!(
            function.display(),
            "function greet: (name: string) => string"
        );
        let union = state
            .quick_info("a.ts", Utf16Pos::new(85))
            .expect("quick info")
            .expect("union");
        assert_eq!(union.type_display, "number | string");
        std::fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn quick_info_uses_reference_token_range_and_returns_none_for_whitespace() {
        let (root, mut state) = state("const answer: number = 1;\nanswer;\n");
        let info = state
            .quick_info("a.ts", Utf16Pos::new(30))
            .expect("quick info")
            .expect("reference");
        assert_eq!(info.range.start(), Utf16Pos::new(26));
        assert_eq!(info.range.end(), Utf16Pos::new(32));
        assert!(
            state
                .quick_info("a.ts", Utf16Pos::new(25))
                .expect("whitespace")
                .is_none()
        );
        std::fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn semantic_ranges_distinguish_shadowed_symbols() {
        let (root, mut state) =
            state("const value: number = 1;\n{ const value: string = \"x\"; value; }\nvalue;\n");
        let inner = state
            .quick_info("a.ts", Utf16Pos::new(54))
            .expect("quick info")
            .expect("inner reference");
        let outer = state
            .quick_info("a.ts", Utf16Pos::new(63))
            .expect("quick info")
            .expect("outer reference");
        assert_eq!(inner.type_display, "string");
        assert_eq!(outer.type_display, "number");
        assert_eq!(
            state
                .references("a.ts", Utf16Pos::new(54))
                .expect("inner references")
                .into_iter()
                .map(|location| location.range.start())
                .collect::<Vec<_>>(),
            [Utf16Pos::new(33), Utf16Pos::new(54)]
        );
        assert_eq!(
            state
                .references("a.ts", Utf16Pos::new(63))
                .expect("outer references")
                .into_iter()
                .map(|location| location.range.start())
                .collect::<Vec<_>>(),
            [Utf16Pos::new(6), Utf16Pos::new(63)]
        );
        std::fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn quick_info_reports_member_property_type() {
        let (root, mut state) =
            state("const value: number = 1;\nconst object = { value: \"x\" };\nobject.value;\n");
        let property = state
            .quick_info("a.ts", Utf16Pos::new(63))
            .expect("quick info")
            .expect("property reference");
        assert_eq!(property.kind, QuickInfoKind::Property);
        assert_eq!(property.type_display, "string");
        assert_eq!(property.display(), "property value: string");
        std::fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn quick_info_honors_utf16_positions_and_cancellation() {
        let (root, mut state) = state("const value: number = 1;\n😀; value;\n");
        let info = state
            .quick_info("a.ts", Utf16Pos::new(29))
            .expect("quick info")
            .expect("reference");
        assert_eq!(info.name, "value");
        let cancellation = bamts_cancel::CancellationToken::new();
        cancellation.cancel();
        assert!(matches!(
            state.quick_info_with_cancel("a.ts", Utf16Pos::new(29), &cancellation),
            Err(ServiceError::Cancelled)
        ));
        std::fs::remove_dir_all(root).expect("remove root");
    }

    fn cursor(source: &str, needle: &str, offset: usize) -> Utf16Pos {
        let position = source.find(needle).expect("fixture contains cursor needle") + offset;
        Utf16Pos::new(position)
    }

    fn edited_text<'a>(source: &'a str, edit: &DocumentEdit) -> &'a str {
        let start = edit.range.start().get();
        let end = edit.range.end().get();
        source.get(start..end).expect("ASCII fixture edit range")
    }

    #[test]
    fn rename_property_covers_anchor_forms_and_preserves_shorthand_binding() {
        let source =
            "const value = 1; const a = { \"other\": 2, value }; a.other; a[\"other\"]; a?.other;";
        let (root, mut state) = state(source);
        let rename = state
            .rename("a.ts", cursor(source, "a.other", 2), "result")
            .expect("static property rename");
        assert_eq!(rename.edit.edits.len(), 4);
        assert!(
            rename
                .edit
                .edits
                .iter()
                .all(|edit| edited_text(source, edit) == "other")
        );

        let shorthand = state
            .rename("a.ts", cursor(source, "value };", 0), "result")
            .expect("shorthand property rename");
        assert_eq!(shorthand.edit.edits.len(), 1);
        assert_eq!(shorthand.edit.edits[0].replacement, "result: value");
        assert_eq!(edited_text(source, &shorthand.edit.edits[0]), "value");
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn rename_property_keeps_unrelated_structurally_equal_owners_separate() {
        let source = "const a = { value: 1 }; const b = { value: 2 }; a.value; b.value;";
        let (root, mut state) = state(source);
        let rename = state
            .rename("a.ts", cursor(source, "a.value", 2), "result")
            .expect("owner-local property rename");
        assert_eq!(rename.edit.edits.len(), 2);
        let mut starts: Vec<usize> = rename
            .edit
            .edits
            .iter()
            .map(|edit| edit.range.start().get())
            .collect();
        starts.sort_unstable();
        assert_eq!(
            starts,
            [
                source.find("value: 1").expect("a declaration"),
                source.find("a.value").expect("a access") + 2,
            ]
        );
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn rename_property_includes_bracket_access_on_annotated_receiver() {
        let source = "interface I { value: string } const a: I = { value: \"x\" }; a[\"value\"];";
        let (root, mut state) = state(source);
        let rename = state
            .rename("a.ts", cursor(source, "a[\"value\"]", 4), "result")
            .expect("bracket property rename");
        assert_eq!(rename.edit.edits.len(), 3, "{rename:?}");
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn rename_property_includes_bracket_access_in_function_body() {
        let source = "interface I { value: string } function f(o: I) { o[\"value\"]; }";
        let (root, mut state) = state(source);
        let from_interface = state
            .rename("a.ts", cursor(source, "{ value", 2), "result")
            .expect("interface trigger");
        assert_eq!(from_interface.edit.edits.len(), 2, "{from_interface:?}");
        let from_bracket = state.rename("a.ts", cursor(source, "o[\"value\"]", 4), "result");
        assert!(
            matches!(&from_bracket, Ok(result) if result.edit.edits.len() == 2),
            "{from_bracket:?}"
        );
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn rename_property_anchors_module_receiver_bracket_inside_function_body() {
        let source = "interface I { value: string } const a: I = { value: \"x\" }; function g() { a[\"value\"]; }";
        let (root, mut state) = state(source);
        let rename = state
            .rename("a.ts", cursor(source, "a[\"value\"]", 3), "result")
            .expect("module receiver bracket rename");
        assert_eq!(rename.edit.edits.len(), 3);
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn rename_property_tracks_named_contextual_parameter_and_alias_owners() {
        let source = "interface I { value: string } const a: I = { value: \"x\" }; const b = a; function f(o: I) { o[\"value\"]; } b.value;";
        let (root, mut state) = state(source);
        let rename = state
            .rename("a.ts", cursor(source, "b.value", 2), "result")
            .expect("named contextual property rename");
        assert_eq!(rename.edit.edits.len(), 4);
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn rename_property_fails_closed_for_dynamic_and_escaped_keys() {
        let dynamic = "declare const k: string; const a = { value: 1 }; a[k];";
        let (dynamic_root, mut dynamic_state) = state(dynamic);
        let rename = dynamic_state
            .rename("a.ts", cursor(dynamic, "value", 0), "result")
            .expect("declared static key remains renameable");
        assert_eq!(rename.edit.edits.len(), 1);
        fs::remove_dir_all(dynamic_root).expect("remove dynamic root");

        let escaped = r"const a = { 'va\u006cue': 1 };";
        let (escaped_root, mut escaped_state) = state(escaped);
        assert!(matches!(
            escaped_state.rename("a.ts", cursor(escaped, r"va\u006cue", 1), "result"),
            Err(ServiceError::RenameUnavailable)
        ));
        fs::remove_dir_all(escaped_root).expect("remove escaped root");
    }

    #[test]
    fn rename_property_rejects_owner_collision_but_not_foreign_owner_name() {
        let collision = "const a = { value: 1, result: 2 }; a.value;";
        let (collision_root, mut collision_state) = state(collision);
        assert!(matches!(
            collision_state.rename("a.ts", cursor(collision, "a.value", 2), "result"),
            Err(ServiceError::InvalidRename(_))
        ));
        fs::remove_dir_all(collision_root).expect("remove collision root");

        let separate = "const a = { value: 1 }; const b = { result: 2 }; a.value;";
        let (separate_root, mut separate_state) = state(separate);
        assert!(
            separate_state
                .rename("a.ts", cursor(separate, "a.value", 2), "result")
                .is_ok()
        );
        fs::remove_dir_all(separate_root).expect("remove separate root");
    }

    #[test]
    fn rename_filters_composite_symbol_ranges_and_refuses_incomplete_properties() {
        let class = "class C { n = 1; m() { return this.n; } } const c = new C(); c.n;";
        let (class_root, mut class_state) = state(class);
        let rename = class_state
            .rename("a.ts", cursor(class, "n = 1", 0), "result")
            .expect("class property rename");
        assert!(rename.edit.edits.len() >= 3);
        assert!(
            rename
                .edit
                .edits
                .iter()
                .all(|edit| edited_text(class, edit) == "n")
        );
        fs::remove_dir_all(class_root).expect("remove class root");

        let spread = "const a = { value: 1 }; const c = { ...a }; c.value;";
        let (spread_root, mut spread_state) = state(spread);
        assert!(matches!(
            spread_state.rename("a.ts", cursor(spread, "c.value", 2), "result"),
            Err(ServiceError::RenameUnavailable)
        ));
        fs::remove_dir_all(spread_root).expect("remove spread root");
    }

    #[test]
    fn property_navigation_resolves_definition_and_exact_reference_ranges() {
        let source = "const a = { value: \"x\" };\na.value;\n";
        let (root, mut state) = state(source);
        let declaration = source.find("value: \"x\"").expect("declaration key");
        let use_position = cursor(source, "a.value", 2);
        let from_use = state
            .definition("a.ts", use_position)
            .expect("property definition from use")
            .expect("declaration location");
        assert_eq!(from_use.range.start(), Utf16Pos::new(declaration));
        assert_eq!(
            from_use.range.end(),
            Utf16Pos::new(declaration + "value".len())
        );
        assert!(from_use.is_declaration);
        let from_declaration = state
            .definition("a.ts", cursor(source, "value: \"x\"", 0))
            .expect("property definition from declaration")
            .expect("declaration location");
        assert_eq!(from_declaration.range, from_use.range);
        let references = state
            .references("a.ts", use_position)
            .expect("property references");
        assert_eq!(
            references
                .iter()
                .map(|location| (
                    location.range.start(),
                    location.range.end(),
                    location.is_declaration
                ))
                .collect::<Vec<_>>(),
            [
                (
                    Utf16Pos::new(declaration),
                    Utf16Pos::new(declaration + "value".len()),
                    true
                ),
                (
                    Utf16Pos::new(use_position.get()),
                    Utf16Pos::new(use_position.get() + "value".len()),
                    false
                ),
            ]
        );
        assert!(matches!(
            state.references("a.ts", Utf16Pos::new(10_000)),
            Err(ServiceError::InvalidPosition { .. })
        ));
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn property_navigation_keeps_same_spelled_properties_distinct() {
        let source = "const a = { value: 1 };\nconst b = { value: 2 };\na.value;\nb.value;\n";
        let (root, mut state) = state(source);
        let a_declaration = source.find("value: 1").expect("a declaration key");
        let b_declaration = source.find("value: 2").expect("b declaration key");
        let a_access = source.find("a.value").expect("a access");
        let definition = state
            .definition("a.ts", cursor(source, "b.value", 2))
            .expect("property definition")
            .expect("declaration location");
        assert_eq!(definition.range.start(), Utf16Pos::new(b_declaration));
        assert_eq!(
            definition.range.end(),
            Utf16Pos::new(b_declaration + "value".len())
        );
        let references = state
            .references("a.ts", cursor(source, "a.value", 2))
            .expect("property references");
        assert_eq!(
            references
                .iter()
                .map(|location| (
                    location.range.start(),
                    location.range.end(),
                    location.is_declaration
                ))
                .collect::<Vec<_>>(),
            [
                (
                    Utf16Pos::new(a_declaration),
                    Utf16Pos::new(a_declaration + "value".len()),
                    true
                ),
                (
                    Utf16Pos::new(a_access + 2),
                    Utf16Pos::new(a_access + "a.value".len()),
                    false
                ),
            ]
        );
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn property_navigation_covers_string_key_bracket_access() {
        let source = "const a = { \"value\": \"x\" };\na[\"value\"];\n";
        let (root, mut state) = state(source);
        let declaration = source.find("\"value\"").expect("string key") + 1;
        let access = source.find("a[\"value\"]").expect("bracket access");
        let definition = state
            .definition("a.ts", cursor(source, "a[\"value\"]", 4))
            .expect("bracket property definition")
            .expect("declaration location");
        assert_eq!(definition.range.start(), Utf16Pos::new(declaration));
        assert_eq!(
            definition.range.end(),
            Utf16Pos::new(declaration + "value".len())
        );
        assert!(definition.is_declaration);
        let references = state
            .references("a.ts", cursor(source, "a[\"value\"]", 4))
            .expect("bracket property references");
        assert_eq!(
            references
                .iter()
                .map(|location| (
                    location.range.start(),
                    location.range.end(),
                    location.is_declaration
                ))
                .collect::<Vec<_>>(),
            [
                (
                    Utf16Pos::new(declaration),
                    Utf16Pos::new(declaration + "value".len()),
                    true
                ),
                (
                    Utf16Pos::new(access + 3),
                    Utf16Pos::new(access + 3 + "value".len()),
                    false
                ),
            ]
        );
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn property_navigation_exposes_declaration_filter_flag() {
        let source = "const a = { value: \"x\" };\na.value;\na?.value;\n";
        let (root, mut state) = state(source);
        let references = state
            .references("a.ts", cursor(source, "a.value", 2))
            .expect("property references");
        let uses = references
            .iter()
            .filter(|location| !location.is_declaration)
            .map(|location| location.range.start())
            .collect::<Vec<_>>();
        assert_eq!(
            uses,
            [
                Utf16Pos::new(source.find("a.value").expect("dot access") + 2),
                Utf16Pos::new(source.find("a?.value").expect("optional access") + 3),
            ]
        );
        let declarations = references
            .iter()
            .filter(|location| location.is_declaration)
            .map(|location| location.range.start())
            .collect::<Vec<_>>();
        assert_eq!(
            declarations,
            [Utf16Pos::new(
                source.find("value: \"x\"").expect("declaration key")
            )]
        );
        fs::remove_dir_all(root).expect("remove root");
    }
}
