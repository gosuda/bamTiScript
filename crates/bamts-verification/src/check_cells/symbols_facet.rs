use super::*;

/// Emit the `.symbols` baseline for a compiled case in the upstream framing:
/// a `//// [path] ////` marker, then one `=== <unit> ===` section per reached
/// unit whose source is echoed with `>name : Symbol(qname, Decl(unit, l, c))`
/// records under each line where a bound name is declared or referenced.
///
/// Coverage is bounded by what the binder tracks: declaration-name symbols and
/// resolved value/type references reproduce upstream records. Enum members
/// qualify against their enum at both declaration and initializer-reference
/// sites (`E.A`); class and interface member qualification lights up once
/// member binding lands (the scope-owner substrate is in place). Namespace
/// exports render bare at declarations per upstream, with access-path
/// qualification (`A.x`) pending member-access reference resolution. Class
/// members not yet bound as symbols and references to intrinsic/library symbols
/// (whose declaration lives outside the unit) remain known gaps — the S2
/// burn-down surface, exactly like the `.types` emitter.
#[must_use]
pub fn emit_symbols_baseline(case: &CheckedCase, logical_path: &str) -> String {
    let mut out = format!("//// [{logical_path}] ////\n\n");
    let units = case.units_in_document_order();
    let mut declaration_anchors: HashMap<(String, SymbolKind), Vec<SymbolDeclAnchor>> =
        HashMap::new();
    for (unit, output) in &units {
        let section = unit_basename(&unit.virtual_path);
        let source_file = output.source_file();
        let model = output.semantic_model();
        // Occurrence-covered interface members contribute every written
        // declaration's anchor — each derived from the occurrence's
        // `declaration_range` (modifiers included) — so foreign units union
        // in every fragment. A singleton canonical anchor would lose
        // duplicate fragments and mis-anchor modifier-led members such as
        // `readonly p`.
        let occurrence_anchors = occurrence_decl_anchors(
            source_file.tokens(),
            source_file.source_text(),
            &section,
            model.declaration_occurrences(),
        );
        for (symbol_index, symbol) in model.symbols().iter().enumerate() {
            let symbol_id = SymbolId::new(symbol_index as u32);
            // Overlay membership: mergeable kinds keep the legacy singleton
            // `symbol_decl_position` anchor; occurrence-covered Function
            // method members and Variable(Let) property members join with
            // every occurrence anchor. `kind_is_mergeable` is unchanged, so
            // arbitrary `let`/`const` locals stay out of the overlay.
            let anchors: Vec<SymbolDeclAnchor> = if let Some(covered) =
                occurrence_anchors.get(&symbol_id)
            {
                if !kind_is_occurrence_overlay_member(symbol.kind()) {
                    continue;
                }
                covered.clone()
            } else {
                // Only mergeable kinds participate in the cross-unit
                // overlay; non-mergeable kinds (type parameters,
                // `let`/`const` locals, parameters, …) use their own
                // per-unit anchor via the `local_decl_positions` fallback
                // in `emit_unit_symbols`.
                if !kind_is_mergeable(symbol.kind()) {
                    continue;
                }
                let Some((line, character)) =
                    symbol_decl_position(source_file.tokens(), source_file.source_text(), symbol)
                else {
                    continue;
                };
                vec![SymbolDeclAnchor {
                    section: section.clone(),
                    line,
                    character,
                }]
            };
            for name in [symbol.name().to_owned(), model.qualified_name(symbol_id)] {
                let entries = declaration_anchors
                    .entry((name, symbol.kind()))
                    .or_default();
                for anchor in &anchors {
                    if !entries.contains(anchor) {
                        entries.push(anchor.clone());
                    }
                }
            }
        }
    }
    for anchors in declaration_anchors.values_mut() {
        anchors.sort();
    }
    let target = case.options().target();
    let libs = case.options().lib();
    for (unit, output) in units {
        let section = unit_basename(&unit.virtual_path);
        emit_unit_symbols(
            output,
            &unit.display_name,
            &section,
            &declaration_anchors,
            target,
            libs,
            &mut out,
        );
    }
    out
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct SymbolDeclAnchor {
    section: String,
    line: usize,
    character: usize,
}

/// One `>name : Symbol(...)` record anchored to a source line.
struct SymbolRecord {
    start: usize,
    end: usize,
    line: usize,
    display: String,
    rendered: String,
}

fn emit_unit_symbols(
    output: &FrontendOutput,
    heading: &str,
    section: &str,
    declaration_anchors: &HashMap<(String, SymbolKind), Vec<SymbolDeclAnchor>>,
    target: Option<&str>,
    libs: &[Arc<str>],
    out: &mut String,
) {
    let model = output.semantic_model();
    let source_file = output.source_file();
    let source = source_file.source_text();
    let tokens = source_file.tokens();
    let local_decl_positions: Vec<Option<(usize, usize)>> = model
        .symbols()
        .iter()
        .map(|symbol| symbol_decl_position(tokens, source, symbol))
        .collect();
    // Interface member declaration occurrences: each covered symbol's own
    // declaration row is replaced by one row per written occurrence, and its
    // Decl list unions this unit's per-occurrence anchors with the
    // cross-unit overlay.
    let occurrence_covered: HashSet<SymbolId> = model
        .declaration_occurrences()
        .iter()
        .map(|occurrence| occurrence.symbol)
        .collect();
    let occurrence_anchors =
        occurrence_decl_anchors(tokens, source, section, model.declaration_occurrences());
    let render = |symbol_id: SymbolId,
                  anchor_override: Option<SymbolDeclAnchor>,
                  name_override: Option<&str>|
     -> Option<String> {
        let index = symbol_id.get() as usize;
        let symbol = model.symbols().get(index)?;
        let name = name_override
            .map(str::to_owned)
            .unwrap_or_else(|| model.qualified_name(symbol_id));
        if matches!(
            symbol.kind(),
            SymbolKind::IntrinsicValue | SymbolKind::IntrinsicType
        ) {
            if name == "undefined" || name == "globalThis" {
                return Some(format!("Symbol({name})"));
            }
            let files = lib_decl_files_for_global(&name, target, libs);
            if !files.is_empty() {
                let declarations = files
                    .iter()
                    .map(|file| format!("Decl({file}, --, --)"))
                    .collect::<Vec<_>>()
                    .join(", ");
                return Some(format!("Symbol({name}, {declarations})"));
            }
        }
        let anchors = if let Some(anchor) = anchor_override {
            vec![anchor]
        } else if let Some(occurrence) = occurrence_anchors.get(&symbol_id) {
            // Occurrence-covered interface member: the Decl list unions this
            // unit's per-occurrence anchors with the (qualified-name-first)
            // cross-unit overlay, so foreign-unit declarations survive for
            // both Function method members and Variable(Let) property
            // members. The union is narrow — only occurrence-covered members
            // of those kinds read the overlay.
            let mut union = occurrence.clone();
            if kind_is_occurrence_overlay_member(symbol.kind())
                && let Some(overlay) = declaration_anchors
                    .get(&(name.clone(), symbol.kind()))
                    .or_else(|| declaration_anchors.get(&(symbol.name().to_owned(), symbol.kind())))
            {
                union.extend(overlay.iter().cloned());
            }
            union.sort();
            union.dedup();
            union
        } else if kind_is_mergeable(symbol.kind()) {
            declaration_anchors
                .get(&(name.clone(), symbol.kind()))
                .or_else(|| declaration_anchors.get(&(symbol.name().to_owned(), symbol.kind())))
                .cloned()
                .or_else(|| {
                    local_decl_positions
                        .get(index)
                        .copied()
                        .flatten()
                        .map(|(line, character)| {
                            vec![SymbolDeclAnchor {
                                section: section.to_owned(),
                                line,
                                character,
                            }]
                        })
                })?
        } else {
            // Non-mergeable kinds use their own per-unit anchor only,
            // preventing same-named distinct symbols (e.g. type parameters
            // `T` in different scopes) from collapsing into one Decl list.
            local_decl_positions
                .get(index)
                .copied()
                .flatten()
                .map(|(line, character)| {
                    vec![SymbolDeclAnchor {
                        section: section.to_owned(),
                        line,
                        character,
                    }]
                })?
        };
        let declarations = anchors
            .iter()
            .map(|anchor| {
                format!(
                    "Decl({}, {}, {})",
                    anchor.section, anchor.line, anchor.character
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        Some(format!("Symbol({name}, {declarations})"))
    };

    let mut records: Vec<SymbolRecord> = Vec::new();
    // Declaration-name records: each source-declared symbol at its
    // identifier. Symbols covered by interface-member declaration
    // occurrences are skipped — each occurrence emits its own row at its
    // `name_range` below, replacing the covered symbol's single row.
    for (index, symbol) in model.symbols().iter().enumerate() {
        if symbol.range().is_empty() {
            continue;
        }
        let symbol_id = SymbolId::new(index as u32);
        if occurrence_covered.contains(&symbol_id) {
            continue;
        }
        if let Some(rendered) = render(symbol_id, None, None)
            && let Some(record) = symbol_record_for(
                source,
                symbol.range(),
                symbol
                    .display_name()
                    .unwrap_or_else(|| symbol.name())
                    .to_owned(),
                rendered,
            )
        {
            records.push(record);
        }
    }
    // Interface member declaration occurrences: one row per written
    // occurrence at its own `name_range` — the identifier span, quotes
    // included for string keys, digits for numeric keys, and the
    // bracket-delimited `[expr]` span for computed keys — rendered with the
    // unioned Decl list.
    for occurrence in model.declaration_occurrences() {
        if occurrence.name_range.is_empty() {
            continue;
        }
        if let Some(rendered) = render(occurrence.symbol, None, None) {
            let display = collapse_whitespace(&slice_source(source, occurrence.name_range));
            if let Some(record) =
                symbol_record_for(source, occurrence.name_range, display, rendered)
            {
                records.push(record);
            }
        }
    }
    // Reference records: each resolved value/type occurrence at its use site.
    let shorthand = model.shorthand_property_ranges();
    for (range, symbol_id) in model.symbol_references() {
        let anchor_override = shorthand_anchor(tokens, source, section, *range, &shorthand);
        let name_override = model.reference_qualified_name(*symbol_id);
        if let Some(rendered) = render(*symbol_id, anchor_override, name_override) {
            let display = collapse_whitespace(&slice_source(source, *range));
            if let Some(record) = symbol_record_for(source, *range, display, rendered) {
                records.push(record);
            }
        }
    }
    // Deduplicate records by (start, end, display, rendered): the binder can
    // record the same (range, symbol) pair multiple times in
    // `symbol_references`, producing identical `>name : Symbol(...)` lines.
    // Upstream emits each unique (position, name, symbol) pair once, so
    // duplicates must be collapsed before the pairwise line comparison.
    // Sort by the full identity key, dedup consecutive, then re-sort upstream.
    records.sort_by(|a, b| {
        a.start
            .cmp(&b.start)
            .then(a.end.cmp(&b.end))
            .then(a.display.cmp(&b.display))
            .then(a.rendered.cmp(&b.rendered))
    });
    records.dedup_by(|a, b| {
        a.start == b.start && a.end == b.end && a.display == b.display && a.rendered == b.rendered
    });
    // Upstream order: by start position, outer node before inner on ties.
    records.sort_by(|left, right| left.start.cmp(&right.start).then(right.end.cmp(&left.end)));
    let mut by_line: BTreeMap<usize, Vec<&SymbolRecord>> = BTreeMap::new();
    for record in &records {
        by_line.entry(record.line).or_default().push(record);
    }

    out.push_str(&format!("=== {heading} ===\n"));
    for (line_index, raw_line) in source.as_str().split('\n').enumerate() {
        let line = raw_line.strip_suffix('\r').unwrap_or(raw_line);
        out.push_str(&strip_library_root(line));
        out.push('\n');
        let Some(line_records) = by_line.get(&line_index) else {
            continue;
        };
        for record in line_records {
            out.push_str(&format!(">{} : {}\n", record.display, record.rendered));
        }
    }
}

/// Build a symbol record, resolving the occurrence's start line.
fn symbol_record_for(
    source: &SourceText,
    range: TextRange,
    display: String,
    rendered: String,
) -> Option<SymbolRecord> {
    let (line, _) = source.line_column(range.start()).ok()?;
    Some(SymbolRecord {
        start: range.start().get(),
        end: range.end().get(),
        line,
        display,
        rendered,
    })
}

/// The 0-based `(line, character)` a symbol renders in its `Decl(...)` marker:
/// the declaration node's full start, i.e. the end of the significant token
/// immediately preceding the declaration (TypeScript's `node.pos`, which
/// counts leading trivia). The identifier token is located in the unit's
/// token stream; for keyword-led declarations (class/function/interface/type/
/// enum/namespace) the scan steps left over the leading keyword and modifiers
/// so the marker anchors at the declaration keyword, not the name.
/// For import aliases the scan steps left over `as` and the imported name,
/// so the marker anchors at the specifier's full start, not the local name.
/// Identifier and dot steps that meet no decorator are rolled back, so dotted
/// members anchor at the last segment instead of the path head.
/// Binding renames step left over the colon and its key, so `{ x: a }`
/// anchors at the element start instead of the value name.
fn symbol_decl_position(
    tokens: &[Token],
    source: &SourceText,
    symbol: &bamts_compiler::checker::Symbol,
) -> Option<(usize, usize)> {
    if symbol.range().is_empty() {
        return None;
    }
    let id_start = symbol.range().start();
    let ident_index = tokens.iter().position(|token| {
        !token.is_missing() && !is_trivia_token(token.kind()) && token.range().start() == id_start
    })?;
    // Step the declaration's first token left over its leading keyword and
    // modifiers (skipping the trivia the parser retains between tokens), so a
    // keyword-led declaration anchors at its keyword rather than its name.
    let mut node_index = ident_index;
    if kind_is_keyword_led(symbol.kind()) {
        while let Some(prev) = prev_significant_token(tokens, node_index) {
            if is_declaration_leading(tokens[prev].kind()) {
                node_index = prev;
            } else {
                break;
            }
        }
    }
    if matches!(
        symbol.kind(),
        SymbolKind::Parameter | SymbolKind::Variable(_)
    ) {
        while let Some(prev) = prev_significant_token(tokens, node_index) {
            if !is_member_modifier(tokens[prev].kind()) {
                break;
            }
            node_index = prev;
        }
        node_index = binding_element_start(tokens, node_index);
    }
    if symbol.kind() == SymbolKind::Import {
        node_index = import_specifier_start(tokens, node_index);
    }
    if symbol.kind() == SymbolKind::Import {
        node_index = import_specifier_start(tokens, node_index);
    }
    if symbol.kind() == SymbolKind::Import {
        node_index = import_specifier_start(tokens, node_index);
    }
    // Decorator walk: scan left over accessor keywords and decorator
    // expression tokens so a decorated member anchors at the decorator's
    // `@` token, not the declaration name. Runs for all symbol kinds
    // since decorators can appear on non-keyword-led members (e.g.
    // `@dec get accessor()` where `accessor` binds as `Variable(Let)`).
    let mut found_at = false;
    let mut undecorated_start: Option<usize> = None;
    while let Some(prev) = prev_significant_token(tokens, node_index) {
        match tokens[prev].kind() {
            TokenKind::At => {
                found_at = true;
                node_index = prev;
            }
            TokenKind::Identifier | TokenKind::Dot => {
                if found_at {
                    // After finding `@`, only step over an identifier that
                    // is itself preceded by `@` (stacked decorators like
                    // `@first @second`). Otherwise stop — the identifier is
                    // an unrelated preceding token, not a decorator name.
                    if let Some(prev2) = prev_significant_token(tokens, prev)
                        && tokens[prev2].kind() == TokenKind::At
                    {
                        node_index = prev2;
                        continue;
                    }
                    break;
                }
                if undecorated_start.is_none() {
                    undecorated_start = Some(node_index);
                }
                node_index = prev;
            }
            TokenKind::RParen => {
                // Skip balanced `(args)` for `@decorator(args)`.
                let mut depth = 1;
                let mut scan = prev;
                while scan > 0 {
                    scan -= 1;
                    let token = &tokens[scan];
                    if token.is_missing() || is_trivia_token(token.kind()) {
                        continue;
                    }
                    match token.kind() {
                        TokenKind::RParen => depth += 1,
                        TokenKind::LParen => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => {}
                    }
                }
                if depth == 0 {
                    node_index = scan;
                } else {
                    break;
                }
            }
            TokenKind::KwGet | TokenKind::KwSet | TokenKind::KwAccessor => {
                node_index = prev;
            }
            _ => break,
        }
    }
    if !found_at && let Some(start) = undecorated_start {
        node_index = start;
    }
    // The declaration's full start is the end of the significant token that
    // precedes it (TypeScript's `node.pos`, which counts leading trivia).
    let full_start = match prev_significant_token(tokens, node_index) {
        Some(prev) => tokens[prev].range().end(),
        None => Utf16Pos::ZERO,
    };
    source.line_column(full_start).ok()
}

fn import_specifier_start(tokens: &[Token], name_index: usize) -> usize {
    let Some(as_index) = prev_significant_token(tokens, name_index) else {
        return name_index;
    };
    if tokens[as_index].kind() != TokenKind::KwAs {
        return name_index;
    }
    prev_significant_token(tokens, as_index).unwrap_or(name_index)
}

/// The element a renamed binding element starts at: stepping left over the
/// colon and its key lands on the element's first token, so `{ x: a }`
/// anchors at `{` and computed `{ [k]: v }` anchors after balancing to `[`.
fn binding_element_start(tokens: &[Token], name_index: usize) -> usize {
    let Some(colon) = prev_significant_token(tokens, name_index) else {
        return name_index;
    };
    if tokens[colon].kind() != TokenKind::Colon {
        return name_index;
    }
    let Some(key) = prev_significant_token(tokens, colon) else {
        return name_index;
    };
    if tokens[key].kind() != TokenKind::RBracket {
        return key;
    }
    let mut depth = 1;
    let mut scan = key;
    while scan > 0 {
        scan -= 1;
        let token = &tokens[scan];
        if token.is_missing() || is_trivia_token(token.kind()) {
            continue;
        }
        match token.kind() {
            TokenKind::RBracket => depth += 1,
            TokenKind::LBracket => {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            _ => {}
        }
    }
    if depth == 0 { scan } else { name_index }
}

/// The shorthand anchor for a reference use site: when the range is a
/// recorded object-literal shorthand, the row anchors at the shorthand's
/// full start instead of the outer binding's declaration.
fn shorthand_anchor(
    tokens: &[Token],
    source: &SourceText,
    section: &str,
    range: TextRange,
    shorthand: &[TextRange],
) -> Option<SymbolDeclAnchor> {
    if !shorthand.contains(&range) {
        return None;
    }
    let index = tokens.iter().position(|token| {
        !token.is_missing()
            && !is_trivia_token(token.kind())
            && token.range().start() == range.start()
    })?;
    let full_start = match prev_significant_token(tokens, index) {
        Some(prev) => tokens[prev].range().end(),
        None => Utf16Pos::ZERO,
    };
    let (line, character) = source.line_column(full_start).ok()?;
    Some(SymbolDeclAnchor {
        section: section.to_owned(),
        line,
        character,
    })
}

/// Per-unit `Decl` anchors for interface member declaration occurrences,
/// keyed by the canonical member `SymbolId`: every written occurrence
/// contributes its own `declaration_range`-derived anchor, so duplicate and
/// merged fragments each keep a distinct anchor.
fn occurrence_decl_anchors(
    tokens: &[Token],
    source: &SourceText,
    section: &str,
    occurrences: &[DeclarationOccurrence],
) -> HashMap<SymbolId, Vec<SymbolDeclAnchor>> {
    let mut anchors: HashMap<SymbolId, Vec<SymbolDeclAnchor>> = HashMap::new();
    for occurrence in occurrences {
        let Some((line, character)) =
            occurrence_decl_position(tokens, source, occurrence.declaration_range)
        else {
            continue;
        };
        anchors
            .entry(occurrence.symbol)
            .or_default()
            .push(SymbolDeclAnchor {
                section: section.to_owned(),
                line,
                character,
            });
    }
    anchors
}

/// The 0-based `(line, character)` a declaration occurrence anchors its
/// `Decl(...)` marker at: the end of the significant token immediately
/// preceding the member's first token (TypeScript's `node.pos`, which counts
/// leading trivia). `declaration_range` already starts at the member's first
/// modifier or name token, so no keyword-led or decorator walk is needed —
/// this routes around `kind_is_keyword_led`, which never fires for
/// `Variable(Let)` members, so `readonly p` anchors before `readonly`.
fn occurrence_decl_position(
    tokens: &[Token],
    source: &SourceText,
    declaration_range: TextRange,
) -> Option<(usize, usize)> {
    if declaration_range.is_empty() {
        return None;
    }
    let first = tokens.iter().position(|token| {
        !token.is_missing()
            && !is_trivia_token(token.kind())
            && token.range().start() >= declaration_range.start()
    })?;
    let full_start = match prev_significant_token(tokens, first) {
        Some(prev) => tokens[prev].range().end(),
        None => Utf16Pos::ZERO,
    };
    source.line_column(full_start).ok()
}

/// The index of the significant (non-trivia, non-missing) token before `index`.
fn prev_significant_token(tokens: &[Token], index: usize) -> Option<usize> {
    tokens[..index]
        .iter()
        .rposition(|token| !token.is_missing() && !is_trivia_token(token.kind()))
}

/// Whether a token is trivia the parser retains in the token stream.
const fn is_trivia_token(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Whitespace
            | TokenKind::LineComment
            | TokenKind::BlockComment
            | TokenKind::Shebang
    )
}

/// Declarations whose node begins with a leading keyword before the name.
pub(super) const fn kind_is_keyword_led(kind: SymbolKind) -> bool {
    matches!(
        kind,
        SymbolKind::Class
            | SymbolKind::Function
            | SymbolKind::Interface
            | SymbolKind::TypeAlias
            | SymbolKind::Enum
            | SymbolKind::Namespace
    )
}

/// Modifiers and the rest marker that belong to a parameter or class member
/// node, so its `Decl` marker anchors before them.
const fn is_member_modifier(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::KwPublic
            | TokenKind::KwPrivate
            | TokenKind::KwProtected
            | TokenKind::KwStatic
            | TokenKind::KwReadonly
            | TokenKind::KwAbstract
            | TokenKind::KwOverride
            | TokenKind::KwDeclare
            | TokenKind::DotDotDot
    )
}

/// Symbol kinds that can merge across compilation units when they share a
/// name: namespaces, interfaces, enums, functions, and `var` redeclarations.
/// Only these participate in the cross-unit `declaration_anchors` overlay;
/// all other kinds (type parameters, parameters, `let`/`const` locals, …)
/// use their own per-unit anchor so same-named distinct symbols do not
/// collapse into one `Decl` list.
pub(super) const fn kind_is_mergeable(kind: SymbolKind) -> bool {
    matches!(
        kind,
        SymbolKind::Variable(bamts_compiler::syntax::VariableKind::Var)
            | SymbolKind::Function
            | SymbolKind::Interface
            | SymbolKind::Enum
            | SymbolKind::Namespace
    )
}

/// Occurrence-covered interface member kinds that join the cross-unit `Decl`
/// overlay: `Function` method members and `Variable(Let)` property members.
/// This is the narrow occurrence union — `kind_is_mergeable` itself is
/// unchanged, so arbitrary `let` locals outside occurrence coverage keep the
/// legacy per-unit boundary.
const fn kind_is_occurrence_overlay_member(kind: SymbolKind) -> bool {
    matches!(
        kind,
        SymbolKind::Function | SymbolKind::Variable(bamts_compiler::syntax::VariableKind::Let)
    )
}

/// Tokens that can lead a keyword-led declaration: its keyword, its modifiers,
/// and the generator star, scanned over to anchor `Decl(...)` at the full start.
const fn is_declaration_leading(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::KwClass
            | TokenKind::KwFunction
            | TokenKind::KwInterface
            | TokenKind::KwType
            | TokenKind::KwEnum
            | TokenKind::KwNamespace
            | TokenKind::KwExport
            | TokenKind::KwDeclare
            | TokenKind::KwAbstract
            | TokenKind::KwDefault
            | TokenKind::KwConst
            | TokenKind::KwAsync
            | TokenKind::KwPublic
            | TokenKind::KwPrivate
            | TokenKind::KwProtected
            | TokenKind::KwStatic
            | TokenKind::KwReadonly
            | TokenKind::KwGet
            | TokenKind::KwSet
            | TokenKind::Star
    )
}

/// Resolve the `.symbols` baseline logical path owned by one case. As for
/// `.types`, classification guarantees sole-stem ownership for included rows,
/// so resolution is by stem: the plain (no-suffix) baseline wins, else the
/// lexicographically first variant, unless `compile_options` names a match.
pub fn resolve_symbols_baseline(groups: &BaselineGroups, logical_path: &str) -> Option<String> {
    resolve_stem_baseline(groups, logical_path, "symbols", &[])
        .ok()
        .flatten()
}

/// Compare one compiled case's emitted `.symbols` document against its baseline.
pub fn check_symbols(
    snapshot: &(impl SnapshotAssets + ?Sized),
    case: &CheckedCase,
    logical_path: &str,
    baseline_path: &str,
) -> Result<SymbolsOutcome> {
    let emitted = emit_symbols_baseline(case, logical_path);
    let bytes = read_verified_snapshot_asset(snapshot, baseline_path)?;
    let expected = String::from_utf8_lossy(&bytes).into_owned();
    let verdict = compare_symbols(&expected, &emitted);
    Ok(SymbolsOutcome { emitted, verdict })
}

/// Execute the S2 `symbols` observation for one planned cell.
///
/// Failure-class discipline mirrors `execute_types_check`: compile failures
/// are `FAIL_BEHAVIOR` (loader/bound) or `CRASH` (panic); comparator `Fail`
/// is `FAIL_BEHAVIOR` (a checker-depth/format mismatch, the S2 burn-down
/// surface); `Unproven` (baseline won't canonicalize) is an oracle-side
/// `HARNESS_ERROR`; a missing owned baseline is a classification/execution
/// drift `HARNESS_ERROR`.
pub(crate) fn execute_symbols_check(
    snapshot: &(impl SnapshotAssets + ?Sized),
    groups: &BaselineGroups,
    plan: &PlannedCell,
    index_entry: &IndexEntry,
) -> Result<CellResult> {
    let text = read_case_text(snapshot, index_entry)?;
    let pragmas = parse_case_pragmas(&text);
    Ok(cell_result(
        plan,
        observe_symbols(snapshot, groups, index_entry, &text, &pragmas),
    ))
}

/// Run the symbols comparator against the selected pragma variation.
pub(crate) fn observe_symbols(
    snapshot: &(impl SnapshotAssets + ?Sized),
    groups: &BaselineGroups,
    index_entry: &IndexEntry,
    text: &str,
    pragmas: &CasePragmas,
) -> CompilerCheckObservation {
    let units = split_case_units(&index_entry.logical_path, text);
    let entry = entry_virtual_path(&index_entry.logical_path, &units);
    let compile_options = compile_option_pairs(pragmas);
    let baseline_path = match resolve_stem_baseline(
        groups,
        &index_entry.logical_path,
        "symbols",
        &compile_options,
    ) {
        Ok(path) => path,
        Err(error) => {
            return CompilerCheckObservation {
                class: FailureClass::HarnessError,
                detail: error.to_string(),
                artifact: None,
            };
        }
    };
    match compile_case_with_pragmas(&units, &entry, pragmas) {
        Err(error) => compile_failure_observation(error),
        Ok(case) => {
            let Some(baseline_path) = baseline_path else {
                return CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: "classification/execution drift: no owned `.symbols` baseline"
                        .to_owned(),
                    artifact: None,
                };
            };
            let outcome =
                match check_symbols(snapshot, &case, &index_entry.logical_path, &baseline_path) {
                    Ok(outcome) => outcome,
                    Err(error) => {
                        return CompilerCheckObservation {
                            class: FailureClass::HarnessError,
                            detail: error.to_string(),
                            artifact: None,
                        };
                    }
                };
            match outcome.verdict {
                FacetVerdict::Pass => CompilerCheckObservation {
                    class: FailureClass::Pass,
                    detail: "symbols parity".to_owned(),
                    artifact: Some(outcome.emitted.into_bytes()),
                },
                FacetVerdict::Fail { reason } => CompilerCheckObservation {
                    class: FailureClass::FailBehavior,
                    detail: reason,
                    artifact: None,
                },
                FacetVerdict::Unproven { reason } => CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: format!("symbols oracle could not prove parity: {reason}"),
                    artifact: None,
                },
            }
        }
    }
}
