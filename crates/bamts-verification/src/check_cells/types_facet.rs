use super::*;

/// One `>display : type` record plus its underline, anchored to a source line.
pub(super) struct TypeAnnotation {
    pub(super) start: usize,
    pub(super) end: usize,
    pub(super) line: usize,
    pub(super) display: String,
    pub(super) rendered: String,
    pub(super) caret: bool,
    pub(super) blanks: Vec<(usize, usize)>,
}

/// Emit the `.types` baseline for a compiled case in the upstream framing:
/// a `//// [path] ////` marker, then one `=== <unit> ===` section per reached
/// unit whose source is echoed with `>expr : type` / `>  : ^^^` records under
/// each line. Only nodes the checker actually typed produce records, so the
/// document reproduces upstream exactly where the checker's coverage matches
/// and drops records where it does not (the S2 burn-down surface).
#[must_use]
pub fn emit_types_baseline(case: &CheckedCase, logical_path: &str) -> String {
    let mut out = format!("//// [{logical_path}] ////\n\n");
    let has_diagnostics = case.reached_units().any(|(_, output)| {
        output
            .diagnostics()
            .iter()
            .any(|diagnostic| !diagnostic.code().as_str().starts_with("BAMTS-W"))
    });
    for (unit, output) in case.units_in_document_order() {
        if is_config_unit_name(&unit.display_name) {
            continue;
        }
        // Skip the empty entry unit that multi-file cases (`@filename:`
        // sections) leave behind — it has no source content and upstream
        // does not emit a section for it.
        if output
            .source_file()
            .source_text()
            .as_str()
            .trim()
            .is_empty()
        {
            continue;
        }
        emit_unit_types(
            output.semantic_model(),
            output.source_file().source_text(),
            output.source_file().tokens(),
            &unit.display_name,
            has_diagnostics,
            &mut out,
        );
    }
    out
}

/// Collapse records with the identical identity tuple (start, end, display,
/// rendered): the binder can push the same (range, type) pair from both its
/// symbol and expression indexes, and upstream emits each unique (position,
/// display, type) triple once. Sort by the identity key, dedup consecutive,
/// then re-sort into the upstream order (by start, outer node before inner
/// on ties).
pub(super) fn dedup_type_records(mut records: Vec<TypeAnnotation>) -> Vec<TypeAnnotation> {
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
    records.sort_by(|left, right| left.start.cmp(&right.start).then(right.end.cmp(&left.end)));
    records
}

fn emit_unit_types(
    model: &SemanticModel,
    source: &SourceText,
    tokens: &[Token],
    section: &str,
    has_diagnostics: bool,
    out: &mut String,
) {
    let mut records: Vec<TypeAnnotation> = Vec::new();
    // Symbols covered by interface-member declaration occurrences emit one
    // record per written occurrence below; the covered symbol's own row is
    // skipped here so every duplicate declaration gets its own span. The
    // skip is mandatory and independent of `dedup_type_records`.
    let occurrence_covered: HashSet<SymbolId> = model
        .declaration_occurrences()
        .iter()
        .map(|occurrence| occurrence.symbol)
        .collect();
    // Declaration-name records come from source-declared symbols (intrinsics
    // carry an empty range, which the range check below filters out).
    for (index, symbol) in model.symbols().iter().enumerate() {
        if occurrence_covered.contains(&SymbolId::new(index as u32)) {
            continue;
        }
        // Interface declaration names carry no `>name : type` record
        // upstream: `interface I { (): number; }` baselines echo only
        // member records (`duplicateConstructSignature.types`,
        // `interfaceDeclaration1.types`), while class, enum, type-alias,
        // and namespace names do get records.
        if matches!(
            symbol.kind(),
            SymbolKind::TypeParameter | SymbolKind::Interface
        ) {
            continue;
        }
        // Class constructors do not get a `>constructor : type` record in
        // upstream `.types` baselines: the constructor keyword is a member
        // declaration, not a value expression, and tsc's type writer only
        // emits records for symbols whose name appears as an expression or
        // declaration name in source order. Verified against
        // `parserClassDeclaration12.types:4` (class C with two constructor
        // signatures — baseline has `>C : C` and `>a : any` but no
        // `>constructor`), and `ClassDeclaration26.types:4` (class with
        // constructor body — same pattern, no `>constructor` record).
        if symbol.kind() == SymbolKind::Function && symbol.name() == "constructor" {
            continue;
        }
        let range = symbol.range();
        if range.start() == range.end() {
            continue;
        }
        let id = SymbolId::new(index as u32);
        let type_id = model.symbol_type(id);
        let display = symbol_record_display(tokens, source, symbol.name(), range);
        if let Some(annotation) = annotation_for(
            source,
            range,
            display,
            writes_caret(model, source, type_id, has_diagnostics, Some(id), range),
            model,
            type_id,
        ) {
            records.push(annotation);
        }
    }
    // Interface member declaration occurrences: one record per written
    // occurrence at its own `name_range` — the identifier span, quotes
    // included for string keys, digits for numeric keys, and the
    // bracket-delimited `[expr]` span for computed keys. The rendered type
    // is the member's semantic `symbol_type` (never `declared_return`), and
    // the symbol loop's exclusions apply against the occurrence's symbol
    // kind and `name_range`.
    for occurrence in model.declaration_occurrences() {
        let symbol = model.symbol(occurrence.symbol);
        if matches!(
            symbol.kind(),
            SymbolKind::TypeParameter | SymbolKind::Interface
        ) {
            continue;
        }
        if symbol.kind() == SymbolKind::Function && symbol.name() == "constructor" {
            continue;
        }
        let range = occurrence.name_range;
        if range.start() == range.end() {
            continue;
        }
        let type_id = model.symbol_type(occurrence.symbol);
        if let Some(annotation) = annotation_for(
            source,
            range,
            slice_source(source, range),
            writes_caret(
                model,
                source,
                type_id,
                has_diagnostics,
                Some(occurrence.symbol),
                range,
            ),
            model,
            type_id,
        ) {
            records.push(annotation);
        }
    }
    // Expression records come from the checker's expression-type index.
    for (range, type_id) in model.typed_expressions() {
        let display = slice_source(source, *range);
        if let Some(annotation) = annotation_for(
            source,
            *range,
            display,
            writes_caret(model, source, *type_id, has_diagnostics, None, *range),
            model,
            *type_id,
        ) {
            records.push(annotation);
        }
    }
    let records = dedup_type_records(records);
    let mut by_line: BTreeMap<usize, Vec<&TypeAnnotation>> = BTreeMap::new();
    for record in &records {
        by_line.entry(record.line).or_default().push(record);
    }

    out.push_str(&format!("=== {section} ===\n"));
    for (line_index, raw_line) in source.as_str().split('\n').enumerate() {
        let line = raw_line.strip_suffix('\r').unwrap_or(raw_line);
        out.push_str(&strip_library_root(line));
        out.push('\n');
        let Some(line_records) = by_line.get(&line_index) else {
            continue;
        };
        for record in line_records {
            let display = collapse_whitespace(&record.display);
            out.push_str(&format!(">{display} : {}\n", record.rendered));
            if record.caret
                && let Some(marks) = caret_marks(record)
            {
                out.push_str(&format!(
                    ">{} : {}\n",
                    " ".repeat(display.chars().count()),
                    marks
                ));
            }
        }
    }
}

/// Build an annotation record, resolving the node's start line. Records whose
/// range cannot be mapped (should not happen for compiled units) are dropped.
fn annotation_for(
    source: &SourceText,
    range: TextRange,
    display: String,
    caret: bool,
    model: &SemanticModel,
    type_id: TypeId,
) -> Option<TypeAnnotation> {
    let (line, _) = source.line_column(range.start()).ok()?;
    let (rendered, blanks) = render_type_annotated(model, type_id);
    Some(TypeAnnotation {
        start: range.start().get(),
        end: range.end().get(),
        line,
        display,
        rendered,
        caret,
        blanks,
    })
}

/// Caret underline for one record: `^` over synthesized text, blanks over
/// spans that reproduce a written type annotation or a function parameter
/// name. Yields `None` when every character is blank, and the caller omits
/// the caret line, matching upstream records with no underline.
fn caret_marks(record: &TypeAnnotation) -> Option<String> {
    if record.rendered.is_empty() {
        return None;
    }
    let mut covered = 0usize;
    let marks: String = record
        .rendered
        .char_indices()
        .map(|(byte, _)| {
            let blank = record
                .blanks
                .iter()
                .any(|span| byte >= span.0 && byte < span.1);
            if blank {
                covered += 1;
                ' '
            } else {
                '^'
            }
        })
        .collect();
    if covered == record.rendered.chars().count() {
        return None;
    }
    Some(marks)
}

pub(super) fn writes_caret(
    model: &SemanticModel,
    source: &SourceText,
    type_id: TypeId,
    has_diagnostics: bool,
    symbol: Option<SymbolId>,
    range: TextRange,
) -> bool {
    if has_diagnostics {
        return true;
    }
    let view = model.types().get(type_id);
    if matches!(view, Type::Error) {
        return false;
    }
    if !matches!(view, Type::Any) {
        return true;
    }
    if let Some(id) = symbol {
        let entry = model.symbol(id);
        if matches!(entry.kind(), SymbolKind::Import) {
            return true;
        }
        if matches!(model.scope(entry.scope()).kind(), ScopeKind::Catch) {
            return true;
        }
    }
    if is_access_site(source, range) {
        return true;
    }
    if symbol.is_some() && is_binding_element(source, range) {
        return true;
    }
    false
}

fn is_access_site(source: &SourceText, range: TextRange) -> bool {
    matches!(prev_sigil(source, range), Some('.' | '<')) || next_starts_with_dot(source, range)
}

fn is_binding_element(source: &SourceText, range: TextRange) -> bool {
    matches!(prev_sigil(source, range), Some('[' | ',' | '{'))
        && matches!(next_sigil(source, range), Some(',' | ']' | '}'))
}

fn prev_sigil(source: &SourceText, range: TextRange) -> Option<char> {
    let mut offset = source.utf16_to_byte(range.start()).ok()?;
    let bytes = source.as_str().as_bytes();
    while offset > 0 {
        offset -= 1;
        let byte = bytes[offset];
        if byte.is_ascii_whitespace() {
            continue;
        }
        return byte.is_ascii().then_some(byte as char);
    }
    None
}

fn next_sigil(source: &SourceText, range: TextRange) -> Option<char> {
    let mut offset = source.utf16_to_byte(range.end()).ok()?;
    let bytes = source.as_str().as_bytes();
    while offset < bytes.len() {
        let byte = bytes[offset];
        offset += 1;
        if byte.is_ascii_whitespace() {
            continue;
        }
        return byte.is_ascii().then_some(byte as char);
    }
    None
}

fn next_starts_with_dot(source: &SourceText, range: TextRange) -> bool {
    let Ok(offset) = source.utf16_to_byte(range.end()) else {
        return false;
    };
    let bytes = source.as_str().as_bytes();
    let mut cursor = offset;
    while cursor < bytes.len() && bytes[cursor].is_ascii_whitespace() {
        cursor += 1;
    }
    if bytes.get(cursor) == Some(&b'.') {
        return true;
    }
    bytes.get(cursor) == Some(&b'?') && bytes.get(cursor + 1) == Some(&b'.')
}

/// Display text for a symbol's `.types` record: the raw source slice when
/// the symbol's range is exactly one token (an identifier, keyword-shaped
/// name, string, numeric, or private name, quotes and escapes included, as
/// upstream echoes source text), otherwise the semantic name (import-equals
/// aliases and similar range over a whole statement).
fn symbol_record_display(
    tokens: &[Token],
    source: &SourceText,
    name: &str,
    range: TextRange,
) -> String {
    let at = tokens.partition_point(|token| token.range().start() < range.start());
    let single = tokens.get(at).is_some_and(|token| token.range() == range);
    if !single {
        return name.to_owned();
    }
    let slice = slice_source(source, range);
    if slice.is_empty() {
        name.to_owned()
    } else {
        slice
    }
}

pub(super) fn slice_source(source: &SourceText, range: TextRange) -> String {
    let text = source.as_str();
    match (
        source.utf16_to_byte(range.start()),
        source.utf16_to_byte(range.end()),
    ) {
        (Ok(start), Ok(end)) if start <= end && end <= text.len() => text[start..end].to_owned(),
        _ => String::new(),
    }
}

/// Collapse runs of whitespace (including newlines) to single spaces so a
/// multi-line node's echo stays on one record line; the comparator is
/// whitespace-insensitive on the record's left side.
pub(super) fn collapse_whitespace(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Resolve the `.types` baseline logical path owned by one case.
///
/// Classification guarantees sole-stem ownership for included rows, so
/// resolution is by stem. When `compile_options` names a variant suffix, that
/// variant wins; otherwise the plain (no-suffix) baseline wins, else the
/// lexicographically first variant.
pub fn resolve_types_baseline(groups: &BaselineGroups, logical_path: &str) -> Option<String> {
    resolve_stem_baseline(groups, logical_path, "types", &[])
        .ok()
        .flatten()
}

/// Compare one compiled case's emitted `.types` document against its baseline.
pub fn check_types(
    snapshot: &(impl SnapshotAssets + ?Sized),
    case: &CheckedCase,
    logical_path: &str,
    baseline_path: &str,
) -> Result<TypesOutcome> {
    let emitted = emit_types_baseline(case, logical_path);
    let bytes = read_verified_snapshot_asset(snapshot, baseline_path)?;
    let expected = String::from_utf8_lossy(&bytes).into_owned();
    let verdict = compare_types(&expected, &emitted);
    Ok(TypesOutcome { emitted, verdict })
}

/// Execute the S2 `types` observation for one planned cell.
///
/// Compile failures are `FAIL_BEHAVIOR` (loader/bound) or `CRASH` (panic);
/// comparator `Fail` is `FAIL_BEHAVIOR` (a checker-depth/format mismatch, the
/// S2 burn-down surface); `Unproven` (baseline won't canonicalize) is an
/// oracle-side `HARNESS_ERROR`; a missing owned baseline is a
/// classification/execution drift `HARNESS_ERROR`.
pub(crate) fn execute_types_check(
    snapshot: &(impl SnapshotAssets + ?Sized),
    groups: &BaselineGroups,
    plan: &PlannedCell,
    index_entry: &IndexEntry,
) -> Result<CellResult> {
    let text = read_case_text(snapshot, index_entry)?;
    let pragmas = parse_case_pragmas(&text);
    Ok(cell_result(
        plan,
        observe_types(snapshot, groups, index_entry, &text, &pragmas),
    ))
}

/// Run the types comparator against the selected pragma variation.
pub(crate) fn observe_types(
    snapshot: &(impl SnapshotAssets + ?Sized),
    groups: &BaselineGroups,
    index_entry: &IndexEntry,
    text: &str,
    pragmas: &CasePragmas,
) -> CompilerCheckObservation {
    let units = split_case_units(&index_entry.logical_path, text);
    let entry = entry_virtual_path(&index_entry.logical_path, &units);
    let compile_options = compile_option_pairs(pragmas);
    let baseline_path =
        match resolve_stem_baseline(groups, &index_entry.logical_path, "types", &compile_options) {
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
                    detail: "classification/execution drift: no owned `.types` baseline".to_owned(),
                    artifact: None,
                };
            };
            let outcome =
                match check_types(snapshot, &case, &index_entry.logical_path, &baseline_path) {
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
                    detail: "types parity".to_owned(),
                    artifact: Some(outcome.emitted.into_bytes()),
                },
                FacetVerdict::Fail { reason } => CompilerCheckObservation {
                    class: FailureClass::FailBehavior,
                    detail: reason,
                    artifact: None,
                },
                FacetVerdict::Unproven { reason } => CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: format!("types oracle could not prove parity: {reason}"),
                    artifact: None,
                },
            }
        }
    }
}

/// Upstream prints a reference directive's path without the virtual `/.lib/`
/// root that the test sources use to point at shared library files.
pub(super) fn strip_library_root(line: &str) -> std::borrow::Cow<'_, str> {
    if line.starts_with("/// <reference") && line.contains("\"/.lib/") {
        std::borrow::Cow::Owned(line.replace("\"/.lib/", "\""))
    } else {
        std::borrow::Cow::Borrowed(line)
    }
}
