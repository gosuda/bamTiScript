//! S2 check-cell machinery: the `diagnostics` facet executor plus the case
//! pragmas, multi-unit splitting, and flat-baseline resolution the U2.8 S2
//! facets share.
//!
//! One check cell materializes its case's virtual unit files into a per-cell
//! temp directory, compiles through the real [`ProgramLoader`] +
//! [`compile_program_frontend`] pipeline (the one real module resolver and the
//! canonical diagnostics union), and compares the emitted observations against
//! the upstream baseline via the `facets.rs` comparators.
//!
//! Baseline resolution is flat by stem (`tests/baselines/reference/<stem>…`):
//! duplicate stems are disambiguated by the baseline's first
//! `//// [<full case logical path>] ////` ownership marker, and the
//! `<stem>(<option>=<value>)` suffix names a variant compile.

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs,
    path::{Path, PathBuf},
    sync::Arc,
};

use bamts_compiler::checker::{
    DeclarationOccurrence, ScopeKind, SemanticModel, SymbolId, SymbolKind, Type, TypeId,
    lib_decl_files_for_global, render_type_annotated,
};
use bamts_compiler::diagnostic::DiagnosticSeverity;
use bamts_compiler::emitter::{EmitFileNames, EmitOptions, ModuleKind, emit_checked};
use bamts_compiler::pipeline::{
    FrontendMode, FrontendOutput, ProgramFrontendOutput, compile_program_frontend,
};
use bamts_compiler::program::{
    JsxRoutingDecision, ModuleEdgeKind, ProgramLoader, ProgramOutputKind, ResolvedProgram,
};
use bamts_compiler::project::build_mode::{
    BUILD_INFO_SCHEMA, BuildInfo, canonical_json, source_signature,
};
use bamts_compiler::project::canonical::canonicalize;
use bamts_compiler::project::resolution::{
    ModuleResolutionKind, ResolutionCache, ResolutionHost, TraceResolutionServices,
    resolve_module_name_with_trace,
};
use bamts_compiler::project::resolution_trace::ResolutionTraceLog;
use bamts_compiler::project::{
    CompilerOptions, JsonObject, JsonValue, ProjectConfig, ProjectRoot, parse_jsonc,
};
use bamts_compiler::source::SourceText;
use bamts_compiler::source::{JsxEmit, SourceId, TextRange, Utf16Pos};
use bamts_compiler::syntax::{Token, TokenKind};

use crate::catalog::CaseConfiguration;
use crate::facets::{
    DiagnosticCategory, DiagnosticCodeMap, FacetDiagnostic, FacetSeverity, FacetVerdict,
    SourcePosition, compare_declaration_emit, compare_diagnostics, compare_js_emit,
    compare_source_map, compare_symbols, compare_types,
};
use crate::suite::{
    CellResult, FailureClass, IndexEntry, PlannedCell, SnapshotAssets, SuiteIndex, TempDir,
    decode_case_source, read_verified_snapshot_asset,
};
use crate::{ErrorCode, Result, VerificationError};

/// Baselines are imported flat under `tests/baselines/reference/`; the runner
/// stores every non-case blob under the snapshot's `baselines/` content store.
const BASELINE_REFERENCE_PREFIX: &str = "tests/baselines/reference/";

/// Everything one check cell needs beyond the snapshot: loaded once per run.
pub struct CheckContext {
    /// The validated BAMTS↔TS diagnostic correspondence table.
    pub code_map: DiagnosticCodeMap,
    /// Stem/suffix baseline groups built once from the snapshot index, so the
    /// per-cell executors do not rescan the entire index on every invocation.
    pub baseline_groups: BaselineGroups,
}

/// One unit of a case blob: the split at each `// @filename:` directive.
///
/// Single-unit cases yield one unit named by the case's own logical path.
/// Names are virtual: relative names are joined under the case's directory,
/// absolute names (`/ref.d.ts`) are remapped under the temp root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaseUnit {
    /// Root-relative virtual path (`foo/testB.ts`).
    pub virtual_path: String,
    /// The unit name exactly as the case spelled it: the verbatim
    /// `// @Filename:` value, or the case basename for the implicit entry
    /// unit. `virtual_path` is lossy (it strips the leading `/` of absolute
    /// names, drops Windows drive prefixes, and joins relative names under
    /// the case directory), but upstream's `.types` section headers echo the
    /// original spelling (`=== /a.ts ===`, `=== A:/foo/bar.ts ===`,
    /// `=== ./a.ts ===`), so the types emitter needs the unmodified name.
    pub display_name: String,
    /// UTF-8 unit text (BOMs handled by `decode_case_source` upstream).
    pub text: String,
}

/// Pragmas parsed from `// @<name>: <value>` case directive lines.
///
/// Option names are lowercased to match `(name=value)` baseline suffixes; a
/// comma-separated value lists the option's variants in declaration order.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CasePragmas {
    /// `(option, values)` pairs in declaration order.
    pub options: Vec<(String, Vec<String>)>,
    /// `@noTypesAndSymbols: true` suppresses types/symbols baseline output.
    pub no_types_and_symbols: bool,
}

impl CasePragmas {
    /// Build the exact single-valued pragma set selected by the catalog.
    #[must_use]
    pub fn from_configuration(configuration: &CaseConfiguration) -> Self {
        Self {
            options: configuration
                .options
                .iter()
                .map(|(name, value)| (name.clone(), vec![value.clone()]))
                .collect(),
            no_types_and_symbols: configuration
                .options
                .get("notypesandsymbols")
                .is_some_and(|value| value.eq_ignore_ascii_case("true")),
        }
    }
}

/// Comparator-backed observation returned to exact compiler-lane callers.
#[derive(Debug, Clone)]
pub struct CompilerCheckObservation {
    pub class: FailureClass,
    pub detail: String,
    /// Canonical BamTS-side observation bytes. Present only after compilation.
    pub artifact: Option<Vec<u8>>,
}

/// One file-anchored error row of an `.errors.txt` baseline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ErrorsDiagnostic {
    /// The virtual unit name exactly as printed by the baseline (`b.ts`).
    pub unit: String,
    /// 1-based line.
    pub line: u32,
    /// 0-based UTF-16 character (baseline prints 1-based; stored minus one).
    pub character: u32,
    /// `error` or `warning` from the baseline text.
    pub category: String,
    /// TypeScript code (`TS2305`).
    pub code: String,
    /// Message text after `TS<code>: `.
    pub message: String,
}

/// One file-less (`error TS5107: …`) header row of an `.errors.txt` baseline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GlobalDiagnostic {
    /// TypeScript code (`TS5107`).
    pub code: String,
    /// Message text.
    pub message: String,
}

/// Parsed `.errors.txt` baseline: the file-anchored rows the comparator sees
/// plus the file-less global rows reported separately.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ErrorsBaseline {
    /// `file(l,c): (error|warning) TSnnnn: message` rows, in baseline order.
    pub diagnostics: Vec<ErrorsDiagnostic>,
    /// File-less global rows (option deprecation etc.); the compiler has no
    /// corresponding observation yet, so these are excluded from comparison.
    pub globals: Vec<GlobalDiagnostic>,
}

impl ErrorsBaseline {
    /// Number of file-anchored diagnostics.
    #[must_use]
    pub fn file_diagnostic_count(&self) -> usize {
        self.diagnostics.len()
    }
}

/// The resolved diagnostics-baseline view of one case: which (if any)
/// `.errors.txt` baselines belong to it.
#[derive(Debug, Clone, Default)]
pub struct DiagnosticsBaselines {
    /// Baselines whose ownership marker names this case, or that carry no
    /// marker when this case is the stem's sole input. None ⇒ upstream
    /// expects zero diagnostics (the strictest row class).
    pub owned: Vec<String>,
    contents: BTreeMap<String, String>,
}

/// The per-cell product of compiling one materialized case.
pub struct CheckedCase {
    /// Units in split order paired with the index of their frontend module in
    /// [`ProgramFrontendOutput::modules`]. Unreachable units (never imported
    /// from the entry) carry no module index.
    pub units: Vec<(CaseUnit, Option<usize>)>,
    /// Virtual path of the entry unit (the unit that was loaded first).
    pub entry: String,
    /// Whole-program frontend product (one module per resolved file).
    output: ProgramFrontendOutput,
    /// The resolved module graph, retained for the trace comparator to
    /// re-resolve import specifiers with `resolve_module_name_with_trace`.
    program: ResolvedProgram,
    /// Compiler options used for this compilation, retained for the trace
    /// comparator to pass to `resolve_module_name_with_trace`.
    options: bamts_compiler::project::CompilerOptions,
    /// The directory `fullEmitPaths` prints in front of every output name.
    emit_directory: Option<String>,
    /// `noResolve`: imports add no files to the program, so units emit in
    /// the order the case lists them.
    no_resolve: bool,
}

fn is_under_node_modules(virtual_path: &str) -> bool {
    virtual_path.split('/').any(|part| part == "node_modules")
}
/// Whether a module sends at least one resolved edge into another document
/// unit. Reference directives, relative imports, and bare specifiers all
/// count; only resolution matters, never the specifier text.
fn has_resolved_outgoing_to_documented(
    case: &CheckedCase,
    from_index: usize,
    documented: &[(usize, &CaseUnit, &FrontendOutput)],
) -> bool {
    let targets: Vec<_> = documented
        .iter()
        .filter(|(index, _, _)| *index != from_index)
        .map(|(index, _, _)| case.program().modules()[*index].source_id())
        .collect();
    case.program().modules()[from_index]
        .dependencies()
        .iter()
        .any(|edge| {
            !edge.is_unresolved()
                && (edge
                    .target()
                    .local_source_id()
                    .is_some_and(|id| targets.contains(&id))
                    || edge
                        .type_target()
                        .and_then(|target| target.local_source_id())
                        .is_some_and(|id| targets.contains(&id)))
        })
}
fn has_incoming_from_test_files(case: &CheckedCase, target_index: usize) -> bool {
    let target = case.program().modules()[target_index].source_id();
    case.units
        .iter()
        .filter_map(|(_, index)| *index)
        .filter(|index| *index != target_index)
        .any(|other| {
            case.program().modules()[other]
                .dependencies()
                .iter()
                .any(|edge| {
                    !edge.is_unresolved()
                        && (edge.target().local_source_id() == Some(target)
                            || edge.type_target().and_then(|t| t.local_source_id()) == Some(target))
                })
        })
}
fn should_exclude_unit(case: &CheckedCase, module_index: usize, unit: &CaseUnit) -> bool {
    if is_config_unit_name(&unit.display_name) {
        return true;
    }
    let base = unit_basename(&unit.virtual_path);
    if is_json_input_name(&base) && !has_incoming_from_test_files(case, module_index) {
        return true;
    }
    if is_under_node_modules(&unit.virtual_path)
        && !has_incoming_from_test_files(case, module_index)
    {
        return true;
    }
    false
}
impl CheckedCase {
    /// The `outDir` printed before each output section name, when the case
    /// asks for full emit paths.
    #[must_use]
    pub fn emit_directory(&self) -> Option<&str> {
        self.emit_directory.as_deref()
    }

    /// Whether the case sets `noResolve`.
    #[must_use]
    pub fn no_resolve(&self) -> bool {
        self.no_resolve
    }

    /// The frontend output of one unit, when the program reached it.
    #[must_use]
    pub fn module_output(&self, unit: &CaseUnit) -> Option<&FrontendOutput> {
        self.units
            .iter()
            .find(|(candidate, _)| candidate.virtual_path == unit.virtual_path)
            .and_then(|(_, index)| index.map(|index| &self.output.modules()[index]))
    }

    /// `(unit, output)` pairs for every unit the program reached.
    pub fn reached_units(&self) -> impl Iterator<Item = (&CaseUnit, &FrontendOutput)> {
        self.units
            .iter()
            .filter_map(|(unit, index)| index.map(|index| (unit, &self.output.modules()[index])))
    }
    /// `(unit, output)` pairs in the order upstream's `.types` and `.symbols`
    /// documents list them. Units the program never reached carry no section;
    /// project-config files, unimported JSON files, and unimported files under
    /// `node_modules` never get a section. A last unit that no other document
    /// unit imports, but that itself resolves an import of a document unit,
    /// is the entry the harness compiles, so it comes first and the others
    /// follow in `// @filename:` order.
    pub fn units_in_document_order(&self) -> Vec<(&CaseUnit, &FrontendOutput)> {
        let mut triples: Vec<(usize, &CaseUnit, &FrontendOutput)> = Vec::new();
        for (unit, index) in &self.units {
            let Some(index) = index else {
                continue;
            };
            if should_exclude_unit(self, *index, unit) {
                continue;
            }
            triples.push((*index, unit, &self.output.modules()[*index]));
        }
        if triples.len() >= 2 {
            let last = triples.len() - 1;
            let (last_index, _, _) = triples[last];
            if !has_incoming_from_test_files(self, last_index)
                && has_resolved_outgoing_to_documented(self, last_index, &triples)
            {
                let moved = triples.remove(last);
                triples.insert(0, moved);
            }
        }
        triples
            .into_iter()
            .map(|(_, unit, output)| (unit, output))
            .collect()
    }

    /// `(unit, output)` pairs in upstream's output-section order: a post-order
    /// descent over imports and `/// <reference>` targets with the case's
    /// roots visited in case order, so a referenced file completes before the
    /// file that names it and every output group follows source order when
    /// nothing depends on anything else. A cycle member completes before the
    /// file that reaches it, so the later-listed member of a cycle completes
    /// first (`asyncFunctionsAcrossFiles.js` carries `//// [b.js]` before
    /// `//// [a.js]` for an `a`/`b` import cycle; independent inputs keep
    /// listing order as in `ambientDeclarationsPatterns_merging1.js`).
    /// Only the JavaScript, declaration, and source-map emitters read this
    /// order; every other facet keeps traversal order.
    pub fn reached_units_in_module_order(&self) -> Vec<(&CaseUnit, &FrontendOutput)> {
        // `ProgramFrontendOutput::modules()` parallels this order exactly, so the
        // rank computed over the resolved graph indexes the frontend products.
        let modules = self.program.modules();
        let mut index_by_source = HashMap::new();
        for (index, module) in modules.iter().enumerate() {
            index_by_source.insert(module.source_id(), index);
        }
        let mut visited = vec![false; modules.len()];
        let mut stack = Vec::new();
        let mut descent = Vec::new();
        for seed in self.units.iter().filter_map(|(_, index)| *index) {
            if visited[seed] {
                continue;
            }
            visited[seed] = true;
            stack.push((seed, false));
            while let Some((index, expanded)) = stack.pop() {
                if expanded {
                    descent.push(index);
                    continue;
                }
                stack.push((index, true));
                for edge in modules[index].dependencies().iter().rev() {
                    let Some(source) = edge.target().local_source_id() else {
                        continue;
                    };
                    let Some(&child) = index_by_source.get(&source) else {
                        continue;
                    };
                    if !visited[child] {
                        visited[child] = true;
                        stack.push((child, false));
                    }
                }
            }
        }
        let mut rank = vec![usize::MAX; modules.len()];
        for (order, index) in descent.into_iter().enumerate() {
            rank[index] = order;
        }
        let mut triples: Vec<(usize, &CaseUnit, &FrontendOutput)> = self
            .units
            .iter()
            .filter_map(|(unit, index)| {
                index.map(|index| (rank[index], unit, &self.output.modules()[index]))
            })
            .collect();
        triples.sort_by_key(|(order, _, _)| *order);
        triples
            .into_iter()
            .map(|(_, unit, output)| (unit, output))
            .collect()
    }

    /// The resolved module graph, for the trace comparator.
    #[must_use]
    pub fn program(&self) -> &ResolvedProgram {
        &self.program
    }

    /// Compiler options, for the trace comparator.
    #[must_use]
    pub fn options(&self) -> &bamts_compiler::project::CompilerOptions {
        &self.options
    }
}

/// The execution verdict of one diagnostics check cell.
#[derive(Debug, Clone)]
pub struct DiagnosticsOutcome {
    /// Diagnostics emitted by the compile (`collect_facet_diagnostics`).
    pub actual: Vec<FacetDiagnostic>,
    /// Diagnostics expected by the resolved baselines (union of all owned
    /// `.errors.txt` rows; empty when no baseline owns the case).
    pub expected: Vec<FacetDiagnostic>,
    /// The comparator verdict.
    pub verdict: FacetVerdict,
}

/// Failure to compile a case for a check cell.
#[derive(Debug)]
pub enum CaseCompileError {
    /// The loader rejected the program (module resolution, root confinement,
    /// unreadable entrypoint). Reported as `FAIL_BEHAVIOR` with the loader's
    /// own text as evidence.
    Load(String),
    /// A unit's text exceeds the frontend's source bound. `ProgramLoader`
    /// reports these as `Read` errors; this variant covers the harness-side
    /// pre-check. Reported as `FAIL_BEHAVIOR`.
    SourceBound(String),
    /// The compiler panicked inside `catch_unwind`. Reported as `CRASH`.
    Panic(String),
}

impl CaseCompileError {
    /// The cell's failure class per the U2.8 discipline (loader/bound errors
    /// are S5-triage behavior failures; panics are crashes).
    #[must_use]
    pub const fn failure_class(&self) -> FailureClass {
        match self {
            Self::Load(_) | Self::SourceBound(_) => FailureClass::FailBehavior,
            Self::Panic(_) => FailureClass::Crash,
        }
    }
}

/// Parse the `// @<name>: <value>` directive block of a case text.
///
/// Only whole-line directives are recognized. `@filename:` units are not
/// options; everything else is recorded with a lowercased name, comma-split
/// values, and `@noTypesAndSymbols: true` pinned to the suppression flag.
pub fn parse_case_pragmas(text: &str) -> CasePragmas {
    let mut options = Vec::new();
    let mut no_types_and_symbols = false;
    for line in text.lines() {
        let Some((name, value)) = directive_parts(line) else {
            continue;
        };
        let name = name.to_ascii_lowercase();
        let value = value.trim();
        if name == "filename" {
            continue;
        }
        if name == "notypesandsymbols" {
            no_types_and_symbols |= value.eq_ignore_ascii_case("true");
            continue;
        }
        let values: Vec<String> = value
            .split(',')
            .map(|part| part.trim().to_owned())
            .filter(|part| !part.is_empty())
            .collect();
        options.push((name, values));
    }
    CasePragmas {
        options,
        no_types_and_symbols,
    }
}

/// Split one whole-line directive into its `(name, value)` pair under
/// upstream's option-directive grammar `^//\s*@\w+\s*:`: exactly two leading
/// slashes, a single ASCII-word option name, then a colon. This is the one
/// grammar pragma parsing, unit splitting, and directive stripping share,
/// so `///` reference directives, `////` lines, and multi-word `@param x:`
/// forms are content on every path. The value keeps its post-colon spacing;
/// callers trim it.
fn directive_parts(line: &str) -> Option<(&str, &str)> {
    // A leading U+FEFF (BOM) may precede the `//` in files saved with a
    // byte-order mark; strip it before the directive test so coordinates
    // are not shifted by the invisible character.
    let line = line.strip_prefix('\u{feff}').unwrap_or(line);
    let rest = line.strip_prefix("//")?;
    // A third leading slash is a `///` directive, not a `// @option`.
    if rest.starts_with('/') {
        return None;
    }
    let body = rest.trim_start().strip_prefix('@')?;
    let name_len = body
        .bytes()
        .take_while(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
        .count();
    if name_len == 0 {
        return None;
    }
    let (name, rest) = body.split_at(name_len);
    let value = rest.trim_start().strip_prefix(':')?;
    Some((name, value))
}

/// Strip every whole-line `// @name: value` compiler-option directive from a
/// unit's compiled content, reproducing upstream `makeUnitsFromTest`.
///
/// TypeScript removes each such line (global options and `@filename:` markers
/// alike) before compiling, joins the surviving lines with `\n`, and — because
/// the first accumulated chunk starts empty — collapses the leading blank lines
/// that a stripped prologue leaves behind. Reproducing all three keeps the
/// compiled source, and therefore every emitted `.errors.txt`/`.types`/
/// `.symbols` position, numbered exactly as the baselines are.
fn strip_directive_lines(text: &str) -> String {
    // Upstream's `lineDelimiter` splits on `\r?\n` per line, so a CRLF line
    // and a bare `\n` line are distinct lines even within one unit;
    // normalizing `\r\n` to `\n` before splitting reproduces exactly that
    // line set (a lone `\r` is not a delimiter on either side).
    let normalized = text.replace("\r\n", "\n");
    let lines: Vec<&str> = normalized.split('\n').collect();
    let mut content: Option<String> = None;
    for line in lines {
        if is_option_directive_line(line) {
            continue;
        }
        match &mut content {
            None => content = Some(line.to_owned()),
            Some(current) => {
                if !current.is_empty() {
                    current.push('\n');
                }
                current.push_str(line);
            }
        }
    }
    content.unwrap_or_default()
}

/// Whether a terminator-free line matches upstream's option-directive grammar
/// `^//\s*@\w+\s*:` — exactly two leading slashes, a single ASCII-word option
/// name, then a colon. This is the exact set upstream strips from unit content;
/// `///` reference directives and `@word` lines without a colon are kept.
/// Shares its grammar with pragma parsing and unit splitting through
/// [`directive_parts`], so the three paths cannot diverge.
fn is_option_directive_line(line: &str) -> bool {
    directive_parts(line).is_some()
}

/// The preamble text is directive-stripped already, so only comments,
/// blanks, strings, and compiled lines remain; block comments may span
/// lines, and a quote hides comment openers.
fn preamble_has_compiled_content(text: &str) -> bool {
    let stripped = strip_directive_lines(text);
    let bytes = stripped.as_bytes();
    let mut index = 0;
    while index < bytes.len() {
        match bytes[index] {
            b'/' if bytes.get(index + 1) == Some(&b'/') => {
                index += 2;
                while index < bytes.len() && bytes[index] != b'\n' {
                    index += 1;
                }
            }
            b'/' if bytes.get(index + 1) == Some(&b'*') => {
                index += 2;
                while index + 1 < bytes.len() && !(bytes[index] == b'*' && bytes[index + 1] == b'/')
                {
                    index += 1;
                }
                index = (index + 2).min(bytes.len());
            }
            b'"' | b'\'' | b'`' => {
                let quote = bytes[index];
                index += 1;
                while index < bytes.len() && bytes[index] != quote {
                    index += usize::from(bytes[index] == b'\\') + 1;
                }
                index += 1;
            }
            byte if byte.is_ascii_whitespace() => index += 1,
            _ => return true,
        }
    }
    false
}

/// Split a case blob at `// @filename:` boundaries.
///
/// A directive must be a whole-line comment. Text before the first directive
/// belongs to the unit named by `logical_path`'s basename; a directive naming
/// the case's own basename is also treated as that first unit (no second
/// empty unit). Unit virtual paths are joined under the case's virtual
/// directory; absolute directive names are remapped to the root.
pub fn split_case_units(logical_path: &str, text: &str) -> Vec<CaseUnit> {
    let case_name = logical_path.rsplit('/').next().unwrap_or(logical_path);
    let case_dir = logical_path
        .rsplit_once('/')
        .map(|(dir, _)| dir)
        .unwrap_or("");

    // Gather directive markers as (line start byte offset, unit name).
    let mut markers: Vec<(usize, String)> = Vec::new();
    let mut offset = 0usize;
    for line in text.split_inclusive('\n') {
        let line_start = offset;
        offset += line.len();
        let name = directive_parts(line.trim_end_matches(['\n', '\r'])).and_then(
            |(name, value)| {
                name.eq_ignore_ascii_case("filename")
                    .then(|| value.trim().to_owned())
            },
        );
        if let Some(name) = name.filter(|name| !name.is_empty()) {
            markers.push((line_start, name));
        }
    }

    let mut units: Vec<CaseUnit> = Vec::new();
    let push_unit = |name: String, text: &str, units: &mut Vec<CaseUnit>| {
        let virtual_path = virtual_unit_path(case_dir, &name);
        // Upstream `makeUnitsFromTest` strips every `// @name: value` directive
        // line (global options and `@filename:` markers alike) from a unit's
        // compiled content, so a case's `.errors.txt`, `.types`, and
        // `.symbols` positions are numbered over directive-free source. Strip
        // the same lines here so emitted positions align with the baselines.
        let content = strip_directive_lines(text);
        // Upstream feeds units into a path-keyed fake FS (`testfs[fileName] =
        // file.Content`), so a directive restating an earlier unit's name
        // makes the later chunk the unit's entire content — it replaces, not
        // appends. Unit order stays at the first-seen position.
        if let Some(existing) = units.iter_mut().find(|u| u.virtual_path == virtual_path) {
            existing.text = content;
        } else {
            units.push(CaseUnit {
                // Slash-normalized verbatim spelling: no `.types` baseline
                // section header ever contains a backslash, but drive-letter
                // (`A:/…`) and dot-slash (`./…`) prefixes are preserved.
                display_name: name.replace('\\', "/"),
                virtual_path,
                text: content,
            });
        }
    };

    if markers.is_empty() {
        push_unit(case_name.to_owned(), text, &mut units);
        return units;
    }

    // Drop a marker that names the case's own basename at position 0: it
    // identifies the entry unit, it does not start a second one.
    let first_names_case = markers
        .first()
        .is_some_and(|(_, name)| name.rsplit('/').next() == Some(case_name));

    let mut body_start = 0usize;
    let mut body_name: Option<String> = None;
    for (index, (marker_start, name)) in markers.iter().enumerate() {
        if index == 0 && first_names_case {
            // The leading marker names the case's own basename: preamble and
            // the marker line both belong to the entry unit.
            body_start = 0;
            body_name = Some(case_name.to_owned());
            continue;
        }
        let end = *marker_start;
        match &body_name {
            Some(name) => push_unit(name.clone(), &text[body_start..end], &mut units),
            None => {
                // Upstream `ParseTestFilesAndSymlinks` (with
                // `AllowImplicitFirstFile: false`) panics on real code before
                // the first `@Filename` and drops comment-only preamble: the
                // implicit case-named unit exists only when it carries
                // compiled content. An options/comment-only preamble is
                // global settings, not a unit, so creating one here echoes a
                // phantom `//// [<case>.ts]` section and emits a phantom
                // `//// [<case>.js]`/`.d.ts` output that shifts every
                // baseline section the emit facets compare.
                if end > 0 && preamble_has_compiled_content(&text[..end]) {
                    push_unit(case_name.to_owned(), &text[..end], &mut units);
                }
            }
        }
        body_start = *marker_start;
        body_name = Some(name.clone());
    }
    if let Some(name) = body_name {
        push_unit(name, &text[body_start..], &mut units);
    }
    if units.is_empty() {
        push_unit(case_name.to_owned(), text, &mut units);
    }
    units
}

/// Map a `@filename:` name onto a root-relative virtual path: relative names
/// join under the case's directory; absolute virtual names (`/ref.d.ts`) and
/// Windows-style drive-letter paths (`c:/root/...`) are remapped to the root
/// so `ProgramLoader` can confine them. The drive letter is a virtual root
/// marker in upstream test cases, not a real directory component; stripping it
/// prevents paths like `/tmp/x/c:/root/...` on Unix hosts.
fn virtual_unit_path(case_dir: &str, name: &str) -> String {
    let name = name.replace('\\', "/");
    // Strip a Windows-style drive-letter prefix (`c:/…`, `D:\…` after
    // backslash→slash normalization). The remainder is a root-relative
    // virtual path (like `/`-prefixed absolute names), NOT joined under the
    // case directory — the drive letter marks an absolute virtual root.
    if name.len() >= 3 && name.as_bytes()[1] == b':' && name.as_bytes()[2] == b'/' {
        return name[3..].to_owned();
    }
    if let Some(rest) = name.strip_prefix('/') {
        return rest.to_owned();
    }
    if case_dir.is_empty() {
        name
    } else {
        format!("{case_dir}/{name}")
    }
}
/// Whether a virtual unit path names a TypeScript declaration file.
fn is_check_cell_declaration_path(path: &str) -> bool {
    let lower = path.to_lowercase();
    lower.ends_with(".d.ts") || lower.ends_with(".d.mts") || lower.ends_with(".d.cts")
}
/// Virtual prefix test sources use for shared library files.
const SHARED_LIB_PREFIX: &str = "/.lib/";
/// Snapshot subtree holding the shared library files.
const SHARED_LIB_ROOT: &str = "tests/lib/";

/// Whether a `/.lib/` reference target names a loadable support file.
fn shared_lib_target(value: &str) -> Option<&str> {
    let rest = value.strip_prefix(SHARED_LIB_PREFIX)?;
    if rest.is_empty()
        || rest.starts_with('/')
        || rest.contains('\\')
        || rest
            .split('/')
            .any(|part| part.is_empty() || part == "." || part == "..")
    {
        return None;
    }
    rest.to_ascii_lowercase().ends_with(".d.ts").then_some(rest)
}

/// Every `/.lib/` reference target one unit text names, in sorted order.
///
/// Only the prologue counts, mirroring the compiler's own loader
/// (`collect_reference_directives` stops at the first statement and
/// rejects a fourth slash): a `////` line is content, a directive after
/// the first compiled line is inert, and block-comment bodies never name
/// a target.
fn shared_lib_refs(text: &str) -> Vec<String> {
    let mut refs = Vec::new();
    let mut in_block_comment = false;
    for line in text.lines() {
        let trimmed = line.trim_start_matches('\u{feff}').trim();
        if in_block_comment {
            if trimmed.contains("*/") {
                in_block_comment = false;
            }
            continue;
        }
        if trimmed.is_empty() {
            continue;
        }
        if trimmed.starts_with("/*") {
            if !trimmed.contains("*/") {
                in_block_comment = true;
            }
            continue;
        }
        if trimmed.starts_with("///") {
            if trimmed.as_bytes().get(3) == Some(&b'/') {
                continue;
            }
            for (name, value) in directive_attributes(line) {
                if name != "path" {
                    continue;
                }
                let Some(target) = shared_lib_target(value) else {
                    continue;
                };
                if !refs.iter().any(|existing| existing == target) {
                    refs.push(target.to_owned());
                }
            }
            continue;
        }
        if trimmed.starts_with("//") {
            continue;
        }
        break;
    }
    refs.sort();
    refs
}

/// Every `(name, value)` attribute of a `/// <reference ... />` directive.
fn directive_attributes(line: &str) -> Vec<(&str, &str)> {
    let mut pairs = Vec::new();
    let Some(tag) = line.find("<reference") else {
        return pairs;
    };
    let mut rest = &line[tag + "<reference".len()..];
    while let Some(eq) = rest.find('=') {
        let name = rest[..eq].trim().trim_start_matches('/');
        rest = &rest[eq + 1..];
        let Some(value) = quoted_value(&mut rest) else {
            break;
        };
        pairs.push((name, value));
    }
    pairs
}

/// The next quoted attribute value, advancing past it.
fn quoted_value<'a>(rest: &mut &'a str) -> Option<&'a str> {
    let source: &'a str = *rest;
    let quote = source.trim_start().chars().next().unwrap_or('\0');
    if quote != '"' && quote != '\'' {
        return None;
    }
    let after_quote = &source.trim_start()[1..];
    let end = after_quote.find(quote)?;
    let value = &after_quote[..end];
    *rest = &after_quote[end + 1..];
    Some(value)
}
/// Rewrite `/.lib/<path>` reference targets to the bare subpath the
/// baselines print, returning every referenced subpath in sorted order.
fn rewrite_shared_lib_refs(units: &mut [CaseUnit]) -> Vec<String> {
    let mut all = Vec::new();
    for unit in units.iter_mut() {
        for target in shared_lib_refs(&unit.text) {
            unit.text = unit.text.replace(
                &format!("\"{SHARED_LIB_PREFIX}{target}\""),
                &format!("\"{target}\""),
            );
            unit.text = unit.text.replace(
                &format!("'{SHARED_LIB_PREFIX}{target}'"),
                &format!("'{target}'"),
            );
            if !all.iter().any(|existing| existing == &target) {
                all.push(target);
            }
        }
    }
    all.sort();
    all
}

/// Load the referenced shared-library files from the snapshot and place
/// one copy beside each importing unit, rewriting `/.lib/` targets to the
/// bare subpath the baselines print. Support files are written to the temp
/// project for the loader only; they are never paired with case units, so
/// no facet echoes them or reports their diagnostics.
pub(crate) fn shared_lib_support_files(
    snapshot: &(impl SnapshotAssets + ?Sized),
    units: &mut [CaseUnit],
) -> Result<Vec<CaseUnit>> {
    let mut support = Vec::new();
    let mut seen = HashSet::new();
    let targets = rewrite_shared_lib_refs(units);
    for target in &targets {
        let bytes = read_verified_snapshot_asset(snapshot, &format!("{SHARED_LIB_ROOT}{target}"))?;
        let text = String::from_utf8_lossy(&bytes).into_owned();
        place_support_file(&mut support, &mut seen, units, target, &text);
    }
    Ok(support)
}

/// One copy of a shared-library file beside each importing unit.
fn place_support_file(
    support: &mut Vec<CaseUnit>,
    seen: &mut HashSet<String>,
    units: &[CaseUnit],
    target: &str,
    text: &str,
) {
    for unit in units {
        let dir = unit
            .virtual_path
            .rsplit_once('/')
            .map(|(dir, _)| dir)
            .unwrap_or("");
        let virtual_path = if dir.is_empty() {
            target.to_owned()
        } else {
            format!("{dir}/{target}")
        };
        if !seen.insert(virtual_path.clone()) {
            continue;
        }
        support.push(CaseUnit {
            virtual_path,
            display_name: target.to_owned(),
            text: text.to_owned(),
        });
    }
}

/// Group snapshot baseline index entries for the flat
/// `tests/baselines/reference/` store by `(stem, extension, suffix)`.
///
/// Key: `(stem, extension)` where extension is `errors.txt`/`types`/`symbols`;
/// value: `(suffix, logical_path)` where suffix is the `(opt=value)` group or
/// empty for the plain baseline.
pub type BaselineGroups = BTreeMap<(String, String), Vec<(String, String)>>;

/// Build the stem/suffix groups once from the snapshot index (flat entries
/// only; `reference/project/…` rows are excluded).
pub fn baseline_groups(index: &SuiteIndex) -> BaselineGroups {
    let mut groups: BaselineGroups = BTreeMap::new();
    for entry in index.entries.values() {
        let Some(file_name) = entry.logical_path.strip_prefix(BASELINE_REFERENCE_PREFIX) else {
            continue;
        };
        if file_name.contains('/') {
            continue;
        }
        let Some((stem, extension, suffix)) = split_baseline_file_name(file_name) else {
            continue;
        };
        groups
            .entry((stem.to_owned(), extension.to_owned()))
            .or_default()
            .push((suffix.to_owned(), entry.logical_path.clone()));
    }
    groups
}

/// Split `<stem>[(suffix)].<ext>`; returns `None` for unrecognized names.
fn split_baseline_file_name(file_name: &str) -> Option<(&str, &str, &str)> {
    let extensions = [
        ".errors.txt",
        ".trace.json",
        ".types",
        ".symbols",
        ".jsx",
        ".js.map",
        ".js",
    ];
    let extension = extensions
        .iter()
        .find(|extension| file_name.ends_with(*extension))?;
    let base = &file_name[..file_name.len() - extension.len()];
    if let Some(open) = base.find('(') {
        let suffix = &base[open..];
        if !suffix.ends_with(')') {
            return None;
        }
        Some((&base[..open], &extension[1..], suffix))
    } else {
        Some((base, &extension[1..], ""))
    }
}

/// Parse a `(opt=value,...)` baseline suffix and check whether it matches the
/// first-value compile options used for the current case.
fn suffix_matches_options(suffix: &str, compile_options: &[(String, String)]) -> bool {
    let Some(inner) = suffix.strip_prefix('(').and_then(|s| s.strip_suffix(')')) else {
        return suffix.is_empty();
    };
    if inner.is_empty() {
        return true;
    }
    let options: std::collections::HashMap<String, String> = compile_options
        .iter()
        .map(|(key, value)| (key.clone(), value.clone()))
        .collect();
    for part in inner.split(',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        let Some((key, value)) = part.split_once('=') else {
            return false;
        };
        let key = key.trim().to_ascii_lowercase();
        let value = value.trim().to_ascii_lowercase();
        let Some(compile_value) = options.get(&key) else {
            return false;
        };
        if compile_value.to_ascii_lowercase() != value {
            return false;
        }
    }
    true
}

/// The stem of a case logical path: basename minus extension, with `.d` kept
/// (`parserEnumDeclaration2.d.ts` ⇒ stem `parserEnumDeclaration2.d`).
pub fn case_stem(logical_path: &str) -> &str {
    let name = logical_path.rsplit('/').next().unwrap_or(logical_path);
    for suffix in [".tsx", ".ts", ".jsx", ".js", ".mts", ".cts", ".mjs", ".cjs"] {
        if let Some(stem) = name.strip_suffix(suffix) {
            return stem;
        }
    }
    name
}

/// The `tests/cases/<area>/` segment owning a harness logical path;
/// empty when the path carries no area (flat trees). Shared by the
/// facet samplers so baseline selection agrees on ownership.
#[must_use]
pub fn baseline_area(harness_logical: &str) -> &str {
    harness_logical
        .split("cases/")
        .nth(1)
        .and_then(|rest| rest.split('/').next())
        .unwrap_or("")
}

/// Resolve a `{stem}[ (variant)].{extension}` authority baseline file
/// under `base`, preferring the owning `area` directory when one stem
/// exists in several areas, then the variant matching the compile
/// options. Authority trees nest baselines one level down
/// (`reference/<area>/*`); the top level is scanned too.
#[must_use]
pub fn resolve_baseline_file(
    base: &Path,
    stem: &str,
    area: &str,
    extension: &str,
    pragmas: &CasePragmas,
) -> Option<std::path::PathBuf> {
    let area_dir = base.join(area);
    let mut dirs = Vec::new();
    if !area.is_empty() {
        dirs.push(area_dir.clone());
    }
    dirs.push(base.to_path_buf());
    if let Ok(entries) = fs::read_dir(base) {
        // `read_dir` order is filesystem-dependent: sort so the first
        // plain baseline found is deterministic across machines.
        let mut siblings: Vec<std::path::PathBuf> = entries
            .flatten()
            .map(|entry| entry.path())
            .filter(|path| path.is_dir() && path != &area_dir)
            .collect();
        siblings.sort();
        dirs.extend(siblings);
    }
    let plain_name = format!("{stem}.{extension}");
    let prefix = format!("{stem}(");
    let suffix_end = format!(").{extension}");
    let mut plain: Option<(std::path::PathBuf, bool)> = None;
    let mut variants: Vec<(String, std::path::PathBuf, bool)> = Vec::new();
    for dir in &dirs {
        let in_area = dir == &area_dir;
        let Ok(entries) = fs::read_dir(dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().to_string();
            if name == plain_name && plain.is_none() {
                plain = Some((entry.path(), in_area));
            } else if name.starts_with(&prefix) && name.ends_with(&suffix_end) {
                let suffix = &name[prefix.len()..name.len() - suffix_end.len()];
                variants.push((suffix.to_owned(), entry.path(), in_area));
            }
        }
        if plain.is_some() {
            break;
        }
    }
    let compile_options: Vec<(String, String)> = pragmas
        .options
        .iter()
        .filter_map(|(name, values)| values.first().map(|v| (name.clone(), v.clone())))
        .collect();
    if !compile_options.is_empty() {
        let matches: Vec<&(String, std::path::PathBuf, bool)> = variants
            .iter()
            .filter(|(suffix, _, _)| baseline_suffix_matches(suffix, &compile_options))
            .collect();
        // Baselines are per-case files: a same-stem variant in another
        // area belongs to another case (the twin precedent). When the
        // owning area holds any stem file, the stem is owned: only
        // owning variants may match, else the owning plain file covers
        // generic options, else there is no compatible authority. The
        // cross-area pool stays for unowned stems only. Specificity
        // ranks within the pool, then filename, then full path.
        let owned: Vec<&(String, std::path::PathBuf, bool)> = matches
            .iter()
            .filter(|candidate| candidate.2)
            .copied()
            .collect();
        let stem_owned = !owned.is_empty()
            || variants.iter().any(|candidate| candidate.2)
            || plain.as_ref().is_some_and(|(_, in_area)| *in_area);
        let pool_source = if owned.is_empty() {
            if stem_owned {
                return plain
                    .as_ref()
                    .filter(|(_, in_area)| *in_area)
                    .map(|(path, _)| path.clone());
            }
            matches
        } else {
            owned
        };
        if !pool_source.is_empty() {
            // Pool rows are (specificity, suffix, path).
            let mut pool: Vec<(usize, &str, &std::path::PathBuf)> = pool_source
                .iter()
                .map(|candidate| {
                    let specificity = candidate
                        .0
                        .split(',')
                        .filter(|part| part.contains('='))
                        .count();
                    (specificity, candidate.0.as_str(), &candidate.1)
                })
                .collect();
            pool.sort_by(|a, b| {
                b.0.cmp(&a.0)
                    .then_with(|| a.1.cmp(b.1))
                    .then_with(|| a.2.cmp(b.2))
            });
            return Some(pool[0].2.clone());
        }
    }
    if let Some((plain, _)) = plain {
        return Some(plain);
    }
    variants.sort_by(|a, b| b.2.cmp(&a.2).then_with(|| a.0.cmp(&b.0)));
    variants.into_iter().next().map(|(_, p, _)| p)
}

/// Whether a `(variant)` suffix selects the given compile options.
fn baseline_suffix_matches(suffix: &str, compile_options: &[(String, String)]) -> bool {
    if suffix.is_empty() {
        return true;
    }
    let options: HashMap<String, String> = compile_options
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    for part in suffix.split(',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        let Some((key, value)) = part.split_once('=') else {
            return false;
        };
        let key = key.trim().to_ascii_lowercase();
        let value = value.trim().to_ascii_lowercase();
        let Some(compile_value) = options.get(&key) else {
            return false;
        };
        if compile_value.to_ascii_lowercase() != value {
            return false;
        }
    }
    true
}
/// Resolve the `.errors.txt` baselines owned by one case, filtered to the
/// variant that matches the compile options actually used.
///
/// A baseline is owned when its first `//// [path] ////` marker names the
/// case's full logical path; a marker-less baseline is owned only when the
/// case is the stem's sole case input in the index. When variant baselines
/// exist (e.g. `(target=es5)`), only the variant matching the compile options
/// is selected; the plain baseline is used as a fallback when no variant matches.
pub fn resolve_errors_baselines(
    snapshot: &(impl SnapshotAssets + ?Sized),
    groups: &BaselineGroups,
    logical_path: &str,
    compile_options: &[(String, String)],
) -> Result<DiagnosticsBaselines> {
    let stem = case_stem(logical_path);
    let Some(candidates) = groups.get(&(stem.to_owned(), "errors.txt".to_owned())) else {
        return Ok(DiagnosticsBaselines::default());
    };
    let sole_input = case_inputs_with_stem(snapshot, stem) == [logical_path];
    let mut variants = Vec::new();
    let mut plain = Vec::new();
    let mut contents = BTreeMap::new();
    for (suffix, path) in candidates {
        let (owner, text) = baseline_owner(snapshot, path)?;
        contents.insert(path.clone(), text);
        let owned = match owner {
            Some(owner) => owner == logical_path,
            None => sole_input,
        };
        if !owned {
            continue;
        }
        if suffix.is_empty() {
            plain.push(path.clone());
        } else if suffix_matches_options(suffix, compile_options) {
            variants.push(path.clone());
        }
    }
    let mut owned = if !variants.is_empty() {
        variants
    } else {
        plain
    };
    owned.sort();
    owned.dedup();
    Ok(DiagnosticsBaselines { owned, contents })
}

/// The case inputs (compiler/conformance/project/projects only matter here)
/// whose stem equals `stem`.
fn case_inputs_with_stem<'a>(
    snapshot: &'a (impl SnapshotAssets + ?Sized),
    stem: &str,
) -> Vec<&'a str> {
    snapshot
        .index()
        .entries
        .values()
        .filter(|entry| {
            matches!(entry.asset_kind, crate::suite::AssetKind::CaseInput)
                && case_stem(&entry.logical_path) == stem
        })
        .map(|entry| entry.logical_path.as_str())
        .collect()
}

/// The first `//// [path] ////` marker of a baseline blob, if any.
fn baseline_owner(
    snapshot: &(impl SnapshotAssets + ?Sized),
    logical_path: &str,
) -> Result<(Option<String>, String)> {
    let bytes = read_verified_snapshot_asset(snapshot, logical_path)?;
    let text = String::from_utf8_lossy(&bytes).into_owned();
    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("//// [") {
            return Ok((
                rest.split_once("] ////")
                    .map(|(path, _)| path.trim().to_owned()),
                text,
            ));
        }
        if !line.is_empty() {
            return Ok((None, text));
        }
    }
    Ok((None, text))
}

/// Parse an `.errors.txt` baseline into file-anchored and global rows.
///
/// Strict row grammar: `^<file>(<l>,<c>): (error|warning) TS\d+: <msg>` and
/// `^(error|warning) TS\d+: <msg>` for file-less globals. `!!!` summaries,
/// `====` source dumps, caret lines, and blank separators are skipped.
pub fn parse_errors_baseline(text: &str) -> ErrorsBaseline {
    let mut baseline = ErrorsBaseline::default();
    for line in text.lines() {
        let line = line.strip_suffix('\r').unwrap_or(line);
        if line.is_empty() || line.starts_with(' ') || line.starts_with('\t') {
            // Source dumps and caret lines are indented.
            continue;
        }
        if line.starts_with("!!!") || line.starts_with("====") {
            continue;
        }
        if let Some(diagnostic) = parse_file_row(line) {
            baseline.diagnostics.push(diagnostic);
        } else if let Some(global) = parse_global_row(line) {
            baseline.globals.push(global);
        }
    }
    baseline
}

/// Parse `file(l,c): (error|warning) TS\d+: message`.
fn parse_file_row(line: &str) -> Option<ErrorsDiagnostic> {
    let open = line.find('(')?;
    let (unit, rest) = line.split_at(open);
    let unit = unit.trim();
    if unit.is_empty() {
        return None;
    }
    let rest = rest.strip_prefix('(')?;
    let (position, rest) = rest.split_once("): ")?;
    let (line_no, character) = position.split_once(',')?;
    let line_no: u32 = line_no.trim().parse().ok()?;
    let character: u32 = character.trim().parse().ok()?;
    let (category, code, message) = parse_category_code(rest)?;
    Some(ErrorsDiagnostic {
        unit: unit.to_owned(),
        line: line_no,
        character: character.saturating_sub(1),
        category,
        code,
        message,
    })
}

/// Parse `(error|warning) TS\d+: message` (no file anchor).
fn parse_global_row(line: &str) -> Option<GlobalDiagnostic> {
    let (_, code, message) = parse_category_code(line)?;
    Some(GlobalDiagnostic { code, message })
}

/// Parse the shared `<category> TS<code>: <message>` tail.
fn parse_category_code(rest: &str) -> Option<(String, String, String)> {
    let (category, rest) = rest.split_once(' ')?;
    if !matches!(category, "error" | "warning") {
        return None;
    }
    let (code, message) = rest.split_once(": ")?;
    let digits = code.strip_prefix("TS")?;
    if digits.is_empty() || !digits.chars().all(|ch| ch.is_ascii_digit()) {
        return None;
    }
    Some((category.to_owned(), code.to_owned(), message.to_owned()))
}

/// Compile one materialized case (all units) into its checked product.
///
/// Materializes the units under a fresh temp root, loads the entry unit
/// through [`ProgramLoader`], and runs [`compile_program_frontend`] in check
/// mode. All units are written even though the loader only reads the ones
/// reachable from the entry's module graph, so `.d.ts`/library-style units
/// Build a JSONC `tsconfig.json` source from a case's `@option` pragmas.
/// Upstream cases default to `strict: true` unless the case explicitly says
/// otherwise, so the harness supplies that default when no `@strict` directive
/// is present. Only the first value of each comma-split option is used.
fn build_tsconfig(pragmas: &CasePragmas) -> String {
    let mut options: Vec<(String, String)> = Vec::new();
    for (name, values) in &pragmas.options {
        let Some(value) = values.first() else {
            continue;
        };
        let json = match name.as_str() {
            "strict"
            | "strictnullchecks"
            | "noimplicitany"
            | "allowjs"
            | "checkjs"
            | "resolvejsonmodule"
            | "noemit"
            | "noemithelpers"
            | "removecomments"
            | "declaration"
            | "alwaysstrict"
            | "exactoptionalpropertytypes"
            | "nouncheckedindexedaccess"
            | "strictpropertyinitialization"
            | "incremental"
            | "composite"
            | "emitdeclarationonly"
            | "sourcemap"
            | "declarationmap"
            | "usedefineforclassfields"
            | "importhelpers"
            | "experimentaldecorators"
            | "emitdecoratormetadata"
            | "esmoduleinterop" => value.eq_ignore_ascii_case("true").to_string(),
            "lib" => {
                let items: Vec<String> = values
                    .iter()
                    .flat_map(|v| v.split(','))
                    .map(|s| s.trim())
                    .filter(|s| !s.is_empty())
                    .map(|s| format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")))
                    .collect();
                format!("[{}]", items.join(", "))
            }
            "typeroots" => {
                let items: Vec<String> = values
                    .iter()
                    .flat_map(|v| v.split(','))
                    .map(|s| s.trim())
                    .filter(|s| !s.is_empty())
                    .map(|s| s.strip_prefix('/').unwrap_or(s))
                    .map(|s| format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")))
                    .collect();
                format!("[{}]", items.join(", "))
            }
            _ => format!("\"{}\"", value.replace('\\', "\\\\").replace('"', "\\\"")),
        };
        let key = match name.as_str() {
            "typeroots" => "typeRoots",
            "strictnullchecks" => "strictNullChecks",
            "noimplicitany" => "noImplicitAny",
            "allowjs" => "allowJs",
            "checkjs" => "checkJs",
            "resolvejsonmodule" => "resolveJsonModule",
            "moduleresolution" => "moduleResolution",
            "noemithelpers" => "noEmitHelpers",
            "removecomments" => "removeComments",
            "noemit" => "noEmit",
            "alwaysstrict" => "alwaysStrict",
            "usedefineforclassfields" => "useDefineForClassFields",
            "importhelpers" => "importHelpers",
            "esmoduleinterop" => "esModuleInterop",
            "experimentaldecorators" => "experimentalDecorators",
            "emitdecoratormetadata" => "emitDecoratorMetadata",
            "verbatimmodulesyntax" => "verbatimModuleSyntax",
            "exactoptionalpropertytypes" => "exactOptionalPropertyTypes",
            "nouncheckedindexedaccess" => "noUncheckedIndexedAccess",
            "strictpropertyinitialization" => "strictPropertyInitialization",
            "emitdeclarationonly" => "emitDeclarationOnly",
            "sourcemap" => "sourceMap",
            "declarationmap" => "declarationMap",
            "tsbuildinfofile" => "tsBuildInfoFile",
            "outfile" => "outFile",
            "outdir" => "outDir",
            "declarationdir" => "declarationDir",
            _ => name.as_str(),
        };
        options.push((key.to_owned(), json));
    }
    if !options.iter().any(|(name, _)| name == "strict") {
        options.push(("strict".to_owned(), "true".to_owned()));
    }
    // The authority harness pins `alwaysStrict` on rather than deriving it from
    // `strict`, which is why 2456 baselines declaring `@strict: false` still
    // carry a `"use strict"` prologue. Leaving it unset lets the compiler fall
    // back to `strict` and drops the prologue on every one of them.
    if !options.iter().any(|(name, _)| name == "alwaysStrict") {
        options.push(("alwaysStrict".to_owned(), "true".to_owned()));
    }
    let compiler_options = options
        .iter()
        .map(|(name, value)| format!("\"{name}\": {value}"))
        .collect::<Vec<_>>()
        .join(", ");
    let mut source = String::new();
    source.push('{');
    source.push_str("\"compilerOptions\": {");
    source.push_str(&compiler_options);
    source.push_str("}}");
    source
}

/// Harness virtual roots a case may reference: `/.lib/*` maps to the
/// authority `tests/lib` tree and `/.ts/*` maps to the pinned TypeScript
/// package output, mirroring tsc's own harness mounts. Only quoted
/// specifier prefixes count; anything containing `..` is ignored so a
/// reference can never escape its mount root.
fn mount_specifiers_in(text: &str) -> Vec<String> {
    let bytes = text.as_bytes();
    let mut found = Vec::new();
    let mut searched = 0;
    while searched < text.len() {
        let rest = &text[searched..];
        let offset = rest
            .find("/.lib/")
            .into_iter()
            .chain(rest.find("/.ts/"))
            .min();
        let Some(offset) = offset else {
            break;
        };
        let start = searched + offset;
        searched = start + 1;
        if !matches!(
            bytes.get(start.saturating_sub(1)).copied(),
            Some(b'\'') | Some(b'"')
        ) {
            continue;
        }
        let quote = bytes[start - 1] as char;
        let after = &text[start + 1..];
        let Some(length) = after.find(quote) else {
            break;
        };
        let specifier = &text[start..start + 1 + length];
        if !specifier.contains("..") && !found.iter().any(|existing| existing == specifier) {
            found.push(specifier.to_owned());
        }
        searched = start + 1 + length + 1;
    }
    found
}

/// Locates the workspace checkout this crate was built from.
fn workspace_root() -> Option<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    root.is_dir().then_some(root)
}

/// Locates the pinned authority tree: an explicit `BAMTS_AUTHORITY_ROOT`
/// first, else the workspace checkout's `target/authority` copy, else the
/// in-repo `.references` testdata the authority copy is fetched from. The
/// last fallback keeps `cargo test` hermetic: a bare checkout has no
/// `target/authority` tree (it needs the network), yet the served `tests/lib`
/// files are identical in both places. Missing trees mean missing mounts,
/// and the case compiles exactly as before.
fn mount_authority_root() -> Option<PathBuf> {
    if let Ok(root) = std::env::var("BAMTS_AUTHORITY_ROOT") {
        let path = PathBuf::from(root);
        if path.is_dir() {
            return Some(path);
        }
    }
    if let Some(root) = workspace_root() {
        let candidate = root.join("target/authority/typescript-7.0.2-tests");
        if candidate.is_dir() {
            return Some(candidate);
        }
    }
    reference_testdata_root()
}

/// The in-repo `.references` TypeScript testdata, found by walking up from
/// this crate so worktree checkouts resolve it too.
fn reference_testdata_root() -> Option<PathBuf> {
    let mut directory = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        let candidate = directory.join(".references/typescript/tsc/testdata");
        if candidate.join("tests/lib").is_dir() {
            return Some(candidate);
        }
        if !directory.pop() {
            return None;
        }
    }
}

/// Copies the harness mount files a case's units reference into the temp
/// root, preserving the virtual layout so the generated `paths` mapping
/// resolves them. `/.lib/*` comes from the authority `tests/lib` tree and
/// `/.ts/*` from the pinned TypeScript package output. Reports which
/// virtual roots were served; missing sources stay unmapped and the case
/// compiles exactly as before.
fn write_mount_files(root: &Path, units: &[CaseUnit]) -> Vec<&'static str> {
    let specifiers: Vec<String> = units
        .iter()
        .flat_map(|unit| mount_specifiers_in(&unit.text))
        .collect();
    if specifiers.is_empty() {
        return Vec::new();
    }
    let authority = mount_authority_root();
    let package = workspace_root().and_then(|root| {
        let candidate = root.join("node_modules/typescript/lib");
        candidate.is_dir().then_some(candidate)
    });
    let mut served = Vec::new();
    for specifier in &specifiers {
        let (prefix, source) = if let Some(rest) = specifier.strip_prefix("/.lib/") {
            (
                "/.lib/",
                authority
                    .as_ref()
                    .map(|root| root.join("tests/lib").join(rest)),
            )
        } else if let Some(rest) = specifier.strip_prefix("/.ts/") {
            ("/.ts/", package.as_ref().map(|root| root.join(rest)))
        } else {
            continue;
        };
        let Some(source) = source else {
            continue;
        };
        let Ok(bytes) = fs::read(&source) else {
            continue;
        };
        let target = root.join(&specifier[1..]);
        let Some(parent) = target.parent() else {
            continue;
        };
        if fs::create_dir_all(parent).is_err() || fs::write(&target, bytes).is_err() {
            continue;
        }
        if !served.contains(&prefix) {
            served.push(prefix);
        }
    }
    served
}

/// Returns a copy of `base` with `key` set to `value`, preserving the
/// position of an existing key and appending a new one. The shared
/// primitive for layering generated, in-case, and harness configuration
/// without ever dropping a mapping the case declares itself.
fn object_set(base: &JsonObject, key: &str, value: JsonValue) -> JsonObject {
    let mut entries = Vec::with_capacity(base.entries().len() + 1);
    let mut replaced = false;
    for (existing, current) in base.entries() {
        if existing.as_ref() == key {
            entries.push((Arc::clone(existing), value.clone()));
            replaced = true;
        } else {
            entries.push((Arc::clone(existing), current.clone()));
        }
    }
    if !replaced {
        entries.push((Arc::from(key), value));
    }
    JsonObject::from_entries(entries)
}

/// Merges harness mount `paths` mappings into a generated tsconfig
/// document. An existing `paths` entry keeps its own mapping, so a case
/// that maps its own specifiers never loses them to the mounts; mounts
/// only fill gaps. Anything unparseable passes through untouched.
fn inject_mount_paths(config_source: String, served: &[&str]) -> String {
    if served.is_empty() {
        return config_source;
    }
    let Ok(JsonValue::Object(root)) = parse_jsonc(&config_source) else {
        return config_source;
    };
    let Some(compiler) = root.get("compilerOptions").and_then(JsonValue::as_object) else {
        return config_source;
    };
    let mut paths = match compiler.get("paths").and_then(JsonValue::as_object) {
        Some(existing) => JsonObject::from_entries(
            existing
                .entries()
                .iter()
                .map(|(key, value)| (Arc::clone(key), value.clone()))
                .collect(),
        ),
        None => JsonObject::from_entries(Vec::new()),
    };
    for prefix in served {
        let mut pattern = String::from(*prefix);
        pattern.push('*');
        if paths.get(&pattern).is_some() {
            continue;
        }
        let target = format!("./{stem}*", stem = &prefix[1..]);
        paths = object_set(
            &paths,
            &pattern,
            JsonValue::Array(Arc::from(vec![JsonValue::String(Arc::from(
                target.as_str(),
            ))])),
        );
    }
    let compiler = object_set(compiler, "paths", JsonValue::Object(paths));
    let root = object_set(&root, "compilerOptions", JsonValue::Object(compiler));
    canonical_json(&JsonValue::Object(root))
}
pub fn compile_case(
    units: &[CaseUnit],
    entry_name: &str,
) -> std::result::Result<CheckedCase, CaseCompileError> {
    compile_case_with_pragmas(units, entry_name, &CasePragmas::default())
}

pub fn compile_case_with_pragmas(
    units: &[CaseUnit],
    entry_name: &str,
    pragmas: &CasePragmas,
) -> std::result::Result<CheckedCase, CaseCompileError> {
    compile_case_with_support(units, entry_name, pragmas, &[])
}

pub fn compile_case_with_support(
    units: &[CaseUnit],
    entry_name: &str,
    pragmas: &CasePragmas,
    support: &[CaseUnit],
) -> std::result::Result<CheckedCase, CaseCompileError> {
    compile_case_frontend_with_support(units, entry_name, pragmas, FrontendMode::Check, support)
}

pub fn compile_case_frontend(
    units: &[CaseUnit],
    entry_name: &str,
    pragmas: &CasePragmas,
    mode: FrontendMode,
) -> std::result::Result<CheckedCase, CaseCompileError> {
    compile_case_frontend_with_support(units, entry_name, pragmas, mode, &[])
}

pub fn compile_case_frontend_with_support(
    units: &[CaseUnit],
    entry_name: &str,
    pragmas: &CasePragmas,
    mode: FrontendMode,
    support: &[CaseUnit],
) -> std::result::Result<CheckedCase, CaseCompileError> {
    let temp = TempDir::new("bamts-check-cell")
        .map_err(|error| CaseCompileError::Load(format!("temp root: {error}")))?;
    for unit in units {
        if unit.text.len() > bamts_compiler::source::MAX_SOURCE_BYTES {
            return Err(CaseCompileError::SourceBound(format!(
                "unit `{}` exceeds the {}-byte frontend source bound",
                unit.virtual_path,
                bamts_compiler::source::MAX_SOURCE_BYTES
            )));
        }
        let path = temp.path().join(&unit.virtual_path);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| CaseCompileError::Load(format!("unit dir: {error}")))?;
        }
        fs::write(&path, &unit.text)
            .map_err(|error| CaseCompileError::Load(format!("unit write: {error}")))?;
    }
    let served = write_mount_files(temp.path(), units);
    for file in support {
        let path = temp.path().join(&file.virtual_path);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| CaseCompileError::Load(format!("support dir: {error}")))?;
        }
        fs::write(&path, &file.text)
            .map_err(|error| CaseCompileError::Load(format!("support write: {error}")))?;
    }
    // Upstream TypeScript test programs compile every unit together, not just
    // the ones reachable from a single entry. Create a synthetic entrypoint that
    // imports every unit so the S2 harness observes the same program shape.
    const ENTRY: &str = "__bamts_check_entry__.ts";
    let mut entry_source = String::new();
    for (index, unit) in units.iter().enumerate() {
        let specifier = unit.virtual_path.replace('\\', "/");
        if is_check_cell_declaration_path(&specifier) {
            entry_source.push_str(&format!(
                "import type * as _bamts_entry_{index} from \"./{specifier}\";\n"
            ));
        } else {
            entry_source.push_str(&format!("import \"./{specifier}\";\n"));
        }
    }
    fs::write(temp.path().join(ENTRY), entry_source)
        .map_err(|error| CaseCompileError::Load(format!("entry write: {error}")))?;
    let compile = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let root = ProjectRoot::new(temp.path())
            .map_err(|error| CaseCompileError::Load(format!("project root: {error}")))?;
        let config_source = build_tsconfig(pragmas);
        let config_source = inject_mount_paths(config_source, &served);
        let config = ProjectConfig::parse(&root, temp.path().join("tsconfig.json"), &config_source)
            .map_err(|error| CaseCompileError::Load(format!("config: {error}")))?;
        let options = config.options().clone();
        let loader = ProgramLoader::new(&root, config.options())
            .map_err(|error| CaseCompileError::Load(format!("loader: {error}")))?
            .tolerating_unresolved_imports();
        let program = loader
            .load(Path::new(ENTRY))
            .map_err(|error| CaseCompileError::Load(error.to_string()))?;
        let output = compile_program_frontend(&program, mode);
        Ok::<_, CaseCompileError>((program, output, options))
    }));
    let (program, output, options) = match compile {
        Ok(Ok(parts)) => parts,
        Ok(Err(error)) => return Err(error),
        Err(_) => {
            return Err(CaseCompileError::Panic(
                "compiler panicked while checking the case".to_owned(),
            ));
        }
    };
    let pairs = pair_units_with_modules(units, temp.path(), &program);
    // The synthetic entry is not part of the case, so it is intentionally absent
    // from `pairs`. Any diagnostics it produced are also ignored.
    Ok(CheckedCase {
        units: pairs,
        entry: entry_name.to_owned(),
        output,
        program,
        options,
        emit_directory: full_emit_directory(pragmas),
        no_resolve: pragma_enabled(pragmas, "noresolve"),
    })
}

/// Match each unit to its resolved module by canonical path. The loader
/// canonicalizes every module path under the confined root, so unit paths are
/// canonicalized the same way before comparison.
fn pair_units_with_modules(
    units: &[CaseUnit],
    root: &Path,
    program: &ResolvedProgram,
) -> Vec<(CaseUnit, Option<usize>)> {
    units
        .iter()
        .map(|unit| {
            let canonical = canonicalize(root.join(&unit.virtual_path)).ok();
            let index = canonical.and_then(|canonical| {
                program
                    .modules()
                    .iter()
                    .position(|module| module.path() == canonical)
            });
            (unit.clone(), index)
        })
        .collect()
}

/// The virtual path of the unit that acts as the compile entry: the first
/// split unit (single-unit cases and cases whose first `@filename` names the
/// case all lead with the entry unit).
pub fn entry_virtual_path(logical_path: &str, units: &[CaseUnit]) -> String {
    let _ = logical_path;
    units
        .first()
        .map(|unit| unit.virtual_path.clone())
        .unwrap_or_else(|| {
            logical_path
                .rsplit('/')
                .next()
                .unwrap_or(logical_path)
                .to_owned()
        })
}

/// Basename of a virtual path (`foo/b.ts` ⇒ `b.ts`), matching the unit name a
/// baseline prints so both sides of the diagnostics comparator agree.
fn unit_basename(virtual_path: &str) -> String {
    virtual_path
        .rsplit('/')
        .next()
        .unwrap_or(virtual_path)
        .to_owned()
}

/// Flatten a checked case into the diagnostics comparator's actual side.
///
/// Positions are 1-based line / 0-based UTF-16 character over the unit text;
/// BAMTS codes carry their `BAMTS-*` spelling for the code map, category
/// follows `error` vs `warning`, and severity mirrors the compiler's
/// error/warning split. The unit basename is carried so a cross-unit position
/// collision cannot pass the check.
pub fn collect_facet_diagnostics(case: &CheckedCase) -> Vec<FacetDiagnostic> {
    let mut diagnostics = Vec::new();
    for (unit, output) in case.reached_units() {
        let unit_name = unit_basename(&unit.virtual_path);
        let source = SourceText::new(unit.text.clone())
            .unwrap_or_else(|_| panic!("unit text was bound-checked before compile"));
        for diagnostic in output.diagnostics() {
            let (line, character) = source
                .line_column(diagnostic.range().start())
                .map(|(line, character)| ((line + 1) as u32, character as u32))
                .unwrap_or((0, 0));
            let severity = match diagnostic.severity() {
                DiagnosticSeverity::Error => FacetSeverity::Error,
                DiagnosticSeverity::Warning => FacetSeverity::Warning,
            };
            let category = match diagnostic.severity() {
                DiagnosticSeverity::Error => DiagnosticCategory::Error,
                DiagnosticSeverity::Warning => DiagnosticCategory::Warning,
            };
            diagnostics.push(FacetDiagnostic {
                unit: unit_name.clone(),
                position: SourcePosition { line, character },
                category,
                severity,
                code: diagnostic.code().as_str().to_owned(),
            });
        }
    }
    diagnostics
}

/// Union the owned `.errors.txt` baselines into the comparator's expected
/// side. File-less global rows stay out: the compiler has no global-diagnostic
/// observation yet (they name option-deprecation semantics owned by S7/S5).
/// The unit basename printed by the baseline is carried through so a
/// cross-unit position collision cannot pass the check.
pub fn expected_facet_diagnostics(
    baselines: &DiagnosticsBaselines,
) -> Result<Vec<FacetDiagnostic>> {
    let mut expected = Vec::new();
    for path in &baselines.owned {
        let Some(text) = baselines.contents.get(path) else {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!("diagnostics baseline `{path}` was selected without retained bytes"),
            ));
        };
        let parsed = parse_errors_baseline(text);
        for row in parsed.diagnostics {
            let category = if row.category == "warning" {
                DiagnosticCategory::Warning
            } else {
                DiagnosticCategory::Error
            };
            let severity = if row.category == "warning" {
                FacetSeverity::Warning
            } else {
                FacetSeverity::Error
            };
            expected.push(FacetDiagnostic {
                unit: row.unit,
                position: SourcePosition {
                    line: row.line,
                    character: row.character,
                },
                category,
                severity,
                code: row.code,
            });
        }
    }
    Ok(expected)
}

/// Run the diagnostics comparison for one compiled case.
pub fn check_diagnostics(
    ctx: &CheckContext,
    case: &CheckedCase,
    baselines: &DiagnosticsBaselines,
) -> Result<DiagnosticsOutcome> {
    let mut actual = collect_facet_diagnostics(case);
    actual.retain(|diagnostic| !diagnostic.code.starts_with("BAMTS-W"));
    let expected = expected_facet_diagnostics(baselines)?;
    let verdict = compare_diagnostics(&expected, &actual, &ctx.code_map);
    Ok(DiagnosticsOutcome {
        actual,
        expected,
        verdict,
    })
}

/// Execute the S2 `diagnostics` observation for one planned cell.
///
/// Failure-class discipline mirrors `execute_parse_check`: compile failures
/// are `FAIL_BEHAVIOR` (loader/bound) or `CRASH` (panic); comparator `Fail`
/// is `FAIL_DIAGNOSTIC`; `Unproven` is an oracle-side `HARNESS_ERROR`; a pass
/// records the emitted/expected counts in the detail.
pub(crate) fn execute_diagnostics_check(
    ctx: &CheckContext,
    snapshot: &(impl SnapshotAssets + ?Sized),
    plan: &PlannedCell,
    index_entry: &IndexEntry,
) -> Result<CellResult> {
    let text = read_case_text(snapshot, index_entry)?;
    let pragmas = parse_case_pragmas(&text);
    Ok(cell_result(
        plan,
        observe_diagnostics(ctx, snapshot, index_entry, &text, &pragmas),
    ))
}

fn compile_option_pairs(pragmas: &CasePragmas) -> Vec<(String, String)> {
    pragmas
        .options
        .iter()
        .filter_map(|(name, values)| values.first().map(|value| (name.clone(), value.clone())))
        .collect()
}

fn read_case_text(
    snapshot: &(impl SnapshotAssets + ?Sized),
    index_entry: &IndexEntry,
) -> Result<String> {
    let bytes = read_verified_snapshot_asset(snapshot, &index_entry.logical_path)?;
    Ok(decode_case_source(&bytes))
}

fn compile_failure_observation(error: CaseCompileError) -> CompilerCheckObservation {
    let detail = match &error {
        CaseCompileError::Load(detail)
        | CaseCompileError::SourceBound(detail)
        | CaseCompileError::Panic(detail) => detail.clone(),
    };
    CompilerCheckObservation {
        class: error.failure_class(),
        detail,
        artifact: None,
    }
}

fn cell_result(plan: &PlannedCell, observation: CompilerCheckObservation) -> CellResult {
    CellResult {
        entry_id: plan.entry.id.clone(),
        facet: plan.entry.facet,
        backend: plan.backend,
        class: observation.class,
        detail: observation.detail,
    }
}

/// Run the diagnostics comparator against the selected pragma variation.
pub(crate) fn observe_diagnostics(
    ctx: &CheckContext,
    snapshot: &(impl SnapshotAssets + ?Sized),
    index_entry: &IndexEntry,
    text: &str,
    pragmas: &CasePragmas,
) -> CompilerCheckObservation {
    let mut units = split_case_units(&index_entry.logical_path, text);
    let support = match shared_lib_support_files(snapshot, &mut units) {
        Ok(support) => support,
        Err(error) => {
            return CompilerCheckObservation {
                class: FailureClass::HarnessError,
                detail: error.to_string(),
                artifact: None,
            };
        }
    };
    let entry = entry_virtual_path(&index_entry.logical_path, &units);
    let compile_options = compile_option_pairs(pragmas);
    let baselines = match resolve_errors_baselines(
        snapshot,
        &ctx.baseline_groups,
        &index_entry.logical_path,
        &compile_options,
    ) {
        Ok(baselines) => baselines,
        Err(error) => {
            return CompilerCheckObservation {
                class: FailureClass::HarnessError,
                detail: error.to_string(),
                artifact: None,
            };
        }
    };
    match compile_case_with_support(&units, &entry, pragmas, &support) {
        Err(error) => compile_failure_observation(error),
        Ok(case) => {
            let outcome = match check_diagnostics(ctx, &case, &baselines) {
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
                    detail: format!(
                        "diagnostic parity: {} expected, {} emitted",
                        outcome.expected.len(),
                        outcome.actual.len()
                    ),
                    artifact: serde_json::to_vec(&outcome.actual).ok(),
                },
                FacetVerdict::Fail { reason } => CompilerCheckObservation {
                    class: FailureClass::FailDiagnostic,
                    detail: reason,
                    artifact: None,
                },
                FacetVerdict::Unproven { reason } => CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: format!("diagnostics oracle could not prove parity: {reason}"),
                    artifact: None,
                },
            }
        }
    }
}

/// Index-only baseline-ownership view for U2.8 S2 `types` classification.
///
/// The classifier (`build_classified_ledger`) has the index but not the blob
/// store, so ownership is decided from index facts alone: a compiler /
/// conformance input owns a `.types` baseline when one exists for its stem and
/// it is the sole case input carrying that stem. Duplicate stems (which need a
/// blob `//// [path] ////` marker to disambiguate) and stems with no `.types`
/// baseline (`APISample_*`, `@noTypesAndSymbols`) are therefore excluded.
pub struct S2Classification {
    /// Stems that have at least one `.types` baseline blob.
    types_stems: HashSet<String>,
    /// Stems that have at least one `.symbols` baseline blob.
    symbols_stems: HashSet<String>,
    /// Case-input count per stem (a duplicate stem has count > 1).
    stem_case_counts: HashMap<String, usize>,
}

impl S2Classification {
    /// Build the index-only ownership lookups once per classification pass.
    #[must_use]
    pub fn from_index(index: &SuiteIndex) -> Self {
        let mut types_stems = HashSet::new();
        let mut symbols_stems = HashSet::new();
        let mut stem_case_counts: HashMap<String, usize> = HashMap::new();
        for entry in index.entries.values() {
            match entry.asset_kind {
                crate::suite::AssetKind::CaseInput => {
                    *stem_case_counts
                        .entry(case_stem(&entry.logical_path).to_owned())
                        .or_default() += 1;
                }
                crate::suite::AssetKind::BaselineFacet => {
                    let Some(name) = entry.logical_path.strip_prefix(BASELINE_REFERENCE_PREFIX)
                    else {
                        continue;
                    };
                    if name.contains('/') {
                        continue;
                    }
                    match split_baseline_file_name(name) {
                        Some((stem, "types", _)) => {
                            types_stems.insert(stem.to_owned());
                        }
                        Some((stem, "symbols", _)) => {
                            symbols_stems.insert(stem.to_owned());
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        Self {
            types_stems,
            symbols_stems,
            stem_case_counts,
        }
    }

    /// Whether a compiler/conformance input uniquely owns a `.types` baseline.
    #[must_use]
    pub fn owns_types_baseline(&self, input: &str) -> bool {
        let stem = case_stem(input);
        self.types_stems.contains(stem) && self.stem_case_counts.get(stem).copied() == Some(1)
    }

    /// Whether a compiler/conformance input uniquely owns a `.symbols`
    /// baseline (sole case input carrying the stem, per the U2.8
    /// duplicate-stem disambiguation rule).
    #[must_use]
    pub fn owns_symbols_baseline(&self, input: &str) -> bool {
        let stem = case_stem(input);
        self.symbols_stems.contains(stem) && self.stem_case_counts.get(stem).copied() == Some(1)
    }
}

/// One `>display : type` record plus its underline, anchored to a source line.
struct TypeAnnotation {
    start: usize,
    end: usize,
    line: usize,
    display: String,
    rendered: String,
    caret: bool,
    blanks: Vec<(usize, usize)>,
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

/// Whether a unit name is a project-config file (`tsconfig.json` /
/// `jsconfig.json`). Upstream parses those as configuration, never as
/// program sources, so no `.types` baseline has a section for either;
/// data `.json` inputs (`b.json`, `package.json`) do get sections with
/// records.
fn is_config_unit_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    matches!(
        lower.rsplit('/').next(),
        Some("tsconfig.json") | Some("jsconfig.json")
    )
}

/// Collapse records with the identical identity tuple (start, end, display,
/// rendered): the binder can push the same (range, type) pair from both its
/// symbol and expression indexes, and upstream emits each unique (position,
/// display, type) triple once. Sort by the identity key, dedup consecutive,
/// then re-sort into the upstream order (by start, outer node before inner
/// on ties).
fn dedup_type_records(mut records: Vec<TypeAnnotation>) -> Vec<TypeAnnotation> {
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

fn writes_caret(
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

fn slice_source(source: &SourceText, range: TextRange) -> String {
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
fn collapse_whitespace(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The verdict of one types check cell.
#[derive(Debug, Clone)]
pub struct TypesOutcome {
    /// The emitted `.types` document.
    pub emitted: String,
    /// The comparator verdict against the owned baseline.
    pub verdict: FacetVerdict,
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

fn resolve_stem_baseline(
    groups: &BaselineGroups,
    logical_path: &str,
    extension: &str,
    compile_options: &[(String, String)],
) -> Result<Option<String>> {
    let stem = case_stem(logical_path);
    let Some(candidates) = groups.get(&(stem.to_owned(), extension.to_owned())) else {
        return Ok(None);
    };
    if !compile_options.is_empty() {
        let matches: Vec<_> = candidates
            .iter()
            .filter(|(suffix, _)| {
                !suffix.is_empty() && suffix_matches_options(suffix, compile_options)
            })
            .collect();
        if matches.len() > 1 {
            return Err(VerificationError::new(
                ErrorCode::Duplicate,
                format!("ambiguous `{extension}` baseline selection for `{logical_path}`"),
            ));
        }
        if let Some((_, path)) = matches.first() {
            return Ok(Some((*path).clone()));
        }
    }
    let plains: Vec<_> = candidates
        .iter()
        .filter(|(suffix, _)| suffix.is_empty())
        .collect();
    if plains.len() > 1 {
        return Err(VerificationError::new(
            ErrorCode::Duplicate,
            format!("duplicate plain `{extension}` baselines for `{logical_path}`"),
        ));
    }
    if let Some((_, path)) = plains.first() {
        return Ok(Some((*path).clone()));
    }
    Ok(candidates
        .iter()
        .min_by(|left, right| left.0.cmp(&right.0))
        .map(|(_, path)| path.clone()))
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

/// Run the javascript emit comparator against the selected pragma variation.
pub(crate) fn observe_javascript(
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
        match resolve_stem_baseline(groups, &index_entry.logical_path, "js", &compile_options) {
            Ok(path) => path,
            Err(error) => {
                return CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: error.to_string(),
                    artifact: None,
                };
            }
        };
    match compile_case_frontend(&units, &entry, pragmas, FrontendMode::JavaScript) {
        Err(error) => compile_failure_observation(error),
        Ok(case) => {
            let Some(baseline_path) = baseline_path else {
                return match emit_javascript_baseline(&case, &index_entry.logical_path) {
                    Err(detail) if detail == NO_JAVASCRIPT_OUTPUT => CompilerCheckObservation {
                        class: FailureClass::Pass,
                        detail: "no javascript output and no javascript baseline".to_owned(),
                        artifact: Some(Vec::new()),
                    },
                    _ => CompilerCheckObservation {
                        class: FailureClass::HarnessError,
                        detail: "classification/execution drift: no owned `.js` baseline"
                            .to_owned(),
                        artifact: None,
                    },
                };
            };
            let emitted = match emit_javascript_baseline(&case, &index_entry.logical_path) {
                Ok(emitted) => emitted,
                Err(detail) => {
                    return CompilerCheckObservation {
                        class: FailureClass::FailBehavior,
                        detail,
                        artifact: None,
                    };
                }
            };
            let bytes = match read_verified_snapshot_asset(snapshot, &baseline_path) {
                Ok(bytes) => bytes,
                Err(error) => {
                    return CompilerCheckObservation {
                        class: FailureClass::HarnessError,
                        detail: error.to_string(),
                        artifact: None,
                    };
                }
            };
            let expected = String::from_utf8_lossy(&bytes).into_owned();
            match compare_js_emit(&expected, &emitted) {
                FacetVerdict::Pass => CompilerCheckObservation {
                    class: FailureClass::Pass,
                    detail: "javascript parity".to_owned(),
                    artifact: Some(emitted.into_bytes()),
                },
                FacetVerdict::Fail { reason } => CompilerCheckObservation {
                    class: FailureClass::FailBehavior,
                    detail: reason,
                    artifact: None,
                },
                FacetVerdict::Unproven { reason } => CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: format!("javascript oracle could not prove parity: {reason}"),
                    artifact: None,
                },
            }
        }
    }
}

/// What `emit_javascript_baseline` reports when the case emits no section: upstream
/// then writes no `.js` baseline at all.
const NO_JAVASCRIPT_OUTPUT: &str = "javascript emit reached no case units";

/// The directory components every emitting unit shares, which tsc drops from
/// the paths under `outDir`.
pub(crate) fn common_directory<'a>(paths: impl Iterator<Item = &'a str>) -> Vec<&'a str> {
    let mut common: Option<Vec<&str>> = None;
    for path in paths {
        let mut parts: Vec<&str> = path.split('/').filter(|part| !part.is_empty()).collect();
        parts.pop();
        common = Some(match common {
            None => parts,
            Some(previous) => previous
                .into_iter()
                .zip(parts)
                .take_while(|(left, right)| left == right)
                .map(|(left, _)| left)
                .collect(),
        });
    }
    common.unwrap_or_default()
}

/// The output path `fullEmitPaths` prints: `outDir`, the unit's directories
/// below the common source directory, then the section name.
pub(crate) fn emitted_path(
    directory: &str,
    common: &[&str],
    unit_path: &str,
    section: &str,
) -> String {
    let parts: Vec<&str> = unit_path
        .split('/')
        .filter(|part| !part.is_empty())
        .collect();
    let below = parts
        .get(common.len()..parts.len().saturating_sub(1))
        .unwrap_or_default();
    let mut path = String::from(directory);
    for part in below {
        path.push('/');
        path.push_str(part);
    }
    path.push('/');
    path.push_str(section);
    path
}

fn pragma_enabled(pragmas: &CasePragmas, name: &str) -> bool {
    pragmas
        .options
        .iter()
        .find(|(key, _)| key == name)
        .and_then(|(_, values)| values.first())
        .is_some_and(|value| value.eq_ignore_ascii_case("true"))
}

/// Whether the program compiles JavaScript inputs: `allowJs`, `checkJs` (which
/// implies it), or a tsconfig unit that sets `allowJs` itself.
fn compiles_scripts(case: &CheckedCase) -> bool {
    let options = case.options();
    options.allow_js()
        || options.check_js()
        || case.units.iter().any(|(unit, _)| {
            is_config_unit_name(&unit_basename(&unit.virtual_path))
                && unit
                    .text
                    .to_ascii_lowercase()
                    .replace(char::is_whitespace, "")
                    .contains("\"allowjs\":true")
        })
}

/// Whether a unit name is a JavaScript source file, which tsc compiles only
/// under `allowJs`.
fn is_script_input_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    [".js", ".jsx", ".mjs", ".cjs"]
        .iter()
        .any(|extension| lower.ends_with(extension))
}

/// The `outDir` that `fullEmitPaths` prints in front of every section name.
fn full_emit_directory(pragmas: &CasePragmas) -> Option<String> {
    let value = |name: &str| {
        pragmas
            .options
            .iter()
            .find(|(key, _)| key == name)
            .and_then(|(_, values)| values.first())
    };
    value("fullemitpaths").filter(|flag| flag.eq_ignore_ascii_case("true"))?;
    let directory = value("outdir")?.trim_end_matches('/');
    Some(directory.strip_prefix("./").unwrap_or(directory).to_owned())
}

pub fn emit_javascript_baseline(
    case: &CheckedCase,
    logical_path: &str,
) -> std::result::Result<String, String> {
    // Upstream `doJsEmitBaseline` framing: a `//// [<case>] ////` document
    // header, one `//// [<basename>]` echo per compiled unit, a blank-line
    // block separator, then the `//// [<output>.js]` sections, then — when the
    // compile declares — a `\n\n` separator and the `//// [<output>.d.ts]`
    // sections. Comparing the whole document keeps the echo honest alongside
    // the emit.
    //
    // Every echo is the unit's bytes verbatim: the separator belongs to the
    // block, not to any unit, so it is appended once after the last one. A
    // unit that ends with a newline keeps it, which is what puts the extra
    // blank line before the emit sections in upstream's documents.
    let options = case.options();
    let jsx_preserve = options.jsx() == Some(JsxEmit::Preserve);
    let bundle = bundle_output_name(options)?;
    let mut out = format!("//// [{logical_path}] ////\n\n");
    let units: Vec<_> = case.reached_units().collect();
    for (unit, _) in &units {
        let name = unit_basename(&unit.virtual_path);
        if name.eq_ignore_ascii_case("tsconfig.json") {
            continue;
        }
        out.push_str(&format!("//// [{name}]\n"));
        out.push_str(&unit.text);
    }
    out.push_str("\n\n");
    // Upstream's `result.JS` is empty for an `emitDeclarationOnly` compile, so
    // the document carries no `.js` sections at all; its `result.DTS` is empty
    // unless declaration emit is on. The section set follows those two maps.
    let mut outputs = 0usize;
    let imported = runtime_imported_source_ids(case);
    let emitted = if case.no_resolve() {
        case.reached_units().collect()
    } else {
        case.reached_units_in_module_order()
    };
    let emit_directory = case.emit_directory();
    let common = common_directory(
        emitted
            .iter()
            .filter(|(unit, _)| !is_declaration_input_name(&unit_basename(&unit.virtual_path)))
            .map(|(unit, _)| unit.virtual_path.as_str()),
    );
    let placed = |section: &str, unit: &CaseUnit| match emit_directory {
        Some(directory) => emitted_path(directory, &common, &unit.virtual_path, section),
        None => section.to_owned(),
    };
    if !options.emit_declaration_only() {
        for (unit, output) in &emitted {
            let name = unit_basename(&unit.virtual_path);
            if is_declaration_input_name(&name)
                || (is_script_input_name(&name) && !compiles_scripts(case))
            {
                continue;
            }
            if is_json_input_name(&name) {
                if bundle.is_some() {
                    continue;
                }
                if options.out_dir().is_none() {
                    continue;
                }
                if is_config_unit_name(&name) || name.eq_ignore_ascii_case("package.json") {
                    continue;
                }
                if unit
                    .virtual_path
                    .split('/')
                    .any(|part| part == "node_modules")
                {
                    continue;
                }
                if !imported.contains(&output.source_file().source_id()) {
                    continue;
                }
                let body = output
                    .emit()
                    .and_then(|emit| emit.javascript.as_ref())
                    .map(|javascript| javascript.code.as_str())
                    .unwrap_or("");
                push_output_section(&mut out, &placed(&name, unit), body);
                outputs += 1;
                continue;
            }
            let Some(emit) = output.emit() else {
                return Err(format!(
                    "unit `{}` produced no javascript emit",
                    unit.virtual_path
                ));
            };
            let Some(javascript) = emit.javascript.as_ref() else {
                return Err(format!(
                    "unit `{}` produced no javascript slot",
                    unit.virtual_path
                ));
            };
            let js_name = output_section_name(&name, bundle.as_deref(), |name| {
                output_extension(name, jsx_preserve).to_owned()
            });
            push_output_section(&mut out, &placed(&js_name, unit), &javascript.code);
            outputs += 1;
        }
    }
    if options.declaration() || options.emit_declaration_only() {
        let mut declarations = Vec::new();
        for (unit, output) in &emitted {
            let name = unit_basename(&unit.virtual_path);
            if is_declaration_input_name(&name)
                || is_json_input_name(&name)
                || (is_script_input_name(&name) && !compiles_scripts(case))
            {
                continue;
            }
            let section = output_section_name(&name, bundle.as_deref(), declaration_extension);
            let Some(declaration) = declaration_code(output)
                .map(str::to_owned)
                .or_else(|| declaration_text_for(output, &section, &name))
            else {
                continue;
            };
            declarations.push((placed(&section, unit), declaration));
        }
        if !declarations.is_empty() {
            // Upstream writes the `\r\n\r\n` block separator and then the
            // declaration sections back to back, with no per-file separator.
            out.push_str("\n\n");
            for (section, code) in declarations {
                out.push_str(&format!("//// [{section}]\n{code}"));
                outputs += 1;
            }
        }
    }
    if outputs == 0 {
        return Err(NO_JAVASCRIPT_OUTPUT.to_owned());
    }
    Ok(out)
}

/// The bundle output name (`outFile`) upstream gives every unit's JavaScript
/// output, as a basename. Upstream's per-unit output path is the `outFile`
/// path itself, and the baseline prints only its basename.
fn bundle_output_name(options: &CompilerOptions) -> std::result::Result<Option<String>, String> {
    let Some(path) = options.out_file() else {
        return Ok(None);
    };
    let Some(name) = path.file_name() else {
        return Ok(None);
    };
    let Some(basename) = name.to_str() else {
        return Err("outFile path is not valid UTF-8".to_owned());
    };
    Ok(Some(basename.to_owned()))
}
fn runtime_imported_source_ids(case: &CheckedCase) -> HashSet<SourceId> {
    let program = case.program();
    let entry = program.entrypoint_id();
    let mut imported = HashSet::new();
    for module in program.modules() {
        if module.source_id() == entry {
            continue;
        }
        for edge in module.dependencies() {
            if edge.is_unresolved() {
                continue;
            }
            if edge.kind() == ModuleEdgeKind::TypeOnly {
                continue;
            }
            if let Some(target) = edge.target().local_source_id() {
                imported.insert(target);
            }
        }
    }
    imported
}

/// The `//// [<name>]` section header for one unit's output of a given kind.
/// A per-file compile names the section after the unit basename; an `outFile`
/// compile names every output after the bundle. Either way the name is that
/// file's basename with `extension` swapped in, and a name already carrying
/// the extension is returned untouched so a `.d.ts` bundle stays `.d.ts`
/// rather than becoming `.d.d.ts`.
fn output_section_name(
    unit_name: &str,
    bundle: Option<&str>,
    extension: impl Fn(&str) -> String,
) -> String {
    let name = match bundle {
        Some(bundle) => bundle,
        None => unit_name,
    };
    let extension = extension(name);
    if name.to_ascii_lowercase().ends_with(&extension) {
        return name.to_owned();
    }
    replace_extension(name, &extension)
}

/// Whether a unit name is itself a declaration file: `.d.ts`, `.d.mts`,
/// `.d.cts`, or a `.ts` file whose name contains `.d.` (`styles.d.css.ts`,
/// an arbitrary-extension declaration). Upstream's output mapping skips
/// declaration inputs entirely: they produce no JavaScript and no
/// declaration output.
fn is_declaration_input_name(name: &str) -> bool {
    is_declaration_section_name(name)
        || (name.to_ascii_lowercase().ends_with(".ts") && name.contains(".d."))
}

/// Whether a unit name is a JSON file (`.json`). Upstream's declaration emit
/// never produces a `.d.ts` for JSON inputs: `resolveJsonModule` lets a JSON
/// file be imported as a typed value, but the output mapping skips it for
/// declaration purposes.
fn is_json_input_name(name: &str) -> bool {
    name.to_ascii_lowercase().ends_with(".json")
}

/// The declaration text one unit's frontend output carries, when it carries
/// one.
fn declaration_code(output: &FrontendOutput) -> Option<&str> {
    output
        .emit()
        .and_then(|emit| emit.declaration.as_ref())
        .map(|declaration| declaration.code.as_str())
}

/// The declaration text for one unit whose frontend output carries only
/// JavaScript.
///
/// The `javascript` lane runs the transform surface, whose `EmitOutput` has no
/// declaration slot, while upstream's `doJsEmitBaseline` documents the
/// declaration sections of the same compile. Re-emitting the unit through the
/// public emitter with declaration emit on produces exactly the text the
/// `declaration` lane documents: the declaration view of `EmitOptions` carries
/// only newline, indent, `isolatedDeclarations`, `stripPrivate`, and
/// `declarationMap`, none of which the lane routing changes.
/// `emit_declaration_only` keeps the call from re-emitting the JavaScript.
fn declaration_text_for(
    output: &FrontendOutput,
    dts_name: &str,
    source_name: &str,
) -> Option<String> {
    let names = EmitFileNames {
        source_name: Arc::from(source_name),
        declaration_file_name: Some(Arc::from(dts_name)),
        ..EmitFileNames::default()
    };
    let options = EmitOptions {
        declaration: true,
        emit_declaration_only: true,
        ..EmitOptions::default()
    };
    let emitted = emit_checked(
        output.source_file(),
        output.semantic_model(),
        &options,
        &names,
    );
    emitted.declaration.map(|declaration| declaration.code)
}

/// Append one `//// [<section>]` output section whose body is newline-terminated.
fn push_output_section(out: &mut String, section: &str, code: &str) {
    out.push_str(&format!("//// [{section}]\n{code}"));
    if !code.ends_with('\n') {
        out.push('\n');
    }
}

/// Append one `//// [<section>]` source-map section carrying map JSON.
fn push_map_section(out: &mut String, section: &str, json: &str) {
    out.push_str(&format!("//// [{section}]\n{json}"));
    if !out.ends_with('\n') {
        out.push('\n');
    }
}

/// The JavaScript output extension upstream derives for one input name
/// (`outputpaths.GetOutputExtension`): `.json` stays `.json`; `.tsx`/`.jsx`
/// become `.jsx` only under `jsx: preserve`; `.mts`/`.mjs` become `.mjs`;
/// `.cts`/`.cjs` become `.cjs`; everything else becomes `.js`.
#[must_use]
pub fn output_extension(file_name: &str, jsx_preserve: bool) -> &'static str {
    let lower = file_name.to_lowercase();
    if lower.ends_with(".json") {
        ".json"
    } else if jsx_preserve && (lower.ends_with(".tsx") || lower.ends_with(".jsx")) {
        ".jsx"
    } else if lower.ends_with(".mts") || lower.ends_with(".mjs") {
        ".mjs"
    } else if lower.ends_with(".cts") || lower.ends_with(".cjs") {
        ".cjs"
    } else {
        ".js"
    }
}

/// The `//// [<name>]` section header for one unit's JavaScript output. The
/// baseline prints the output path's basename, so only the extension changes
/// from the unit name (`a.ts` ⇒ `a.js`, `file.tsx` ⇒ `file.jsx` under
/// `jsx: preserve`, `m.cts` ⇒ `m.cjs`).
#[must_use]
pub fn javascript_section_name(unit_name: &str, jsx_preserve: bool) -> String {
    replace_extension(unit_name, output_extension(unit_name, jsx_preserve))
}

/// The declaration-output extension upstream derives for one input name
/// (`tspath.GetDeclarationEmitExtensionForPath`).
#[must_use]
pub fn declaration_extension(file_name: &str) -> String {
    let lower = file_name.to_lowercase();
    if lower.ends_with(".mjs") || lower.ends_with(".mts") {
        ".d.mts".to_owned()
    } else if lower.ends_with(".cjs") || lower.ends_with(".cts") {
        ".d.cts".to_owned()
    } else if lower.ends_with(".ts")
        || lower.ends_with(".tsx")
        || lower.ends_with(".js")
        || lower.ends_with(".jsx")
    {
        ".d.ts".to_owned()
    } else if let Some((_, extension)) = lower.rsplit_once('.') {
        format!(".d.{extension}.ts")
    } else {
        ".d.ts".to_owned()
    }
}

/// Swap a unit basename to its declaration-output name (`a.ts` ⇒ `a.d.ts`,
/// `.mjs`/`.mts` ⇒ `.d.mts`, `.cjs`/`.cts` ⇒ `.d.cts`), matching upstream's
/// declaration emit extension rule for per-file output naming.
#[must_use]
pub fn declaration_section_name(unit_name: &str) -> String {
    replace_extension(unit_name, &declaration_extension(unit_name))
}

/// Replaces `file_name`'s extension with `extension`, appending it when the
/// name has none.
fn replace_extension(file_name: &str, extension: &str) -> String {
    match file_name.rsplit_once('.') {
        Some((stem, _)) => format!("{stem}{extension}"),
        None => format!("{file_name}{extension}"),
    }
}

/// Emit the declaration slice of an upstream `.js` baseline document: one
/// `//// [<output>.d.ts]` section per reached unit that declares, framed
/// exactly like upstream's `doJsEmitBaseline` `fileOutput` sections (header
/// without trailing slashes, newline-terminated code, no separator between
/// declaration sections).
pub fn emit_declaration_baseline(case: &CheckedCase) -> std::result::Result<String, String> {
    let options = case.options();
    let bundle = bundle_output_name(options)?;
    let mut out = String::new();
    for (unit, output) in case.reached_units_in_module_order() {
        let name = unit_basename(&unit.virtual_path);
        // Declaration inputs and JSON inputs produce no declaration output;
        // upstream's output mapping skips them entirely.
        if is_declaration_input_name(&name) || is_json_input_name(&name) {
            continue;
        }
        let section = output_section_name(&name, bundle.as_deref(), declaration_extension);
        // The declaration lane's frontend output already carries the
        // declaration; the fallback covers a caller that hands this function a
        // JavaScript-lane case.
        let Some(declaration) = declaration_code(output)
            .map(str::to_owned)
            .or_else(|| declaration_text_for(output, &section, &name))
        else {
            continue;
        };
        push_output_section(&mut out, &section, &declaration);
    }
    if out.is_empty() {
        return Err("declaration emit reached no case units".to_owned());
    }
    Ok(out)
}

/// The `//// [name]` header text of an upstream baseline section, or `None`
/// for any other line. The document header (`//// [case] ////`) carries
/// trailing slashes and is never a section header.
fn section_header_name(line: &str) -> Option<&str> {
    line.strip_prefix("//// [")
        .and_then(|rest| rest.strip_suffix(']'))
}

/// Whether a baseline section name is a declaration output (`a.d.ts`,
/// `a.d.mts`, `a.d.cts`).
fn is_declaration_section_name(name: &str) -> bool {
    let lower = name.to_lowercase();
    lower.ends_with(".d.ts") || lower.ends_with(".d.mts") || lower.ends_with(".d.cts")
}

/// Extract the declaration output sections (header + body) of an upstream
/// `.js` baseline document. The `declaration` observable speaks only about
/// this slice; input echoes, `.js` outputs, and `[DtsFileErrors]` markers stay
/// out of the comparison.
///
/// `echo_count` is the number of input-file echo sections at the top of the
/// document (one per `// @filename:` unit). Upstream's `doJsEmitBaseline`
/// writes all input echoes first, then generated outputs; a `.d.ts`-named
/// section in the echo zone is an input echo, not a generated declaration.
/// Skipping `echo_count` sections before extracting prevents echo
/// contamination when a case has `.d.ts` inputs alongside generated
/// declarations of the same basename.
#[must_use]
pub fn extract_dts_sections(baseline: &str, echo_count: usize) -> String {
    let mut out = String::new();
    let mut in_section = false;
    let mut sections_seen = 0usize;
    for line in baseline.lines() {
        match section_header_name(line) {
            Some(name) => {
                sections_seen += 1;
                in_section = sections_seen > echo_count && is_declaration_section_name(name);
                if in_section {
                    out.push_str(line.trim_end());
                    out.push('\n');
                }
            }
            None if in_section => {
                out.push_str(line.trim_end());
                out.push('\n');
            }
            None => {}
        }
    }
    out
}

/// Run the declaration emit comparator against the selected pragma variation.
///
/// The upstream `.js` baseline document embeds declaration output as
/// `//// [<stem>.d.ts]` sections (harness `doJsEmitBaseline`); the comparator
/// compares only those sections with the javascript facet's line-wise
/// normalization. Compile failures are `FAIL_BEHAVIOR`/`CRASH`; a missing
/// owned `.js` baseline is a classification/execution drift `HARNESS_ERROR`.
pub(crate) fn observe_declaration(
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
        match resolve_stem_baseline(groups, &index_entry.logical_path, "js", &compile_options) {
            Ok(path) => path,
            Err(error) => {
                return CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: error.to_string(),
                    artifact: None,
                };
            }
        };
    match compile_case_frontend(&units, &entry, pragmas, FrontendMode::Declaration) {
        Err(error) => compile_failure_observation(error),
        Ok(case) => {
            let Some(baseline_path) = baseline_path else {
                return CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail:
                        "classification/execution drift: no owned `.js` baseline document for the declaration facet"
                            .to_owned(),
                    artifact: None,
                };
            };
            let emitted = match emit_declaration_baseline(&case) {
                Ok(emitted) => emitted,
                Err(detail) => {
                    return CompilerCheckObservation {
                        class: FailureClass::FailBehavior,
                        detail,
                        artifact: None,
                    };
                }
            };
            let bytes = match read_verified_snapshot_asset(snapshot, &baseline_path) {
                Ok(bytes) => bytes,
                Err(error) => {
                    return CompilerCheckObservation {
                        class: FailureClass::HarnessError,
                        detail: error.to_string(),
                        artifact: None,
                    };
                }
            };
            let expected = extract_dts_sections(&String::from_utf8_lossy(&bytes), units.len());
            match compare_declaration_emit(&expected, &emitted) {
                FacetVerdict::Pass => CompilerCheckObservation {
                    class: FailureClass::Pass,
                    detail: "declaration parity".to_owned(),
                    artifact: Some(emitted.into_bytes()),
                },
                FacetVerdict::Fail { reason } => CompilerCheckObservation {
                    class: FailureClass::FailBehavior,
                    detail: reason,
                    artifact: None,
                },
                FacetVerdict::Unproven { reason } => CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: format!("declaration oracle could not prove parity: {reason}"),
                    artifact: None,
                },
            }
        }
    }
}

/// Whether the selected compile options ask for an inline source map, which
/// upstream baselines only through the `.sourcemap.txt` record.
fn is_inline_source_map(compile_options: &[(String, String)]) -> bool {
    compile_options
        .iter()
        .any(|(name, value)| name == "inlinesourcemap" && value.eq_ignore_ascii_case("true"))
}

/// The precise gap an inline-source-map `source-map` obligation records: the
/// `.js.map` JSON facet does not exist for inline maps, and the comparable
/// artifact — the `.sourcemap.txt` sourcemap record — has no producer yet.
fn inline_source_map_producer_gap() -> String {
    "producer missing: `.sourcemap.txt` sourcemap-record producer (inline source maps are never baselined as `.js.map` upstream)".to_owned()
}

/// Emit the source-map slice of an upstream `.js.map` baseline document: the
/// `//// [<output>.js.map]` sections (when `sourceMap` is on) followed by the
/// `//// [<output>.d.ts.map]` sections (when `declarationMap` is on), each
/// carrying the real printer map as Source Map v3 JSON. Upstream's
/// `DoSourcemapBaseline` writes exactly `result.Maps`, whose order is the
/// program's source order per surface, so JavaScript maps precede declaration
/// maps. Maps are produced through the public emitter surface with external-map
/// naming (`file`, `sources`, and the `sourceMappingURL` mirror upstream's
/// per-file baseline shape).
pub fn emit_source_map_baseline(
    case: &CheckedCase,
    inline_sources: bool,
) -> std::result::Result<String, String> {
    let program_options = case.options();
    let mut out = String::new();
    let jsx_preserve = program_options.jsx() == Some(JsxEmit::Preserve);
    let bundle = bundle_output_name(program_options)?;
    let source_map = program_options.source_map();
    let declaration_map = program_options.declaration_map();
    // An `emitDeclarationOnly` compile produces no JavaScript at all, so its
    // `.js.map` baseline carries only declaration maps.
    let want_js_map = source_map && !program_options.emit_declaration_only();
    let want_dts_map = declaration_map;
    let mut js_maps: Vec<(String, String)> = Vec::new();
    let mut dts_maps: Vec<(String, String)> = Vec::new();
    for (unit, output) in case.reached_units_in_module_order() {
        let source_name = unit_basename(&unit.virtual_path);
        if is_declaration_input_name(&source_name) || is_json_input_name(&source_name) {
            continue;
        }
        let js_name = output_section_name(&source_name, bundle.as_deref(), |name| {
            output_extension(name, jsx_preserve).to_owned()
        });
        let dts_name = output_section_name(&source_name, bundle.as_deref(), declaration_extension);
        let names = EmitFileNames {
            source_name: Arc::from(source_name.as_str()),
            js_file_name: Some(Arc::from(js_name.as_str())),
            js_source_name: Some(Arc::from(source_name.as_str())),
            js_source_map_url: Some(Arc::from(format!("{js_name}.map").as_str())),
            declaration_file_name: Some(Arc::from(dts_name.as_str())),
            declaration_source_name: Some(Arc::from(source_name.as_str())),
            declaration_source_map_url: Some(Arc::from(format!("{dts_name}.map").as_str())),
            ..EmitFileNames::default()
        };
        let mut options = EmitOptions {
            source_map: want_js_map,
            declaration: want_dts_map || program_options.declaration(),
            emit_declaration_only: program_options.emit_declaration_only(),
            declaration_map: want_dts_map,
            inline_sources,
            ..EmitOptions::default()
        };
        // Forward the resolved program's emit fields (target, always_strict,
        // module, jsx) the same way pipeline.rs does, so the verification
        // lane and the CLI cannot diverge on downleveling, the strict-mode
        // prologue, or module-wrapper structure.
        let prog = case.program();
        let check = prog.check_options();
        options.apply_emit_fields(
            check.target(),
            check.always_strict(),
            prog.is_commonjs().then_some(ModuleKind::CommonJs),
            prog.use_define_for_class_fields(),
            prog.import_helpers(),
        );
        options.es_module_interop = prog.es_module_interop().unwrap_or(true);
        options.no_emit_helpers = check.no_emit_helpers();
        options.remove_comments = check.remove_comments();
        options.verbatim_module_syntax = prog.verbatim_module_syntax();
        match prog.jsx_routing_decision(ProgramOutputKind::JavaScript) {
            JsxRoutingDecision::Emit | JsxRoutingDecision::TransformAndEmit => {
                options.jsx = prog.jsx();
                options.jsx_factory = prog.jsx_factory().map(Arc::from);
                options.jsx_fragment_factory = prog.jsx_fragment_factory().map(Arc::from);
                options.jsx_import_source = prog.jsx_import_source().map(Arc::from);
            }
            JsxRoutingDecision::Lower | JsxRoutingDecision::RejectPreservedNative => {
                unreachable!("JavaScript output never selects a native JSX route");
            }
        }
        let emitted = emit_checked(
            output.source_file(),
            output.semantic_model(),
            &options,
            &names,
        );
        if want_js_map {
            let Some(map) = emitted
                .javascript
                .as_ref()
                .and_then(|file| file.source_map.as_ref())
            else {
                return Err(format!(
                    "unit `{}` produced no javascript source map",
                    unit.virtual_path
                ));
            };
            js_maps.push((format!("{js_name}.map"), map.to_json()));
        }
        if want_dts_map {
            let Some(map) = emitted
                .declaration
                .as_ref()
                .and_then(|file| file.source_map.as_ref())
            else {
                return Err(format!(
                    "unit `{}` produced no declaration source map",
                    unit.virtual_path
                ));
            };
            dts_maps.push((format!("{dts_name}.map"), map.to_json()));
        }
    }
    // Upstream's `result.Maps` consumes one `.js.map` per source file in
    // program order, then appends the unhandled declaration maps sorted by
    // unit name, so JavaScript maps always precede declaration maps.
    for (section, json) in js_maps {
        push_map_section(&mut out, &section, &json);
    }
    dts_maps.sort_by(|left, right| left.0.cmp(&right.0));
    for (section, json) in dts_maps {
        push_map_section(&mut out, &section, &json);
    }
    // `emitDeclarationOnly` without `declarationMap` requests no map at all;
    // only a case with no units is malformed.
    if out.is_empty() && case.units.is_empty() {
        return Err("source-map emit reached no case units".to_owned());
    }
    Ok(out)
}

/// Run the source-map comparator against the selected pragma variation.
///
/// External-map configurations (`sourcemap=true`) compare the emitted maps
/// against the owned `.js.map` baseline under JSON canonicalization. Inline
/// configurations have no `.js.map` baseline upstream and are recorded as the
/// precise producer gap instead. A non-inline configuration with no owned
/// `.js.map` baseline is a classification/execution drift `HARNESS_ERROR`.
pub(crate) fn observe_source_map(
    snapshot: &(impl SnapshotAssets + ?Sized),
    groups: &BaselineGroups,
    index_entry: &IndexEntry,
    text: &str,
    pragmas: &CasePragmas,
) -> CompilerCheckObservation {
    let units = split_case_units(&index_entry.logical_path, text);
    let entry = entry_virtual_path(&index_entry.logical_path, &units);
    let compile_options = compile_option_pairs(pragmas);
    if is_inline_source_map(&compile_options) {
        return CompilerCheckObservation {
            class: FailureClass::HarnessError,
            detail: inline_source_map_producer_gap(),
            artifact: None,
        };
    }
    let baseline_path = match resolve_stem_baseline(
        groups,
        &index_entry.logical_path,
        "js.map",
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
    match compile_case_frontend(&units, &entry, pragmas, FrontendMode::JavaScript) {
        Err(error) => compile_failure_observation(error),
        Ok(case) => {
            let Some(baseline_path) = baseline_path else {
                return CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: "classification/execution drift: no owned `.js.map` baseline"
                        .to_owned(),
                    artifact: None,
                };
            };
            let inline_sources = compile_options
                .iter()
                .any(|(name, value)| name == "inlinesources" && value.eq_ignore_ascii_case("true"));
            let emitted = match emit_source_map_baseline(&case, inline_sources) {
                Ok(emitted) => emitted,
                Err(detail) => {
                    return CompilerCheckObservation {
                        class: FailureClass::FailBehavior,
                        detail,
                        artifact: None,
                    };
                }
            };
            let bytes = match read_verified_snapshot_asset(snapshot, &baseline_path) {
                Ok(bytes) => bytes,
                Err(error) => {
                    return CompilerCheckObservation {
                        class: FailureClass::HarnessError,
                        detail: error.to_string(),
                        artifact: None,
                    };
                }
            };
            let expected = String::from_utf8_lossy(&bytes).into_owned();
            match compare_source_map(&expected, &emitted) {
                FacetVerdict::Pass => CompilerCheckObservation {
                    class: FailureClass::Pass,
                    detail: "source-map parity".to_owned(),
                    artifact: Some(emitted.into_bytes()),
                },
                FacetVerdict::Fail { reason } => CompilerCheckObservation {
                    class: FailureClass::FailBehavior,
                    detail: reason,
                    artifact: None,
                },
                FacetVerdict::Unproven { reason } => CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: format!("source-map oracle could not prove parity: {reason}"),
                    artifact: None,
                },
            }
        }
    }
}

/// Whether a baseline section name is a `.tsbuildinfo` output.
fn is_tsbuildinfo_section_name(name: &str) -> bool {
    name.ends_with(".tsbuildinfo")
}
/// Extract the `.tsbuildinfo` body content from an upstream `.js` baseline
/// document. Returns just the body lines (without the `//// [name]` header)
/// so the comparator can compare against the raw emitted content.
pub fn extract_tsbuildinfo_sections(baseline: &str) -> String {
    let mut out = String::new();
    let mut in_section = false;
    for line in baseline.lines() {
        match section_header_name(line) {
            Some(name) => {
                in_section = is_tsbuildinfo_section_name(name);
            }
            None if in_section => {
                out.push_str(line.trim_end());
                out.push('\n');
            }
            None => {}
        }
    }
    out
}

/// Whether the case's resolved options turn on build-info emission, mirroring
/// the catalog's `ObservableKind::BuildInfo` source predicate: `incremental`
/// or `composite` must be true (a bare `tsBuildInfoFile` does not emit —
/// optionsTsBuildInfoFileWithoutIncrementalAndComposite writes no artifact).
fn build_info_implied(pragmas: &CasePragmas) -> bool {
    let config_source = build_tsconfig(pragmas);
    let Ok(value) = bamts_compiler::project::parse_jsonc(&config_source) else {
        return false;
    };
    let bamts_compiler::project::JsonValue::Object(obj) = &value else {
        return false;
    };
    let Some(compiler) = obj
        .get("compilerOptions")
        .and_then(|value| value.as_object())
    else {
        return false;
    };
    ["incremental", "composite"].iter().any(|key| {
        matches!(
            compiler.get(key),
            Some(bamts_compiler::project::JsonValue::Bool(true))
        )
    })
}

/// Produce the BAMTS `.tsbuildinfo` content for a compiled case.
///
/// Constructs a [`BuildInfo`] from the program's source modules and the
/// canonical compiler-options signature, then encodes it in the on-disk JSON
/// format. The output is deterministic for the same inputs. Returns empty
/// when the config implies no build-info emission (`incremental` or
/// `composite` unset).
#[must_use]
pub fn emit_build_info_baseline(case: &CheckedCase, pragmas: &CasePragmas) -> String {
    if !build_info_implied(pragmas) {
        return String::new();
    }
    let config_source = build_tsconfig(pragmas);
    let option_signature = match bamts_compiler::project::parse_jsonc(&config_source) {
        Ok(value) => match &value {
            bamts_compiler::project::JsonValue::Object(obj) => match obj.get("compilerOptions") {
                Some(compiler) => canonical_json(compiler),
                None => "null".to_owned(),
            },
            _ => "null".to_owned(),
        },
        Err(_) => "null".to_owned(),
    };
    let sources: BTreeMap<std::path::PathBuf, Arc<str>> = case
        .program()
        .modules()
        .iter()
        .map(|module| {
            (
                module.path().to_path_buf(),
                source_signature(module.source().as_str()),
            )
        })
        .collect();
    let info = BuildInfo {
        version: Arc::from(BUILD_INFO_SCHEMA),
        options: Arc::from(option_signature),
        sources,
        outputs: std::collections::BTreeSet::new(),
        signature: Arc::from("0000000000000000"),
    };
    match info.encode() {
        Ok(bytes) => String::from_utf8_lossy(&bytes).into_owned(),
        Err(error) => format!("build-info encode error: {error}"),
    }
}

/// Run the build-info comparator against the selected pragma variation.
///
/// The upstream `.js` baseline document may embed `.tsbuildinfo` output as
/// `//// [name.tsbuildinfo]` sections; the comparator compares only those
/// sections with the javascript facet's line-wise normalization. Compile
/// failures are `FAIL_BEHAVIOR`/`CRASH`; a missing owned `.js` baseline is a
/// classification/execution drift `HARNESS_ERROR`. No baseline in the entire
/// 7.0.2 reference tree carries a `.tsbuildinfo` section (the harness drops
/// the artifact as environment dependent), so the no-section path is the
/// live one: it demands emission exactly when the config implies it
/// (`incremental` or `composite`) and no artifact otherwise.
pub(crate) fn observe_build_info(
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
        match resolve_stem_baseline(groups, &index_entry.logical_path, "js", &compile_options) {
            Ok(path) => path,
            Err(error) => {
                return CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: error.to_string(),
                    artifact: None,
                };
            }
        };
    match compile_case_frontend(&units, &entry, pragmas, FrontendMode::JavaScript) {
        Err(error) => compile_failure_observation(error),
        Ok(case) => {
            let Some(baseline_path) = baseline_path else {
                return CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: "classification/execution drift: no owned `.js` baseline".to_owned(),
                    artifact: None,
                };
            };
            let emitted = emit_build_info_baseline(&case, pragmas);
            let bytes = match read_verified_snapshot_asset(snapshot, &baseline_path) {
                Ok(bytes) => bytes,
                Err(error) => {
                    return CompilerCheckObservation {
                        class: FailureClass::HarnessError,
                        detail: error.to_string(),
                        artifact: None,
                    };
                }
            };
            let expected = String::from_utf8_lossy(&bytes).into_owned();
            let expected_sections = extract_tsbuildinfo_sections(&expected);
            if expected_sections.is_empty() {
                // Upstream never baselines `.tsbuildinfo` content: zero
                // sections exist across the entire 7.0.2 reference tree.
                // With no expected bytes the contract is emission-shape:
                // produce an artifact exactly when the config implies one
                // (`incremental`/`composite`), none otherwise.
                let implied = build_info_implied(pragmas);
                let produced =
                    !emitted.is_empty() && !emitted.starts_with("build-info encode error:");
                return match (implied, produced) {
                    (true, true) => CompilerCheckObservation {
                        class: FailureClass::Pass,
                        detail: "build-info produced; content not baselined upstream".to_owned(),
                        artifact: Some(emitted.into_bytes()),
                    },
                    (true, false) => CompilerCheckObservation {
                        class: FailureClass::FailBehavior,
                        detail: "config implies a .tsbuildinfo artifact but the \
                            producer emitted none"
                            .to_owned(),
                        artifact: Some(emitted.into_bytes()),
                    },
                    (false, false) => CompilerCheckObservation {
                        class: FailureClass::Pass,
                        detail: "config implies no .tsbuildinfo artifact; none emitted".to_owned(),
                        artifact: Some(
                            "config implies no .tsbuildinfo artifact; none emitted\n"
                                .as_bytes()
                                .to_vec(),
                        ),
                    },
                    (false, true) => CompilerCheckObservation {
                        class: FailureClass::FailBehavior,
                        detail: "producer emitted a .tsbuildinfo artifact the config \
                            does not imply"
                            .to_owned(),
                        artifact: Some(emitted.into_bytes()),
                    },
                };
            }
            match compare_js_emit(&expected_sections, &emitted) {
                FacetVerdict::Pass => CompilerCheckObservation {
                    class: FailureClass::Pass,
                    detail: "build-info parity".to_owned(),
                    artifact: Some(emitted.into_bytes()),
                },
                FacetVerdict::Fail { reason } => CompilerCheckObservation {
                    class: FailureClass::FailBehavior,
                    detail: reason,
                    artifact: Some(emitted.into_bytes()),
                },
                FacetVerdict::Unproven { reason } => CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: format!("build-info oracle could not prove parity: {reason}"),
                    artifact: None,
                },
            }
        }
    }
}

/// A [`ResolutionHost`] backed by the real filesystem, confined to a project
/// root. Used by the trace comparator to re-resolve import specifiers with
/// `resolve_module_name_with_trace` against the same files the loader saw.
struct FilesystemResolutionHost;

impl ResolutionHost for FilesystemResolutionHost {
    fn file_exists(&self, path: &Path) -> bool {
        path.is_file()
    }

    fn directory_exists(&self, path: &Path) -> bool {
        path.is_dir()
    }

    fn read_file(&self, path: &Path) -> Option<Arc<str>> {
        fs::read_to_string(path).ok().map(Arc::from)
    }
}

/// Determine the `ModuleResolutionKind` from compiler options. Upstream test
/// cases default to `bundler` when `moduleResolution` is not set; `node16` and
/// `nodenext` are parsed when present.
fn resolution_kind(options: &CompilerOptions) -> ModuleResolutionKind {
    match options.module_resolution() {
        Some(value) => ModuleResolutionKind::parse(value).unwrap_or(ModuleResolutionKind::Bundler),
        None => ModuleResolutionKind::Bundler,
    }
}
pub(crate) fn collect_resolution_trace(
    program: &ResolvedProgram,
    options: &CompilerOptions,
) -> ResolutionTraceLog {
    collect_trace_with_skip(program, options, None)
}

pub(crate) fn collect_case_resolution_trace(case: &CheckedCase) -> ResolutionTraceLog {
    let program = case.program();
    collect_trace_with_skip(program, case.options(), Some(program.entrypoint_id()))
}

fn collect_trace_with_skip(
    program: &ResolvedProgram,
    options: &CompilerOptions,
    skip: Option<SourceId>,
) -> ResolutionTraceLog {
    let root = program.root();
    let kind = resolution_kind(options);
    let host = FilesystemResolutionHost;
    let mut cache = ResolutionCache::new();
    let mut log = ResolutionTraceLog::default();
    for module in program.modules() {
        if Some(module.source_id()) == skip {
            continue;
        }
        let importer = module.path();
        for edge in module.dependencies() {
            if edge.kind() == ModuleEdgeKind::DynamicRuntime {
                continue;
            }
            let _ = resolve_module_name_with_trace(
                root,
                options,
                importer,
                edge.specifier(),
                (kind, edge.mode(), edge.flavor()),
                TraceResolutionServices {
                    host: &host,
                    cache: &mut cache,
                    log: &mut log,
                },
            );
        }
    }
    log
}

/// Record the `trace` observable: compile the case, re-resolve each import
/// specifier through `resolve_module_name_with_trace` to produce upstream
/// `traceResolution` log lines, and compare the collected lines against the
/// `<stem>.trace.json` baseline. Resolution kinds the tracer does not cover
/// (`DirectoryPackage`, `PackageImport`, `PackageName`, `PathsMapping`) are
/// reported honestly as producer-missing detail rather than fabricated.
pub(crate) fn observe_trace(
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
        "trace.json",
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
    let case = match compile_case_with_pragmas(&units, &entry, pragmas) {
        Err(error) => return compile_failure_observation(error),
        Ok(case) => case,
    };
    let Some(baseline_path) = baseline_path else {
        return CompilerCheckObservation {
            class: FailureClass::Inapplicable,
            detail: "trace observable inapplicable: no owned `.trace.json` baseline for this case/configuration".to_owned(),
            artifact: None,
        };
    };
    let log = collect_case_resolution_trace(&case);
    let unsupported: Vec<&str> = log
        .unsupported()
        .iter()
        .map(|kind| match kind {
            bamts_compiler::project::resolution_trace::UnsupportedTraceKind::DirectoryPackage => {
                "DirectoryPackage"
            }
            bamts_compiler::project::resolution_trace::UnsupportedTraceKind::PackageImport => {
                "PackageImport"
            }
            bamts_compiler::project::resolution_trace::UnsupportedTraceKind::PackageName => {
                "PackageName"
            }
            bamts_compiler::project::resolution_trace::UnsupportedTraceKind::PathsMapping => {
                "PathsMapping"
            }
        })
        .collect();
    let produced_lines = log.lines();
    let bytes = match read_verified_snapshot_asset(snapshot, &baseline_path) {
        Ok(bytes) => bytes,
        Err(error) => {
            return CompilerCheckObservation {
                class: FailureClass::HarnessError,
                detail: error.to_string(),
                artifact: None,
            };
        }
    };
    let expected_text = String::from_utf8_lossy(&bytes).into_owned();
    let expected_lines: Vec<String> = match serde_json::from_str::<Vec<String>>(&expected_text) {
        Ok(lines) => lines,
        Err(error) => {
            return CompilerCheckObservation {
                class: FailureClass::HarnessError,
                detail: format!(
                    "trace baseline `{baseline_path}` is not a JSON string array: {error}"
                ),
                artifact: None,
            };
        }
    };
    let produced_json = serde_json::to_string_pretty(produced_lines)
        .unwrap_or_default()
        .into_bytes();
    if produced_lines == expected_lines.as_slice() {
        CompilerCheckObservation {
            class: FailureClass::Pass,
            detail: String::new(),
            artifact: Some(produced_json),
        }
    } else if !unsupported.is_empty() {
        CompilerCheckObservation {
            class: FailureClass::HarnessError,
            detail: format!(
                "producer missing: resolution tracer does not cover {{{}}}; produced {} of {} expected trace lines",
                unsupported.join(", "),
                produced_lines.len(),
                expected_lines.len()
            ),
            artifact: Some(produced_json),
        }
    } else {
        CompilerCheckObservation {
            class: FailureClass::FailBehavior,
            detail: format!(
                "trace mismatch: produced {} lines, expected {} lines",
                produced_lines.len(),
                expected_lines.len()
            ),
            artifact: Some(produced_json),
        }
    }
}

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
            output.semantic_model(),
            output.source_file(),
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
    model: &SemanticModel,
    source_file: &bamts_compiler::syntax::SourceFile,
    heading: &str,
    section: &str,
    declaration_anchors: &HashMap<(String, SymbolKind), Vec<SymbolDeclAnchor>>,
    target: Option<&str>,
    libs: &[Arc<str>],
    out: &mut String,
) {
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

/// Upstream prints a reference directive's path without the virtual `/.lib/`
/// root that the test sources use to point at shared library files.
fn strip_library_root(line: &str) -> std::borrow::Cow<'_, str> {
    if line.starts_with("/// <reference") && line.contains("\"/.lib/") {
        std::borrow::Cow::Owned(line.replace("\"/.lib/", "\""))
    } else {
        std::borrow::Cow::Borrowed(line)
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
    if !found_at {
        if let Some(start) = undecorated_start {
            node_index = start;
        }
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
const fn kind_is_keyword_led(kind: SymbolKind) -> bool {
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
const fn kind_is_mergeable(kind: SymbolKind) -> bool {
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

/// The verdict of one symbols check cell.
#[derive(Debug, Clone)]
pub struct SymbolsOutcome {
    /// The emitted `.symbols` document.
    pub emitted: String,
    /// The comparator verdict against the owned baseline.
    pub verdict: FacetVerdict,
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

#[cfg(test)]
mod tests;
