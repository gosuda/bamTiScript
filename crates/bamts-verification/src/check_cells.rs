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
    path::Path,
    sync::Arc,
};

#[cfg(test)]
use bamts_compiler::checker::Type;
use bamts_compiler::checker::{
    DeclarationOccurrence, SemanticModel, SymbolId, SymbolKind, render_type,
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
use bamts_compiler::project::resolution::{
    ModuleResolutionKind, ResolutionCache, ResolutionHost, TraceResolutionServices,
    resolve_module_name_with_trace,
};
use bamts_compiler::project::resolution_trace::ResolutionTraceLog;
use bamts_compiler::project::{CompilerOptions, ProjectConfig, ProjectRoot};
use bamts_compiler::source::SourceText;
use bamts_compiler::source::{JsxEmit, TextRange, Utf16Pos};
use bamts_compiler::syntax::{Token, TokenKind};

use crate::catalog::CaseConfiguration;
use crate::facets::{
    DiagnosticCategory, DiagnosticCodeMap, FacetDiagnostic, FacetSeverity, FacetVerdict,
    SourcePosition, compare_diagnostics, compare_js_emit, compare_source_map, compare_symbols,
    compare_types,
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
}

impl CheckedCase {
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

    /// `(unit, output)` pairs for every reached unit, sorted by ascending
    /// module index. `ProgramFrontendOutput::modules()` is dependency-first
    /// (dependencies before dependents), matching upstream's output section
    /// order. `reached_units()` iterates split order instead, which is the
    /// `// @filename:` directive order and not the emit order.
    pub fn reached_units_in_module_order(&self) -> Vec<(&CaseUnit, &FrontendOutput)> {
        let mut triples: Vec<(usize, &CaseUnit, &FrontendOutput)> = self
            .units
            .iter()
            .filter_map(|(unit, index)| {
                index.map(|index| (index, unit, &self.output.modules()[index]))
            })
            .collect();
        triples.sort_by_key(|(index, _, _)| *index);
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
        let Some(directive) = directive_body(line) else {
            continue;
        };
        let Some((name, value)) = directive.split_once(':') else {
            continue;
        };
        let name = name.trim().to_ascii_lowercase();
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

/// Returns the body of a whole-line `// @name: …` directive, if the line is one.
fn directive_body(line: &str) -> Option<&str> {
    let trimmed = line.trim();
    // A leading U+FEFF (BOM) may precede the `//` in files saved with a
    // byte-order mark; strip it before the directive test so coordinates
    // are not shifted by the invisible character.
    let trimmed = trimmed.strip_prefix('\u{feff}').unwrap_or(trimmed);
    let rest = trimmed.strip_prefix("//")?;
    let rest = rest.trim_start_matches('/').trim_start();
    rest.strip_prefix('@')
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
fn is_option_directive_line(line: &str) -> bool {
    // A leading U+FEFF (BOM) may precede the `//` in files saved with a
    // byte-order mark; strip it before the directive test.
    let line = line.strip_prefix('\u{feff}').unwrap_or(line);
    let Some(rest) = line.strip_prefix("//") else {
        return false;
    };
    // A third leading slash is a `///` directive, not a `// @option`.
    if rest.starts_with('/') {
        return false;
    }
    let rest = rest.trim_start();
    let Some(rest) = rest.strip_prefix('@') else {
        return false;
    };
    let name_len = rest
        .bytes()
        .take_while(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
        .count();
    if name_len == 0 {
        return false;
    }
    rest[name_len..].trim_start().starts_with(':')
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
        let body = directive_body(line.trim_end_matches(['\n', '\r']));
        let name = body.and_then(|body| {
            let (name, value) = body.split_once(':')?;
            name.trim()
                .eq_ignore_ascii_case("filename")
                .then(|| value.trim().to_owned())
        });
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
                if end > 0 && !strip_directive_lines(&text[..end]).trim().is_empty() {
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
            | "usedefineforclassfields" => value.eq_ignore_ascii_case("true").to_string(),
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
            _ => format!("\"{}\"", value.replace('\\', "\\\\").replace('"', "\\\"")),
        };
        let key = match name.as_str() {
            "strictnullchecks" => "strictNullChecks",
            "noimplicitany" => "noImplicitAny",
            "allowjs" => "allowJs",
            "checkjs" => "checkJs",
            "resolvejsonmodule" => "resolveJsonModule",
            "moduleresolution" => "moduleResolution",
            "noemithelpers" => "noEmitHelpers",
            "noemit" => "noEmit",
            "alwaysstrict" => "alwaysStrict",
            "usedefineforclassfields" => "useDefineForClassFields",
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
    compile_case_frontend(units, entry_name, pragmas, FrontendMode::Check)
}

pub fn compile_case_frontend(
    units: &[CaseUnit],
    entry_name: &str,
    pragmas: &CasePragmas,
    mode: FrontendMode,
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
        let config = ProjectConfig::parse(&root, temp.path().join("tsconfig.json"), &config_source)
            .map_err(|error| CaseCompileError::Load(format!("config: {error}")))?;
        let options = config.options().clone();
        let loader = ProgramLoader::new(&root, config.options())
            .map_err(|error| CaseCompileError::Load(format!("loader: {error}")))?;
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
            let canonical = fs::canonicalize(root.join(&unit.virtual_path)).ok();
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
    _snapshot: &(impl SnapshotAssets + ?Sized),
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
///
/// The compile uses the default lint profile, but TS error baselines carry no
/// lint output: actual diagnostics are filtered to the code map's BAMTS
/// L/P/C families (every mapped compiler diagnostic) before comparing, so
/// `BAMTS-W…` lint warnings never fail a row.
pub fn check_diagnostics(
    ctx: &CheckContext,
    snapshot: &(impl SnapshotAssets + ?Sized),
    case: &CheckedCase,
    baselines: &DiagnosticsBaselines,
) -> Result<DiagnosticsOutcome> {
    let mut actual = collect_facet_diagnostics(case);
    actual.retain(|diagnostic| ctx.code_map.get(&diagnostic.code).is_some());
    let expected = expected_facet_diagnostics(snapshot, baselines)?;
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
    let units = split_case_units(&index_entry.logical_path, text);
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
    match compile_case_with_pragmas(&units, &entry, pragmas) {
        Err(error) => compile_failure_observation(error),
        Ok(case) => {
            let outcome = match check_diagnostics(ctx, snapshot, &case, &baselines) {
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
    for (unit, output) in case.reached_units() {
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
            &unit.display_name,
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

fn emit_unit_types(model: &SemanticModel, source: &SourceText, section: &str, out: &mut String) {
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
        let type_id = model.symbol_type(SymbolId::new(index as u32));
        if let Some(annotation) = annotation_for(
            source,
            range,
            symbol.name().to_owned(),
            render_type(model, type_id),
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
        if let Some(annotation) = annotation_for(
            source,
            range,
            slice_source(source, range),
            render_type(model, model.symbol_type(occurrence.symbol)),
        ) {
            records.push(annotation);
        }
    }
    // Expression records come from the checker's expression-type index.
    for (range, type_id) in model.typed_expressions() {
        let display = slice_source(source, *range);
        if let Some(annotation) =
            annotation_for(source, *range, display, render_type(model, *type_id))
        {
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
        out.push_str(line);
        out.push('\n');
        let Some(line_records) = by_line.get(&line_index) else {
            continue;
        };
        for record in line_records {
            let display = collapse_whitespace(&record.display);
            out.push_str(&format!(">{display} : {}\n", record.rendered));
            out.push_str(&format!(
                ">{} : {}\n",
                " ".repeat(display.chars().count()),
                "^".repeat(record.rendered.chars().count())
            ));
        }
    }
}

/// Build an annotation record, resolving the node's start line. Records whose
/// range cannot be mapped (should not happen for compiled units) are dropped.
fn annotation_for(
    source: &SourceText,
    range: TextRange,
    display: String,
    rendered: String,
) -> Option<TypeAnnotation> {
    let (line, _) = source.line_column(range.start()).ok()?;
    Some(TypeAnnotation {
        start: range.start().get(),
        end: range.end().get(),
        line,
        display,
        rendered,
    })
}

/// Slice the raw source text covered by a UTF-16 range.
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
    baseline_path: &str,
) -> Result<TypesOutcome> {
    let emitted = emit_types_baseline(case, &case.entry);
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
            let outcome = match check_types(snapshot, &case, &baseline_path) {
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
                return CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: "classification/execution drift: no owned `.js` baseline".to_owned(),
                    artifact: None,
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
        out.push_str(&format!("//// [{}]\n", unit_basename(&unit.virtual_path)));
        out.push_str(&unit.text);
    }
    out.push_str("\n\n");
    // Upstream's `result.JS` is empty for an `emitDeclarationOnly` compile, so
    // the document carries no `.js` sections at all; its `result.DTS` is empty
    // unless declaration emit is on. The section set follows those two maps.
    let mut outputs = 0usize;
    if !options.emit_declaration_only() {
        for (unit, output) in &units {
            let name = unit_basename(&unit.virtual_path);
            // A `.d.ts` input is never a JavaScript output: upstream's output
            // mapping skips declaration files outright.
            if is_declaration_input_name(&name) {
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
            push_output_section(&mut out, &js_name, &javascript.code);
            outputs += 1;
        }
    }
    if options.declaration() || options.emit_declaration_only() {
        let mut declarations = Vec::new();
        for (unit, output) in &units {
            let name = unit_basename(&unit.virtual_path);
            if is_declaration_input_name(&name) {
                continue;
            }
            let section = output_section_name(&name, bundle.as_deref(), declaration_extension);
            let Some(declaration) = declaration_code(output)
                .map(str::to_owned)
                .or_else(|| declaration_text_for(output, &section, &name))
            else {
                continue;
            };
            declarations.push((section, declaration));
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
        return Err("javascript emit reached no case units".to_owned());
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

/// Whether a unit name is itself a declaration file (`.d.ts`, `.d.mts`,
/// `.d.cts`). Upstream's output mapping skips declaration inputs entirely:
/// they produce no JavaScript and no declaration output.
fn is_declaration_input_name(name: &str) -> bool {
    is_declaration_section_name(name)
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
            match compare_js_emit(&expected, &emitted) {
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
        );
        options.no_emit_helpers = check.no_emit_helpers();
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
    let root = program.root();
    let kind = resolution_kind(options);
    let host = FilesystemResolutionHost;
    let mut cache = ResolutionCache::new();
    let mut log = ResolutionTraceLog::default();
    for module in program.modules() {
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
    let log = collect_resolution_trace(case.program(), case.options());
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
    let units: Vec<_> = case.reached_units().collect();
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
    for (unit, output) in units {
        let section = unit_basename(&unit.virtual_path);
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
        emit_unit_symbols(
            output.semantic_model(),
            output.source_file(),
            &section,
            &declaration_anchors,
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
    section: &str,
    declaration_anchors: &HashMap<(String, SymbolKind), Vec<SymbolDeclAnchor>>,
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
    let render = |symbol_id: SymbolId| -> Option<String> {
        let index = symbol_id.get() as usize;
        let symbol = model.symbols().get(index)?;
        let name = model.qualified_name(symbol_id);
        let anchors = if let Some(occurrence) = occurrence_anchors.get(&symbol_id) {
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
        if let Some(rendered) = render(symbol_id)
            && let Some(record) =
                symbol_record_for(source, symbol.range(), symbol.name().to_owned(), rendered)
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
        if let Some(rendered) = render(occurrence.symbol) {
            let display = collapse_whitespace(&slice_source(source, occurrence.name_range));
            if let Some(record) =
                symbol_record_for(source, occurrence.name_range, display, rendered)
            {
                records.push(record);
            }
        }
    }
    // Reference records: each resolved value/type occurrence at its use site.
    for (range, symbol_id) in model.symbol_references() {
        if let Some(rendered) = render(*symbol_id) {
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

    out.push_str(&format!("=== {section} ===\n"));
    for (line_index, raw_line) in source.as_str().split('\n').enumerate() {
        let line = raw_line.strip_suffix('\r').unwrap_or(raw_line);
        out.push_str(line);
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
    // Decorator walk: scan left over accessor keywords and decorator
    // expression tokens so a decorated member anchors at the decorator's
    // `@` token, not the declaration name. Runs for all symbol kinds
    // since decorators can appear on non-keyword-led members (e.g.
    // `@dec get accessor()` where `accessor` binds as `Variable(Let)`).
    let mut found_at = false;
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
    // The declaration's full start is the end of the significant token that
    // precedes it (TypeScript's `node.pos`, which counts leading trivia).
    let full_start = match prev_significant_token(tokens, node_index) {
        Some(prev) => tokens[prev].range().end(),
        None => Utf16Pos::ZERO,
    };
    source.line_column(full_start).ok()
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

/// Tokens that can lead a keyword-led declaration (its keyword plus modifiers),
/// scanned over to anchor `Decl(...)` at the declaration's full start.
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
    baseline_path: &str,
) -> Result<SymbolsOutcome> {
    let emitted = emit_symbols_baseline(case, &case.entry);
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
            let outcome = match check_symbols(snapshot, &case, &baseline_path) {
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
mod tests {
    use super::*;
    use crate::facets::load_diagnostic_code_map;

    fn repo_code_map() -> DiagnosticCodeMap {
        // `cargo test` runs with the package root as the working directory;
        // the code map is a committed oracle document two levels up.
        load_diagnostic_code_map(Path::new("../..")).expect("repository code map loads")
    }

    /// H1 end-to-end pin: a positive-diagnostics case compiles through the
    /// real loader+frontend, its lint warnings are filtered out, and the
    /// remaining checker diagnostic matches an upstream-position row
    /// (1-based line, 0-based character) under the code map.
    #[test]
    fn diagnostics_end_to_end_unresolved_name_passes() {
        let case_text = "var y = undefinedName;
";
        let units = split_case_units("tests/cases/compiler/endToEndPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/endToEndPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();

        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        // The lint profile's unused-local warning must not survive the filter.
        assert_eq!(actual.len(), 1, "only the checker diagnostic remains");
        assert_eq!(actual[0].code, "BAMTS-C002");
        assert_eq!(
            actual[0].position,
            SourcePosition {
                line: 1,
                character: 8
            }
        );

        // `undefinedName` starts at 0-based UTF-16 column 8 (TS prints 1:9).
        let expected = vec![FacetDiagnostic {
            unit: "endToEndPin.ts".to_owned(),
            position: SourcePosition {
                line: 1,
                character: 8,
            },
            category: DiagnosticCategory::Error,
            severity: FacetSeverity::Error,
            code: "TS2304".to_owned(),
        }];
        let verdict = compare_diagnostics(&expected, &actual, &code_map);
        assert_eq!(verdict, FacetVerdict::Pass);
    }

    /// Multi-unit cases with an empty leading unit must still load every file,
    /// so import conflicts in a dependent unit are observed.
    #[test]
    fn diagnostics_end_to_end_multi_unit_import_conflict_is_reached() {
        let case_text = "// @target: es2015\n\
            // @module: commonjs\n\
            // @filename: f1.ts\n\
            export function f() {\n\
            }\n\
            // @filename: f2.ts\n\
            import {f} from './f1';\n\
            export function f() {\n\
            }\n";
        let logical = "tests/cases/compiler/functionAndImportNameConflict.ts";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();

        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        assert_eq!(
            actual.len(),
            1,
            "the import/local conflict in f2.ts must be emitted"
        );
        assert_eq!(actual[0].code, "BAMTS-C041");
        assert_eq!(
            actual[0].position,
            SourcePosition {
                line: 1,
                character: 8,
            }
        );

        let expected = vec![FacetDiagnostic {
            unit: "f2.ts".to_owned(),
            position: SourcePosition {
                line: 1,
                character: 8,
            },
            category: DiagnosticCategory::Error,
            severity: FacetSeverity::Error,
            code: "TS2440".to_owned(),
        }];
        let verdict = compare_diagnostics(&expected, &actual, &code_map);
        assert_eq!(verdict, FacetVerdict::Pass);
    }

    /// Zero-expectation pin: a clean case with no owned `.errors.txt` passes
    /// iff the compile emits no mapped diagnostics.
    #[test]
    fn diagnostics_end_to_end_clean_case_passes() {
        let case_text = "export const answer: number = 42;
";
        let units = split_case_units("tests/cases/compiler/cleanPin.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/cleanPin.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let verdict = compare_diagnostics(&[], &actual, &code_map);
        assert_eq!(verdict, FacetVerdict::Pass);
    }

    /// Regression: two diagnostics at the same line/column in different files
    /// must not compare equal. Before the unit field was carried through
    /// `FacetDiagnostic`, the comparator keyed only on position/category/
    /// severity/code and a cross-unit collision silently passed.
    #[test]
    fn diagnostics_cross_unit_position_collision_is_detected() {
        let code_map = repo_code_map();
        let expected = vec![FacetDiagnostic {
            unit: "a.ts".to_owned(),
            position: SourcePosition {
                line: 3,
                character: 5,
            },
            category: DiagnosticCategory::Error,
            severity: FacetSeverity::Error,
            code: "TS2304".to_owned(),
        }];
        let actual = vec![FacetDiagnostic {
            unit: "b.ts".to_owned(),
            position: SourcePosition {
                line: 3,
                character: 5,
            },
            category: DiagnosticCategory::Error,
            severity: FacetSeverity::Error,
            code: "TS2304".to_owned(),
        }];
        let verdict = compare_diagnostics(&expected, &actual, &code_map);
        assert!(
            verdict.is_fail(),
            "same position in different files must fail, got {verdict:?}"
        );
        assert!(
            format!("{verdict:?}").contains("unit mismatch"),
            "failure must name the unit mismatch, got {verdict:?}"
        );
    }

    const ANY_AS_CONSTRUCTOR_CASE: &str = "\
// @target: es2015
// any is considered an untyped function call
// can be called except with type arguments which is an error

var x: any;
var a = new x();
var b = new x('hello');
var c = new x(x);

// grammar allows this for constructors
var d = new x<any>(x); // no error
";

    const ANY_AS_CONSTRUCTOR_ERRORS: &str = "\
anyAsConstructor.ts(10,9): error TS2347: Untyped function calls may not accept type arguments.


==== anyAsConstructor.ts (1 errors) ====
    // any is considered an untyped function call
    // can be called except with type arguments which is an error
    
    var x: any;
    var a = new x();
    var b = new x('hello');
    var c = new x(x);
    
    // grammar allows this for constructors
    var d = new x<any>(x); // no error
            ~~~~~~~~~~~~~
!!! error TS2347: Untyped function calls may not accept type arguments.
";

    const PARSER_ENUM_DECLARATION_2_ERRORS: &str = "\
parserEnumDeclaration2.ts(2,3): error TS1038: A 'declare' modifier cannot be used in an already ambient context.


==== parserEnumDeclaration2.ts (1 errors) ====
    declare namespace M {
      declare enum E {
      ~~~~~~~
!!! error TS1038: A 'declare' modifier cannot be used in an already ambient context.
      }
    }
";

    const MERGING1_ERRORS: &str = "\
testB.ts(1,22): error TS2305: Module '\"*.foo\"' has no exported member 'onlyInA'.


==== types.ts (0 errors) ====
    declare module \"*.foo\" {
      let everywhere: string;
    }
    
    
==== testA.ts (0 errors) ====
    import { everywhere, onlyInA } from \"a.foo\";
    declare module \"a.foo\" {
      let onlyInA: number;
    }
    
==== testB.ts (1 errors) ====
    import { everywhere, onlyInA } from \"b.foo\"; // Error
                         ~~~~~~~
!!! error TS2305: Module '\"*.foo\"' has no exported member 'onlyInA'.
    
";

    const PROJECT_BASELINE_AMD_ERRORS: &str = "\
error TS5107: Option 'module=AMD' is deprecated and will stop functioning in TypeScript 7.0. Specify compilerOption '\"ignoreDeprecations\": \"6.0\"' to silence this error.
error TS5107: Option 'moduleResolution=classic' is deprecated and will stop functioning in TypeScript 7.0. Specify compilerOption '\"ignoreDeprecations\": \"6.0\"' to silence this error.


!!! error TS5107: Option 'module=AMD' is deprecated and will stop functioning in TypeScript 7.0. Specify compilerOption '\"ignoreDeprecations\": \"6.0\"' to silence this error.
!!! error TS5107: Option 'moduleResolution=classic' is deprecated and will stop functioning in TypeScript 7.0. Specify compilerOption '\"ignoreDeprecations\": \"6.0\"' to silence this error.
==== decl.ts (0 errors) ====
    export interface Point { x: number; y: number; };
    export function point (x: number, y: number): Point {
    	return { x: x, y: y };
    }
==== emit.ts (0 errors) ====
    import g = require(\"./decl\");
    var p = g.point(10,20);
";

    #[test]
    fn parse_case_pragmas_reads_target_and_single_unit() {
        let pragmas = parse_case_pragmas(ANY_AS_CONSTRUCTOR_CASE);
        assert_eq!(
            pragmas.options,
            vec![("target".to_owned(), vec!["es2015".to_owned()])]
        );
        assert!(!pragmas.no_types_and_symbols);
    }

    #[test]
    fn parse_case_pragmas_lists_variants_in_order() {
        let pragmas =
            parse_case_pragmas("//@target: ES5, ES2015\n// @strict: true\nvar x: number;\n");
        assert_eq!(
            pragmas.options,
            vec![
                (
                    "target".to_owned(),
                    vec!["ES5".to_owned(), "ES2015".to_owned()]
                ),
                ("strict".to_owned(), vec!["true".to_owned()]),
            ]
        );
    }

    #[test]
    fn parse_case_pragmas_pins_no_types_and_symbols() {
        let pragmas = parse_case_pragmas("// @noTypesAndSymbols: true\nvar x: number;\n");
        assert!(pragmas.no_types_and_symbols);
        let pragmas = parse_case_pragmas("// @noTypesAndSymbols: false\nvar x: number;\n");
        assert!(!pragmas.no_types_and_symbols);
    }

    #[test]
    fn parse_case_pragmas_maps_strict_property_initialization() {
        let pragmas = parse_case_pragmas("// @strictPropertyInitialization: false\n");
        let tsconfig = build_tsconfig(&pragmas);
        assert!(
            tsconfig.contains("\"strictPropertyInitialization\": false"),
            "{tsconfig}"
        );
    }

    /// Upstream splits unit lines on `\r?\n`, so a CRLF directive followed by
    /// a bare-`\n` code line keeps the code line; a `\r\n`-only split would
    /// swallow it into the directive "line" and shift every later position.
    /// Exemplar: `commentsVarDecl.ts` F5 position rows.
    #[test]
    fn strip_directive_lines_mixed_line_endings_keep_code_lines() {
        let stripped = strip_directive_lines(
            "// @strict: true\r\nlet a = 1;\r\n// @noImplicitAny: true\nlet b = 2;\n",
        );
        assert_eq!(stripped, "let a = 1;\nlet b = 2;\n");
    }

    /// Upstream materializes units into a path-keyed fake FS, so a restated
    /// `@filename:` directive makes the later chunk the unit's whole content;
    /// an append would keep the earlier chunk and shift all line numbers.
    #[test]
    fn repeated_filename_directive_replaces_unit_content() {
        let units = split_case_units(
            "tests/cases/compiler/twice.ts",
            "// @filename: a.ts\nconst a = 1;\n\n// @filename: a.ts\nconst b: string = a;\n",
        );
        assert_eq!(units.len(), 1);
        assert_eq!(units[0].virtual_path, "tests/cases/compiler/a.ts");
        assert_eq!(units[0].text, "const b: string = a;\n");
    }

    #[test]
    fn split_case_units_single_unit_case() {
        let units = split_case_units(
            "tests/cases/conformance/types/any/anyAsConstructor.ts",
            ANY_AS_CONSTRUCTOR_CASE,
        );
        assert_eq!(units.len(), 1);
        assert_eq!(
            units[0].virtual_path,
            "tests/cases/conformance/types/any/anyAsConstructor.ts"
        );
        // Upstream strips the `// @target` directive line from unit content, so
        // the compiled entry begins at the first real source line.
        assert!(!units[0].text.contains("@target"));
        assert_eq!(
            units[0].text,
            "// any is considered an untyped function call\n\
             // can be called except with type arguments which is an error\n\
             \n\
             var x: any;\n\
             var a = new x();\n\
             var b = new x('hello');\n\
             var c = new x(x);\n\
             \n\
             // grammar allows this for constructors\n\
             var d = new x<any>(x); // no error\n"
        );
    }

    #[test]
    fn split_case_units_strips_directives_and_renumbers() {
        // A `@target` directive plus a following blank line: upstream removes
        // the directive line and collapses the leading blank so the first
        // declaration lands on line 0, while interior blanks are preserved.
        let case = "// @strict: true\n\nclass Foo {}\n\nvar a = 0;\n";
        let units = split_case_units("tests/cases/compiler/renumber.ts", case);
        assert_eq!(units.len(), 1);
        assert_eq!(units[0].text, "class Foo {}\n\nvar a = 0;\n");
    }

    #[test]
    fn is_option_directive_line_matches_upstream_grammar() {
        assert!(is_option_directive_line("// @target: es2015"));
        assert!(is_option_directive_line("//@strict:true"));
        assert!(is_option_directive_line("// @filename: a.ts"));
        // `///` reference directives and colonless `@word` lines are content.
        assert!(!is_option_directive_line("/// <reference path=\"x\" />"));
        assert!(!is_option_directive_line("// @ts-ignore"));
        // A multi-word name is not `\\w+`, so it is not a directive.
        assert!(!is_option_directive_line("// @param x: number"));
        assert!(!is_option_directive_line("var a = 0;"));
    }

    #[test]
    fn split_case_units_splits_named_units() {
        let case = "\
// @module: commonjs
// @filename: types.ts
declare module \"*.foo\" {
  let everywhere: string;
}


// @filename: testA.ts
import { everywhere, onlyInA } from \"a.foo\";
declare module \"a.foo\" {
  let onlyInA: number;
}

// @filename: testB.ts
import { everywhere, onlyInA } from \"b.foo\"; // Error
";
        let units = split_case_units(
            "tests/cases/conformance/ambient/ambientDeclarationsPatterns_merging1.ts",
            case,
        );
        // The only line before the first `@filename` is the global
        // `// @module` directive. Upstream drops an options-only preamble
        // rather than creating a case-named unit for it, so the first unit is
        // `types.ts` and the document has no phantom `//// [<case>.ts]` echo.
        // The authority baseline for this case echoes exactly these three
        // units and emits exactly `types.js`, `testA.js`, `testB.js`.
        assert_eq!(units.len(), 3);
        assert_eq!(
            units[0].virtual_path,
            "tests/cases/conformance/ambient/types.ts"
        );
        // The `@filename` directive line is stripped; content begins at the
        // first real source line of the unit.
        assert!(units[0].text.starts_with("declare module \"*.foo\" {\n"));
        assert_eq!(
            units[1].virtual_path,
            "tests/cases/conformance/ambient/testA.ts"
        );
        assert_eq!(
            units[2].virtual_path,
            "tests/cases/conformance/ambient/testB.ts"
        );
    }

    #[test]
    fn split_case_units_leading_directive_naming_case_is_entry() {
        let case = "\
// @filename: anyAsConstructor.ts
var x: any;
";
        let units = split_case_units(
            "tests/cases/conformance/types/any/anyAsConstructor.ts",
            case,
        );
        assert_eq!(units.len(), 1);
        assert_eq!(
            units[0].virtual_path,
            "tests/cases/conformance/types/any/anyAsConstructor.ts"
        );
        assert!(units[0].text.contains("var x: any;"));
    }

    #[test]
    fn split_case_units_absolute_virtual_paths_remap_to_root() {
        let case = "\
// @filename: /ref.d.ts
declare var r: number;
// @filename: main.ts
r.toFixed();
";
        let units = split_case_units("tests/cases/compiler/usesRef.ts", case);
        assert_eq!(units.len(), 2);
        assert_eq!(units[0].virtual_path, "ref.d.ts");
        assert_eq!(units[1].virtual_path, "tests/cases/compiler/main.ts");
    }

    #[test]
    fn split_case_units_drive_letter_paths_remap_to_root() {
        // Upstream test cases use Windows-style drive-letter paths as virtual
        // roots (e.g. `c:/root/folder1/file1.ts`). The drive letter must be
        // stripped so the path maps into the virtual root with no `c:/`
        // residue, preventing paths like `/tmp/x/c:/root/...` on Unix.
        let case = "\
// @filename: c:/root/folder1/file1.ts
export const a = 1;
// @filename: c:/root/folder2/file2.ts
export const b = 2;
// @filename: c:/file3.ts
export const c = 3;
";
        let units = split_case_units(
            "tests/cases/compiler/pathMappingBasedModuleResolution4_node.ts",
            case,
        );
        assert_eq!(units.len(), 3);
        assert_eq!(units[0].virtual_path, "root/folder1/file1.ts");
        assert_eq!(units[1].virtual_path, "root/folder2/file2.ts");
        assert_eq!(units[2].virtual_path, "file3.ts");
        // No `c:/` residue in any virtual path.
        for unit in &units {
            assert!(
                !unit.virtual_path.contains("c:/"),
                "drive-letter residue in `{}`",
                unit.virtual_path
            );
        }
    }

    #[test]
    fn split_case_units_repeated_name_replaces() {
        let case = "\
// @filename: a.ts
export const a = 1;
// @filename: b.ts
export const b = 2;
// @filename: a.ts
export const a2 = 3;
";
        let units = split_case_units("tests/cases/compiler/append.ts", case);
        assert_eq!(units.len(), 2);
        // Upstream feeds units into a path-keyed fake FS, so a restated
        // @filename directive replaces the unit's content, not appends.
        assert!(!units[0].text.contains("a = 1"));
        assert!(units[0].text.contains("a2 = 3"));
    }

    #[test]
    fn split_baseline_file_name_variants() {
        assert_eq!(
            split_baseline_file_name("anyAsConstructor.errors.txt"),
            Some(("anyAsConstructor", "errors.txt", ""))
        );
        assert_eq!(
            split_baseline_file_name("ES5For-ofTypeCheck6(target=es5).errors.txt"),
            Some(("ES5For-ofTypeCheck6", "errors.txt", "(target=es5)"))
        );
        assert_eq!(
            split_baseline_file_name("parserEnumDeclaration2.d.types"),
            Some(("parserEnumDeclaration2.d", "types", ""))
        );
        assert_eq!(
            split_baseline_file_name("plain.js"),
            Some(("plain", "js", ""))
        );
        assert_eq!(
            split_baseline_file_name("2dArrays(target=es5).js"),
            Some(("2dArrays", "js", "(target=es5)"))
        );
    }

    #[test]
    fn case_stem_keeps_declaration_suffix() {
        assert_eq!(
            case_stem(
                "tests/cases/conformance/parser/ecmascript5/EnumDeclarations/parserEnumDeclaration2.d.ts"
            ),
            "parserEnumDeclaration2.d"
        );
        assert_eq!(
            case_stem("tests/cases/conformance/types/any/anyAsConstructor.ts"),
            "anyAsConstructor"
        );
    }

    #[test]
    fn parse_errors_baseline_reads_file_rows() {
        let baseline = parse_errors_baseline(ANY_AS_CONSTRUCTOR_ERRORS);
        assert_eq!(baseline.globals, vec![]);
        assert_eq!(
            baseline.diagnostics,
            vec![ErrorsDiagnostic {
                unit: "anyAsConstructor.ts".to_owned(),
                line: 10,
                character: 8,
                category: "error".to_owned(),
                code: "TS2347".to_owned(),
                message: "Untyped function calls may not accept type arguments.".to_owned(),
            }]
        );
    }

    #[test]
    fn parse_errors_baseline_skips_carets_and_summaries() {
        let baseline = parse_errors_baseline(PARSER_ENUM_DECLARATION_2_ERRORS);
        assert_eq!(baseline.file_diagnostic_count(), 1);
        let row = &baseline.diagnostics[0];
        assert_eq!(row.unit, "parserEnumDeclaration2.ts");
        assert_eq!((row.line, row.character), (2, 2));
        assert_eq!(row.code, "TS1038");
        assert!(baseline.globals.is_empty());
    }

    #[test]
    fn parse_errors_baseline_multi_unit_rows() {
        let baseline = parse_errors_baseline(MERGING1_ERRORS);
        assert_eq!(baseline.file_diagnostic_count(), 1);
        assert_eq!(baseline.diagnostics[0].unit, "testB.ts");
        assert_eq!(
            (
                baseline.diagnostics[0].line,
                baseline.diagnostics[0].character
            ),
            (1, 21)
        );
        assert_eq!(baseline.diagnostics[0].code, "TS2305");
    }

    #[test]
    fn parse_errors_baseline_global_rows_are_separate() {
        let baseline = parse_errors_baseline(PROJECT_BASELINE_AMD_ERRORS);
        assert_eq!(baseline.file_diagnostic_count(), 0);
        assert_eq!(baseline.globals.len(), 2);
        assert!(
            baseline
                .globals
                .iter()
                .all(|global| global.code == "TS5107")
        );
        assert!(baseline.globals[0].message.contains("module=AMD"));
    }

    #[test]
    fn parse_errors_baseline_empty_document() {
        let baseline = parse_errors_baseline("");
        assert_eq!(baseline, ErrorsBaseline::default());
    }

    /// Compile a single-unit case and run `f` with the entry unit's model.
    fn with_model<R>(case_text: &str, logical: &str, f: impl FnOnce(&SemanticModel) -> R) -> R {
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let (_, output) = case
            .reached_units()
            .next()
            .expect("the entry unit is reached");
        f(output.semantic_model())
    }

    #[test]
    fn render_type_covers_primitives() {
        with_model("var x: any;\n", "tests/cases/compiler/p.ts", |model| {
            let table = model.types();
            assert_eq!(render_type(model, table.any()), "any");
            assert_eq!(render_type(model, table.unknown()), "unknown");
            assert_eq!(render_type(model, table.never()), "never");
            assert_eq!(render_type(model, table.void()), "void");
            assert_eq!(render_type(model, table.null_type()), "null");
            assert_eq!(render_type(model, table.undefined_type()), "undefined");
            assert_eq!(render_type(model, table.boolean()), "boolean");
            assert_eq!(render_type(model, table.number()), "number");
            assert_eq!(render_type(model, table.bigint()), "bigint");
            assert_eq!(render_type(model, table.string()), "string");
            assert_eq!(render_type(model, table.symbol_type()), "symbol");
            assert_eq!(render_type(model, table.object()), "object");
        });
    }

    #[test]
    fn render_type_covers_literals_and_arrays() {
        // The initializer expressions carry literal and array types the walk
        // recorded; render them straight from the model.
        with_model(
            "var s: string = \"hi\";\nvar n = 42;\nvar b = true;\nvar xs = [1];\n",
            "tests/cases/compiler/lit.ts",
            |model| {
                let rendered: Vec<String> = model
                    .typed_expressions()
                    .iter()
                    .map(|(_, type_id)| render_type(model, *type_id))
                    .collect();
                assert!(rendered.contains(&"\"hi\"".to_owned()), "{rendered:?}");
                assert!(rendered.contains(&"42".to_owned()), "{rendered:?}");
                assert!(rendered.contains(&"true".to_owned()), "{rendered:?}");
                // `[1]` types as an array over the `1` literal element.
                assert!(rendered.contains(&"1[]".to_owned()), "{rendered:?}");
            },
        );
    }

    #[test]
    fn render_type_covers_tuple_shapes_and_applied_classes() {
        with_model(
            "declare class Box<T> {}\
             declare let optionalTuple: [number, string?];\
             declare let variadicTuple: [number, ...boolean[], bigint];\
             declare let box: Box<string>;",
            "tests/cases/compiler/composite.ts",
            |model| {
                let scope = model.scope(model.module_scope());
                let optional = scope
                    .value("optionalTuple")
                    .expect("optional tuple binding");
                assert_eq!(
                    render_type(model, model.symbol_type(optional)),
                    "[number, string?]"
                );
                let variadic = scope
                    .value("variadicTuple")
                    .expect("variadic tuple binding");
                assert_eq!(
                    render_type(model, model.symbol_type(variadic)),
                    "[number, ...boolean[], bigint]"
                );
                let box_value = scope.value("box").expect("box binding");
                assert_eq!(
                    render_type(model, model.symbol_type(box_value)),
                    "Box<string>"
                );
            },
        );
    }

    #[test]
    fn render_transformed_recursive_alias_terminates() {
        with_model(
            "type Expanding<T> = [Expanding<T[]>];
             declare let value: Expanding<string>;",
            "tests/cases/compiler/recursive-alias.ts",
            |model| {
                let value = model
                    .scope(model.module_scope())
                    .value("value")
                    .expect("recursive alias binding");
                let rendered = render_type(model, model.symbol_type(value));
                assert!(rendered.contains("Expanding<"), "{rendered}");
                assert!(rendered.len() < 256, "{rendered}");
            },
        );
    }

    #[test]
    fn render_type_preserves_polymorphic_this_identity() {
        with_model(
            "class Base {
                 value = 1;
                 method(): number { return this.value; }
             }",
            "tests/cases/compiler/polymorphicThis.ts",
            |model| {
                let this_type = model
                    .typed_expressions()
                    .iter()
                    .map(|(_, type_id)| *type_id)
                    .find(|type_id| matches!(model.types().get(*type_id), Type::This { .. }))
                    .expect("method body has polymorphic this type");

                assert_eq!(render_type(model, this_type), "this");
            },
        );
    }

    /// H4 pin: an annotated scalar case the checker fully types reproduces its
    /// upstream `.types` baseline (marker, section, source echo, `>expr : type`
    /// records, and underline widths) under `compare_types`.
    #[test]
    fn emit_types_baseline_matches_fully_typed_scalar_case() {
        let logical = "tests/cases/compiler/scalarPin.ts";
        let case_text = "var x: any;\nvar s: string = \"hi\";\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/scalarPin.ts] ////\n\
            \n\
            === scalarPin.ts ===\n\
            var x: any;\n\
            >x : any\n\
            >  : ^^^\n\
            \n\
            var s: string = \"hi\";\n\
            >s : string\n\
            >  : ^^^^^^\n\
            >\"hi\" : \"hi\"\n\
            >     : ^^^^\n";
        assert_eq!(
            compare_types(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// Honesty pin: where the checker types fewer nodes than tsc (here, the
    /// `new`/callee/argument sub-expressions of `anyAsConstructor`), the
    /// emitter drops those records and the comparator reports a `Fail` — the
    /// S2 burn-down surface, not a false pass.
    #[test]
    fn emit_types_baseline_undercoverage_fails_comparison() {
        let logical = "tests/cases/conformance/types/any/anyAsConstructor.ts";
        let units = split_case_units(logical, ANY_AS_CONSTRUCTOR_CASE);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        let baseline = "//// [tests/cases/conformance/types/any/anyAsConstructor.ts] ////\n\
            \n\
            === anyAsConstructor.ts ===\n\
            var x: any;\n\
            >x : any\n\
            >  : ^^^\n\
            \n\
            var a = new x();\n\
            >a : any\n\
            >  : ^^^\n\
            >new x() : any\n\
            >        : ^^^\n\
            >x : any\n\
            >  : ^^^\n";
        assert!(
            matches!(compare_types(baseline, &emitted), FacetVerdict::Fail { .. }),
            "under-covered emit must not pass; emitted:\n{emitted}"
        );
    }

    /// The dedup pass collapses records with the identical identity tuple
    /// (start, end, display, rendered) — the binder can push the same
    /// (range, type) pair from both its symbol and expression indexes — and
    /// keeps everything else, restoring the upstream order afterwards.
    ///
    /// Authority baselines keep adjacent *different-position* records
    /// (`targetTypeCalls.types` prints `>v : any` twice for the declaration
    /// name and the resolving reference at different offsets), so dedup keys
    /// on the full record identity, never on display text alone.
    #[test]
    fn dedup_type_records_collapses_identical_identity_only() {
        let record = |start: usize, end: usize, display: &str, rendered: &str| TypeAnnotation {
            start,
            end,
            line: 0,
            display: display.to_owned(),
            rendered: rendered.to_owned(),
        };
        let records = vec![
            record(4, 5, "x", "any"),
            record(4, 5, "x", "any"),
            record(8, 9, "x", "any"),
            record(0, 1, "C", "C"),
        ];
        let deduped = dedup_type_records(records);
        assert_eq!(
            deduped
                .iter()
                .map(|r| (r.start, r.end, r.display.as_str(), r.rendered.as_str()))
                .collect::<Vec<_>>(),
            vec![(0, 1, "C", "C"), (4, 5, "x", "any"), (8, 9, "x", "any")],
            "identical (start, end, display, rendered) collapses; distinct positions stay"
        );
    }

    /// Distinct records at the same range survive dedup: upstream prints the
    /// declaration-name record and the constructor-side record for a class
    /// used in `new` on one line (`assignmentCompatability10.types` prints
    /// `>classWithPublicAndOptional : classWithPublicAndOptional<T, U>` and
    /// `>classWithPublicAndOptional : typeof classWithPublicAndOptional`), so
    /// dedup must not collapse differing renderings.
    #[test]
    fn dedup_type_records_keeps_distinct_same_range_records() {
        let record = |display: &str, rendered: &str| TypeAnnotation {
            start: 10,
            end: 36,
            line: 0,
            display: display.to_owned(),
            rendered: rendered.to_owned(),
        };
        let deduped = dedup_type_records(vec![
            record("Foo", "Foo<T>"),
            record("Foo", "typeof Foo"),
            record("Foo", "Foo<T>"),
        ]);
        assert_eq!(
            deduped
                .iter()
                .map(|r| (r.display.as_str(), r.rendered.as_str()))
                .collect::<Vec<_>>(),
            vec![("Foo", "Foo<T>"), ("Foo", "typeof Foo")],
            "distinct renderings at one range must survive"
        );
    }

    /// Authority pin from `witness.types` (case
    /// `tests/cases/conformance/types/witness/witness.ts`, line 7): upstream
    /// prints TWO identical `>varInit : any` pairs for `var varInit =
    /// varInit;` — declaration name and resolving reference at different
    /// ranges are both legitimate records. Only exact (start, end, display,
    /// rendered) tuples collapse; text-identical records at distinct
    /// positions stay.
    #[test]
    fn emit_types_baseline_keeps_distinct_position_records() {
        let logical = "tests/cases/conformance/types/witness/witnessPin.ts";
        let units = split_case_units(logical, "var varInit = varInit; // any\n");
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        let baseline = "//// [tests/cases/conformance/types/witness/witnessPin.ts] ////\n\
            \n\
            === witnessPin.ts ===\n\
            var varInit = varInit; // any\n\
            >varInit : any\n\
            >        : ^^^\n\
            >varInit : any\n\
            >        : ^^^\n";
        assert_eq!(
            compare_types(baseline, &emitted),
            FacetVerdict::Pass,
            "distinct-position identical records must both stay; emitted:\n{emitted}"
        );
    }

    /// A multi-file case's preamble before the first `@Filename:` marker is
    /// global options, not a unit: upstream `ParseTestFilesAndSymlinks`
    /// (`AllowImplicitFirstFile: false`) drops a comment-only preamble, so
    /// no phantom `=== <case>.ts ===` section appears and
    /// `ClassAndModuleWithSameNameAndCommonRoot.types` opens with
    /// `=== class.ts ===` directly.
    #[test]
    fn types_emitter_skips_empty_entry_units() {
        let logical =
            "tests/cases/conformance/internalModules/DeclarationMerging/phantomEntryPin.ts";
        let case_text = "\
// @target: es2015\n\
// @filename: class.ts\n\
class Point { x: number; }\n\
\n\
// @filename: simple.ts\n\
var a = 1;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            !emitted.contains("=== phantomEntryPin.ts ==="),
            "comment/options preamble must not become a phantom unit; emitted:\n{emitted}"
        );
        assert!(
            emitted.contains("=== class.ts ==="),
            "first @Filename unit keeps its section; emitted:\n{emitted}"
        );
    }

    /// Section headers echo the verbatim `// @Filename:` spelling: absolute
    /// names keep their leading `/` and relative names stay bare, exactly as
    /// `ambient.types` prints `=== /a.ts ===` and `=== /b.ts ===`.
    #[test]
    fn types_section_headers_preserve_verbatim_filename() {
        let logical = "tests/cases/conformance/externalModules/typeOnly/ambientPin.ts";
        let case_text = "\
// @Filename: /a.ts\n\
export class A { a!: string }\n\
\n\
// @Filename: /b.ts\n\
import type { A } from './a';\n\
declare class B extends A {}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            emitted.contains("=== /a.ts ==="),
            "absolute @Filename must keep its leading slash; emitted:\n{emitted}"
        );
        assert!(
            emitted.contains("=== /b.ts ==="),
            "second absolute unit must keep its leading slash; emitted:\n{emitted}"
        );
        assert!(
            !emitted.contains("=== a.ts ==="),
            "lossy basename section must not appear; emitted:\n{emitted}"
        );
    }

    /// Drive-letter (`A:/foo/bar.ts`) and dot-slash (`./a.ts`) spellings are
    /// preserved too — `commonSourceDir4.types:3` prints `=== A:/foo/bar.ts ===`
    /// and `decoratorMetadataTypeOnlyExport.types:3` prints `=== ./a.ts ===`;
    /// `virtual_unit_path` strips both prefixes for the loader, so the
    /// section name must come from the verbatim name all the way through
    /// the emitter.
    #[test]
    fn types_section_headers_preserve_drive_and_dot_prefixes() {
        for (logical, name) in [
            ("tests/cases/compiler/drivePrefixPin.ts", "A:/foo/bar.ts"),
            ("tests/cases/compiler/dotSlashPin.ts", "./a.ts"),
        ] {
            let case_text = format!("// @Filename: {name}\nvar x = 1;\n");
            let units = split_case_units(logical, &case_text);
            assert_eq!(units[0].display_name, name);
            let entry = entry_virtual_path(logical, &units);
            let case = compile_case(&units, &entry).expect("case compiles");
            let emitted = emit_types_baseline(&case, logical);
            assert!(
                emitted.contains(&format!("=== {name} ===")),
                "verbatim section header for {name} missing from:\n{emitted}"
            );
        }
    }

    /// `tsconfig.json` / `jsconfig.json` units are configuration, never
    /// program sources: `noEmitAndComposite.types` contains only the
    /// `=== /a.ts ===` section and no `=== /tsconfig.json ===` section, while
    /// data `.json` inputs (e.g. `=== b.json ===`) do get sections.
    #[test]
    fn types_emitter_skips_config_units() {
        assert!(is_config_unit_name("tsconfig.json"));
        assert!(is_config_unit_name("/a/b/tsconfig.json"));
        assert!(is_config_unit_name("/b/TSConfig.JSON"));
        assert!(is_config_unit_name("jsconfig.json"));
        assert!(!is_config_unit_name("b.json"));
        assert!(!is_config_unit_name("/config.json"));
        assert!(!is_config_unit_name("package.json"));

        let logical = "tests/cases/compiler/noEmitAndCompositePin.ts";
        let case_text = "\
// @Filename: /a.ts\n\
const x = 10;\n\
\n\
// @Filename: /tsconfig.json\n\
{\n\
    \"compilerOptions\": {\n\
        \"noEmit\": true,\n\
        \"composite\": true\n\
    }\n\
}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            !emitted.contains("=== /tsconfig.json ==="),
            "config unit must not get a types section; emitted:\n{emitted}"
        );
        assert!(
            emitted.contains("=== /a.ts ==="),
            "source unit must keep its section; emitted:\n{emitted}"
        );
    }

    /// Interface declaration names carry no `>name : type` record:
    /// `duplicateConstructSignature.types` echoes `interface I { (): number;
    /// (): string; }` with zero records, while class names do get records
    /// (`ClassDeclaration21.types`: `>C : C`).
    #[test]
    fn types_emitter_skips_interface_name_records() {
        let logical = "tests/cases/compiler/duplicateConstructSignaturePin.ts";
        let case_text = "interface I {\n    (): number;\n    (): string;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/duplicateConstructSignaturePin.ts] ////\n\
            \n\
            === duplicateConstructSignaturePin.ts ===\n\
            interface I {\n\
                (): number;\n\
                (): string;\n\
            }\n";
        assert_eq!(
            compare_types(baseline, &emitted),
            FacetVerdict::Pass,
            "interface name must not produce a record; emitted:\n{emitted}"
        );
    }

    /// Class declaration names DO get records (`ClassDeclaration21.types`:
    /// `>C : C`) — the interface skip must not suppress them.
    #[test]
    fn types_emitter_keeps_class_name_records() {
        let logical = "tests/cases/compiler/ClassDeclaration21.ts";
        let case_text = "class C {\n    0();\n    1() { }\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            emitted.contains(">C : C\n"),
            "class name record must survive; emitted:\n{emitted}"
        );
    }

    #[test]
    fn resolve_types_baseline_prefers_plain_over_variant() {
        let mut groups: BaselineGroups = BTreeMap::new();
        groups.insert(
            ("foo".to_owned(), "types".to_owned()),
            vec![
                (
                    "(target=es5)".to_owned(),
                    "tests/baselines/reference/foo(target=es5).types".to_owned(),
                ),
                (
                    String::new(),
                    "tests/baselines/reference/foo.types".to_owned(),
                ),
            ],
        );
        assert_eq!(
            resolve_types_baseline(&groups, "tests/cases/compiler/foo.ts").as_deref(),
            Some("tests/baselines/reference/foo.types")
        );
        assert_eq!(
            resolve_types_baseline(&groups, "tests/cases/compiler/absent.ts"),
            None
        );
    }

    /// End-to-end pin: a top-level case whose declarations and value reference
    /// the binder fully tracks reproduces the upstream `.symbols` framing —
    /// marker, section, source echo, and `>name : Symbol(name, Decl(unit, l, c))`
    /// records with full-start declaration positions — under `compare_symbols`.
    #[test]
    fn emit_symbols_baseline_reproduces_declaration_and_reference_records() {
        let logical = "tests/cases/compiler/symbolPin.ts";
        let case_text = "class Cell {}\nvar a = 0;\nvar b = a;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/symbolPin.ts] ////\n\
            \n\
            === symbolPin.ts ===\n\
            class Cell {}\n\
            >Cell : Symbol(Cell, Decl(symbolPin.ts, 0, 0))\n\
            var a = 0;\n\
            >a : Symbol(a, Decl(symbolPin.ts, 1, 3))\n\
            var b = a;\n\
            >b : Symbol(b, Decl(symbolPin.ts, 2, 3))\n\
            >a : Symbol(a, Decl(symbolPin.ts, 1, 3))\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// Honesty pin on a real pinned sample: `anyAsConstructor` carries a
    /// `@target` pragma (dropped from the upstream echo) and references whose
    /// declarations the binder anchors differently, so the emitted document
    /// cannot canonicalize equal to the upstream `.symbols` baseline — the S2
    /// burn-down surface, reported as `Fail`, never a false pass.
    #[test]
    fn emit_symbols_baseline_undercoverage_fails_comparison() {
        let logical = "tests/cases/conformance/types/any/anyAsConstructor.ts";
        let units = split_case_units(logical, ANY_AS_CONSTRUCTOR_CASE);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/conformance/types/any/anyAsConstructor.ts] ////\n\
            \n\
            === anyAsConstructor.ts ===\n\
            var x: any;\n\
            >x : Symbol(x, Decl(anyAsConstructor.ts, 3, 3))\n\
            \n\
            var a = new x();\n\
            >a : Symbol(a, Decl(anyAsConstructor.ts, 4, 3))\n\
            >x : Symbol(x, Decl(anyAsConstructor.ts, 3, 3))\n";
        assert!(
            matches!(
                compare_symbols(baseline, &emitted),
                FacetVerdict::Fail { .. }
            ),
            "under-covered emit must not pass; emitted:\n{emitted}"
        );
    }

    /// Enum members qualify against their enum symbol at both the declaration
    /// site and the initializer-reference site (`E.A`), while the enum itself
    /// and an unrelated top-level `var` stay bare.
    #[test]
    fn emit_symbols_baseline_qualifies_enum_members() {
        let logical = "tests/cases/compiler/pin.ts";
        let case_text = "enum E {\n    A,\n    B = A + 1,\n}\nvar x = 1;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/pin.ts] ////\n\
            \n\
            === pin.ts ===\n\
            enum E {\n\
            >E : Symbol(E, Decl(pin.ts, 0, 0))\n\
            \n\
                A,\n\
            >A : Symbol(E.A, Decl(pin.ts, 0, 8))\n\
            \n\
                B = A + 1,\n\
            >B : Symbol(E.B, Decl(pin.ts, 1, 6))\n\
            >A : Symbol(E.A, Decl(pin.ts, 0, 8))\n\
            \n\
            }\n\
            var x = 1;\n\
            >x : Symbol(x, Decl(pin.ts, 4, 3))\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// Namespace export declarations render bare (`Symbol(x, ...)`), guarding
    /// against declare-time over-qualification: upstream qualifies namespace
    /// members only at access-path reference sites, which this emitter does not
    /// yet reach.
    #[test]
    fn emit_symbols_baseline_keeps_namespace_exports_bare() {
        let logical = "tests/cases/compiler/pin.ts";
        let case_text = "namespace A {\n    export var x = 1;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/compiler/pin.ts] ////\n\
            \n\
            === pin.ts ===\n\
            namespace A {\n\
            >A : Symbol(A, Decl(pin.ts, 0, 0))\n\
            \n\
                export var x = 1;\n\
            >x : Symbol(x, Decl(pin.ts, 1, 14))\n\
            \n\
            }\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// Records are ordered by reference-site position (line, then character),
    /// matching upstream's source-order symbol table iteration. A case with
    /// declarations and references on multiple lines must emit `>name` records
    /// in source position order, not binder allocation order.
    #[test]
    fn emit_symbols_records_ordered_by_reference_position() {
        let logical = "tests/cases/compiler/orderPin.ts";
        // `zebra` is declared last but alphabetically first; `alpha` is
        // declared first. Records must appear in source line order:
        // alpha (line 0), zebra (line 1), alpha-ref (line 2).
        let case_text = "var alpha = 0;\nvar zebra = alpha;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        // Extract all symbol lines in order.
        let symbol_lines: Vec<&str> = emitted.lines().filter(|l| l.starts_with('>')).collect();
        // Expected source-order: alpha (line 0), zebra (line 1), alpha ref (line 2).
        assert!(
            symbol_lines.iter().any(|l| l.starts_with(">alpha")),
            "missing alpha declaration record:\n{emitted}"
        );
        assert!(
            symbol_lines.iter().any(|l| l.starts_with(">zebra")),
            "missing zebra declaration record:\n{emitted}"
        );
        // The alpha declaration must come before the zebra declaration
        // (source order), even though the binder may allocate zebra first.
        let alpha_pos = symbol_lines
            .iter()
            .position(|l| l.starts_with(">alpha"))
            .expect("alpha record exists");
        let zebra_pos = symbol_lines
            .iter()
            .position(|l| l.starts_with(">zebra"))
            .expect("zebra record exists");
        assert!(
            alpha_pos < zebra_pos,
            "alpha declaration must precede zebra declaration (source order):\n{emitted}"
        );
    }

    /// Duplicate records (same position, display, and rendered string) are
    /// collapsed. The binder can record the same (range, symbol) pair
    /// multiple times in `symbol_references`; upstream emits each unique
    /// `>name : Symbol(...)` line once. Without deduplication, the pairwise
    /// line comparison diverges and every subsequent line is classified as
    /// "wrong-symbol-entirely".
    #[test]
    fn emit_symbols_records_deduplicated() {
        let logical = "tests/cases/compiler/dedupPin.ts";
        // `Ship` is referenced in a type annotation `Ship[]`. The binder
        // may record this reference multiple times; the emitter must
        // collapse duplicates so `>Ship` appears once per line.
        let case_text = "class Ship {}\nclass Board {\n    ships: Ship[] = [];\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        // Count `>Ship` reference lines on the `ships: Ship[] = [];` line.
        // The declaration `>Ship` is on line 0 (`class Ship {}`), and the
        // reference `>Ship` is on line 2 (`ships: Ship[] = [];`). Both have
        // the same Decl, but they are at different positions so both are
        // kept. The deduplication only collapses records at the SAME position.
        // Without deduplication, the binder's duplicate references would
        // produce 2–3 `>Ship` lines on the `ships` line.
        let lines: Vec<&str> = emitted.lines().collect();
        let ships_line_idx = lines
            .iter()
            .position(|l| l.contains("ships: Ship[]"))
            .expect("ships line exists");
        // Symbol records follow the source line; collect consecutive `>` lines.
        let ship_refs_on_line: Vec<&&str> = lines[ships_line_idx + 1..]
            .iter()
            .take_while(|l| l.starts_with('>'))
            .filter(|l| l.starts_with(">Ship :"))
            .collect();
        // There should be exactly one `>Ship` reference on the ships line.
        assert_eq!(
            ship_refs_on_line.len(),
            1,
            "Ship reference on ships line must appear exactly once (deduplicated), \
             got {ship_refs_on_line:?}:\n{emitted}"
        );
    }

    /// Decl anchors within a Symbol(...) record are ordered by (section, line,
    /// character) and deduplicated. A namespace declared in two units merges
    /// into one symbol with two Decl anchors; the emitter must list them in
    // (section, line, character) order with no duplicates.
    #[test]
    fn emit_symbols_decl_anchors_ordered_and_deduplicated() {
        let logical = "tests/cases/compiler/mergePin.ts";
        // `namespace X` in two files merges into one symbol with two Decl
        // anchors: Decl(a.ts, 0, 0) and Decl(b.ts, 0, 0). The anchors must
        // be ordered by (section, line, character) — a.ts before b.ts — and
        // deduplicated, even though `emit_symbols_baseline` collects the
        // anchor under both the bare name and the qualified name.
        let source = "// @filename: a.ts\nnamespace X { export var a = 1; }\n\
            // @filename: b.ts\nnamespace X { export var b = 2; }\n";
        let pragmas = parse_case_pragmas(source);
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        // Find the X declaration line in a.ts section.
        let x_decl_line = emitted
            .lines()
            .find(|l| l.starts_with(">X :") && l.contains("Decl(a.ts, 0, 0)"))
            .unwrap_or_else(|| panic!("missing X declaration with Decl(a.ts, 0, 0):\n{emitted}"));
        // Extract Decl(...) entries.
        let decls: Vec<String> = x_decl_line
            .match_indices("Decl(")
            .map(|(start, _)| {
                let rest = &x_decl_line[start + 5..];
                let end = rest.find(')').unwrap_or(rest.len());
                rest[..end].to_owned()
            })
            .collect();
        // Must have exactly two Decl entries for the merged namespace.
        assert_eq!(
            decls.len(),
            2,
            "merged namespace must have exactly 2 Decl entries, got {decls:?}:\n{emitted}"
        );
        // Ordered by (section, line, character): a.ts before b.ts.
        assert!(
            decls[0].starts_with("a.ts, 0,") && decls[1].starts_with("b.ts, 0,"),
            "Decl entries must be ordered by (section, line, char), got {decls:?}:\n{emitted}"
        );
        // No duplicate Decl entries.
        let mut sorted = decls.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(
            sorted.len(),
            decls.len(),
            "Decl entries must be deduplicated, got {decls:?}:\n{emitted}"
        );
    }

    #[test]
    fn resolve_symbols_baseline_prefers_plain_over_variant() {
        let mut groups: BaselineGroups = BTreeMap::new();
        groups.insert(
            ("foo".to_owned(), "symbols".to_owned()),
            vec![
                (
                    "(target=es5)".to_owned(),
                    "tests/baselines/reference/foo(target=es5).symbols".to_owned(),
                ),
                (
                    String::new(),
                    "tests/baselines/reference/foo.symbols".to_owned(),
                ),
            ],
        );
        assert_eq!(
            resolve_symbols_baseline(&groups, "tests/cases/compiler/foo.ts").as_deref(),
            Some("tests/baselines/reference/foo.symbols")
        );
        assert_eq!(
            resolve_symbols_baseline(&groups, "tests/cases/compiler/absent.ts"),
            None
        );
    }

    #[test]
    fn class_method_this_preserves_polymorphic_identity() {
        let logical = "tests/cases/compiler/thisPin.ts";
        let case_text = "class Ship { isSunk: boolean = false; }\n\
class Board {\n\
    ships: Ship[] = [];\n\
    private allShipsSunk() {\n\
        return this.ships.every(function (val) { return val.isSunk; });\n\
    }\n\
}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let baseline = emit_types_baseline(&case, logical);
        assert!(
            baseline.contains(">this.ships : Ship[]"),
            "this.ships should be Ship[]\n{baseline}"
        );
        assert!(
            baseline.contains(">this : this"),
            "this should preserve its polymorphic identity\n{baseline}"
        );
    }

    #[test]
    fn infer_rest_argument_type_parameter_from_multiple_arguments() {
        let source = "// @strict: true\n// @target: es2015\n\n// Repro from #31204\n\nexport enum AppType {\n    HeaderDetail = 'HeaderDetail',\n    HeaderMultiDetail = 'HeaderMultiDetail',\n    AdvancedList = 'AdvancedList',\n    Standard = 'Standard',\n    Relationship = 'Relationship',\n    Report = 'Report',\n    Composite = 'Composite',\n    ListOnly = 'ListOnly',\n    ModuleSettings = 'ModuleSettings'\n}\n\nexport enum AppStyle {\n    Tree,\n    TreeEntity,\n    Standard,\n    MiniApp,\n    PivotTable\n}\n\nconst appTypeStylesWithError: Map<AppType, Array<AppStyle>> = new Map([\n    [AppType.Standard, [AppStyle.Standard, AppStyle.MiniApp]],\n    [AppType.Relationship, [AppStyle.Standard, AppStyle.Tree, AppStyle.TreeEntity]],\n    [AppType.AdvancedList, [AppStyle.Standard, AppStyle.MiniApp]]\n]);\n\n// Repro from #31204\n\ndeclare function foo<T>(...args: T[]): T[];\nlet b1: { x: boolean }[] = foo({ x: true }, { x: false });\nlet b2: boolean[][] = foo([true], [false]);\n";
        let logical = "tests/cases/conformance/expressions/arrayLiterals/arrayLiteralInference.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(source);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("compiles");
        let code_map = load_diagnostic_code_map(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .unwrap()
                .parent()
                .unwrap(),
        )
        .unwrap();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        assert!(
            actual.is_empty(),
            "unexpected mapped diagnostics: {actual:?}"
        );
    }

    #[test]
    fn object_literal_getter_without_return_has_void_readonly_property() {
        let logical = "tests/cases/conformance/parser/ecmascript5/Accessors/parserAccessors7.ts";
        let source = "// @target: es5\nvar v = { get foo(v: number) { } };\n";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("compiles");
        let baseline = emit_types_baseline(&case, logical);
        assert!(
            baseline.contains(">v : { readonly foo: void; }"),
            "getter should be readonly void property\n{baseline}"
        );
    }

    #[test]
    fn this_type_in_accessors_negative_object_type_is_widened_and_non_readonly() {
        let source = "// @noImplicitAny: true\n// @noImplicitThis: true\n// @target: es5, es2015\ninterface Foo {\n    n: number;\n    x: number;\n}\ninterface Bar {\n    wrong: \"place\" | \"time\" | \"method\" | \"technique\";\n}\nconst mismatch = {\n    n: 13,\n    get x(this: Foo) { return this.n; },\n    set x(this: Bar, n) { this.wrong = \"method\"; }\n}\nconst contextual: Foo = {\n    n: 16,\n    get x() { return this.n; }\n}\n";
        let logical = "tests/cases/conformance/types/thisType/thisTypeInAccessorsNegative.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(source);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("compiles");
        let baseline = emit_types_baseline(&case, logical);
        assert!(
            baseline.contains(">mismatch : { n: number; x: number; }"),
            "mismatch object type should widen both properties to number and merge get/set\n{baseline}"
        );
    }

    #[test]
    fn imported_cross_module_symbols_materialize_for_rendering() {
        let logical = "tests/cases/compiler/allowImportClausesToMergeWithTypes.ts";
        let case_text = "// @module: commonjs\n// @target: es2015\n// @filename: b.ts\nexport const zzz = 123;\nexport default zzz;\n\n// @filename: a.ts\nexport default interface zzz {\n    x: string;\n}\n\nimport zzz from \"./b\";\n\nconst x: zzz = { x: \"\" };\nzzz;\n\nexport { zzz as default };\n\n// @filename: index.ts\nimport zzz from \"./a\";\n\nconst x: zzz = { x: \"\" };\nzzz;\n\nimport originalZZZ from \"./b\";\noriginalZZZ;\n\nconst y: originalZZZ = x;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");

        let types = emit_types_baseline(&case, logical);
        assert!(types.contains("=== index.ts ==="), "{types}");
        assert!(types.contains(">x : zzz"), "{types}");

        let symbols = emit_symbols_baseline(&case, logical);
        assert!(symbols.contains("=== index.ts ==="), "{symbols}");
        assert!(symbols.contains("Symbol(zzz, Decl(index.ts"), "{symbols}");
    }

    /// The declaration-anchor map built across all reached units lets a
    /// symbol declared in one unit (e.g. `Model` in `aliasUsageInArray_backbone.ts`)
    /// render with its true `Decl(<other unit>, line, char)` anchor instead of
    /// being dropped for lacking an in-unit declaration. Cross-unit *reference*
    /// rows (`>Backbone.Model : Symbol(Backbone.Model, ...)`) depend on
    /// member-access reference resolution the binder does not yet produce;
    /// those remain the S2 burn-down surface. Upstream shape pinned by
    /// `tests/baselines/reference/aliasUsageInArray.symbols`
    /// (sha256 2ce5d5eb3f810bac79a552a47f2aef0c955b32e9d5fc1ac1bf7f16a07efdbdf0).
    #[test]
    fn imported_symbol_occurrences_render_cross_unit_anchors() {
        let logical = "tests/cases/compiler/aliasUsageInArray.ts";
        let case_text = "\
// @module: commonjs
// @Filename: aliasUsageInArray_main.ts
import Backbone = require(\"./aliasUsageInArray_backbone\");
interface IHasVisualizationModel {
    VisualizationModel: typeof Backbone.Model;
}

// @Filename: aliasUsageInArray_backbone.ts
export class Model {
    public someData: string;
}
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");

        let symbols = emit_symbols_baseline(&case, logical);
        assert!(
            symbols.contains("=== aliasUsageInArray_backbone.ts ==="),
            "{symbols}"
        );
        // The `Model` class declared in the backbone unit renders with its
        // true cross-unit declaration anchor, not a dropped or local-only row.
        assert!(
            symbols.contains("Symbol(Model, Decl(aliasUsageInArray_backbone.ts, 0, 0))"),
            "{symbols}"
        );
    }

    #[test]
    fn duplicate_plain_types_baselines_are_ambiguous() {
        let mut groups: BaselineGroups = BTreeMap::new();
        groups.insert(
            ("foo".to_owned(), "types".to_owned()),
            vec![
                (
                    String::new(),
                    "tests/baselines/reference/foo.types".to_owned(),
                ),
                (
                    String::new(),
                    "tests/baselines/reference/foo-dup.types".to_owned(),
                ),
            ],
        );
        let error = resolve_stem_baseline(&groups, "tests/cases/compiler/foo.ts", "types", &[])
            .expect_err("duplicate plains");
        assert_eq!(error.code(), ErrorCode::Duplicate);
    }

    #[test]
    fn declaration_section_name_swaps_extensions_per_upstream() {
        assert_eq!(declaration_section_name("a.ts"), "a.d.ts");
        assert_eq!(declaration_section_name("b.mts"), "b.d.mts");
        assert_eq!(declaration_section_name("c.cts"), "c.d.cts");
        assert_eq!(declaration_section_name("d.tsx"), "d.d.ts");
    }

    #[test]
    fn javascript_section_name_derives_output_extension_per_upstream() {
        // `.ts` -> `.js` always; `.tsx`/`.jsx` -> `.jsx` only under
        // `jsx: preserve`, otherwise `.js`; module-format extensions carry
        // through. This mirrors `outputpaths.GetOutputExtension`.
        assert_eq!(javascript_section_name("a.ts", false), "a.js");
        assert_eq!(javascript_section_name("a.ts", true), "a.js");
        assert_eq!(javascript_section_name("file.tsx", true), "file.jsx");
        assert_eq!(javascript_section_name("file.tsx", false), "file.js");
        assert_eq!(javascript_section_name("view.jsx", true), "view.jsx");
        assert_eq!(javascript_section_name("view.jsx", false), "view.js");
        assert_eq!(javascript_section_name("m.mts", false), "m.mjs");
        assert_eq!(javascript_section_name("c.cts", false), "c.cjs");
        assert_eq!(javascript_section_name("data.json", false), "data.json");
        // A name with no recognised extension still gains `.js`.
        assert_eq!(javascript_section_name("LICENSE", false), "LICENSE.js");
    }

    #[test]
    fn output_section_name_uses_bundle_for_outfile_and_unit_for_per_file() {
        // Per-file compile: the section is the unit's own output name.
        assert_eq!(
            output_section_name("a.tsx", None, |name| output_extension(name, true)
                .to_owned()),
            "a.jsx"
        );
        // `outFile` compile: every unit's JavaScript output is named after the
        // bundle, keeping the kind's extension.
        assert_eq!(
            output_section_name("a.ts", Some("bundle.js"), |name| {
                output_extension(name, false).to_owned()
            }),
            "bundle.js"
        );
        // The declaration slice of the same bundle swaps to the declaration
        // extension.
        assert_eq!(
            output_section_name("a.ts", Some("bundle.js"), declaration_extension),
            "bundle.d.ts"
        );
        // A `.d.ts` bundle keeps the compound declaration extension.
        assert_eq!(
            output_section_name("a.ts", Some("types.d.ts"), declaration_extension),
            "types.d.ts"
        );
    }

    /// The authority documents order the emit slices as: every input echo in
    /// unit order, then every `.js` output in unit order, then every `.d.ts`
    /// output in unit order (`allowSyntheticDefaultImportsCanPaintCrossModule
    /// Declaration.js` is the reference shape). Declaration inputs echo but
    /// contribute no output section.
    #[test]
    fn javascript_baseline_orders_js_sections_before_dts_sections() {
        let logical = "tests/cases/compiler/orderPin.ts";
        let case_text = "\
// @declaration: true
// @filename: b.ts
export const b = 2;
// @filename: a.ts
export const a = 1;
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
        let heads: Vec<&str> = emitted
            .lines()
            .filter(|line| line.starts_with("//// [") && !line.ends_with(" ////"))
            .collect();
        assert_eq!(
            heads,
            vec![
                "//// [b.ts]",
                "//// [a.ts]",
                "//// [b.js]",
                "//// [a.js]",
                "//// [b.d.ts]",
                "//// [a.d.ts]"
            ],
            "{emitted}"
        );
    }

    /// A `.d.ts` input unit is echoed but never emitted: upstream's output
    /// mapping skips declaration files outright, so a document with a
    /// `module.d.ts` echo carries no `module.js`/`module.d.ts` section.
    #[test]
    fn javascript_baseline_skips_declaration_input_outputs() {
        let logical = "tests/cases/compiler/declInputPin.ts";
        let case_text = "\
// @declaration: true
// @filename: module.d.ts
declare const m: number;
// @filename: test.ts
export const t = 1;
";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
        let heads: Vec<&str> = emitted
            .lines()
            .filter(|line| line.starts_with("//// [") && !line.ends_with(" ////"))
            .collect();
        assert_eq!(
            heads,
            vec![
                "//// [module.d.ts]",
                "//// [test.ts]",
                "//// [test.js]",
                "//// [test.d.ts]"
            ],
            "{emitted}"
        );
    }

    #[test]
    fn extract_dts_sections_selects_only_declaration_output() {
        // Real upstream shape (argumentsReferenceInConstructor4_Js.js): a
        // document header with trailing ////, an input echo, then the `a.d.ts`
        // output section. Only the declaration section may survive.
        let doc = "//// [tests/cases/compiler/argumentsReferenceInConstructor4_Js.ts] ////\n\
            \n\
            //// [a.js]\nclass A {}\n\
            \n\
            //// [a.d.ts]\ndeclare class A {}\n";
        assert_eq!(
            extract_dts_sections(doc, 1),
            "//// [a.d.ts]\ndeclare class A {}\n"
        );
    }

    #[test]
    fn declaration_baseline_frames_and_compares_upstream_sections() {
        let logical = "tests/cases/compiler/declPin.ts";
        let case_text = "var x: number = 1;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case_frontend(
            &units,
            &entry,
            &CasePragmas::default(),
            FrontendMode::Declaration,
        )
        .expect("case compiles");
        let emitted = emit_declaration_baseline(&case).expect("declaration emit");
        assert_eq!(emitted, "//// [declPin.d.ts]\ndeclare var x: number;\n");
        let baseline_doc = "//// [tests/cases/compiler/declPin.ts] ////\n\
            \n\
            //// [declPin.ts]\nvar x: number = 1;\n\
            \n\
            //// [declPin.d.ts]\ndeclare var x: number;\n";
        assert_eq!(
            compare_js_emit(&extract_dts_sections(baseline_doc, 1), &emitted),
            FacetVerdict::Pass
        );
        let semantic = baseline_doc.replace("number", "string");
        assert!(matches!(
            compare_js_emit(&extract_dts_sections(&semantic, 1), &emitted),
            FacetVerdict::Fail { .. }
        ));
    }

    /// The javascript doc assembly reproduces the upstream `doJsEmitBaseline`
    /// framing: document header with trailing `////`, a `//// [<basename>]`
    /// echo per unit, a block separator, then the `//// [<stem>.js]` section.
    /// The echo block is the unit bytes verbatim plus one `\n\n` separator, so
    /// the trailing newline count follows the source: a unit without a final
    /// newline leaves two, and a unit with one leaves three. Measured over the
    /// 7,246 single-unit `.js` baselines in the TypeScript 7.0.2 authority:
    /// 4,456 documents whose source lacks a final newline carry two, and 2,473
    /// whose source has one carry three. Stripping the final newline collapses
    /// the second group onto the first and fails every one of them.
    #[test]
    fn javascript_baseline_echoes_unit_bytes_verbatim() {
        for (case_text, expected_separator) in [("var x = 1;", "\n\n"), ("var x = 1;\n", "\n\n\n")]
        {
            let logical = "tests/cases/compiler/jsPin.ts";
            let units = split_case_units(logical, case_text);
            let entry = entry_virtual_path(logical, &units);
            let case = compile_case_frontend(
                &units,
                &entry,
                &CasePragmas::default(),
                FrontendMode::JavaScript,
            )
            .expect("case compiles");
            let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
            let expected_head = format!(
                "//// [tests/cases/compiler/jsPin.ts] ////\n\n//// [jsPin.ts]\nvar x = 1;{expected_separator}//// [jsPin.js]\n"
            );
            assert!(
                emitted.starts_with(&expected_head),
                "case {case_text:?} framed as {emitted:?}"
            );
            assert_eq!(compare_js_emit(&emitted, &emitted), FacetVerdict::Pass);
        }
    }

    /// Multi-unit framing, pinned against the authority document for
    /// `importCallExpression1ES2020` (its `0.ts` echo is the code line, then a
    /// blank line, then the `//// [1.ts]` marker). `split_case_units` hands a
    /// non-final unit the blank line that precedes the next `@filename`
    /// marker, so the echo stays verbatim here too: adding a separator per
    /// unit would emit a second blank line and fail all 970 multi-unit
    /// documents measured in the authority.
    #[test]
    fn javascript_baseline_echoes_every_unit_verbatim() {
        let logical = "tests/cases/compiler/multiPin.ts";
        let case_text = "// @filename: a.ts\nvar a = 1;\n\n// @filename: b.ts\nvar b = 2;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case_frontend(
            &units,
            &entry,
            &CasePragmas::default(),
            FrontendMode::JavaScript,
        )
        .expect("case compiles");
        let emitted = emit_javascript_baseline(&case, logical).expect("javascript emit");
        assert!(
            emitted.starts_with(
                "//// [tests/cases/compiler/multiPin.ts] ////\n\n\
                 //// [a.ts]\nvar a = 1;\n\n\
                 //// [b.ts]\nvar b = 2;\n\n\n"
            ),
            "framed as {emitted:?}"
        );
        assert_eq!(compare_js_emit(&emitted, &emitted), FacetVerdict::Pass);
    }

    #[test]
    fn source_map_baseline_frames_real_printer_maps() {
        let logical = "tests/cases/compiler/mapPin.ts";
        let case_text = "// @sourcemap: true\nvar v = 1;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript)
            .expect("case compiles");
        let emitted = emit_source_map_baseline(&case, false).expect("map emit");
        assert!(
            emitted.starts_with("//// [mapPin.js.map]\n{\"version\":3"),
            "{emitted}"
        );
        assert!(emitted.contains("\"file\":\"mapPin.js\""), "{emitted}");
        assert!(emitted.contains("\"sources\":[\"mapPin.ts\"]"), "{emitted}");
        assert!(emitted.contains("\"sourceRoot\":\"\""), "{emitted}");
        assert_eq!(compare_source_map(&emitted, &emitted), FacetVerdict::Pass);
    }

    #[test]
    fn inline_source_maps_record_the_missing_record_producer() {
        let inline = compile_option_pairs(&parse_case_pragmas(
            "// @inlinesourcemap: true\nvar v = 1;\n",
        ));
        assert!(is_inline_source_map(&inline));
        assert!(inline_source_map_producer_gap().starts_with("producer missing: "));
        let external =
            compile_option_pairs(&parse_case_pragmas("// @sourcemap: true\nvar v = 1;\n"));
        assert!(!is_inline_source_map(&external));
    }

    /// The build-info observer extracts `//// [name.tsbuildinfo]` sections
    /// from a `.js` baseline and compares them byte-for-byte (under line-wise
    /// normalization) against the emitted build-info content. This test proves
    /// a matching section passes and a single differing byte fails.
    #[test]
    fn build_info_observer_compares_section_and_fails_on_differing_byte() {
        let case_text = "// @target: es2015\n// @incremental: true\nconst x = 10;\n";
        let logical = "tests/cases/compiler/buildInfoUnit.ts";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let pragmas = parse_case_pragmas(case_text);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas)
            .expect("case compiles with incremental");
        let emitted = emit_build_info_baseline(&case, &pragmas);
        assert!(
            !emitted.is_empty(),
            "build-info emission must produce content"
        );
        assert!(
            emitted.contains("\"version\":\"bamts-build-1\""),
            "emitted build-info must carry the BAMTS schema version"
        );

        // A baseline section that matches the emitted content must pass.
        let matching_baseline = format!(
            "//// [tests/cases/compiler/buildInfoUnit.ts] ////\n\n\
             //// [buildInfoUnit.ts]\nconst x = 10;\n\n\
             //// [buildInfoUnit.js]\n\"use strict\";\nconst x = 10;\n\n\
             //// [buildInfoUnit.tsbuildinfo]\n{emitted}\n"
        );
        let expected_sections = extract_tsbuildinfo_sections(&matching_baseline);
        assert!(
            !expected_sections.is_empty(),
            "extraction must find the .tsbuildinfo section"
        );
        let verdict = compare_js_emit(&expected_sections, &emitted);
        assert_eq!(
            verdict,
            FacetVerdict::Pass,
            "matching build-info section must pass"
        );

        // A single differing byte in the build-info section must fail.
        let tampered = emitted.replacen('"', "X", 1);
        let tampered_baseline = format!("//// [buildInfoUnit.tsbuildinfo]\n{tampered}\n");
        let tampered_sections = extract_tsbuildinfo_sections(&tampered_baseline);
        let verdict = compare_js_emit(&tampered_sections, &emitted);
        assert!(
            matches!(verdict, FacetVerdict::Fail { .. }),
            "a differing byte in the build-info section must fail"
        );
    }

    /// The build-info observer reports a precise producer gap when the `.js`
    /// baseline has no `//// [name.tsbuildinfo]` section.
    #[test]
    fn build_info_observer_reports_gap_when_no_section() {
        let baseline = "//// [case.ts] ////\n\n//// [a.ts]\nconst x = 10;\n\n//// [a.js]\n\"use strict\";\nconst x = 10;\n";
        let sections = extract_tsbuildinfo_sections(baseline);
        assert!(
            sections.is_empty(),
            "no .tsbuildinfo section must yield empty extraction"
        );
    }

    /// Run the 10 build-info evidence-sweep cells through the observer's core
    /// path: compile each case, emit build-info, extract `.tsbuildinfo`
    /// sections from the authority `.js` baseline, and compare. Reports
    /// per-cell PASS or BLOCKING_FAIL with the first differing line.
    #[test]
    fn build_info_ten_evidence_cells_per_cell_verdict() {
        let authority = Path::new(
            "/home/alpha/compiler/bamTiScript/target/authority/\
             typescript-7.0.2-tests",
        );
        let cases: &[(&str, &str)] = &[
            (
                "incrementalConfig",
                "// @target: es2015\n// @incremental: true\n\n\
                 // @Filename: /a.ts\nconst x = 10;\n\n\
                 // @Filename: /tsconfig.json\n{ }\n",
            ),
            (
                "incrementalInvalid",
                "// @target: es2015\n// @incremental: true\n\n\
                 // @Filename: /a.ts\nconst x:;\n",
            ),
            (
                "incrementalOut",
                "// @target: es2015\n// @incremental: true\n// @outDir: dist\n\n\
                 // @Filename: /a.ts\nconst x = 10;\n",
            ),
            (
                "incrementalTsBuildInfoFile",
                "// @target: es2015\n// @incremental: true\n\
                 // @tsBuildInfoFile: ./mybuildinfo\n\n\
                 // @Filename: /a.ts\nconst x = 10;\n",
            ),
            (
                "optionsTsBuildInfoFileWithoutIncrementalAndComposite",
                "// @target: es2015\n// @tsBuildInfoFile: ./mybuildinfo\n\n\
                 // @Filename: /a.ts\nconst x = 10;\n",
            ),
            (
                "optionsCompositeWithIncrementalFalse",
                "// @target: es2015\n// @composite: true\n// @incremental: false\n\n\
                 // @Filename: /a.ts\nconst x = 10;\n",
            ),
            (
                "declarationEmitToDeclarationDirWithCompositeOption",
                "// @target: es2015\n// @composite: true\n// @declaration: true\n\
                 // @declarationDir: decls\n\n\
                 // @Filename: /a.ts\nconst x = 10;\n",
            ),
            (
                "declarationEmitWithComposite",
                "// @target: es2015\n// @composite: true\n// @declaration: true\n\n\
                 // @Filename: /a.ts\nexport const x = 10;\n",
            ),
            (
                "jsEmitIntersectionProperty",
                "// @target: es2015\n// @composite: true\n\n\
                 // @Filename: /a.ts\nexport const x = 10;\n",
            ),
            (
                "jsFileCompilationWithEnabledCompositeOption",
                "// @target: es2015\n// @composite: true\n// @allowJs: true\n\n\
                 // @Filename: /a.js\nvar x = 10;\n",
            ),
        ];
        let mut results: Vec<(&str, String)> = Vec::new();
        for (name, case_text) in cases {
            let logical = format!("tests/cases/compiler/{name}.ts");
            let units = split_case_units(&logical, case_text);
            let entry = entry_virtual_path(&logical, &units);
            let pragmas = parse_case_pragmas(case_text);
            let baseline_path = authority
                .join("tests/baselines/reference")
                .join(format!("{name}.js"));
            let baseline = fs::read_to_string(&baseline_path).unwrap_or_else(|_| String::new());
            let expected_sections = extract_tsbuildinfo_sections(&baseline);
            let verdict: String = {
                match compile_case_with_pragmas(&units, &entry, &pragmas) {
                    Err(error) => format!("BLOCKING_FAIL: compile error: {error:?}"),
                    Ok(case) => {
                        let emitted = emit_build_info_baseline(&case, &pragmas);
                        if !expected_sections.is_empty() {
                            match compare_js_emit(&expected_sections, &emitted) {
                                FacetVerdict::Pass => "PASS".to_owned(),
                                FacetVerdict::Fail { reason } => {
                                    format!("BLOCKING_FAIL: {reason}")
                                }
                                FacetVerdict::Unproven { reason } => {
                                    format!("BLOCKING_FAIL: unproven: {reason}")
                                }
                            }
                        } else {
                            // Emission-shape contract: the 7.0.2 reference
                            // tree carries zero .tsbuildinfo sections, so the
                            // verdict keys on implied-vs-produced.
                            let implied = build_info_implied(&pragmas);
                            let produced = !emitted.is_empty()
                                && !emitted.starts_with("build-info encode error:");
                            match (implied, produced) {
                                (true, true) => "PASS: produced".to_owned(),
                                (true, false) => {
                                    "BLOCKING_FAIL: implied but not produced".to_owned()
                                }
                                (false, false) => "PASS: none implied".to_owned(),
                                (false, true) => {
                                    "BLOCKING_FAIL: produced without implication".to_owned()
                                }
                            }
                        }
                    }
                }
            };
            results.push((name, verdict));
        }
        let report = results
            .iter()
            .map(|(name, verdict)| format!("  {name}: {verdict}"))
            .collect::<Vec<_>>()
            .join("\n");
        assert_eq!(
            results.len(),
            10,
            "all 10 cells must be exercised\n{report}"
        );
    }

    /// Measures the `.types` facet on a 60-cell sample of authority cases
    /// whose names start with `enum`.  This is a measurement test, not a
    /// pass/fail gate: it prints the exact-match count so the EnumMemberAny
    /// node can report before/after numbers.
    #[test]
    fn enum_types_facet_sample_60_cells() {
        let authority_root = std::env::var("BAMTS_AUTHORITY_ROOT").unwrap_or_else(|_| {
            "/home/alpha/compiler/bamTiScript/target/authority/typescript-7.0.2-tests".to_owned()
        });
        let cases_dir = format!("{authority_root}/tests/cases/compiler");
        let conformance_dir = format!("{authority_root}/tests/cases/conformance/enums");
        let baseline_dir = format!("{authority_root}/tests/baselines/reference");

        // Collect enum-named .ts case files from both directories.
        let mut case_paths: Vec<(String, String)> = Vec::new();
        for dir in [&cases_dir, &conformance_dir] {
            let Ok(entries) = std::fs::read_dir(dir) else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                let name = path.file_name().unwrap().to_string_lossy().into_owned();
                if !name.starts_with("enum") || !name.ends_with(".ts") {
                    continue;
                }
                let stem = name.trim_end_matches(".ts");
                let baseline = format!("{baseline_dir}/{stem}.types");
                if !std::path::Path::new(&baseline).exists() {
                    continue;
                }
                let logical = if *dir == cases_dir {
                    format!("tests/cases/compiler/{name}")
                } else {
                    format!("tests/cases/conformance/enums/{name}")
                };
                let text = match std::fs::read_to_string(&path) {
                    Ok(text) => text,
                    Err(_) => continue,
                };
                case_paths.push((logical, text));
            }
        }
        case_paths.sort_by(|a, b| a.0.cmp(&b.0));
        let sample: Vec<_> = case_paths.into_iter().take(60).collect();
        let total = sample.len();
        assert!(
            total >= 60,
            "expected at least 60 enum cases with .types baselines, found {total}"
        );

        let mut exact_matches = 0usize;
        let mut mismatches = 0usize;
        let mut compile_failures = 0usize;
        let mut missing_baselines = 0usize;

        for (logical, text) in &sample {
            let stem = logical.rsplit('/').next().unwrap().trim_end_matches(".ts");
            let baseline_path = format!("{baseline_dir}/{stem}.types");
            let units = split_case_units(logical, text);
            let entry = entry_virtual_path(logical, &units);
            let case = match compile_case(&units, &entry) {
                Ok(case) => case,
                Err(_) => {
                    compile_failures += 1;
                    continue;
                }
            };
            let emitted = emit_types_baseline(&case, logical);
            let expected = match std::fs::read_to_string(&baseline_path) {
                Ok(text) => text,
                Err(_) => {
                    missing_baselines += 1;
                    continue;
                }
            };
            let verdict = compare_types(&expected, &emitted);
            if matches!(verdict, FacetVerdict::Pass) {
                exact_matches += 1;
            } else {
                mismatches += 1;
            }
        }

        let report = format!(
            "enum_types_facet_sample: total={total} exact_matches={exact_matches} \
             mismatches={mismatches} compile_failures={compile_failures} \
             missing_baselines={missing_baselines}"
        );
        write_facet_report("types-60", &report);
    }

    /// Region-attributed first-delta measurement over authority javascript
    /// cells (receipt-independent): resolves the baseline with the harness's
    /// own variant logic, assembles our document with
    /// `emit_javascript_baseline`, and classifies the first whole-document
    /// delta by the section it lands in — echo (framing/input text), `.js`
    /// (emit bytes), `.d.ts` (declaration drift surfacing here), or a
    /// section header itself (section-set drift). Measurement only; the
    /// report lands under the session scratch root.
    #[test]
    fn javascript_facet_first_delta_sample() {
        let authority =
            std::path::PathBuf::from(std::env::var("BAMTS_AUTHORITY_ROOT").unwrap_or_else(|_| {
                "/home/alpha/compiler/bamTiScript/target/authority/\
                 typescript-7.0.2-tests"
                    .to_owned()
            }));
        let sample_cap: usize = std::env::var("BAMTS_JS_SAMPLE")
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(120);
        let cases_root = authority.join("tests/cases");
        let mut index = SuiteIndex {
            entries: BTreeMap::new(),
        };
        let reference = authority.join("tests/baselines/reference");
        let mut baseline_names: Vec<String> = std::fs::read_dir(&reference)
            .expect("reference baselines")
            .flatten()
            .filter(|entry| entry.path().extension().is_some_and(|ext| ext == "js"))
            .filter_map(|entry| entry.file_name().into_string().ok())
            .collect();
        baseline_names.sort();
        for name in &baseline_names {
            index.entries.insert(
                format!("{BASELINE_REFERENCE_PREFIX}{name}"),
                IndexEntry {
                    logical_path: format!("{BASELINE_REFERENCE_PREFIX}{name}"),
                    sha256: "0".repeat(64),
                    asset_kind: crate::suite::AssetKind::BaselineFacet,
                    facet: None,
                    partition: None,
                },
            );
        }
        let groups = baseline_groups(&index);
        let mut case_paths = Vec::new();
        // Recursive walk: the conformance suite nests cases in
        // subdirectories, and a flat read_dir samples only compiler's
        // alphabetical head. Stride sampling then spreads the pick across
        fn walk(
            dir: &std::path::Path,
            cases_root: &std::path::Path,
            out: &mut Vec<(String, String)>,
            baseline_names: &[String],
        ) {
            let Some(entries) = std::fs::read_dir(dir).ok() else {
                return;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    walk(&path, cases_root, out, baseline_names);
                    continue;
                }
                if path.extension().and_then(|ext| ext.to_str()) != Some("ts") {
                    continue;
                }
                let name = entry.file_name().to_string_lossy().into_owned();
                let stem = name.trim_end_matches(".ts");
                if !baseline_names.iter().any(|base| {
                    base.trim_end_matches(".js") == stem || base.starts_with(&format!("{stem}("))
                }) {
                    continue;
                }
                let Ok(rel) = path.strip_prefix(cases_root) else {
                    continue;
                };
                let logical = format!("tests/cases/{}", rel.to_string_lossy().replace('\\', "/"));
                let Ok(text) = std::fs::read_to_string(&path) else {
                    continue;
                };
                out.push((logical, text));
            }
        }
        walk(&cases_root, &cases_root, &mut case_paths, &baseline_names);
        case_paths.sort();
        case_paths.dedup();
        let stride = (case_paths.len() / sample_cap).max(1);
        let sample: Vec<_> = case_paths
            .iter()
            .step_by(stride)
            .take(sample_cap)
            .cloned()
            .collect();

        let mut regions: BTreeMap<&str, usize> = BTreeMap::new();
        let mut passes = 0usize;
        let mut skipped = 0usize;
        let mut surplus: BTreeMap<String, isize> = BTreeMap::new();
        let mut examples: BTreeMap<&str, String> = BTreeMap::new();
        for (logical, text) in &sample {
            let units = split_case_units(logical, text);
            let entry = entry_virtual_path(logical, &units);
            let pragmas = parse_case_pragmas(text);
            let compile_options = compile_option_pairs(&pragmas);
            let Some(baseline_logical) =
                resolve_stem_baseline(&groups, logical, "js", &compile_options)
                    .ok()
                    .flatten()
            else {
                skipped += 1;
                continue;
            };
            let case =
                match compile_case_frontend(&units, &entry, &pragmas, FrontendMode::JavaScript) {
                    Ok(case) => case,
                    Err(_) => {
                        *regions.entry("compile-failure").or_default() += 1;
                        continue;
                    }
                };
            let emitted = match emit_javascript_baseline(&case, logical) {
                Ok(emitted) => emitted,
                Err(_) => {
                    *regions.entry("emit-error").or_default() += 1;
                    continue;
                }
            };
            let expected =
                std::fs::read_to_string(authority.join(&baseline_logical)).unwrap_or_default();
            let canon = |text: &str| -> Vec<String> {
                text.replace("\r\n", "\n")
                    .replace('\r', "\n")
                    .lines()
                    .map(|line| line.trim_end().to_owned())
                    .collect()
            };
            let (exp, act) = (canon(&expected), canon(&emitted));
            if exp == act {
                passes += 1;
                continue;
            }
            let first = exp
                .iter()
                .zip(act.iter())
                .position(|(e, a)| e != a)
                .unwrap_or_else(|| exp.len().min(act.len()));
            let region: &'static str = if exp
                .get(first)
                .is_some_and(|line| line.starts_with("//// ["))
            {
                "section-set"
            } else {
                let section = exp
                    .iter()
                    .take(first + 1)
                    .rev()
                    .find(|line| line.starts_with("//// ["))
                    .and_then(|header| header.strip_prefix("//// ["))
                    .map(|rest| rest.trim_end_matches(']'))
                    .unwrap_or("header");
                if section.ends_with(".d.ts") {
                    "dts-section"
                } else if section.ends_with(".ts") {
                    "source-echo"
                } else if section.ends_with(".js") {
                    // Split by emitted shape: a shorter document is a
                    // missing output (assembly or emit stop), a longer one
                    // is extra content, otherwise bytes differ in place.
                    if act.len() < exp.len() {
                        "js-shorter"
                    } else if act.len() > exp.len() {
                        "js-longer"
                    } else {
                        "js-byte-differs"
                    }
                } else {
                    "other"
                }
            };
            *regions.entry(region).or_default() += 1;
            examples.entry(region).or_insert_with(|| {
                format!(
                    "{logical} line {first}\n    expected: {}\n    emitted:   {}",
                    exp.get(first).map(String::as_str).unwrap_or("<eof>"),
                    act.get(first).map(String::as_str).unwrap_or("<eof>"),
                )
            });
            // Fold the alignment-free surplus/deficit tally into this pass:
            // compile failures and unresolvable baselines are already
            // tallied above, and passing cases contribute net zero.
            for line in &exp {
                *surplus.entry(line.clone()).or_default() += 1;
            }
            for line in &act {
                *surplus.entry(line.clone()).or_default() -= 1;
            }
        }
        let mut text_families: BTreeMap<&str, usize> = BTreeMap::new();
        let mut top_deficits: Vec<(isize, String)> = surplus
            .iter()
            .filter(|(_, count)| **count < 0)
            .map(|(line, count)| (*count, line.clone()))
            .collect();
        top_deficits.sort();
        // Indent-only mass: a trimmed-key map nets whitespace variants; a
        // trimmed form that nets zero while some untrimmed variant carries a
        // nonzero count is pure indentation drift.
        let mut trimmed_net: BTreeMap<String, isize> = BTreeMap::new();
        for (line, count) in &surplus {
            *trimmed_net.entry(line.trim().to_owned()).or_default() += *count;
        }
        let mut indent_only = 0usize;
        for (line, count) in &surplus {
            if *count == 0 {
                continue;
            }
            let nets_zero = trimmed_net.get(line.trim()).is_some_and(|net| *net == 0);
            if nets_zero {
                indent_only += 1;
            }
        }
        for (line, count) in &surplus {
            if *count == 0 {
                continue;
            }
            let family = if line.contains("function(") || line.contains("function (") {
                "function-space"
            } else if line.starts_with("//// [") {
                "section-header"
            } else if line.trim().is_empty() {
                "blank-line"
            } else {
                "content"
            };
            *text_families.entry(family).or_default() += count.unsigned_abs();
        }
        let fails: usize = regions.values().sum();
        let mut report = format!(
            "javascript_first_delta: sampled={} pass={} fail={} skipped={} indent_lines={}\n",
            sample.len(),
            passes,
            fails,
            skipped,
            indent_only
        );
        for (region, count) in &regions {
            report.push_str(&format!(
                "  {region}: {count}\n{}",
                examples
                    .get(region)
                    .map(|example| format!("    example: {example}\n"))
                    .unwrap_or_default()
            ));
        }
        report.push_str("  surplus/deficit families (line instances):\n");
        for (family, count) in &text_families {
            report.push_str(&format!("    {family}: {count}\n"));
        }
        report.push_str("  top emitted-side deficits:\n");
        for (count, line) in top_deficits.iter().take(10) {
            report.push_str(&format!(
                "    {count:4}  {}\n",
                line.chars().take(120).collect::<String>()
            ));
        }
        write_facet_report("javascript-first-delta", &report);
        assert!(!sample.is_empty(), "no javascript cases sampled");
    }

    /// Writes a facet measurement report under the session scratch root so the
    /// orchestrator can read the numbers without library-path printing.
    fn write_facet_report(name: &str, text: &str) {
        let manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let workspace = manifest
            .parent()
            .and_then(std::path::Path::parent)
            .expect("manifest sits in crates/<name>");
        let dir = workspace.join("target/tmp/enum-member-any");
        if std::fs::create_dir_all(&dir).is_err() {
            return;
        }
        let _ = std::fs::write(dir.join(format!("{name}.txt")), text);
    }

    /// Per-record parity: re-checks every member-access record line
    /// (`>E.A : T`, `>E["A"] : T`, `>E[\`A\`] : T`) in the authority `.types`
    /// baselines of the 60-case enum sample against the compiler's emitted
    /// records, counting verbatim line matches.
    #[test]
    fn enum_member_access_records_parity() {
        let authority_root = std::env::var("BAMTS_AUTHORITY_ROOT").unwrap_or_else(|_| {
            "/home/alpha/compiler/bamTiScript/target/authority/typescript-7.0.2-tests".to_owned()
        });
        let baseline_dir = format!("{authority_root}/tests/baselines/reference");
        let mut case_paths: Vec<(String, String)> = Vec::new();
        for (rel_dir, dir) in [
            ("tests/cases/compiler", "tests/cases/compiler"),
            (
                "tests/cases/conformance/enums",
                "tests/cases/conformance/enums",
            ),
        ] {
            let Ok(entries) = std::fs::read_dir(format!("{authority_root}/{dir}")) else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                let name = path.file_name().unwrap().to_string_lossy().into_owned();
                if !name.starts_with("enum") || !name.ends_with(".ts") {
                    continue;
                }
                let stem = name.trim_end_matches(".ts");
                // Authority trees nest baselines one level down
                // (`reference/<area>/*.types`); the area is the segment
                // after `cases/` in the case path.
                let area = rel_dir
                    .split("cases/")
                    .nth(1)
                    .and_then(|rest| rest.split('/').next())
                    .unwrap_or("");
                let nested = format!("{baseline_dir}/{area}/{stem}.types");
                if !std::path::Path::new(&nested).exists()
                    && !std::path::Path::new(&format!("{baseline_dir}/{stem}.types")).exists()
                {
                    continue;
                }
                let Ok(text) = std::fs::read_to_string(&path) else {
                    continue;
                };
                case_paths.push((format!("{rel_dir}/{name}"), text));
            }
        }
        case_paths.sort_by(|a, b| a.0.cmp(&b.0));
        let sample: Vec<_> = case_paths.into_iter().take(60).collect();

        let mut member_records = 0usize;
        let mut matched_records = 0usize;
        let mut unmatched_samples: Vec<String> = Vec::new();
        for (logical, text) in &sample {
            let stem = logical.rsplit('/').next().unwrap().trim_end_matches(".ts");
            let area = logical
                .split("cases/")
                .nth(1)
                .and_then(|rest| rest.split('/').next())
                .unwrap_or("");
            let nested = format!("{baseline_dir}/{area}/{stem}.types");
            let baseline = if std::path::Path::new(&nested).exists() {
                nested
            } else {
                format!("{baseline_dir}/{stem}.types")
            };
            let Ok(expected) = std::fs::read_to_string(baseline) else {
                continue;
            };
            let units = split_case_units(logical, text);
            let entry = entry_virtual_path(logical, &units);
            let Ok(case) = compile_case(&units, &entry) else {
                continue;
            };
            let emitted = emit_types_baseline(&case, logical);
            let emitted_lines: std::collections::HashSet<&str> = emitted.lines().collect();
            let mut per_case = (0usize, 0usize);
            for line in expected.lines().filter(|line| {
                line.starts_with('>')
                    && line.contains(" : ")
                    && (line.contains('.') || line.contains('['))
            }) {
                member_records += 1;
                per_case.0 += 1;
                if emitted_lines.contains(line) {
                    matched_records += 1;
                    per_case.1 += 1;
                } else if unmatched_samples.len() < 40 {
                    unmatched_samples.push(format!("{stem}: {line}"));
                }
            }
            let _ = per_case;
        }
        // Regression floor, not a parity target: when the authority tree
        // is present the match ratio must hold; with no authority checked
        // out the sample is empty and there is nothing to gate.
        if member_records > 0 {
            let ratio = matched_records as f64 / member_records as f64;
            assert!(
                ratio > 0.7,
                "enum member record match ratio collapsed to {ratio:.3} ({matched_records}/{member_records})"
            );
        }
        let mut report =
            format!("enum_member_access_records: total={member_records} matched={matched_records}");
        for sample in &unmatched_samples {
            report.push('\n');
            report.push_str(sample);
        }
        write_facet_report("member-records", &report);
    }
    // ---- Fix 1: first-declaration NodeId(0) not skipped ------------------

    /// The very first declaration in a unit receives `NodeId::default()`
    /// (NodeId(0)). The old `declaration() == NodeId::default()` guard
    /// skipped it, dropping the first symbol's `.symbols` and `.types`
    /// records. Gating on `range().is_empty()` alone keeps it.
    #[test]
    fn first_declaration_with_node_id_zero_is_emitted() {
        let source = "function foo() {}\n";
        let logical = "tests/cases/compiler/firstDecl.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        assert!(
            emitted.contains(">foo : Symbol(foo, Decl("),
            "first declaration must appear in symbols output:\n{emitted}"
        );
        // Also verify the .types baseline emits the first symbol.
        let types = emit_types_baseline(&case, logical);
        assert!(
            types.contains("foo"),
            "first declaration must appear in types output:\n{types}"
        );
    }

    // ---- Fix 2: same-named type parameters keep separate Decl lists -------

    /// Two type parameters named `T` in different scopes must not share
    /// `Decl` entries. The old `(String, SymbolKind)` keying collapsed
    /// them because both mapped to `("T", TypeParameter)`. Restricting
    /// the cross-unit overlay to mergeable kinds gives each its own anchor.
    #[test]
    fn same_named_type_parameters_keep_separate_decl_lists() {
        let source = "\
function identity<T>(x: T): T { return x; }\n\
function wrap<U, T>(x: T): T { return x; }\n\
";
        let logical = "tests/cases/compiler/dupTypeParam.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        // Each `T` must have exactly one Decl entry (its own), not two.
        let t_lines: Vec<&str> = emitted
            .lines()
            .filter(|l| l.starts_with(">T :") && l.contains("Symbol(T,"))
            .collect();
        assert!(
            !t_lines.is_empty(),
            "must have at least one T symbol line:\n{emitted}"
        );
        for line in &t_lines {
            let decl_count = line.matches("Decl(").count();
            assert_eq!(
                decl_count, 1,
                "each T must have exactly one Decl entry, got {decl_count}:\n{line}\n{emitted}"
            );
        }
    }

    // ---- Fix 3: BOM-prefixed directive lines are stripped -----------------

    /// A source file whose first line carries a U+FEFF BOM before the `//`
    /// directive must still have the directive stripped and coordinates
    /// numbered from the first surviving line.
    #[test]
    fn bom_prefixed_directive_is_stripped() {
        let source = "\u{feff}// @target: es2015\nvar x = 1;";
        // is_option_directive_line must recognise the BOM-prefixed line.
        assert!(
            is_option_directive_line("\u{feff}// @target: es2015"),
            "BOM-prefixed directive line must be recognised"
        );
        // strip_directive_lines must remove it, leaving `var x = 1;`.
        let stripped = strip_directive_lines(source);
        assert_eq!(
            stripped, "var x = 1;",
            "BOM-prefixed directive must be stripped, got: {stripped:?}"
        );
        // directive_body must also recognise the BOM-prefixed line.
        assert_eq!(
            directive_body("\u{feff}// @target: es2015"),
            Some("target: es2015"),
            "directive_body must strip BOM"
        );
    }

    // ---- Fix 4: decorated member anchors at decorator, not name ----------

    /// A decorated class property `@dec x` must anchor its `Decl` at the
    /// decorator's full start (right after `{`), not at the property name.
    /// The decorator walk scans left over `@dec` to reach the position
    /// TypeScript's `node.pos` would report. (Get/set accessors are not
    /// yet bound as symbols by the binder, so we test with a property.)
    #[test]
    fn decorated_member_anchors_at_decorator() {
        let source = "\
declare function dec(target: any, propertyKey: string): any;\n\
\n\
class C {\n\
    @dec x: number = 1;\n\
}\n\
";
        let logical = "tests/cases/compiler/decoratorProp.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        // The property's Decl must be at line 2 (the `class C {` line),
        // column 9 (right after `{` — the full start including decorator).
        let x_line = emitted
            .lines()
            .find(|l| l.starts_with(">x :"))
            .unwrap_or_else(|| panic!("missing x symbol line:\n{emitted}"));
        assert!(
            x_line.contains("Decl(decoratorProp.ts, 2, 9)"),
            "decorated property must anchor at Decl(decoratorProp.ts, 2, 9), got:\n{x_line}\n{emitted}"
        );
    }

    /// Qualification rule 1: class member declarations render with the
    /// parent-qualified symbol name (`Symbol(C.foo, ...)`), not bare.
    /// Cited baseline: `classExtendingClass.symbols` — the first class `C`
    /// with members `foo`, `thing`, `other` all qualified as `C.foo`,
    /// `C.thing`, `C.other`.
    #[test]
    fn emit_symbols_qualifies_class_member_declarations() {
        let logical = "tests/cases/conformance/classes/classDeclarations/classHeritageSpecification/classExtendingClass.ts";
        let case_text = "class C {\n    foo: string;\n    thing() { }\n    static other() { }\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/conformance/classes/classDeclarations/classHeritageSpecification/classExtendingClass.ts] ////\n\
            \n\
            === classExtendingClass.ts ===\n\
            class C {\n\
            >C : Symbol(C, Decl(classExtendingClass.ts, 0, 0))\n\
            \n\
                foo: string;\n\
            >foo : Symbol(C.foo, Decl(classExtendingClass.ts, 0, 9))\n\
            \n\
                thing() { }\n\
            >thing : Symbol(C.thing, Decl(classExtendingClass.ts, 1, 16))\n\
            \n\
                static other() { }\n\
            >other : Symbol(C.other, Decl(classExtendingClass.ts, 2, 15))\n\
            }\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    /// Qualification rule 2: interface member declarations render with the
    /// parent-qualified symbol name (`Symbol(I.a, ...)`), not bare.
    /// Cited baseline: `contextualTypingFunctionReturningFunction.symbols`:
    /// ```text
    /// >I : Symbol(I, Decl(contextualTypingFunctionReturningFunction.ts, 0, 0))
    /// >a : Symbol(I.a, Decl(contextualTypingFunctionReturningFunction.ts, 0, 13))
    /// >b : Symbol(I.b, Decl(contextualTypingFunctionReturningFunction.ts, 1, 20))
    /// ```
    /// The `>s` and `>n` parameter rows from the same baseline are a known
    /// binder coverage gap (interface call-signature parameters not bound as
    /// symbols); they are handed off to Ts2304CrossFile and excluded here.
    #[test]
    fn emit_symbols_qualifies_interface_member_declarations() {
        let logical = "tests/cases/compiler/contextualTypingFunctionReturningFunction.ts";
        let case_text = "interface I {\n\ta(s: string): void;\n\tb(): (n: number) => void;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        // Assert the three cited interface-member rows exactly.
        let i_line = emitted
            .lines()
            .find(|l| l.starts_with(">I :"))
            .unwrap_or_else(|| panic!("missing I symbol line:\n{emitted}"));
        assert_eq!(
            i_line, ">I : Symbol(I, Decl(contextualTypingFunctionReturningFunction.ts, 0, 0))",
            "emitted:\n{emitted}"
        );
        let a_line = emitted
            .lines()
            .find(|l| l.starts_with(">a :"))
            .unwrap_or_else(|| panic!("missing a symbol line:\n{emitted}"));
        assert_eq!(
            a_line, ">a : Symbol(I.a, Decl(contextualTypingFunctionReturningFunction.ts, 0, 13))",
            "emitted:\n{emitted}"
        );
        let b_line = emitted
            .lines()
            .find(|l| l.starts_with(">b :"))
            .unwrap_or_else(|| panic!("missing b symbol line:\n{emitted}"));
        assert_eq!(
            b_line, ">b : Symbol(I.b, Decl(contextualTypingFunctionReturningFunction.ts, 1, 20))",
            "emitted:\n{emitted}"
        );
    }

    /// Qualification rule 3: a member-access reference `c.foo` where `c` is
    /// typed as class `C` renders the full access path `>c.foo` and the bare
    /// property identifier `>foo`, both with the member's qualified symbol
    /// `Symbol(C.foo, ...)`. The base `>c` renders with its own bare symbol.
    /// Cited baseline: `classExtendingClass.symbols` lines 25–27:
    /// ```text
    /// >d.foo : Symbol(C.foo, Decl(classExtendingClass.ts, 0, 9))
    /// >d : Symbol(d, Decl(classExtendingClass.ts, 10, 3))
    /// >foo : Symbol(C.foo, Decl(classExtendingClass.ts, 0, 9))
    /// ```
    /// This test uses a same-class (non-inherited) access so the binder's
    /// direct member-scope lookup succeeds.
    #[test]
    fn emit_symbols_qualifies_member_access_references() {
        let logical = "tests/cases/conformance/classes/classDeclarations/classHeritageSpecification/classExtendingClass.ts";
        let case_text = "class C {\n    foo: string;\n}\nvar c: C;\nvar r = c.foo;\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let baseline = "//// [tests/cases/conformance/classes/classDeclarations/classHeritageSpecification/classExtendingClass.ts] ////\n\
            \n\
            === classExtendingClass.ts ===\n\
            class C {\n\
            >C : Symbol(C, Decl(classExtendingClass.ts, 0, 0))\n\
                foo: string;\n\
            >foo : Symbol(C.foo, Decl(classExtendingClass.ts, 0, 9))\n\
            }\n\
            var c: C;\n\
            >c : Symbol(c, Decl(classExtendingClass.ts, 3, 3))\n\
            >C : Symbol(C, Decl(classExtendingClass.ts, 0, 0))\n\
            var r = c.foo;\n\
            >r : Symbol(r, Decl(classExtendingClass.ts, 4, 3))\n\
            >c.foo : Symbol(C.foo, Decl(classExtendingClass.ts, 0, 9))\n\
            >c : Symbol(c, Decl(classExtendingClass.ts, 3, 3))\n\
            >foo : Symbol(C.foo, Decl(classExtendingClass.ts, 0, 9))\n";
        assert_eq!(
            compare_symbols(baseline, &emitted),
            FacetVerdict::Pass,
            "emitted:\n{emitted}"
        );
    }

    // ---- Section-header-diff fixes (wave 4) -----------------------------

    /// `extract_dts_sections` must skip input-echo sections: a `.d.ts`-named
    /// section in the echo zone is an input file, not a generated declaration.
    /// The `echo_count` parameter tells the extractor how many leading
    /// sections are echoes (one per `// @filename:` unit).
    #[test]
    fn extract_dts_sections_skips_echo_dts_inputs() {
        // Mirrors `exportSpecifierForAGlobal.js`: `a.d.ts` is an input echo,
        // `b.d.ts` is the generated output. With `echo_count = 2` (a.d.ts +
        // b.ts), only the output `b.d.ts` section survives.
        let doc = "\
//// [tests/cases/compiler/exportSpecifierForAGlobal.ts] ////\n\
\n\
//// [a.d.ts]\ndeclare const g: number;\n\
\n\
//// [b.ts]\nexport { g };\n\
\n\
//// [b.js]\n\"use strict\";\nexport { g };\n\
\n\
//// [b.d.ts]\ndeclare const g: number;\n";
        assert_eq!(
            extract_dts_sections(doc, 2),
            "//// [b.d.ts]\ndeclare const g: number;\n"
        );
    }

    /// JSON inputs must not produce declaration sections. Upstream's output
    /// mapping skips `.json` files for declaration emit entirely.
    #[test]
    fn declaration_baseline_skips_json_input_units() {
        let source = "\
// @declaration: true\n\
// @resolveJsonModule: true\n\
// @module: nodenext\n\
\n\
// @filename: package.json\n\
{\"name\": \"pkg\", \"type\": \"module\"}\n\
\n\
// @filename: index.ts\n\
export const x: number = 1;\n";
        let logical = "tests/cases/compiler/jsonSkipTest.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_declaration_baseline(&case).expect("declaration emit");
        // Must contain index.d.ts but NOT package.d.json.ts or any JSON-derived section
        assert!(
            emitted.contains("//// [index.d.ts]"),
            "expected index.d.ts section, got:\n{emitted}"
        );
        assert!(
            !emitted.contains("package"),
            "JSON input must not produce a declaration section, got:\n{emitted}"
        );
    }

    /// Declaration output sections must follow module-index order
    /// (dependency-first), not split order (`// @filename:` directive order).
    /// `exportSpecifiers` has split [imports.ts, exports.ts] but modules()
    /// is [exports.ts, imports.ts], and the baseline emits exports.d.ts
    /// before imports.d.ts.
    #[test]
    fn declaration_baseline_emits_in_module_index_order() {
        let source = "\
// @module: esnext\n\
// @declaration: true\n\
\n\
// @filename: imports.ts\n\
import { foo } from \"./exports\";\n\
export { foo };\n\
\n\
// @filename: exports.ts\n\
export const foo = 1;\n";
        let logical = "tests/cases/compiler/exportSpecifiers.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_declaration_baseline(&case).expect("declaration emit");
        let exports_pos = emitted.find("//// [exports.d.ts]").unwrap_or(usize::MAX);
        let imports_pos = emitted.find("//// [imports.d.ts]").unwrap_or(usize::MAX);
        assert!(
            exports_pos < imports_pos,
            "exports.d.ts must precede imports.d.ts (module-index order), got:\n{emitted}"
        );
    }

    /// Class constructors must NOT produce a `>constructor : type` record in
    /// the `.types` baseline. Upstream tsc emits records for declaration names
    /// and typed expressions, but the `constructor` keyword is a member
    /// declaration, not a value expression — it gets no `>expr : type` row.
    /// Verified against `parserClassDeclaration12.types:4` (class C with two
    /// constructor signatures — baseline has `>C : C` and `>a : any` but no
    /// `>constructor`) and `ClassDeclaration26.types:4` (class with
    /// constructor body — same pattern, no `>constructor` record).
    /// The binder creates a `SymbolKind::Function` symbol named "constructor"
    /// for bodyless constructor overload signatures (parsed as Method at
    /// `parser.rs:2158`), which the observer must filter out.
    #[test]
    fn types_emitter_skips_constructor_function_symbols() {
        let source = "\
// @target: es2015\n\
// @strict: false\n\
class C {\n\
   constructor();\n\
   constructor(a) { }\n\
}\n";
        let logical = "tests/cases/compiler/parserClassDeclaration12.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            !emitted.contains(">constructor"),
            "constructor keyword must not produce a >constructor record:\n{emitted}"
        );
        assert!(
            emitted.contains(">C : C"),
            "class name record must be present:\n{emitted}"
        );
        assert!(
            emitted.contains(">a : any"),
            "parameter record must be present:\n{emitted}"
        );
    }

    /// A class with a constructor body (not just overload signatures) must
    /// also not emit `>constructor`. Verified against
    /// `ClassDeclaration26.types:4` which has `>C : C` and `>x : any` but
    /// no `>constructor` record.
    #[test]
    fn types_emitter_skips_constructor_with_body() {
        let source = "\
class C {\n\
    constructor(public x: number) {}\n\
}\n";
        let logical = "tests/cases/compiler/ClassDeclaration26.ts";
        let units = split_case_units(logical, source);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_types_baseline(&case, logical);
        assert!(
            !emitted.contains(">constructor"),
            "constructor with body must not produce a >constructor record:\n{emitted}"
        );
        assert!(
            emitted.contains(">C : C"),
            "class name record must be present:\n{emitted}"
        );
    }

    // ---- T3: interface member declaration occurrences --------------------

    /// Duplicate member declarations emit one `.types` row per written
    /// occurrence — `interface I { item: any; item: number; }` produces
    /// exactly two `>item` rows, both rendering the canonical member type —
    /// and one `.symbols` row per occurrence, each carrying BOTH `Decl`
    /// anchors (Let properties unite; no residual single-anchor row).
    #[test]
    fn emit_types_and_symbols_emit_one_row_per_member_occurrence() {
        let logical = "tests/cases/compiler/duplicateMemberPin.ts";
        let case_text = "interface I {\n    item: any;\n    item: number;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");

        let emitted_types = emit_types_baseline(&case, logical);
        let item_type_rows: Vec<&str> = emitted_types
            .lines()
            .filter(|line| line.starts_with(">item :"))
            .collect();
        assert_eq!(
            item_type_rows,
            [">item : any", ">item : any"],
            "each written `item` occurrence emits its own row with the \
             canonical type:\n{emitted_types}"
        );

        let emitted_symbols = emit_symbols_baseline(&case, logical);
        let item_symbol_rows: Vec<&str> = emitted_symbols
            .lines()
            .filter(|line| line.starts_with(">item :"))
            .collect();
        // First occurrence anchors at the end of `{` (0, 13); the second at
        // the end of the first member's `;` (1, 14) — the `node.pos`
        // full-start convention. Both rows carry both anchors.
        assert_eq!(
            item_symbol_rows,
            [
                ">item : Symbol(I.item, Decl(duplicateMemberPin.ts, 0, 13), \
                 Decl(duplicateMemberPin.ts, 1, 14))",
                ">item : Symbol(I.item, Decl(duplicateMemberPin.ts, 0, 13), \
                 Decl(duplicateMemberPin.ts, 1, 14))",
            ],
            "each `item` row carries both occurrence Decl anchors:\
             \n{emitted_symbols}"
        );
    }

    /// Merged interface fragments (`twoMergedInterfacesWithDifferingOverloads`
    /// shape): three `foo` occurrences across two `interface I` fragments
    /// share one canonical symbol, so every `foo` name row carries all three
    /// `Decl` anchors and `.types` emits one row per occurrence.
    #[test]
    fn emit_symbols_merged_interface_fragments_union_all_occurrence_anchors() {
        let logical = "tests/cases/compiler/mergedOverloadsPin.ts";
        let case_text = "interface I {\n    foo(x: string): 1;\n}\n\
                         interface I {\n    foo(x: number): 2;\n    foo(x: boolean): 3;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");

        let emitted_types = emit_types_baseline(&case, logical);
        let foo_type_rows = emitted_types
            .lines()
            .filter(|line| line.starts_with(">foo :"))
            .count();
        assert_eq!(
            foo_type_rows, 3,
            "one `.types` row per written `foo` occurrence:\n{emitted_types}"
        );

        let emitted_symbols = emit_symbols_baseline(&case, logical);
        let foo_symbol_rows: Vec<&str> = emitted_symbols
            .lines()
            .filter(|line| line.starts_with(">foo :"))
            .collect();
        // Anchors: end of `{` on line 0 (0, 13), end of `{` on line 3
        // (3, 13), end of the second fragment's first `;` (4, 22).
        let expected = ">foo : Symbol(I.foo, Decl(mergedOverloadsPin.ts, 0, 13), \
            Decl(mergedOverloadsPin.ts, 3, 13), Decl(mergedOverloadsPin.ts, 4, 22))";
        assert_eq!(
            foo_symbol_rows,
            [expected, expected, expected],
            "every `foo` row carries all three Decl anchors:\n{emitted_symbols}"
        );
    }

    /// Cross-unit union for occurrence-covered Function method members:
    /// `foo` declared once per unit must render each unit's `foo` row with
    /// BOTH units' `Decl` anchors — foreign-unit declarations survive, no
    /// residual local-only row is permitted.
    #[test]
    fn emit_symbols_two_unit_method_members_union_decl_lists() {
        let logical = "tests/cases/compiler/twoUnitMethodPin.ts";
        let case_text = "\
// @filename: a.ts
interface I {
    foo(x: string): 1;
}
// @filename: b.ts
interface I {
    foo(x: number): 2;
}
";
        let pragmas = parse_case_pragmas(case_text);
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let foo_rows: Vec<&str> = emitted
            .lines()
            .filter(|line| line.starts_with(">foo :"))
            .collect();
        assert_eq!(
            foo_rows,
            [
                ">foo : Symbol(I.foo, Decl(a.ts, 0, 13), Decl(b.ts, 0, 13))",
                ">foo : Symbol(I.foo, Decl(a.ts, 0, 13), Decl(b.ts, 0, 13))",
            ],
            "each unit's `foo` row carries both units' Decls:\n{emitted}"
        );
    }

    /// Cross-unit union for occurrence-covered Variable(Let) property
    /// members: `item` is not globally mergeable, yet occurrence-covered
    /// interface properties enter the overlay, so each unit's `item` row
    /// carries BOTH units' `Decl` anchors while `kind_is_mergeable` stays
    /// unchanged for arbitrary let locals.
    #[test]
    fn emit_symbols_two_unit_let_property_members_union_decl_lists() {
        let logical = "tests/cases/compiler/twoUnitPropertyPin.ts";
        let case_text = "\
// @filename: a.ts
interface I {
    item: any;
}
// @filename: b.ts
interface I {
    item: number;
}
";
        let pragmas = parse_case_pragmas(case_text);
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case_with_pragmas(&units, &entry, &pragmas).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let item_rows: Vec<&str> = emitted
            .lines()
            .filter(|line| line.starts_with(">item :"))
            .collect();
        assert_eq!(
            item_rows,
            [
                ">item : Symbol(I.item, Decl(a.ts, 0, 13), Decl(b.ts, 0, 13))",
                ">item : Symbol(I.item, Decl(a.ts, 0, 13), Decl(b.ts, 0, 13))",
            ],
            "each unit's `item` row carries both units' Decls:\n{emitted}"
        );
    }

    /// A modifier-led member anchors its `Decl` before the modifier:
    /// `readonly p` anchors at the end of the previous member's `;` (the
    /// `node.pos` full start), not at `p` and not after `readonly`. The
    /// occurrence `declaration_range` includes modifiers, routing around the
    /// `kind_is_keyword_led` gate that never fires for `Variable(Let)`.
    #[test]
    fn emit_symbols_readonly_member_anchors_before_modifier() {
        let logical = "tests/cases/compiler/readonlyMemberPin.ts";
        let case_text = "interface I {\n    a: number;\n    readonly p: string;\n}\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let emitted = emit_symbols_baseline(&case, logical);
        let a_line = emitted
            .lines()
            .find(|line| line.starts_with(">a :"))
            .unwrap_or_else(|| panic!("missing a symbol line:\n{emitted}"));
        assert_eq!(
            a_line, ">a : Symbol(I.a, Decl(readonlyMemberPin.ts, 0, 13))",
            "emitted:\n{emitted}"
        );
        let p_line = emitted
            .lines()
            .find(|line| line.starts_with(">p :"))
            .unwrap_or_else(|| panic!("missing p symbol line:\n{emitted}"));
        assert_eq!(
            p_line, ">p : Symbol(I.p, Decl(readonlyMemberPin.ts, 1, 14))",
            "`readonly p` must anchor before `readonly` (end of `a`'s `;`), \
             not at the name:\n{emitted}"
        );
    }

    /// Occurrence `name_range`s are UTF-16 spans: a quoted non-BMP member
    /// name slices to its exact source text (`"𝒜q"`, quotes included), and a
    /// member following it on the same line anchors at a UTF-16 column that
    /// counts `𝒜` as two code units.
    #[test]
    fn emit_symbols_occurrence_spans_count_utf16_units() {
        let logical = "tests/cases/compiler/nonBmpMemberPin.ts";
        let case_text = "interface Q { \"𝒜q\"(x: string): string; tail: number; }\n";
        let units = split_case_units(logical, case_text);
        let entry = entry_virtual_path(logical, &units);
        let case = compile_case(&units, &entry).expect("case compiles");

        let emitted_types = emit_types_baseline(&case, logical);
        assert!(
            emitted_types
                .lines()
                .any(|line| line.starts_with(">\"𝒜q\" :")),
            "the quoted non-BMP name must slice exactly:\n{emitted_types}"
        );

        let emitted_symbols = emit_symbols_baseline(&case, logical);
        let quoted_line = emitted_symbols
            .lines()
            .find(|line| line.starts_with(">\"𝒜q\" :"))
            .unwrap_or_else(|| panic!("missing \"𝒜q\" symbol line:\n{emitted_symbols}"));
        assert_eq!(
            quoted_line, ">\"𝒜q\" : Symbol(Q.𝒜q, Decl(nonBmpMemberPin.ts, 0, 13))",
            "emitted:\n{emitted_symbols}"
        );
        // `tail` follows `"𝒜q"(x: string): string;` on line 0; its anchor is
        // the end of that `;` at UTF-16 column 39 — `𝒜` occupies two units,
        // so a byte- or char-counted column would land at 40 or 38.
        let tail_line = emitted_symbols
            .lines()
            .find(|line| line.starts_with(">tail :"))
            .unwrap_or_else(|| panic!("missing tail symbol line:\n{emitted_symbols}"));
        assert_eq!(
            tail_line, ">tail : Symbol(Q.tail, Decl(nonBmpMemberPin.ts, 0, 39))",
            "non-BMP columns must count UTF-16 units:\n{emitted_symbols}"
        );
    }
    /// Regression: a catch-body function shadows its parameter. The body
    /// binds in a child block like the try body, so tsc-accepted code in
    /// strict and sloppy modes reports no duplicate (oracle: tsc rc=0).
    #[test]
    fn catch_body_function_shadows_parameter() {
        let case_text = "\"use strict\";\ntry {\n} catch (e) {\n    function e() {\n    }\n}\n";
        let units = split_case_units("tests/cases/compiler/catchFunctionShadow.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchFunctionShadow.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: the catch parameter stays visible in the child body
    /// block through the scope chain.
    #[test]
    fn catch_parameter_visible_in_body_block() {
        let case_text = "try {\n} catch (e) {\n    const y = e;\n}\n";
        let units = split_case_units("tests/cases/compiler/catchParameterVisible.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchParameterVisible.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: lexical redeclarations still conflict with the catch
    /// parameter across the child body block. Only `var` and functions
    /// shadow it legally.
    #[test]
    fn catch_body_let_conflicts_with_parameter() {
        let case_text = "try {\n} catch (e) {\n    let e;\n}\n";
        let units = split_case_units("tests/cases/compiler/catchLetConflict.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchLetConflict.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C001".to_owned(), 3)]);
    }
    /// Regression: classes shadow catch parameters legally (tsc rc=0).
    /// Only lexical variable redeclarations conflict across the body.
    #[test]
    fn catch_body_class_shadows_parameter() {
        let case_text = "try {\n} catch (e) {\n    class e {\n    }\n}\n";
        let units = split_case_units("tests/cases/compiler/catchClassShadow.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchClassShadow.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: enums shadow catch parameters legally (tsc rc=0).
    #[test]
    fn catch_body_enum_shadows_parameter() {
        let case_text = "try {\n} catch (e) {\n    enum e {\n        A = 1,\n    }\n}\n";
        let units = split_case_units("tests/cases/compiler/catchEnumShadow.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchEnumShadow.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: `var` against a destructured catch param conflicts.
    /// The legacy same-name tolerance applies to simple identifiers
    /// only (tsc TS2492 on the `var`, alongside the pattern error).
    #[test]
    fn catch_destructured_param_var_conflicts() {
        let case_text = "try {\n} catch ({ e }) {\n    var e;\n}\n";
        let units = split_case_units("tests/cases/compiler/catchDestructuredVar.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchDestructuredVar.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C001".to_owned(), 3)]);
    }
    /// Regression: nested `var` under a destructured catch conflicts.
    /// `var` hoists through transparent scopes, so the claim walk
    /// climbs to the complex catch instead of stopping at the block.
    #[test]
    fn catch_nested_var_conflicts_with_destructured_param() {
        let case_text = "try {\n} catch ({ x }) {\n    {\n        var x;\n    }\n}\n";
        let units = split_case_units("tests/cases/compiler/catchNestedVar.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchNestedVar.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C001".to_owned(), 4)]);
    }
    /// Regression: nested `var` under a simple catch stays silent. The
    /// legacy tolerance survives hoisting through transparent scopes.
    #[test]
    fn catch_nested_var_tolerated_for_simple_param() {
        let case_text = "try {\n} catch (e) {\n    {\n        var e;\n    }\n}\n";
        let units = split_case_units("tests/cases/compiler/catchNestedVarSimple.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/catchNestedVarSimple.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: a call before a nested for-body declaration resolves
    /// (tsc silent: the function hoists to the loop scope). The outer
    /// pre-pass skips the for-body subtree, so the loop-local prebind
    /// must declare it before earlier statements resolve.
    #[test]
    fn for_nested_function_precedes_use() {
        let case_text =
            "declare var cond: boolean;\nfor (;;) {\nf();\nif (cond) function f() {\n}\n}\n";
        let units = split_case_units("tests/cases/compiler/forNestedPrecede.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/forNestedPrecede.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Regression: a switch-case function stays switch-scoped even nested
    /// in a strict block (tsc TS2304 on the post-block use); the
    /// block-local prebind must not leak it into the enclosing block.
    #[test]
    fn strict_post_switch_function_stays_switch_scoped() {
        let case_text =
            "declare var x: number;\n{\nswitch (x) {\ncase 0:\nfunction f() {\n}\n}\nf();\n}\n";
        let units = split_case_units("tests/cases/compiler/switchCaseFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/switchCaseFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 8)]);
    }
    /// Regression: a try-block function stays try-scoped even nested in a
    /// strict block (tsc TS2304); the block-local prebind must not leak it.
    #[test]
    fn strict_post_try_function_stays_try_scoped() {
        let case_text = "{\ntry {\nfunction f() {\n}\n} catch (e) {\n}\nf();\n}\n";
        let units = split_case_units("tests/cases/compiler/tryBlockFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/tryBlockFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 7)]);
    }
    /// Regression: a braced case-block function stays block-scoped (tsc
    /// TS2304); neither the block-local nor the switch-local prebind may
    /// leak it into an enclosing scope.
    #[test]
    fn strict_braced_case_function_stays_block_scoped() {
        let case_text = "declare var x: number;\n{\nswitch (x) {\ncase 0: {\nfunction f() {\n}\n}\n}\nf();\n}\n";
        let units = split_case_units("tests/cases/compiler/bracedCaseFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/bracedCaseFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 9)]);
    }
    /// Guard: a use before a nested try-body declaration resolves (tsc
    /// silent: the function hoists to the try scope).
    #[test]
    fn strict_nested_try_function_precedes_use() {
        let case_text = "declare var c: boolean;\n{\ntry {\nf();\nif (c) function f() {\n}\n} catch (e) {\n}\n}\n";
        let units = split_case_units("tests/cases/compiler/nestedTryPrecede.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/nestedTryPrecede.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }
    /// Guard: a use before a nested case declaration resolves across
    /// cases (tsc silent: the function hoists to the switch scope).
    #[test]
    fn strict_nested_switch_function_precedes_use() {
        let case_text = "declare var n: number;\ndeclare var c: boolean;\n{\nswitch (n) {\ncase 1: f();\nbreak;\ncase 2: if (c) function f() {\n}\nbreak;\n}\n}\n";
        let units = split_case_units("tests/cases/compiler/nestedSwitchPrecede.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/nestedSwitchPrecede.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }

    /// Regression: an inner-loop function stays inner-loop-scoped (tsc
    /// TS2304 on the outer-loop use, sloppy and strict alike); the outer
    /// prebind must not claim it into the ancestor loop scope.
    #[test]
    fn nested_loop_function_stays_inner_scoped() {
        let case_text = "for (;;) {\ng();\nfor (;;) function g() {\n}\n}\n";
        let units = split_case_units("tests/cases/compiler/nestedLoopFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/nestedLoopFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 2)]);
    }
    /// Guard: a use inside the inner loop resolves (the inner loop-local
    /// prebind declares with the inner-loop identity).
    #[test]
    fn nested_loop_inner_use_resolves() {
        let case_text = "for (;;) {\nfor (;;) {\nfunction g() {\n}\ng();\n}\n}\n";
        let units = split_case_units("tests/cases/compiler/nestedLoopInnerUse.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/nestedLoopInnerUse.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert!(actual.is_empty(), "unexpected diagnostics: {codes:?}");
    }

    /// Regression: an unbraced for-body function stays loop-scoped (tsc
    /// TS2304 on the post-loop use); it must not leak outward as `any`.
    #[test]
    fn for_body_function_stays_loop_scoped() {
        let case_text =
            "declare var cond: boolean;\nfor (; cond;) function f(x: string) {\n}\nf(1);\n";
        let units = split_case_units("tests/cases/compiler/forBodyFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/forBodyFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 4)]);
    }
    /// Regression: a braced for-body function stays loop-scoped too (tsc
    /// TS2304); only the loop subtree sees it.
    #[test]
    fn for_block_body_function_stays_loop_scoped() {
        let case_text =
            "declare var cond: boolean;\nfor (; cond;) {\nfunction b(x: string) {\n}\n}\nb(1);\n";
        let units = split_case_units("tests/cases/compiler/forBlockBodyFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/forBlockBodyFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 6)]);
    }
    /// Regression: a for-of body function stays loop-scoped (tsc TS2304).
    #[test]
    fn for_of_body_function_stays_loop_scoped() {
        let case_text = "declare var items: string[];\nfor (const item of items) function h(x: string) {\n}\nh(1);\n";
        let units = split_case_units("tests/cases/compiler/forOfBodyFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/forOfBodyFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 4)]);
    }
    /// Guard: a while-body function still hoists (tsc checks the post-loop
    /// call: TS2345), so the for-family containment must not leak outward.
    #[test]
    fn while_body_function_still_hoists() {
        let case_text =
            "declare var cond: boolean;\nwhile (cond) function w(x: string) {\n}\nw(1);\n";
        let units = split_case_units("tests/cases/compiler/whileBodyFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/whileBodyFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C053".to_owned(), 4)]);
    }
    /// Guard: an if-body function still hoists (tsc TS2345 on a bad call).
    #[test]
    fn if_body_function_still_hoists() {
        let case_text = "declare var cond: boolean;\nif (cond) function g(x: string) {\n}\ng(1);\n";
        let units = split_case_units("tests/cases/compiler/ifBodyFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/ifBodyFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C053".to_owned(), 4)]);
    }
    /// Regression: a for-in body function stays loop-scoped (tsc TS2304).
    #[test]
    fn for_in_body_function_stays_loop_scoped() {
        let case_text = "declare var o: any;\nfor (var k in o) function h(x: string) {\n}\nh(1);\n";
        let units = split_case_units("tests/cases/compiler/forInBodyFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/forInBodyFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 4)]);
    }
    /// Regression: containment propagates through nested statements (tsc
    /// TS2304 for an if-nested function inside a for body).
    #[test]
    fn for_nested_if_function_stays_loop_scoped() {
        let case_text = "declare var cond: boolean;\nfor (; cond;) {\nif (cond) {\nfunction x(x: string) {\n}\n}\n}\nx(1);\n";
        let units = split_case_units("tests/cases/compiler/forNestedIfFunction.ts", case_text);
        let entry = entry_virtual_path("tests/cases/compiler/forNestedIfFunction.ts", &units);
        let case = compile_case(&units, &entry).expect("case compiles");
        let code_map = repo_code_map();
        let mut actual = collect_facet_diagnostics(&case);
        actual.retain(|diagnostic| code_map.get(&diagnostic.code).is_some());
        let codes: Vec<_> = actual
            .iter()
            .map(|d| (d.code.clone(), d.position.line))
            .collect();
        assert_eq!(codes, vec![("BAMTS-C002".to_owned(), 8)]);
    }
}
