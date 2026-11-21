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
use bamts_compiler::scanner;
use bamts_compiler::source::SourceText;
use bamts_compiler::source::{JsxEmit, ScriptKind, SourceId, TextRange, Utf16Pos};
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
mod baselines;
mod build_info_facet;
mod case_units;
mod compile;
mod declaration_facet;
mod errors_facet;
mod js_facet;
mod source_map_facet;
mod symbols_facet;
mod trace_facet;
mod types_facet;
pub use baselines::{baseline_area, baseline_groups, case_stem, resolve_baseline_file};
use baselines::{
    baseline_owner, case_inputs_with_stem, resolve_stem_baseline, split_baseline_file_name,
    suffix_matches_options,
};
pub(crate) use build_info_facet::observe_build_info;
pub use build_info_facet::{emit_build_info_baseline, extract_tsbuildinfo_sections};
pub(crate) use case_units::shared_lib_support_files;
pub use case_units::{entry_virtual_path, parse_case_pragmas, split_case_units};
use case_units::{
    is_check_cell_declaration_path, is_config_unit_name, is_declaration_input_name,
    is_declaration_section_name, is_json_input_name, is_script_input_name,
    is_tsbuildinfo_section_name, section_header_name, unit_basename,
};
use compile::{
    build_tsconfig, cell_result, compile_failure_observation, compile_option_pairs, read_case_text,
};
pub use compile::{
    compile_case, compile_case_frontend, compile_case_frontend_with_support,
    compile_case_with_pragmas, compile_case_with_support,
};
pub(crate) use declaration_facet::observe_declaration;
pub use declaration_facet::{emit_declaration_baseline, extract_dts_sections};
pub use errors_facet::{
    check_diagnostics, collect_facet_diagnostics, expected_facet_diagnostics,
    parse_errors_baseline, resolve_errors_baselines,
};
pub(crate) use errors_facet::{execute_diagnostics_check, observe_diagnostics};
use js_facet::{
    bundle_output_name, declaration_code, declaration_text_for, full_emit_directory,
    output_section_name, push_map_section, push_output_section,
};
pub(crate) use js_facet::{common_directory, emitted_path, observe_javascript};
pub use js_facet::{
    declaration_extension, declaration_section_name, emit_javascript_baseline,
    javascript_section_name, output_extension,
};
pub use source_map_facet::emit_source_map_baseline;
pub(crate) use source_map_facet::observe_source_map;
pub use symbols_facet::{check_symbols, emit_symbols_baseline, resolve_symbols_baseline};
pub(crate) use symbols_facet::{execute_symbols_check, observe_symbols};
pub(crate) use trace_facet::{collect_resolution_trace, observe_trace};
pub use types_facet::{check_types, emit_types_baseline, resolve_types_baseline};
use types_facet::{collapse_whitespace, slice_source, strip_library_root};
pub(crate) use types_facet::{execute_types_check, observe_types};

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

/// Group snapshot baseline index entries for the flat
/// `tests/baselines/reference/` store by `(stem, extension, suffix)`.
///
/// Key: `(stem, extension)` where extension is `errors.txt`/`types`/`symbols`;
/// value: `(suffix, logical_path)` where suffix is the `(opt=value)` group or
/// empty for the plain baseline.
pub type BaselineGroups = BTreeMap<(String, String), Vec<(String, String)>>;

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

/// The verdict of one types check cell.
#[derive(Debug, Clone)]
pub struct TypesOutcome {
    /// The emitted `.types` document.
    pub emitted: String,
    /// The comparator verdict against the owned baseline.
    pub verdict: FacetVerdict,
}

/// The verdict of one symbols check cell.
#[derive(Debug, Clone)]
pub struct SymbolsOutcome {
    /// The emitted `.symbols` document.
    pub emitted: String,
    /// The comparator verdict against the owned baseline.
    pub verdict: FacetVerdict,
}

#[cfg(test)]
mod tests;
