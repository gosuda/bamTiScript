//! Deterministic logical-catalog extraction for TypeScript harness cases and
//! stable test262 obligations.
//!
//! Cells are configuration-and-observable identities, never source-path-only
//! PASS units. Multi-file `@filename` fixtures stay atomic. Fourslash cases are
//! classified by public-operation reachability. Proposal-stage `test/staging`
//! rows are labeled for exact policy exclusion rather than guessed away.

use crate::{
    ErrorCode, Result, VerificationError,
    schema::{
        CATALOG_NAMES, Catalog, CatalogSource, MANIFEST_PATH, TYPESCRIPT_SUITE_SOURCE,
        VerificationManifest, catalog_source_from_pin, encode_manifest, identifiers_sha256,
        load_sources, parse_json, reject_duplicate_json_keys, required_source, sha256_hex,
        validate_manifest,
    },
};
use serde::{Deserialize, Serialize};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    fs::{self, File, OpenOptions},
    io::Write,
    path::{Component, Path},
    sync::atomic::{AtomicU64, Ordering},
};

const DEFAULT_CONFIGURATION: &str = "default";
const CATALOG_INPUTS_PATH: &str = "verification/catalog-inputs.json";
const LOCAL_CATALOG_NAMES: [&str; 5] = [
    "formal-quint",
    "formal-lean",
    "formal-redex",
    "target-cells",
    "benchmarks",
];
static MANIFEST_TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);
const IDENTITY_SEPARATOR: char = '#';

const STRUCTURAL_DIRECTIVES: [&str; 2] = ["filename", "link"];
const BASELINE_DIRECTIVES: [&str; 1] = ["notypesandsymbols"];

const VARY_BY_OPTIONS: [&str; 64] = [
    "allowjs",
    "allowsyntheticdefaultimports",
    "alwaysstrict",
    "checkjs",
    "composite",
    "declaration",
    "declarationmap",
    "downleveliteration",
    "emitdeclarationonly",
    "emitdecoratormetadata",
    "esmoduleinterop",
    "exactoptionalpropertytypes",
    "experimentaldecorators",
    "forceconsistentcasinginfilenames",
    "importhelpers",
    "importsnotusedasvalues",
    "incremental",
    "inlinesourcemap",
    "inlinesources",
    "isolateddeclarations",
    "isolatedmodules",
    "jsx",
    "moduledetection",
    "moduleresolution",
    "module",
    "newline",
    "nocheck",
    "noemit",
    "noemitonerror",
    "noimplicitany",
    "noimplicitoverride",
    "noimplicitreturns",
    "noimplicitthis",
    "noimplicitusestrict",
    "nolib",
    "noresolve",
    "nounusedlocals",
    "nounusedparameters",
    "preserveconstenums",
    "preservesymlinks",
    "preservevalueimports",
    "removecomments",
    "resolvejsonmodule",
    "resolvepackagejsonexports",
    "resolvepackagejsonimports",
    "skiplibcheck",
    "skipdefaultlibcheck",
    "sourcemap",
    "strict",
    "strictbindcallapply",
    "strictfunctiontypes",
    "strictnullchecks",
    "strictpropertyinitialization",
    "stripinternal",
    "target",
    "traceresolution",
    "usedefineforclassfields",
    "useunknownincatchvariables",
    "verbatimmodulesyntax",
    "erasablesyntaxonly",
    "noemithelpers",
    "noerrortruncation",
    "nouncheckedindexedaccess",
    "strictbuiltiniteratorreturn",
];

const KNOWN_DIRECTIVES: [&str; 178] = [
    "all",
    "allowarbitraryextensions",
    "allowimportingtextensions",
    "allowimportingtsextensions",
    "allowjs",
    "allownontextensions",
    "allownontsextensions",
    "allowsyntheticdefaultimports",
    "allowumdglobalaccess",
    "allowunreachablecode",
    "allowunusedlabels",
    "alwaysstrict",
    "assumechangesonlyaffectdirectdependencies",
    "baselinefile",
    "baseurl",
    "build",
    "capturesuggestions",
    "charset",
    "checkjs",
    "clean",
    "compileonsave",
    "compileroptions",
    "composite",
    "condition",
    "currentdirectory",
    "customconditions",
    "declaration",
    "declarationdir",
    "declarationmap",
    "diagnostics",
    "disablefilenamebasedtypeacquisition",
    "disablereferencedprojectload",
    "disablesizelimit",
    "disablesolutionsearching",
    "disablesourceofprojectreferenceredirect",
    "downleveliteration",
    "dry",
    "emitbom",
    "emitdeclarationonly",
    "emitdecoratormetadata",
    "emitthisfile",
    "enable",
    "erasablesyntaxonly",
    "esmoduleinterop",
    "exactoptionalpropertytypes",
    "exclude",
    "excludedirectories",
    "excludedirectory",
    "excludefile",
    "excludefiles",
    "experimentaldecorators",
    "explainfiles",
    "extendeddiagnostics",
    "extends",
    "fallbackpolling",
    "filename",
    "files",
    "force",
    "forceconsistentcasinginfilenames",
    "fullemitpaths",
    "generatecpuprofile",
    "generatetrace",
    "help",
    "ignoreconfig",
    "ignoredeprecations",
    "importhelpers",
    "importsnotusedasvalues",
    "include",
    "includebuiltfile",
    "incremental",
    "init",
    "inlinesourcemap",
    "inlinesources",
    "isolateddeclarations",
    "isolatedmodules",
    "jsx",
    "jsxfactory",
    "jsxfragmentfactory",
    "jsximportsource",
    "keyofstringsonly",
    "lib",
    "libfiles",
    "libreplacement",
    "link",
    "listemittedfiles",
    "listfiles",
    "listfilesonly",
    "locale",
    "maproot",
    "maxnodemodulejsdepth",
    "module",
    "moduledetection",
    "moduleresolution",
    "modulesuffixes",
    "newline",
    "nocheck",
    "noemit",
    "noemithelpers",
    "noemitonerror",
    "noerrortruncation",
    "nofallthroughcasesinswitch",
    "noimplicitany",
    "noimplicitoverride",
    "noimplicitreferences",
    "noimplicitreturns",
    "noimplicitthis",
    "noimplicitusestrict",
    "nolib",
    "nopropertyaccessfromindexsignature",
    "noresolve",
    "nostrictgenericchecks",
    "notypesandsymbols",
    "nouncheckedindexedaccess",
    "nouncheckedsideeffectimports",
    "nounusedlocals",
    "nounusedparameters",
    "out",
    "outdir",
    "outfile",
    "paths",
    "plugin",
    "plugins",
    "preserveconstenums",
    "preservesymlinks",
    "preservevalueimports",
    "preservewatchoutput",
    "pretty",
    "project",
    "reactnamespace",
    "reference",
    "references",
    "removecomments",
    "reportdiagnostics",
    "resolvejsonmodule",
    "resolvepackagejsonexports",
    "resolvepackagejsonimports",
    "resolvereference",
    "rewriterelativeimportextensions",
    "rootdir",
    "rootdirs",
    "showconfig",
    "skipdefaultlibcheck",
    "skiplibcheck",
    "sourcemap",
    "sourceroot",
    "stabletypeordering",
    "stopbuildonerrors",
    "strict",
    "strictbindcallapply",
    "strictbuiltiniteratorreturn",
    "strictfunctiontypes",
    "strictnullchecks",
    "strictpropertyinitialization",
    "stripinternal",
    "suffix",
    "suppressexcesspropertyerrors",
    "suppressimplicitanyindexerrors",
    "suppressoutputpathcheck",
    "symlink",
    "synchronouswatchdirectory",
    "target",
    "todo",
    "traceresolution",
    "tsbuildinfofile",
    "typeacquisition",
    "typeroots",
    "types",
    "typescriptversion",
    "usecasesensitivefilenames",
    "usedefineforclassfields",
    "useunknownincatchvariables",
    "verbatimmodulesyntax",
    "verbose",
    "version",
    "watch",
    "watchdirectory",
    "watchfile",
    "watchoptions",
];

const TARGET_STAR_VALUES: [&str; 16] = [
    "es3", "es5", "es6", "es2015", "es2016", "es2017", "es2018", "es2019", "es2020", "es2021",
    "es2022", "es2023", "es2024", "es2025", "esnext", "json",
];
const MODULE_STAR_VALUES: [&str; 14] = [
    "none", "commonjs", "amd", "umd", "system", "es6", "es2015", "es2020", "es2022", "esnext",
    "node16", "node18", "nodenext", "preserve",
];
const BOOLEAN_STAR_VALUES: [&str; 2] = ["true", "false"];

const TEST262_STABLE_PREFIXES: [&str; 4] = [
    "test/annexB/",
    "test/built-ins/",
    "test/intl402/",
    "test/language/",
];
const TEST262_STAGING_PREFIX: &str = "test/staging/";

const API_OPERATIONS: [(&str, PublicSurface, ObservableKind); 42] = [
    (
        "baselineCompletions",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Types,
    ),
    (
        "baselineFindAllReferences",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Symbols,
    ),
    (
        "baselineFindAllReferencesAtRangesWithText",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Symbols,
    ),
    (
        "baselineGetDefinitionAtPosition",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Symbols,
    ),
    (
        "baselineGetDefinitionAtRangesWithText",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Symbols,
    ),
    (
        "baselineGetFileReferences",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Symbols,
    ),
    (
        "baselineGoToDefinition",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Symbols,
    ),
    (
        "baselineGoToDefinitionAtRangesWithText",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Symbols,
    ),
    (
        "baselineGoToImplementation",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Symbols,
    ),
    (
        "baselineGoToImplementationAtRangesWithText",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Symbols,
    ),
    (
        "baselineGoToSourceDefinition",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Symbols,
    ),
    (
        "baselineGoToType",
        PublicSurface::CompilerApi,
        ObservableKind::Types,
    ),
    (
        "baselineGoToTypeAtRangesWithText",
        PublicSurface::CompilerApi,
        ObservableKind::Types,
    ),
    (
        "baselineGetEmitOutput",
        PublicSurface::CompilerApi,
        ObservableKind::JavaScript,
    ),
    (
        "baselineQuickInfo",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Types,
    ),
    (
        "baselineSignatureHelp",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Types,
    ),
    (
        "baselineSyntacticAndSemanticDiagnostics",
        PublicSurface::CompilerApi,
        ObservableKind::Diagnostics,
    ),
    (
        "baselineSyntacticDiagnostics",
        PublicSurface::CompilerApi,
        ObservableKind::Diagnostics,
    ),
    (
        "completions",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Types,
    ),
    (
        "errorExistsAfterMarker",
        PublicSurface::CompilerApi,
        ObservableKind::Diagnostics,
    ),
    (
        "errorExistsAtRange",
        PublicSurface::CompilerApi,
        ObservableKind::Diagnostics,
    ),
    (
        "errorExistsBeforeMarker",
        PublicSurface::CompilerApi,
        ObservableKind::Diagnostics,
    ),
    (
        "errorExistsBetweenMarkers",
        PublicSurface::CompilerApi,
        ObservableKind::Diagnostics,
    ),
    (
        "getEmitOutput",
        PublicSurface::CompilerApi,
        ObservableKind::JavaScript,
    ),
    (
        "getRegionSemanticDiagnostics",
        PublicSurface::CompilerApi,
        ObservableKind::Diagnostics,
    ),
    (
        "getSemanticDiagnostics",
        PublicSurface::CompilerApi,
        ObservableKind::Diagnostics,
    ),
    (
        "getSuggestionDiagnostics",
        PublicSurface::CompilerApi,
        ObservableKind::Diagnostics,
    ),
    (
        "getSyntacticDiagnostics",
        PublicSurface::CompilerApi,
        ObservableKind::Diagnostics,
    ),
    (
        "noErrors",
        PublicSurface::CompilerApi,
        ObservableKind::Diagnostics,
    ),
    (
        "noSignatureHelp",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Types,
    ),
    (
        "noSignatureHelpForTriggerReason",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Types,
    ),
    (
        "numberOfErrorsInCurrentFile",
        PublicSurface::CompilerApi,
        ObservableKind::Diagnostics,
    ),
    (
        "quickInfoAt",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Types,
    ),
    (
        "quickInfoExists",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Types,
    ),
    (
        "quickInfoIs",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Types,
    ),
    (
        "quickInfos",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Types,
    ),
    (
        "semanticClassificationsAre",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Types,
    ),
    (
        "signatureHelp",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Types,
    ),
    (
        "signatureHelpPresentForTriggerReason",
        PublicSurface::LanguageServiceApi,
        ObservableKind::Types,
    ),
    (
        "symbolAtLocation",
        PublicSurface::CompilerApi,
        ObservableKind::Symbols,
    ),
    (
        "typeAtLocation",
        PublicSurface::CompilerApi,
        ObservableKind::Types,
    ),
    (
        "typeOfSymbolAtLocation",
        PublicSurface::CompilerApi,
        ObservableKind::Types,
    ),
];
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum RunnerKind {
    Compiler,
    Conformance,
    Project,
    Transpile,
    Fourslash,
    Test262,
}

impl RunnerKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Compiler => "compiler",
            Self::Conformance => "conformance",
            Self::Project => "project",
            Self::Transpile => "transpile",
            Self::Fourslash => "fourslash",
            Self::Test262 => "test262",
        }
    }
}

impl fmt::Display for RunnerKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ObservableKind {
    Parse,
    Diagnostics,
    JavaScript,
    Declaration,
    SourceMap,
    Trace,
    BuildInfo,
    Types,
    Symbols,
    Runtime,
}

impl ObservableKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Parse => "parse",
            Self::Diagnostics => "diagnostics",
            Self::JavaScript => "javascript",
            Self::Declaration => "declaration",
            Self::SourceMap => "source-map",
            Self::Trace => "trace",
            Self::BuildInfo => "build-info",
            Self::Types => "types",
            Self::Symbols => "symbols",
            Self::Runtime => "runtime",
        }
    }
}

impl fmt::Display for ObservableKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum PublicSurface {
    Cli,
    CompilerApi,
    LanguageServiceApi,
    AstApi,
    Runtime,
    InternalHarness,
    ProposalStage,
}

impl PublicSurface {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Cli => "cli",
            Self::CompilerApi => "compiler-api",
            Self::LanguageServiceApi => "language-service-api",
            Self::AstApi => "ast-api",
            Self::Runtime => "runtime",
            Self::InternalHarness => "internal-harness",
            Self::ProposalStage => "proposal-stage",
        }
    }

    fn rank(self) -> u8 {
        match self {
            Self::CompilerApi => 6,
            Self::LanguageServiceApi => 5,
            Self::AstApi => 4,
            Self::Cli => 3,
            Self::Runtime => 2,
            Self::InternalHarness => 1,
            Self::ProposalStage => 0,
        }
    }
}

impl fmt::Display for PublicSurface {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CatalogCell {
    pub authority: String,
    pub runner: RunnerKind,
    pub case: String,
    pub configuration: String,
    pub observable: ObservableKind,
    pub public_surface: PublicSurface,
}

impl CatalogCell {
    fn new(
        authority: &str,
        runner: RunnerKind,
        case: String,
        configuration: String,
        observable: ObservableKind,
        public_surface: PublicSurface,
    ) -> Result<Self> {
        validate_identity_part("authority", authority)?;
        validate_case_path(&case)?;
        validate_identity_part("configuration", &configuration)?;
        Ok(Self {
            authority: authority.to_owned(),
            runner,
            case,
            configuration,
            observable,
            public_surface,
        })
    }

    pub fn rendered_identity(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for CatalogCell {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{}/{}/{}#{}#{}",
            self.authority, self.runner, self.case, self.configuration, self.observable
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaseConfiguration {
    pub name: String,
    pub options: BTreeMap<String, String>,
    pub virtual_files: Vec<String>,
    pub observables: BTreeSet<ObservableKind>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct CatalogFile {
    release: String,
    sha256: String,
    cells: Vec<CatalogCell>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct CatalogInputs {
    schema: String,
    catalogs: Vec<CatalogInput>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct CatalogInput {
    extractor: serde_json::Value,
    id: String,
    identifiers: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ManifestRegeneration {
    pub catalogs: usize,
    pub identifiers: usize,
    pub wrote_manifest: bool,
}

/// Extracts one upstream logical catalog from its pinned materialized source.
pub fn extract_catalog_cells(root: &Path, catalog: &str) -> Result<Vec<CatalogCell>> {
    match catalog {
        "typescript-7.0.2" => extract_typescript_cells(
            &root.join("target/authority/typescript-7.0.2-tests"),
            catalog,
        ),
        "typescript-6.0.2" => extract_typescript_cells(
            &root.join("target/authority/typescript-6.0.2-tests"),
            catalog,
        ),
        "typescript-5.9.3" => extract_typescript_cells(
            &root.join("target/authority/typescript-5.9.3-tests"),
            catalog,
        ),
        "test262" => extract_test262_cells(&root.join("target/authority/test262"), catalog),
        _ => Err(VerificationError::new(
            ErrorCode::Usage,
            format!("catalog `{catalog}` is not an extractable upstream catalog"),
        )),
    }
}

pub fn extract_typescript_cells(root: &Path, authority: &str) -> Result<Vec<CatalogCell>> {
    let mut cells = Vec::new();
    extract_compiler_tree(
        root,
        authority,
        RunnerKind::Compiler,
        "tests/cases/compiler",
        PublicSurface::CompilerApi,
        &mut cells,
    )?;
    extract_compiler_tree(
        root,
        authority,
        RunnerKind::Conformance,
        "tests/cases/conformance",
        PublicSurface::CompilerApi,
        &mut cells,
    )?;
    extract_project_tree(root, authority, &mut cells)?;
    extract_transpile_tree(root, authority, &mut cells)?;
    extract_fourslash_tree(root, authority, "tests/cases/fourslash", &mut cells)?;
    extract_fourslash_tree(root, authority, "tests/cases/fourslash/server", &mut cells)?;
    finalize_cells(cells)
}

pub fn extract_test262_cells(root: &Path, authority: &str) -> Result<Vec<CatalogCell>> {
    let mut cells = Vec::new();
    for relative in walk_files(root, "test", is_js_file, true)? {
        if is_test262_fixture(&relative) {
            continue;
        }
        let surface = if relative.starts_with(TEST262_STAGING_PREFIX) {
            PublicSurface::ProposalStage
        } else if TEST262_STABLE_PREFIXES
            .iter()
            .any(|prefix| relative.starts_with(prefix))
        {
            PublicSurface::Runtime
        } else {
            continue;
        };
        cells.push(CatalogCell::new(
            authority,
            RunnerKind::Test262,
            relative,
            DEFAULT_CONFIGURATION.to_owned(),
            ObservableKind::Runtime,
            surface,
        )?);
    }
    finalize_cells(cells)
}

pub fn catalog_sha256(cells: &[CatalogCell]) -> Result<String> {
    let mut hasher = Sha256::new();
    let mut previous: Option<String> = None;
    for cell in cells {
        let identity = cell.rendered_identity();
        if let Some(previous_identity) = &previous
            && identity == *previous_identity
        {
            return Err(duplicate_identity(&identity));
        }
        hasher.update(identity.as_bytes());
        hasher.update(b"\n");
        previous = Some(identity);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

pub fn write_catalog_json<W: Write>(
    mut writer: W,
    release: &str,
    cells: &[CatalogCell],
) -> Result<()> {
    let bytes = catalog_file_bytes(release, cells)?;
    writer.write_all(&bytes).map_err(|error| {
        VerificationError::new(ErrorCode::Io, format!("cannot write catalog: {error}"))
    })
}

pub fn check_catalog_json(path: &Path, release: &str, cells: &[CatalogCell]) -> Result<()> {
    let expected = catalog_file_bytes(release, cells)?;
    let actual = fs::read(path).map_err(|error| io_error(path, &error))?;
    if actual == expected {
        Ok(())
    } else {
        Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "{}: catalog bytes do not match the extracted catalog",
                path.display()
            ),
        ))
    }
}

pub fn regenerate_manifest(root: &Path, check: bool) -> Result<ManifestRegeneration> {
    let manifest = generate_manifest(root)?;
    let bytes = encode_manifest(&manifest)?;
    let path = root.join(MANIFEST_PATH);
    let identifiers = manifest
        .catalogs
        .iter()
        .try_fold(0usize, |total, catalog| {
            total.checked_add(catalog.identifier_count).ok_or_else(|| {
                VerificationError::new(ErrorCode::Schema, "manifest identifier count overflow")
            })
        })?;
    if check {
        check_generated_manifest(&path, &bytes)?;
    } else {
        replace_file_atomically(&path, &bytes)?;
    }
    Ok(ManifestRegeneration {
        catalogs: manifest.catalogs.len(),
        identifiers,
        wrote_manifest: !check,
    })
}

fn generate_manifest(root: &Path) -> Result<VerificationManifest> {
    let (sources, source_ledger_sha256) = load_sources(root)?;
    let mut catalogs = BTreeMap::new();

    let typescript_catalogs = [
        (
            "typescript-7.0.2",
            TYPESCRIPT_SUITE_SOURCE,
            "target/authority/typescript-7.0.2-tests",
        ),
        (
            "typescript-6.0.2",
            "typescript-6.0-tests",
            "target/authority/typescript-6.0.2-tests",
        ),
        (
            "typescript-5.9.3",
            "typescript-compat-tests",
            "target/authority/typescript-5.9.3-tests",
        ),
    ];
    for (id, source_name, relative_root) in typescript_catalogs {
        let cells = extract_catalog_cells(root, id)?;
        let extractor = json!({
            "identity": "authority/runner/case#configuration#observable",
            "kind": "typescript-logical-cell/v1",
            "source_root": relative_root,
        });
        let source = catalog_source_from_pin(required_source(&sources, source_name)?);
        insert_catalog(
            &mut catalogs,
            catalog_from_cells(id, extractor, source, &cells)?,
        )?;
    }

    let test262_root = "target/authority/test262";
    let cells = extract_test262_cells(&root.join(test262_root), "test262")?;
    insert_catalog(
        &mut catalogs,
        catalog_from_cells(
            "test262",
            json!({
                "exclude": "*_FIXTURE*.js",
                "identity": "authority/runner/case#configuration#observable",
                "include": ["test/built-ins/**/*.js", "test/intl402/**/*.js", "test/language/**/*.js", "test/staging/**/*.js"],
                "kind": "test262-logical-cell/v1",
                "source_root": test262_root,
            }),
            catalog_source_from_pin(required_source(&sources, "test262")?),
            &cells,
        )?,
    )?;

    for catalog in load_local_catalog_inputs(root)? {
        insert_catalog(&mut catalogs, catalog)?;
    }

    let ordered = CATALOG_NAMES
        .iter()
        .map(|id| {
            catalogs.remove(*id).ok_or_else(|| {
                VerificationError::new(
                    ErrorCode::SetMismatch,
                    format!("catalog generator did not produce `{id}`"),
                )
            })
        })
        .collect::<Result<Vec<_>>>()?;
    if let Some(extra) = catalogs.keys().next() {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!("catalog generator produced unexpected `{extra}`"),
        ));
    }
    let manifest = VerificationManifest {
        schema: "bamti.verification-manifest/v1".to_owned(),
        source_ledger_sha256,
        catalogs: ordered,
    };
    let path = root.join(MANIFEST_PATH);
    let (sources, source_ledger_sha256) = load_sources(root)?;
    validate_manifest(&manifest, &path, &source_ledger_sha256, &sources)?;
    Ok(manifest)
}

fn load_local_catalog_inputs(root: &Path) -> Result<Vec<Catalog>> {
    let path = root.join(CATALOG_INPUTS_PATH);
    let bytes = fs::read(&path).map_err(|error| io_error(&path, &error))?;
    reject_duplicate_json_keys(&path, &bytes)?;
    let inputs: CatalogInputs = parse_json(&path, &bytes)?;
    if inputs.schema != "bamti.catalog-inputs/v1" {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "{}: expected schema `bamti.catalog-inputs/v1`, found `{}`",
                path.display(),
                inputs.schema
            ),
        ));
    }
    let source = CatalogSource {
        pin: "catalog-inputs/v1".to_owned(),
        url: format!("local://{CATALOG_INPUTS_PATH}"),
        digest_algorithm: "sha256".to_owned(),
        digest: sha256_hex(&bytes),
    };
    let mut names = BTreeSet::new();
    let catalogs = inputs
        .catalogs
        .into_iter()
        .map(|input| {
            if !names.insert(input.id.clone()) {
                return Err(VerificationError::new(
                    ErrorCode::Duplicate,
                    format!("{}: duplicate local catalog `{}`", path.display(), input.id),
                ));
            }
            catalog_from_identifiers(
                &input.id,
                input.extractor,
                source.clone(),
                input.identifiers,
            )
        })
        .collect::<Result<Vec<_>>>()?;
    let expected: BTreeSet<String> = LOCAL_CATALOG_NAMES
        .iter()
        .map(|name| (*name).to_owned())
        .collect();
    if names != expected {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!(
                "{}: local catalog names differ: expected {:?}, found {:?}",
                path.display(),
                expected,
                names
            ),
        ));
    }
    Ok(catalogs)
}

fn catalog_from_cells(
    id: &str,
    extractor: serde_json::Value,
    source: CatalogSource,
    cells: &[CatalogCell],
) -> Result<Catalog> {
    let mut identifiers: Vec<_> = cells.iter().map(CatalogCell::rendered_identity).collect();
    identifiers.sort();
    catalog_from_identifiers(id, extractor, source, identifiers)
}

fn catalog_from_identifiers(
    id: &str,
    extractor: serde_json::Value,
    source: CatalogSource,
    identifiers: Vec<String>,
) -> Result<Catalog> {
    if identifiers
        .windows(2)
        .any(|pair| pair[0].as_str() >= pair[1].as_str())
    {
        return Err(VerificationError::new(
            ErrorCode::Duplicate,
            format!("catalog `{id}` identifiers must be strictly sorted and unique"),
        ));
    }
    Ok(Catalog {
        extractor,
        id: id.to_owned(),
        identifier_count: identifiers.len(),
        identifiers_sha256: identifiers_sha256(&identifiers),
        identifiers,
        source,
    })
}

fn insert_catalog(catalogs: &mut BTreeMap<String, Catalog>, catalog: Catalog) -> Result<()> {
    let id = catalog.id.clone();
    if catalogs.insert(id.clone(), catalog).is_some() {
        return Err(VerificationError::new(
            ErrorCode::Duplicate,
            format!("catalog generator produced duplicate `{id}`"),
        ));
    }
    Ok(())
}

fn check_generated_manifest(path: &Path, expected: &[u8]) -> Result<()> {
    let actual = fs::read(path).map_err(|error| io_error(path, &error))?;
    if actual == expected {
        return Ok(());
    }
    Err(VerificationError::new(
        ErrorCode::Digest,
        format!(
            "{}: generated manifest differs; run `catalog regenerate --release typescript-7.0.2`",
            path.display()
        ),
    ))
}

fn replace_file_atomically(path: &Path, bytes: &[u8]) -> Result<()> {
    let parent = path.parent().ok_or_else(|| {
        VerificationError::new(
            ErrorCode::Io,
            format!("{}: manifest has no parent directory", path.display()),
        )
    })?;
    fs::create_dir_all(parent).map_err(|error| io_error(parent, &error))?;
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| {
            VerificationError::new(
                ErrorCode::Io,
                format!("{}: manifest file name is not UTF-8", path.display()),
            )
        })?;
    let nonce = MANIFEST_TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temporary = parent.join(format!(".{file_name}.{}.{}.tmp", std::process::id(), nonce));
    let result = (|| {
        let mut file = OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&temporary)
            .map_err(|error| io_error(&temporary, &error))?;
        file.write_all(bytes)
            .map_err(|error| io_error(&temporary, &error))?;
        file.sync_all()
            .map_err(|error| io_error(&temporary, &error))?;
        fs::rename(&temporary, path).map_err(|error| io_error(path, &error))?;
        File::open(parent)
            .and_then(|directory| directory.sync_all())
            .map_err(|error| io_error(parent, &error))
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    result
}

pub fn parse_case_configuration(source: &str) -> Result<Vec<CaseConfiguration>> {
    let (options, virtual_files) = parse_directives(source)?;
    let variations = expand_variations(&options)?;
    let mut configurations = Vec::with_capacity(variations.len());
    for variation in variations {
        let mut merged = options.clone();
        let names: BTreeSet<String> = variation.keys().cloned().collect();
        for name in names {
            merged.remove(&name);
        }
        merged.extend(variation);
        let name = configuration_name(&merged);
        let observables = compiler_observables(&merged);
        configurations.push(CaseConfiguration {
            name,
            options: merged,
            virtual_files: virtual_files.clone(),
            observables,
        });
    }
    configurations.sort_by(|left, right| left.name.cmp(&right.name));
    let mut previous: Option<&str> = None;
    for configuration in &configurations {
        if previous == Some(configuration.name.as_str()) {
            return Err(VerificationError::new(
                ErrorCode::Duplicate,
                format!("duplicate configuration `{}`", configuration.name),
            ));
        }
        previous = Some(configuration.name.as_str());
    }
    Ok(configurations)
}

fn catalog_file_bytes(release: &str, cells: &[CatalogCell]) -> Result<Vec<u8>> {
    validate_identity_part("release", release)?;
    let document = CatalogFile {
        release: release.to_owned(),
        sha256: catalog_sha256(cells)?,
        cells: cells.to_vec(),
    };
    let mut bytes = serde_json::to_vec(&document).map_err(|error| {
        VerificationError::new(
            ErrorCode::Json,
            format!("cannot serialize catalog: {error}"),
        )
    })?;
    bytes.push(b'\n');
    Ok(bytes)
}

fn extract_compiler_tree(
    root: &Path,
    authority: &str,
    runner: RunnerKind,
    relative_dir: &str,
    surface: PublicSurface,
    cells: &mut Vec<CatalogCell>,
) -> Result<()> {
    for relative in walk_files(root, relative_dir, is_ts_source, true)? {
        let source = read_text(&root.join(&relative))?;
        let configurations = parse_case_configuration(&source).map_err(|error| {
            VerificationError::new(error.code(), format!("{relative}: {error}"))
        })?;
        for configuration in configurations {
            push_configuration_cells(
                cells,
                authority,
                runner,
                relative.clone(),
                &configuration,
                surface,
            )?;
        }
    }
    Ok(())
}

fn extract_project_tree(root: &Path, authority: &str, cells: &mut Vec<CatalogCell>) -> Result<()> {
    for relative in walk_files(root, "tests/cases/project", is_json_file, true)? {
        let source = read_text(&root.join(&relative))?;
        serde_json::from_str::<serde_json::Value>(&source).map_err(|error| {
            VerificationError::new(
                ErrorCode::Schema,
                format!("{relative}: invalid project fixture: {error}"),
            )
        })?;
        let configuration = CaseConfiguration {
            name: DEFAULT_CONFIGURATION.to_owned(),
            options: BTreeMap::new(),
            virtual_files: Vec::new(),
            observables: BTreeSet::from([
                ObservableKind::Diagnostics,
                ObservableKind::JavaScript,
                ObservableKind::Declaration,
                ObservableKind::Trace,
            ]),
        };
        push_configuration_cells(
            cells,
            authority,
            RunnerKind::Project,
            relative,
            &configuration,
            PublicSurface::Cli,
        )?;
    }
    Ok(())
}

fn extract_transpile_tree(
    root: &Path,
    authority: &str,
    cells: &mut Vec<CatalogCell>,
) -> Result<()> {
    for relative in walk_files(root, "tests/cases/transpile", is_transpile_file, true)? {
        let source = read_text(&root.join(&relative))?;
        let configurations = parse_case_configuration(&source).map_err(|error| {
            VerificationError::new(error.code(), format!("{relative}: {error}"))
        })?;
        for mut configuration in configurations {
            configuration.observables = transpile_observables(&configuration.options);
            push_configuration_cells(
                cells,
                authority,
                RunnerKind::Transpile,
                relative.clone(),
                &configuration,
                PublicSurface::CompilerApi,
            )?;
        }
    }
    Ok(())
}

fn extract_fourslash_tree(
    root: &Path,
    authority: &str,
    relative_dir: &str,
    cells: &mut Vec<CatalogCell>,
) -> Result<()> {
    for relative in walk_files(root, relative_dir, is_ts_file, false)? {
        if path_file_name(&relative) == Some("fourslash.ts") {
            continue;
        }
        let source = read_text(&root.join(&relative))?;
        let configurations = parse_case_configuration(&source).map_err(|error| {
            VerificationError::new(error.code(), format!("{relative}: {error}"))
        })?;
        let operations = classify_fourslash_operations(&source);
        for configuration in configurations {
            push_fourslash_cells(
                cells,
                authority,
                relative.clone(),
                &configuration,
                &operations,
            )?;
        }
    }
    Ok(())
}

fn push_configuration_cells(
    cells: &mut Vec<CatalogCell>,
    authority: &str,
    runner: RunnerKind,
    case: String,
    configuration: &CaseConfiguration,
    surface: PublicSurface,
) -> Result<()> {
    if configuration.observables.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("{case}: fixture declares no observable cells"),
        ));
    }
    for observable in &configuration.observables {
        cells.push(CatalogCell::new(
            authority,
            runner,
            case.clone(),
            configuration.name.clone(),
            *observable,
            surface,
        )?);
    }
    Ok(())
}

fn push_fourslash_cells(
    cells: &mut Vec<CatalogCell>,
    authority: &str,
    case: String,
    configuration: &CaseConfiguration,
    operations: &FourslashOperations,
) -> Result<()> {
    if operations.public_observables.is_empty() {
        cells.push(CatalogCell::new(
            authority,
            RunnerKind::Fourslash,
            case,
            configuration.name.clone(),
            ObservableKind::Parse,
            PublicSurface::InternalHarness,
        )?);
        return Ok(());
    }
    for (observable, surface) in &operations.public_observables {
        cells.push(CatalogCell::new(
            authority,
            RunnerKind::Fourslash,
            case.clone(),
            configuration.name.clone(),
            *observable,
            *surface,
        )?);
    }
    Ok(())
}

#[derive(Default)]
struct FourslashOperations {
    public_observables: BTreeMap<ObservableKind, PublicSurface>,
}

fn classify_fourslash_operations(source: &str) -> FourslashOperations {
    let imperative = fourslash_imperative(source);
    let mut operations = FourslashOperations::default();
    for method in method_calls(&imperative) {
        if let Some((_, surface, observable)) = lookup_api_operation(method) {
            operations
                .public_observables
                .entry(observable)
                .and_modify(|existing| {
                    if surface.rank() > existing.rank() {
                        *existing = surface;
                    }
                })
                .or_insert(surface);
        }
    }
    operations
}

fn lookup_api_operation(method: &str) -> Option<(&'static str, PublicSurface, ObservableKind)> {
    API_OPERATIONS
        .iter()
        .find(|candidate| candidate.0 == method)
        .copied()
}

fn fourslash_imperative(source: &str) -> String {
    source
        .lines()
        .filter(|line| !line.trim_start().starts_with("////"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn method_calls(source: &str) -> Vec<&str> {
    const RECEIVERS: [&str; 7] = [
        "verify.", "edit.", "format.", "debug.", "goTo.", "test.", "config.",
    ];
    let mut methods = Vec::new();
    for receiver in RECEIVERS {
        let mut rest = source;
        while let Some(index) = rest.find(receiver) {
            let after = &rest[index + receiver.len()..];
            let method = after
                .char_indices()
                .take_while(|(_, ch)| ch.is_ascii_alphanumeric() || *ch == '_')
                .last()
                .map(|(end, ch)| &after[..end + ch.len_utf8()])
                .unwrap_or("");
            if !method.is_empty() {
                methods.push(method);
            }
            rest = &after[method.len()..];
        }
    }
    methods
}

fn parse_directives(source: &str) -> Result<(BTreeMap<String, String>, Vec<String>)> {
    let mut options = BTreeMap::new();
    let mut virtual_files = Vec::new();
    for raw_line in source.split(['\r', '\n']) {
        let line = raw_line.trim();
        let Some(directive) = parse_directive_line(line) else {
            continue;
        };
        let (name, value) = directive?;
        if name == "filename" {
            if value.is_empty() {
                return Err(VerificationError::new(
                    ErrorCode::Schema,
                    "empty @filename virtual file",
                ));
            }
            virtual_files.push(value);
            continue;
        }
        if name == "link" {
            continue;
        }
        options.insert(name, value);
    }
    Ok((options, virtual_files))
}

fn parse_directive_line(line: &str) -> Option<Result<(String, String)>> {
    let rest = line.strip_prefix("//")?;
    let rest = rest.trim_start();
    let rest = rest.strip_prefix('@')?;
    let colon = rest.find(':')?;
    let name = rest[..colon].trim().to_ascii_lowercase();
    if name.is_empty() || !name.bytes().all(|byte| byte.is_ascii_alphanumeric()) {
        return None;
    }
    if !is_known_directive(&name) {
        return Some(Err(VerificationError::new(
            ErrorCode::Schema,
            format!("unknown semantic directive `@{name}`"),
        )));
    }
    let value = rest[colon + 1..].trim().to_owned();
    Some(Ok((name, value)))
}

fn is_known_directive(name: &str) -> bool {
    KNOWN_DIRECTIVES.binary_search(&name).is_ok()
}

fn expand_variations(options: &BTreeMap<String, String>) -> Result<Vec<BTreeMap<String, String>>> {
    let mut vary_by = Vec::new();
    for (key, value) in options {
        if !is_vary_by_option(key) {
            continue;
        }
        if let Some(entries) = split_variation_values(key, value)? {
            vary_by.push((key.clone(), entries));
        }
    }
    if vary_by.is_empty() {
        return Ok(vec![BTreeMap::new()]);
    }
    let mut count = 1usize;
    for (_, entries) in &vary_by {
        count = count
            .checked_mul(entries.len())
            .filter(|value| *value <= 25)
            .ok_or_else(|| {
                VerificationError::new(
                    ErrorCode::Schema,
                    "repeat/config directives exceeded 25 variations",
                )
            })?;
    }
    let mut configurations = Vec::new();
    cartesian_variations(&vary_by, 0, &mut BTreeMap::new(), &mut configurations);
    Ok(configurations)
}

fn cartesian_variations(
    vary_by: &[(String, Vec<String>)],
    offset: usize,
    current: &mut BTreeMap<String, String>,
    out: &mut Vec<BTreeMap<String, String>>,
) {
    if offset >= vary_by.len() {
        out.push(current.clone());
        return;
    }
    let (key, entries) = &vary_by[offset];
    for entry in entries {
        current.insert(key.clone(), entry.clone());
        cartesian_variations(vary_by, offset + 1, current, out);
        current.remove(key);
    }
}

fn split_variation_values(key: &str, value: &str) -> Result<Option<Vec<String>>> {
    if value.trim().is_empty() {
        return Ok(None);
    }
    let mut includes = Vec::new();
    let mut excludes = Vec::new();
    let mut star = false;
    for part in value.split(',') {
        let token = part.trim().to_ascii_lowercase();
        if token.is_empty() {
            continue;
        }
        if token == "*" {
            star = true;
            continue;
        }
        if let Some(rest) = token.strip_prefix('-').or_else(|| token.strip_prefix('!')) {
            excludes.push(rest.to_owned());
        } else {
            includes.push(token);
        }
    }
    if !star && includes.len() <= 1 && excludes.is_empty() {
        return Ok(None);
    }
    let mut values = includes;
    if star {
        values.extend(star_values(key)?.iter().map(|value| (*value).to_owned()));
    }
    values.sort();
    values.dedup();
    values.retain(|value| !excludes.iter().any(|exclude| exclude == value));
    if values.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("@{key} variations produced an empty set"),
        ));
    }
    if values.len() == 1 && !star {
        return Ok(None);
    }
    Ok(Some(values))
}

fn star_values(key: &str) -> Result<&'static [&'static str]> {
    match key {
        "target" => Ok(&TARGET_STAR_VALUES),
        "module" => Ok(&MODULE_STAR_VALUES),
        key if BOOLEAN_STAR_VALUES_FOR.binary_search(&key).is_ok() => Ok(&BOOLEAN_STAR_VALUES),
        _ => Err(VerificationError::new(
            ErrorCode::Schema,
            format!("cannot expand `@{key}: *` without a closed value set"),
        )),
    }
}

const BOOLEAN_STAR_VALUES_FOR: [&str; 52] = [
    "allowjs",
    "allowsyntheticdefaultimports",
    "alwaysstrict",
    "checkjs",
    "composite",
    "declaration",
    "declarationmap",
    "downleveliteration",
    "emitdeclarationonly",
    "emitdecoratormetadata",
    "erasablesyntaxonly",
    "esmoduleinterop",
    "exactoptionalpropertytypes",
    "experimentaldecorators",
    "forceconsistentcasinginfilenames",
    "importhelpers",
    "incremental",
    "inlinesourcemap",
    "inlinesources",
    "isolateddeclarations",
    "isolatedmodules",
    "noemit",
    "noemitonerror",
    "noimplicitany",
    "noimplicitoverride",
    "noimplicitreturns",
    "noimplicitthis",
    "noimplicitusestrict",
    "nolib",
    "noresolve",
    "nounusedlocals",
    "nounusedparameters",
    "preserveconstenums",
    "preservesymlinks",
    "preservevalueimports",
    "removecomments",
    "resolvejsonmodule",
    "resolvepackagejsonexports",
    "resolvepackagejsonimports",
    "skipdefaultlibcheck",
    "skiplibcheck",
    "sourcemap",
    "strict",
    "strictbindcallapply",
    "strictfunctiontypes",
    "strictnullchecks",
    "strictpropertyinitialization",
    "stripinternal",
    "traceresolution",
    "usedefineforclassfields",
    "useunknownincatchvariables",
    "verbatimmodulesyntax",
];

fn is_vary_by_option(name: &str) -> bool {
    VARY_BY_OPTIONS.binary_search(&name).is_ok()
}

fn configuration_name(options: &BTreeMap<String, String>) -> String {
    let mut parts = Vec::new();
    for (key, value) in options {
        if is_structural_or_baseline(key) {
            continue;
        }
        parts.push(format!("{}={}", key, value.to_ascii_lowercase()));
    }
    if parts.is_empty() {
        DEFAULT_CONFIGURATION.to_owned()
    } else {
        parts.join(",")
    }
}

fn is_structural_or_baseline(name: &str) -> bool {
    STRUCTURAL_DIRECTIVES.binary_search(&name).is_ok()
        || BASELINE_DIRECTIVES.binary_search(&name).is_ok()
}

fn compiler_observables(options: &BTreeMap<String, String>) -> BTreeSet<ObservableKind> {
    let mut observables = BTreeSet::new();
    observables.insert(ObservableKind::Diagnostics);
    let emit_declaration_only = option_is_true(options, "emitdeclarationonly");
    if !option_is_true(options, "noemit") && !emit_declaration_only {
        observables.insert(ObservableKind::JavaScript);
    }
    if option_is_true(options, "declaration") || emit_declaration_only {
        observables.insert(ObservableKind::Declaration);
    }
    if option_is_true(options, "sourcemap")
        || option_is_true(options, "inlinesourcemap")
        || option_is_true(options, "declarationmap")
    {
        observables.insert(ObservableKind::SourceMap);
    }
    if option_is_true(options, "traceresolution") {
        observables.insert(ObservableKind::Trace);
    }
    if option_is_true(options, "incremental")
        || option_is_true(options, "composite")
        || options.contains_key("tsbuildinfofile")
    {
        observables.insert(ObservableKind::BuildInfo);
    }
    if !option_is_true(options, "notypesandsymbols") {
        observables.insert(ObservableKind::Types);
        observables.insert(ObservableKind::Symbols);
    }
    observables
}

fn transpile_observables(options: &BTreeMap<String, String>) -> BTreeSet<ObservableKind> {
    let mut observables = BTreeSet::new();
    if !option_is_true(options, "emitdeclarationonly") {
        observables.insert(ObservableKind::JavaScript);
    }
    if option_is_true(options, "declaration") || option_is_true(options, "emitdeclarationonly") {
        observables.insert(ObservableKind::Declaration);
    }
    if option_is_true(options, "sourcemap")
        || option_is_true(options, "inlinesourcemap")
        || option_is_true(options, "declarationmap")
    {
        observables.insert(ObservableKind::SourceMap);
    }
    if observables.is_empty() {
        observables.insert(ObservableKind::JavaScript);
    }
    observables
}

fn option_is_true(options: &BTreeMap<String, String>, name: &str) -> bool {
    options
        .get(name)
        .is_some_and(|value| value.eq_ignore_ascii_case("true"))
}

fn finalize_cells(mut cells: Vec<CatalogCell>) -> Result<Vec<CatalogCell>> {
    cells.sort();
    let mut previous: Option<String> = None;
    for cell in &cells {
        let identity = cell.rendered_identity();
        if previous.as_deref() == Some(identity.as_str()) {
            return Err(duplicate_identity(&identity));
        }
        previous = Some(identity);
    }
    Ok(cells)
}

fn walk_files(
    root: &Path,
    relative_dir: &str,
    matches: fn(&str) -> bool,
    recursive: bool,
) -> Result<Vec<String>> {
    let dir = root.join(relative_dir);
    if !dir.exists() {
        return Ok(Vec::new());
    }
    if !dir.is_dir() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("{} is not a directory", dir.display()),
        ));
    }
    let mut files = Vec::new();
    walk_files_from(root, &dir, matches, recursive, &mut files)?;
    files.sort();
    files.dedup();
    Ok(files)
}

fn walk_files_from(
    root: &Path,
    dir: &Path,
    matches: fn(&str) -> bool,
    recursive: bool,
    files: &mut Vec<String>,
) -> Result<()> {
    let mut entries = fs::read_dir(dir)
        .map_err(|error| io_error(dir, &error))?
        .collect::<std::io::Result<Vec<_>>>()
        .map_err(|error| io_error(dir, &error))?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let file_type = entry.file_type().map_err(|error| io_error(&path, &error))?;
        if file_type.is_symlink() {
            continue;
        }
        if file_type.is_dir() {
            if recursive {
                walk_files_from(root, &path, matches, recursive, files)?;
            }
            continue;
        }
        if !file_type.is_file() {
            continue;
        }
        let relative = relative_posix(root, &path)?;
        if matches(&relative) {
            files.push(relative);
        }
    }
    Ok(())
}

fn relative_posix(root: &Path, path: &Path) -> Result<String> {
    let relative = path.strip_prefix(root).map_err(|_| {
        VerificationError::new(
            ErrorCode::Schema,
            format!("{} escapes source root {}", path.display(), root.display()),
        )
    })?;
    let mut parts = Vec::new();
    for component in relative.components() {
        match component {
            Component::Normal(part) => {
                let part = part.to_str().ok_or_else(|| {
                    VerificationError::new(
                        ErrorCode::Schema,
                        format!("{} is not valid UTF-8", path.display()),
                    )
                })?;
                parts.push(part);
            }
            _ => {
                return Err(VerificationError::new(
                    ErrorCode::Schema,
                    format!("{} is not a clean relative path", path.display()),
                ));
            }
        }
    }
    Ok(parts.join("/"))
}

fn read_text(path: &Path) -> Result<String> {
    let bytes = fs::read(path).map_err(|error| io_error(path, &error))?;
    // One decoding contract with suite verification: odd trailing bytes pad
    // and malformed units decode lossily (see decode_case_source), so catalog
    // extract and regenerate accept exactly what the suite accepts.
    Ok(crate::suite::decode_case_source(&bytes))
}

fn is_ts_source(path: &str) -> bool {
    path.ends_with(".ts") || path.ends_with(".tsx")
}

fn is_ts_file(path: &str) -> bool {
    matches!(path, p if p.to_ascii_lowercase().ends_with(".ts"))
}

fn is_json_file(path: &str) -> bool {
    path.ends_with(".json")
}

fn is_js_file(path: &str) -> bool {
    path.ends_with(".js")
}

fn is_transpile_file(path: &str) -> bool {
    extension(path).is_some_and(|ext| {
        matches!(
            ext,
            "ts" | "tsx"
                | "js"
                | "jsx"
                | "mts"
                | "cts"
                | "mjs"
                | "cjs"
                | "mtsx"
                | "ctsx"
                | "mjsx"
                | "cjsx"
        )
    })
}

fn extension(path: &str) -> Option<&str> {
    path.rsplit('/')
        .next()?
        .rsplit_once('.')
        .map(|(_, ext)| ext)
}

fn path_file_name(path: &str) -> Option<&str> {
    path.rsplit('/').next()
}

fn is_test262_fixture(path: &str) -> bool {
    path_file_name(path).is_some_and(|name| name.contains("_FIXTURE") && name.ends_with(".js"))
}

fn validate_identity_part(field: &str, value: &str) -> Result<()> {
    if value.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("{field} must be nonempty"),
        ));
    }
    if value.contains(IDENTITY_SEPARATOR) || value.contains('\\') {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("{field} `{value}` contains a forbidden identity character"),
        ));
    }
    Ok(())
}

fn validate_case_path(path: &str) -> Result<()> {
    validate_identity_part("case", path)?;
    if path.starts_with('/') {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("case `{path}` is absolute"),
        ));
    }
    if path.split('/').any(|segment| {
        segment.is_empty() || segment == "." || segment == ".." || segment.contains('\\')
    }) {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("case `{path}` has a forbidden path segment"),
        ));
    }
    Ok(())
}

fn duplicate_identity(identity: &str) -> VerificationError {
    VerificationError::new(
        ErrorCode::Duplicate,
        format!("duplicate catalog identity `{identity}`"),
    )
}

fn io_error(path: &Path, error: &std::io::Error) -> VerificationError {
    VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        path::{Path, PathBuf},
        sync::atomic::{AtomicU64, Ordering},
    };

    static COUNTER: AtomicU64 = AtomicU64::new(0);

    fn scratch(tag: &str) -> PathBuf {
        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!(
            "bamts-catalog-{tag}-{}-{unique}",
            std::process::id()
        ));
        fs::create_dir_all(&dir).expect("create scratch dir");
        dir
    }

    fn write_file(root: &Path, relative: &str, contents: &str) {
        let path = root.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("create parent");
        }
        fs::write(path, contents).expect("write fixture");
    }

    fn typescript_fixture() -> PathBuf {
        let root = scratch("ts");
        write_file(
            &root,
            "tests/cases/compiler/simple.ts",
            "export const value = 1;\n",
        );
        write_file(
            &root,
            "tests/cases/compiler/multi.ts",
            "// @filename: a.ts\nexport const a = 1;\n// @filename: b.ts\nimport { a } from \"./a\";\nexport const b = a;\n",
        );
        write_file(
            &root,
            "tests/cases/compiler/repeat.ts",
            "// @target: es5, es2015\nexport const value = 1;\n",
        );
        write_file(
            &root,
            "tests/cases/compiler/observables.ts",
            "// @declaration: true\n// @sourceMap: true\nexport const value = 1;\n",
        );
        write_file(
            &root,
            "tests/cases/conformance/types/alias.ts",
            "type Alias = number;\nexport type T = Alias;\n",
        );
        write_file(
            &root,
            "tests/cases/project/basic.json",
            r#"{"scenario":"basic","projectRoot":"tests/cases/projects/basic","inputFiles":["main.ts"]}"#,
        );
        write_file(
            &root,
            "tests/cases/transpile/emit.ts",
            "// @sourceMap: true,false\nexport const value = 1;\n",
        );
        write_file(&root, "tests/cases/fourslash/fourslash.ts", "export {};\n");
        write_file(
            &root,
            "tests/cases/fourslash/publicCompletions.ts",
            "/// <reference path=\"fourslash.ts\" />\n//// const value = { field: 1 };\n//// value./*1*/\n\ngoTo.marker(\"1\");\nverify.completions({ marker: \"1\", includes: \"field\" });\n",
        );
        write_file(
            &root,
            "tests/cases/fourslash/internalRefactor.ts",
            "/// <reference path=\"fourslash.ts\" />\n//// function /*a*/fn/*b*/() { return 1; }\n\ngoTo.select(\"a\", \"b\");\nedit.applyRefactor({ refactorName: \"Infer function return type\", actionName: \"Infer function return type\" });\n",
        );
        write_file(
            &root,
            "tests/cases/fourslash/server/serverCompletions.ts",
            "/// <reference path=\"../fourslash.ts\" />\n//// const value = { field: 1 };\n//// value./*1*/\n\nverify.completions({ marker: \"1\", includes: \"field\" });\n",
        );
        root
    }

    fn test262_fixture() -> PathBuf {
        let root = scratch("test262");
        write_file(&root, "test/language/types/boolean.js", "void 0;\n");
        write_file(&root, "test/built-ins/Array/from.js", "void 0;\n");
        write_file(&root, "test/intl402/Collator/constructor.js", "void 0;\n");
        write_file(&root, "test/annexB/built-ins/escape.js", "void 0;\n");
        write_file(&root, "test/staging/proposal.js", "void 0;\n");
        write_file(&root, "test/harness/assert.js", "void 0;\n");
        write_file(&root, "test/language/types/boolean_FIXTURE.js", "void 0;\n");
        root
    }

    fn identities(cells: &[CatalogCell]) -> Vec<String> {
        cells.iter().map(CatalogCell::rendered_identity).collect()
    }

    fn cells_for<'a>(cells: &'a [CatalogCell], case: &str) -> Vec<&'a CatalogCell> {
        cells.iter().filter(|cell| cell.case == case).collect()
    }

    #[test]
    fn typescript_cells_are_logical_obligations() {
        let root = typescript_fixture();
        let cells = extract_typescript_cells(&root, "typescript-7.0.2").unwrap();
        assert!(!cells.is_empty());
        for cell in &cells {
            let identity = cell.rendered_identity();
            assert!(
                identity.matches('#').count() == 2,
                "{identity} must be a logical obligation, not a source path"
            );
            assert_ne!(identity, cell.case);
            assert!(!identity.ends_with(&cell.case));
        }

        let multi = cells_for(&cells, "tests/cases/compiler/multi.ts");
        assert!(!multi.is_empty());
        assert!(
            multi
                .iter()
                .all(|cell| cell.case == "tests/cases/compiler/multi.ts"),
            "multi-file fixtures stay atomic"
        );
        let parsed = parse_case_configuration(
            "// @filename: a.ts\nexport const a = 1;\n// @filename: b.ts\nimport { a } from \"./a\";\n",
        )
        .unwrap();
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].virtual_files, ["a.ts", "b.ts"]);
        assert_eq!(parsed[0].name, DEFAULT_CONFIGURATION);

        let repeat =
            parse_case_configuration("// @target: es5, es2015\nexport const value = 1;\n").unwrap();
        assert_eq!(repeat.len(), 2);
        assert_eq!(repeat[0].name, "target=es2015");
        assert_eq!(repeat[1].name, "target=es5");
        let repeat_cells = cells_for(&cells, "tests/cases/compiler/repeat.ts");
        let configs: BTreeSet<_> = repeat_cells
            .iter()
            .map(|cell| cell.configuration.as_str())
            .collect();
        assert_eq!(configs, BTreeSet::from(["target=es5", "target=es2015"]));

        let observables = cells_for(&cells, "tests/cases/compiler/observables.ts");
        let kinds: BTreeSet<_> = observables.iter().map(|cell| cell.observable).collect();
        assert!(kinds.contains(&ObservableKind::Diagnostics));
        assert!(kinds.contains(&ObservableKind::Declaration));
        assert!(kinds.contains(&ObservableKind::SourceMap));
        assert!(kinds.contains(&ObservableKind::JavaScript));
        assert!(kinds.len() > 1);
    }

    #[test]
    fn typescript_catalog_is_deterministic() {
        let root = typescript_fixture();
        let first = extract_typescript_cells(&root, "typescript-7.0.2").unwrap();
        let second = extract_typescript_cells(&root, "typescript-7.0.2").unwrap();
        assert_eq!(first, second);
        assert_eq!(
            catalog_sha256(&first).unwrap(),
            catalog_sha256(&second).unwrap()
        );
        let mut rendered = identities(&first);
        rendered.sort();
        rendered.dedup();
        assert_eq!(rendered.len(), first.len());

        let path = root.join("catalog.json");
        write_catalog_json(fs::File::create(&path).unwrap(), "typescript-7.0.2", &first).unwrap();
        check_catalog_json(&path, "typescript-7.0.2", &first).unwrap();
        write_catalog_json(fs::File::create(&path).unwrap(), "typescript-7.0.2", &first).unwrap();
        let first_bytes = fs::read(&path).unwrap();
        write_catalog_json(
            fs::File::create(&path).unwrap(),
            "typescript-7.0.2",
            &second,
        )
        .unwrap();
        assert_eq!(first_bytes, fs::read(&path).unwrap());
    }

    #[test]
    fn source_mutation_invalidates_catalog() {
        let root = typescript_fixture();
        let original = extract_typescript_cells(&root, "typescript-7.0.2").unwrap();
        let original_sha = catalog_sha256(&original).unwrap();
        let path = root.join("catalog.json");
        write_catalog_json(
            fs::File::create(&path).unwrap(),
            "typescript-7.0.2",
            &original,
        )
        .unwrap();

        write_file(
            &root,
            "tests/cases/compiler/added.ts",
            "export const added = 1;\n",
        );
        let added = extract_typescript_cells(&root, "typescript-7.0.2").unwrap();
        assert_ne!(catalog_sha256(&added).unwrap(), original_sha);
        assert_eq!(
            check_catalog_json(&path, "typescript-7.0.2", &added)
                .unwrap_err()
                .code(),
            ErrorCode::Digest
        );

        fs::remove_file(root.join("tests/cases/compiler/added.ts")).unwrap();
        fs::remove_file(root.join("tests/cases/compiler/simple.ts")).unwrap();
        let removed = extract_typescript_cells(&root, "typescript-7.0.2").unwrap();
        assert_ne!(catalog_sha256(&removed).unwrap(), original_sha);
        assert!(cells_for(&removed, "tests/cases/compiler/simple.ts").is_empty());

        write_file(
            &root,
            "tests/cases/compiler/simple.ts",
            "export const value = 1;\n",
        );
        fs::rename(
            root.join("tests/cases/compiler/simple.ts"),
            root.join("tests/cases/compiler/renamed.ts"),
        )
        .unwrap();
        let renamed = extract_typescript_cells(&root, "typescript-7.0.2").unwrap();
        assert!(cells_for(&renamed, "tests/cases/compiler/simple.ts").is_empty());
        assert!(!cells_for(&renamed, "tests/cases/compiler/renamed.ts").is_empty());
        assert_ne!(catalog_sha256(&renamed).unwrap(), original_sha);
    }

    #[test]
    fn classifies_fourslash_by_public_reachability() {
        let root = typescript_fixture();
        let cells = extract_typescript_cells(&root, "typescript-7.0.2").unwrap();

        let public_cells = cells_for(&cells, "tests/cases/fourslash/publicCompletions.ts");
        assert!(!public_cells.is_empty());
        assert!(public_cells.iter().any(|cell| cell.public_surface
            == PublicSurface::LanguageServiceApi
            && cell.observable == ObservableKind::Types));
        assert!(
            public_cells
                .iter()
                .all(|cell| cell.public_surface != PublicSurface::InternalHarness)
        );

        let internal_cells = cells_for(&cells, "tests/cases/fourslash/internalRefactor.ts");
        assert_eq!(internal_cells.len(), 1);
        assert_eq!(
            internal_cells[0].public_surface,
            PublicSurface::InternalHarness
        );
        assert_eq!(internal_cells[0].observable, ObservableKind::Parse);

        let server_cells = cells_for(&cells, "tests/cases/fourslash/server/serverCompletions.ts");
        assert!(
            server_cells
                .iter()
                .any(|cell| cell.public_surface == PublicSurface::LanguageServiceApi)
        );
        assert!(
            cells_for(&cells, "tests/cases/fourslash/fourslash.ts").is_empty(),
            "harness DSL file itself is excluded"
        );
    }

    #[test]
    fn test262_scope_matches_policy() {
        let root = test262_fixture();
        let cells = extract_test262_cells(&root, "test262").unwrap();
        let cases: BTreeSet<_> = cells.iter().map(|cell| cell.case.as_str()).collect();
        assert!(cases.contains("test/language/types/boolean.js"));
        assert!(cases.contains("test/built-ins/Array/from.js"));
        assert!(cases.contains("test/intl402/Collator/constructor.js"));
        assert!(cases.contains("test/annexB/built-ins/escape.js"));
        assert!(cases.contains("test/staging/proposal.js"));
        assert!(!cases.contains("test/harness/assert.js"));
        assert!(!cases.contains("test/language/types/boolean_FIXTURE.js"));

        for cell in &cells {
            assert_eq!(cell.runner, RunnerKind::Test262);
            assert_eq!(cell.observable, ObservableKind::Runtime);
            if cell.case.starts_with("test/staging/") {
                assert_eq!(cell.public_surface, PublicSurface::ProposalStage);
            } else {
                assert_eq!(cell.public_surface, PublicSurface::Runtime);
            }
        }
    }

    #[test]
    fn unknown_directive_is_rejected() {
        let error = parse_case_configuration("// @notARealFlag: true\nexport {};\n").unwrap_err();
        assert_eq!(error.code(), ErrorCode::Schema);
        assert!(error.to_string().contains("notarealflag"));

        let root = scratch("unknown");
        write_file(
            &root,
            "tests/cases/compiler/unknown.ts",
            "// @notARealFlag: true\nexport {};\n",
        );
        assert_eq!(
            extract_typescript_cells(&root, "typescript-7.0.2")
                .unwrap_err()
                .code(),
            ErrorCode::Schema
        );
    }

    #[test]
    fn duplicate_virtual_file_boundaries_are_preserved() {
        let configurations = parse_case_configuration(
            "// @filename: a.ts\nexport const a = 1;\n// @filename: a.ts\nexport const b = 2;\n",
        )
        .unwrap();
        assert_eq!(configurations[0].virtual_files, ["a.ts", "a.ts"]);
    }

    #[test]
    fn hash_is_newline_delimited_identities() {
        let root = typescript_fixture();
        let cells = extract_typescript_cells(&root, "typescript-7.0.2").unwrap();
        let mut hasher = Sha256::new();
        for cell in &cells {
            hasher.update(cell.rendered_identity().as_bytes());
            hasher.update(b"\n");
        }
        assert_eq!(
            catalog_sha256(&cells).unwrap(),
            format!("{:x}", hasher.finalize())
        );
    }
    #[test]
    fn manifest_regeneration_is_idempotent() {
        let root = scratch("manifest-idempotent");
        let path = root.join("manifest.lock.json");
        let expected = b"{\"schema\":\"fixture\"}\n";
        replace_file_atomically(&path, expected).unwrap();
        let first = fs::read(&path).unwrap();
        replace_file_atomically(&path, expected).unwrap();
        assert_eq!(fs::read(&path).unwrap(), first);
    }

    #[test]
    fn rejects_stale_generated_manifest() {
        let root = scratch("manifest-stale");
        let path = root.join("manifest.lock.json");
        fs::write(&path, b"stale\n").unwrap();
        let error = check_generated_manifest(&path, b"generated\n").unwrap_err();
        assert_eq!(error.code(), ErrorCode::Digest);
        assert!(error.to_string().contains("catalog regenerate"));
    }

    /// Catalog extraction must accept exactly what suite verification
    /// accepts: odd trailing bytes pad and malformed units decode lossily
    /// through the shared contract instead of failing strict.
    #[test]
    fn read_text_shares_suite_lossy_decoding_contract() {
        let root = scratch("decode-contract");
        // Odd trailing byte: strict UTF-16 rejects, the suite pads lossy.
        let odd = [0xFF, 0xFE, b'h', b'i', 0x00];
        fs::write(root.join("odd.ts"), odd).expect("write odd fixture");
        // Lone surrogate: strict from_utf16 rejects, the suite emits U+FFFD.
        let lone = [0xFF, 0xFE, 0x00, 0xD8, b'x', 0x00];
        fs::write(root.join("lone.ts"), lone).expect("write lone fixture");
        let odd_text = read_text(&root.join("odd.ts")).expect("odd bytes must decode");
        assert_eq!(odd_text, crate::suite::decode_case_source(&odd));
        let lone_text = read_text(&root.join("lone.ts")).expect("lone surrogate must decode");
        assert_eq!(lone_text, crate::suite::decode_case_source(&lone));
        assert!(
            lone_text.contains('\u{FFFD}'),
            "lossy unit must surface: {lone_text:?}"
        );
    }
}
