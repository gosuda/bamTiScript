//! TypeScript 7.0.2 `tsc` argv surface and exit-status mapping.
//!
//! Parses the pinned native `tsc` command line (boolean `true`/`false`/`null`
//! consumption, short names, `--build` mode, response files, tsconfig-only
//! options) into existing bamts CLI driver types. Invalid argv fails with the
//! TypeScript diagnostic texts; this parser never silently drops tokens.

use std::collections::{BTreeMap, HashSet};
use std::fmt;
use std::fs;
use std::path::Path;

use bamts_compiler::checker::diagnostic_messages::{Args, by_u32};

use crate::args::{
    ArgsError, CliArgs, DiagnosticsFormat, ExecutionTarget, JsCompatMode, JsCompatOptions, Mode,
    OutputOptions,
};

/// TypeScript 7.0.2 `tsc` exit statuses (`internal/execute/tsc/compile.go`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(i32)]
pub enum TscExitStatus {
    Success = 0,
    DiagnosticsPresentOutputsSkipped = 1,
    DiagnosticsPresentOutputsGenerated = 2,
    InvalidProjectOutputsSkipped = 3,
    ProjectReferenceCycleOutputsSkipped = 4,
    NotImplemented = 5,
}

impl TscExitStatus {
    #[must_use]
    pub const fn code(self) -> i32 {
        self as i32
    }

    /// Maps a completed compilation onto the TypeScript 7.0.2 exit vector.
    #[must_use]
    pub const fn from_compilation(has_errors: bool, outputs_generated: bool) -> Self {
        if !has_errors {
            Self::Success
        } else if outputs_generated {
            Self::DiagnosticsPresentOutputsGenerated
        } else {
            Self::DiagnosticsPresentOutputsSkipped
        }
    }
}

impl From<TscExitStatus> for i32 {
    fn from(status: TscExitStatus) -> Self {
        status.code()
    }
}

/// One collected command-line diagnostic. Codes match TypeScript 7.0.2.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TscArgError {
    pub code: u32,
    pub message: String,
}

impl TscArgError {
    #[must_use]
    pub fn new(code: u32, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
        }
    }

    #[must_use]
    pub fn pretty_false_line(&self) -> String {
        format!("error TS{}: {}", self.code, self.message)
    }
}

impl fmt::Display for TscArgError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.pretty_false_line())
    }
}

impl std::error::Error for TscArgError {}

/// All argv failures from one parse. Empty never constructs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TscArgErrors {
    errors: Vec<TscArgError>,
}

impl TscArgErrors {
    fn new(errors: Vec<TscArgError>) -> Self {
        debug_assert!(!errors.is_empty());
        Self { errors }
    }

    #[must_use]
    pub fn errors(&self) -> &[TscArgError] {
        &self.errors
    }

    #[must_use]
    pub fn exit_status(&self) -> TscExitStatus {
        if self.errors.iter().any(|error| error.code == 5108) {
            TscExitStatus::DiagnosticsPresentOutputsGenerated
        } else {
            TscExitStatus::DiagnosticsPresentOutputsSkipped
        }
    }

    #[must_use]
    pub fn pretty_false(&self) -> String {
        let mut out = String::new();
        for error in &self.errors {
            out.push_str(&error.pretty_false_line());
            out.push('\n');
        }
        out
    }
}

impl fmt::Display for TscArgErrors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.pretty_false())
    }
}

impl std::error::Error for TscArgErrors {}

/// A parsed compiler-option value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TscOptionValue {
    Bool(bool),
    String(String),
    Number(i32),
    List(Vec<String>),
    Null,
}

impl TscOptionValue {
    #[must_use]
    pub const fn as_bool(&self) -> Option<bool> {
        match *self {
            Self::Bool(value) => Some(value),
            Self::Null => None,
            Self::String(_) | Self::Number(_) | Self::List(_) => None,
        }
    }

    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::String(value) => Some(value),
            Self::Bool(_) | Self::Number(_) | Self::List(_) | Self::Null => None,
        }
    }

    #[must_use]
    pub fn as_list(&self) -> Option<&[String]> {
        match self {
            Self::List(values) => Some(values),
            Self::Bool(_) | Self::String(_) | Self::Number(_) | Self::Null => None,
        }
    }
}

/// One successful TypeScript 7.0.2 command-line parse.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedTscCommand {
    /// Positional file names, in argv order. Empty when `-p` / tsconfig drives input.
    pub file_names: Vec<String>,
    /// Parsed options keyed by canonical long name (`pretty`, `noEmit`, …).
    pub options: BTreeMap<String, TscOptionValue>,
    /// First argv token selected `--build` / `-b`.
    pub is_build: bool,
}

impl ParsedTscCommand {
    #[must_use]
    pub fn flag(&self, name: &str) -> bool {
        matches!(self.options.get(name), Some(TscOptionValue::Bool(true)))
    }

    #[must_use]
    pub fn option_str(&self, name: &str) -> Option<&str> {
        self.options.get(name).and_then(TscOptionValue::as_str)
    }

    /// `--pretty false` is the canonical test/CI text. Unspecified maps to that
    /// non-TTY default so baselines stay byte-stable.
    #[must_use]
    pub fn pretty(&self) -> bool {
        match self.options.get("pretty") {
            Some(TscOptionValue::Bool(value)) => *value,
            Some(
                TscOptionValue::Null
                | TscOptionValue::String(_)
                | TscOptionValue::Number(_)
                | TscOptionValue::List(_),
            )
            | None => false,
        }
    }

    #[must_use]
    pub fn diagnostics_format(&self) -> DiagnosticsFormat {
        if self.pretty() {
            DiagnosticsFormat::Pretty
        } else {
            DiagnosticsFormat::Text
        }
    }

    /// Maps onto the existing driver [`CliArgs`] without silently capping diagnostics.
    #[must_use]
    pub fn to_cli_args(&self) -> CliArgs {
        let allow_js = self.flag("allowJs");
        let check_js = self.flag("checkJs");
        let jsx_preserve = matches!(self.option_str("jsx"), Some("preserve"));
        let mut extra_inputs = self.file_names.clone();
        let entrypoint = if extra_inputs.is_empty() {
            None
        } else {
            Some(extra_inputs.remove(0))
        };
        CliArgs {
            mode: if self.flag("noEmit") {
                Mode::Check
            } else {
                Mode::Compile
            },
            target: ExecutionTarget::Aot,
            entrypoint,
            extra_inputs,
            program_args: Vec::new(),
            js_compat: JsCompatOptions {
                enabled: allow_js || check_js || jsx_preserve,
                mode: JsCompatMode::Standard,
                allow_js,
                check_js,
                jsx_preserve,
            },
            output: OutputOptions {
                file: self
                    .option_str("outFile")
                    .or_else(|| self.option_str("out"))
                    .map(str::to_owned),
                dir: self.option_str("outDir").map(str::to_owned),
                emit_declarations: self.flag("declaration"),
                source_maps: self.flag("sourceMap"),
            },
            diagnostics_format: self.diagnostics_format(),
            lint_overrides: Vec::new(),
            strict: self.flag("strict"),
            pedantic: false,
            // Never silently drop diagnostics: the historical 50-line cap hid hard errors.
            error_limit: usize::MAX,
            explain_rule: None,
            help: self.flag("help"),
            version: self.flag("version"),
        }
    }

    /// `-p` / `--project`. Not folded into [`CliArgs::entrypoint`]: that field
    /// is a source file. The driver must read this separately.
    #[must_use]
    pub fn project(&self) -> Option<&str> {
        self.option_str("project")
    }

    /// Exit status for a parse that already succeeded. Compilation diagnostics
    /// are applied later via [`TscExitStatus::from_compilation`].
    #[must_use]
    pub const fn parse_exit_status(&self) -> TscExitStatus {
        TscExitStatus::Success
    }

    /// First parsed option the dispatch mode cannot consume, in stable
    /// (alphabetical) option order. Every parse-table entry classifies in
    /// every mode, so an accepted option can never silently disappear: the
    /// driver turns `Some` into the stable TS5047 not-implemented failure
    /// before loading or executing anything.
    #[must_use]
    pub fn first_unsupported_option(&self, mode: TscDispatchMode) -> Option<&str> {
        self.options
            .keys()
            .find(|name| classify_option(name, mode) == ModeOptionClassification::Unsupported)
            .map(String::as_str)
    }
}

/// The dispatch mode whose option surface classifies a parsed command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TscDispatchMode {
    /// Explicit source files compiled by the native driver.
    Direct,
    /// `-p` / `--project` / tsconfig-discovery project compilation.
    Project,
    /// `--build` reference-closure compilation.
    Build,
}

/// How one dispatch mode consumes a parsed compiler option.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModeOptionClassification {
    /// The mode reads the option: a dispatch control or a native
    /// `ProjectOptionOverrides` / `ProjectBuildOptions` mapping.
    Consumed,
    /// The mode has no canonical native mapping. The driver must fail
    /// closed with the stable TS5047 diagnostic instead of ignoring the
    /// option.
    Unsupported,
}

/// Options `Direct` dispatch consumes. `project` and `init` classify as
/// consumed because dispatch routes them before classification runs
/// (`--init` initializes the config, `-p` selects project mode); listing
/// them keeps classification total over the parse table. `showConfig`
/// prints the effective configuration instead of compiling; direct
/// dispatch routes it after ordinary argument validation.
///
/// The set is every `CompilerOptions` field the project layer carries
/// (typed struct field or raw `compilerOptions` key forwarded through
/// `ProjectOptionOverrides`) plus the dispatch controls. An option the
/// parser admits but the project pipeline cannot carry stays
/// `Unsupported` so the driver fails closed with TS5047.
const DIRECT_CONSUMED: &[&str] = &[
    "allowJs",
    "alwaysStrict",
    "baseUrl",
    "checkJs",
    "composite",
    "declaration",
    "declarationDir",
    "declarationMap",
    "emitDeclarationOnly",
    "esModuleInterop",
    "help",
    "ignoreConfig",
    "importHelpers",
    "incremental",
    "init",
    "inlineSourceMap",
    "inlineSources",
    "isolatedModules",
    "jsx",
    "jsxFactory",
    "jsxFragmentFactory",
    "jsxImportSource",
    "lib",
    "mapRoot",
    "module",
    "moduleDetection",
    "moduleResolution",
    "newLine",
    "noEmit",
    "noEmitOnError",
    "noImplicitAny",
    "out",
    "outDir",
    "outFile",
    "pretty",
    "project",
    "resolveJsonModule",
    "rootDir",
    "showConfig",
    "sourceMap",
    "sourceRoot",
    "strict",
    "strictNullChecks",
    "strictPropertyInitialization",
    "target",
    "traceResolution",
    "tsBuildInfoFile",
    "verbatimModuleSyntax",
    "version",
];

/// Options `Project` dispatch consumes: the dispatch controls plus every
/// `ProjectOptionOverrides` mapping the driver forwards into project
/// loading. `ignoreConfig` is deliberately absent: it only guards the
/// direct files-plus-config conflict, which project dispatch never
/// reaches, so project mode rejects it. `showConfig` prints the effective
/// merged configuration instead of compiling; project dispatch routes it
/// after `EffectiveProject::load`. The compiler-option surface mirrors
/// [`DIRECT_CONSUMED`] so argv and tsconfig route through one option set.
const PROJECT_CONSUMED: &[&str] = &[
    "allowJs",
    "alwaysStrict",
    "baseUrl",
    "checkJs",
    "composite",
    "declaration",
    "declarationDir",
    "declarationMap",
    "emitDeclarationOnly",
    "esModuleInterop",
    "help",
    "importHelpers",
    "incremental",
    "init",
    "inlineSourceMap",
    "inlineSources",
    "isolatedModules",
    "jsx",
    "jsxFactory",
    "jsxFragmentFactory",
    "jsxImportSource",
    "lib",
    "listFiles",
    "listFilesOnly",
    "mapRoot",
    "module",
    "moduleDetection",
    "moduleResolution",
    "newLine",
    "noEmit",
    "noEmitOnError",
    "noImplicitAny",
    "out",
    "outDir",
    "outFile",
    "pretty",
    "project",
    "resolveJsonModule",
    "rootDir",
    "showConfig",
    "sourceMap",
    "sourceRoot",
    "strict",
    "strictNullChecks",
    "strictPropertyInitialization",
    "target",
    "traceResolution",
    "tsBuildInfoFile",
    "verbatimModuleSyntax",
    "version",
];

/// Options `Build` dispatch consumes: the build controls plus the dispatch
/// commands and `pretty` outcome formatting. `verbose` reports per-project
/// build status; `dry`, `force`, `clean`, and `stopBuildOnErrors` drive the
/// reference-closure build. Common emit and watch options have no build
/// mapping and are rejected.
const BUILD_CONSUMED: &[&str] = &[
    "build",
    "clean",
    "dry",
    "force",
    "help",
    "pretty",
    "stopBuildOnErrors",
    "verbose",
    "version",
];

/// Classifies one canonical option name for a dispatch mode. Names outside
/// the mode's consumed set — including options the parser only admits in
/// other modes — classify as unsupported so the driver fails closed.
/// Consumed sets stay ASCII-sorted for `binary_search`.
#[must_use]
pub fn classify_option(name: &str, mode: TscDispatchMode) -> ModeOptionClassification {
    let consumed = match mode {
        TscDispatchMode::Direct => DIRECT_CONSUMED,
        TscDispatchMode::Project => PROJECT_CONSUMED,
        TscDispatchMode::Build => BUILD_CONSUMED,
    };
    if consumed.binary_search(&name).is_ok() {
        ModeOptionClassification::Consumed
    } else {
        ModeOptionClassification::Unsupported
    }
}

/// Parse TypeScript 7.0.2 `tsc` argv. The first token is stripped when it is a
/// program name (`tsc`, `bamts`, `bamti`, or a path ending in those).
pub fn parse_tsc_args<I, S>(args: I) -> Result<ParsedTscCommand, TscArgErrors>
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    parse_tsc_args_with(args, |path| {
        fs::read_to_string(path).map_err(|error| error.to_string())
    })
}

/// Parse with an injected response-file reader. Production uses [`parse_tsc_args`].
pub fn parse_tsc_args_with<I, S, R>(
    args: I,
    mut read_response_file: R,
) -> Result<ParsedTscCommand, TscArgErrors>
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
    R: FnMut(&str) -> Result<String, String>,
{
    let mut tokens: Vec<String> = args.into_iter().map(|s| s.as_ref().to_owned()).collect();
    if tokens
        .first()
        .is_some_and(|first| is_program_name(first) && !first.starts_with('-'))
    {
        tokens.remove(0);
    }

    let is_build = tokens.first().is_some_and(|first| is_build_token(first));
    let mut parser = Parser {
        is_build,
        options: BTreeMap::new(),
        file_names: Vec::new(),
        errors: Vec::new(),
        response_stack: HashSet::new(),
        read_response_file: &mut read_response_file,
    };
    parser.parse_strings(&tokens);
    parser.finish()
}

fn is_program_name(token: &str) -> bool {
    let name = Path::new(token)
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or(token);
    matches!(name, "tsc" | "tsgo" | "bamts" | "bamti" | "bamts-cli")
}

fn is_build_token(token: &str) -> bool {
    matches!(
        token.to_ascii_lowercase().as_str(),
        "-b" | "--b" | "-build" | "--build"
    )
}

struct Parser<'a, R> {
    is_build: bool,
    options: BTreeMap<String, TscOptionValue>,
    file_names: Vec<String>,
    errors: Vec<TscArgError>,
    response_stack: HashSet<String>,
    read_response_file: &'a mut R,
}

impl<R> Parser<'_, R>
where
    R: FnMut(&str) -> Result<String, String>,
{
    fn parse_strings(&mut self, args: &[String]) {
        let mut index = 0;
        while index < args.len() {
            let token = &args[index];
            index += 1;
            if token.is_empty() {
                continue;
            }
            match token.as_bytes()[0] {
                b'@' => self.parse_response_file(&token[1..]),
                b'-' => {
                    let input_name = option_name(token);
                    match lookup_option(input_name, self.is_build) {
                        Some(spec) => {
                            index = self.parse_option_value(args, index, spec);
                        }
                        None => self.push_unknown(input_name, token),
                    }
                }
                _ => self.file_names.push(token.clone()),
            }
        }
    }

    fn parse_option_value(&mut self, args: &[String], mut index: usize, spec: OptionSpec) -> usize {
        if spec.tsconfig_only {
            let next = args.get(index).map(String::as_str).unwrap_or("");
            if next == "null" {
                self.options
                    .insert(spec.name.to_owned(), TscOptionValue::Null);
                return index + 1;
            }
            if spec.kind == OptionKind::Boolean && next == "false" {
                self.options
                    .insert(spec.name.to_owned(), TscOptionValue::Bool(false));
                return index + 1;
            }
            if spec.kind == OptionKind::Boolean {
                if next == "true" {
                    index += 1;
                }
                self.errors.push(TscArgError::new(
                    5093,
                    format!(
                        "Option '{name}' can only be specified in 'tsconfig.json' file or set to 'false' or 'null' on command line.",
                        name = spec.name
                    ),
                ));
                return index;
            }
            self.errors.push(TscArgError::new(
                6064,
                format!(
                    "Option '{name}' can only be specified in 'tsconfig.json' file or set to 'null' on command line.",
                    name = spec.name
                ),
            ));
            if !next.is_empty() && !next.starts_with('-') {
                index += 1;
            }
            return index;
        }

        if index >= args.len() {
            if spec.kind == OptionKind::Boolean {
                self.options
                    .insert(spec.name.to_owned(), TscOptionValue::Bool(true));
            } else {
                self.errors.push(type_mismatch(spec));
            }
            return index;
        }

        let value = args[index].as_str();
        if value == "null" {
            self.options
                .insert(spec.name.to_owned(), TscOptionValue::Null);
            return index + 1;
        }

        match spec.kind {
            OptionKind::Boolean => {
                if value == "false" {
                    self.options
                        .insert(spec.name.to_owned(), TscOptionValue::Bool(false));
                    index + 1
                } else if value == "true" {
                    self.options
                        .insert(spec.name.to_owned(), TscOptionValue::Bool(true));
                    index + 1
                } else {
                    self.options
                        .insert(spec.name.to_owned(), TscOptionValue::Bool(true));
                    index
                }
            }
            OptionKind::String => {
                self.options.insert(
                    spec.name.to_owned(),
                    TscOptionValue::String(value.to_owned()),
                );
                index + 1
            }
            OptionKind::Number => {
                match value.parse::<i32>() {
                    Ok(number) if number >= spec.min_value => {
                        self.options
                            .insert(spec.name.to_owned(), TscOptionValue::Number(number));
                    }
                    Ok(_) => self.errors.push(TscArgError::new(
                        5072,
                        format!(
                            "Option '{name}' requires a value greater than {min}.",
                            name = spec.name,
                            min = spec.min_value - 1
                        ),
                    )),
                    Err(_) => self.errors.push(type_mismatch(spec)),
                }
                index + 1
            }
            OptionKind::Enum => {
                // `target=ES3` was removed in TypeScript 7.0.2 (TS5108).
                // `target=ES5` is deprecated but still accepted (TS5107 is a
                // runtime warning, not a parse failure), so it parses cleanly
                // and is stored as the canonical lower-case spelling.
                if spec.name == "target" && value.eq_ignore_ascii_case("es3") {
                    self.errors.push(TscArgError::new(
                        5108,
                        by_u32(5108)
                            .expect("TS5108 is in the generated catalog")
                            .format(Args::new(["target", "ES3"]))
                            .expect("arity matches"),
                    ));
                } else if spec.name == "target" && value.eq_ignore_ascii_case("es5") {
                    self.options.insert(
                        spec.name.to_owned(),
                        TscOptionValue::String("es5".to_owned()),
                    );
                } else if let Some(canonical) = match_enum(value, spec.enum_values) {
                    self.options.insert(
                        spec.name.to_owned(),
                        TscOptionValue::String(canonical.to_owned()),
                    );
                } else {
                    self.errors.push(invalid_enum(spec, value));
                }
                index + 1
            }
            OptionKind::List => {
                if value.starts_with('-') {
                    self.errors.push(type_mismatch(spec));
                    return index;
                }
                let (items, errors) = parse_list(spec, value);
                self.errors.extend(errors);
                self.options
                    .insert(spec.name.to_owned(), TscOptionValue::List(items));
                index + 1
            }
        }
    }

    fn parse_response_file(&mut self, file_name: &str) {
        if !self.response_stack.insert(file_name.to_owned()) {
            return;
        }
        match (self.read_response_file)(file_name) {
            Ok(contents) => match split_response_file(&contents, file_name) {
                Ok(nested) => self.parse_strings(&nested),
                Err(error) => self.errors.push(error),
            },
            Err(_) => self.errors.push(TscArgError::new(
                5012,
                format!("Cannot read file '{file_name}'."),
            )),
        }
        self.response_stack.remove(file_name);
    }

    fn push_unknown(&mut self, input_name: &str, original: &str) {
        // `--build` is a mode switch (first token only), not a late compiler option.
        if let Some(other) = lookup_option(input_name, !self.is_build)
            && other.name != "build"
        {
            let (code, message) = if self.is_build {
                (
                    6387,
                    format!(
                        "Compiler option '{name}' may not be used with '--build'.",
                        name = other.name
                    ),
                )
            } else {
                (
                    6388,
                    format!(
                        "Compiler option '{name}' may only be used with '--build'.",
                        name = other.name
                    ),
                )
            };
            self.errors.push(TscArgError::new(code, message));
            return;
        }
        if let Some(suggestion) = did_you_mean(input_name, self.is_build) {
            self.errors.push(TscArgError::new(
                5025,
                by_u32(5025)
                    .expect("TS5025 is in the generated catalog")
                    .format(Args::new([original, suggestion]))
                    .expect("arity matches"),
            ));
        } else {
            self.errors.push(TscArgError::new(
                5023,
                by_u32(5023)
                    .expect("TS5023 is in the generated catalog")
                    .format(Args::new([original]))
                    .expect("arity matches"),
            ));
        }
    }

    fn finish(self) -> Result<ParsedTscCommand, TscArgErrors> {
        let mut errors = self.errors;
        let command = ParsedTscCommand {
            file_names: self.file_names,
            options: self.options,
            is_build: self.is_build,
        };
        if command.flag("init") && !command.is_build {
            return Ok(command);
        }
        if command.flag("watch") && command.flag("listFilesOnly") {
            errors.push(TscArgError::new(
                6370,
                "Options 'watch' and 'listFilesOnly' cannot be combined.".to_owned(),
            ));
        }
        if command.option_str("project").is_some() && !command.file_names.is_empty() {
            errors.push(TscArgError::new(
                5042,
                "Option 'project' cannot be mixed with source files on a command line.".to_owned(),
            ));
        }
        if command.is_build {
            let clean = command.flag("clean");
            if clean && command.flag("force") {
                errors.push(TscArgError::new(
                    6370,
                    "Options 'clean' and 'force' cannot be combined.".to_owned(),
                ));
            }
            if clean && command.flag("verbose") {
                errors.push(TscArgError::new(
                    6370,
                    "Options 'clean' and 'verbose' cannot be combined.".to_owned(),
                ));
            }
            if clean && command.flag("watch") {
                errors.push(TscArgError::new(
                    6370,
                    "Options 'clean' and 'watch' cannot be combined.".to_owned(),
                ));
            }
            if command.flag("watch") && command.flag("dry") {
                errors.push(TscArgError::new(
                    6370,
                    "Options 'watch' and 'dry' cannot be combined.".to_owned(),
                ));
            }
        }
        if errors.is_empty() {
            Ok(command)
        } else {
            Err(TscArgErrors::new(errors))
        }
    }
}

fn type_mismatch(spec: OptionSpec) -> TscArgError {
    TscArgError::new(
        6044,
        format!(
            "Compiler option '{name}' expects an argument.",
            name = spec.name
        ),
    )
}

fn option_name(token: &str) -> &str {
    token.trim_start_matches('-')
}

fn split_response_file(contents: &str, file_name: &str) -> Result<Vec<String>, TscArgError> {
    let mut args = Vec::new();
    let chars: Vec<char> = contents.chars().collect();
    let mut pos = 0;
    while pos < chars.len() {
        while pos < chars.len() && (chars[pos] as u32) <= b' ' as u32 {
            pos += 1;
        }
        if pos >= chars.len() {
            break;
        }
        if chars[pos] == '"' {
            pos += 1;
            let start = pos;
            while pos < chars.len() && chars[pos] != '"' {
                pos += 1;
            }
            if pos < chars.len() {
                args.push(chars[start..pos].iter().collect());
                pos += 1;
            } else {
                return Err(TscArgError::new(
                    5004,
                    format!("Unterminated quoted string in response file '{file_name}'."),
                ));
            }
        } else {
            let start = pos;
            while pos < chars.len() && (chars[pos] as u32) > b' ' as u32 {
                pos += 1;
            }
            args.push(chars[start..pos].iter().collect());
        }
    }
    Ok(args)
}

fn parse_list(spec: OptionSpec, value: &str) -> (Vec<String>, Vec<TscArgError>) {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        return (Vec::new(), Vec::new());
    }
    let mut items = Vec::new();
    let mut errors = Vec::new();
    for part in trimmed.split(',') {
        let item = part.trim();
        if item.is_empty() {
            continue;
        }
        if spec.enum_values.is_empty() {
            items.push(item.to_owned());
            continue;
        }
        match match_enum(item, spec.enum_values) {
            Some(canonical) => items.push(canonical.to_owned()),
            None => errors.push(invalid_enum(spec, item)),
        }
    }
    (items, errors)
}

fn match_enum<'a>(value: &str, allowed: &'a [&'a str]) -> Option<&'a str> {
    allowed
        .iter()
        .copied()
        .find(|candidate| candidate.eq_ignore_ascii_case(value))
}

fn invalid_enum(spec: OptionSpec, _value: &str) -> TscArgError {
    let expected = spec
        .enum_values
        .iter()
        .map(|item| format!("'{item}'"))
        .collect::<Vec<_>>()
        .join(", ");
    let flag = format!("--{}", spec.name);
    TscArgError::new(
        6046,
        by_u32(6046)
            .expect("TS6046 is in the generated catalog")
            .format(Args::new([&flag, &expected]))
            .expect("arity matches"),
    )
}

fn did_you_mean(input: &str, is_build: bool) -> Option<&'static str> {
    let needle = input.to_ascii_lowercase();
    let mut best: Option<(&'static str, usize)> = None;
    for spec in option_table(is_build) {
        let distance = edit_distance(&needle, &spec.name.to_ascii_lowercase());
        if distance == 0 || distance > 2 {
            continue;
        }
        match best {
            Some((_, current)) if current <= distance => {}
            _ => best = Some((spec.name, distance)),
        }
    }
    best.map(|(name, _)| name)
}

fn edit_distance(a: &str, b: &str) -> usize {
    let a_chars: Vec<char> = a.chars().collect();
    let b_chars: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b_chars.len()).collect();
    let mut current = vec![0; b_chars.len() + 1];
    for (i, a_ch) in a_chars.iter().enumerate() {
        current[0] = i + 1;
        for (j, b_ch) in b_chars.iter().enumerate() {
            let cost = usize::from(a_ch != b_ch);
            current[j + 1] = (prev[j + 1] + 1).min(current[j] + 1).min(prev[j] + cost);
        }
        std::mem::swap(&mut prev, &mut current);
    }
    prev[b_chars.len()]
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum OptionKind {
    Boolean,
    String,
    Number,
    Enum,
    List,
}

#[derive(Clone, Copy)]
struct OptionSpec {
    name: &'static str,
    short: Option<&'static str>,
    kind: OptionKind,
    tsconfig_only: bool,
    min_value: i32,
    enum_values: &'static [&'static str],
}

const fn flag(name: &'static str, short: Option<&'static str>) -> OptionSpec {
    OptionSpec {
        name,
        short,
        kind: OptionKind::Boolean,
        tsconfig_only: false,
        min_value: 0,
        enum_values: &[],
    }
}

const fn tsconfig_flag(name: &'static str) -> OptionSpec {
    OptionSpec {
        name,
        short: None,
        kind: OptionKind::Boolean,
        tsconfig_only: true,
        min_value: 0,
        enum_values: &[],
    }
}

const fn string_opt(name: &'static str, short: Option<&'static str>) -> OptionSpec {
    OptionSpec {
        name,
        short,
        kind: OptionKind::String,
        tsconfig_only: false,
        min_value: 0,
        enum_values: &[],
    }
}

const fn number_opt(name: &'static str, min_value: i32) -> OptionSpec {
    OptionSpec {
        name,
        short: None,
        kind: OptionKind::Number,
        tsconfig_only: false,
        min_value,
        enum_values: &[],
    }
}

const fn enum_opt(
    name: &'static str,
    short: Option<&'static str>,
    values: &'static [&'static str],
) -> OptionSpec {
    OptionSpec {
        name,
        short,
        kind: OptionKind::Enum,
        tsconfig_only: false,
        min_value: 0,
        enum_values: values,
    }
}

const fn list_opt(name: &'static str, values: &'static [&'static str]) -> OptionSpec {
    OptionSpec {
        name,
        short: None,
        kind: OptionKind::List,
        tsconfig_only: false,
        min_value: 0,
        enum_values: values,
    }
}

const TARGETS: &[&str] = &[
    "es6", "es2015", "es2016", "es2017", "es2018", "es2019", "es2020", "es2021", "es2022",
    "es2023", "es2024", "es2025", "esnext",
];
const MODULES: &[&str] = &[
    "commonjs", "amd", "system", "umd", "es6", "es2015", "es2020", "es2022", "esnext", "node16",
    "node18", "node20", "nodenext", "preserve",
];
const JSX: &[&str] = &[
    "preserve",
    "react-native",
    "react-jsx",
    "react-jsxdev",
    "react",
];
const MODULE_RESOLUTION: &[&str] = &["node16", "nodenext", "bundler", "classic", "node", "node10"];
const MODULE_DETECTION: &[&str] = &["auto", "legacy", "force"];
const NEW_LINE: &[&str] = &["crlf", "lf"];
const LIBS: &[&str] = &[
    "es5",
    "es6",
    "es2015",
    "es7",
    "es2016",
    "es2017",
    "es2018",
    "es2019",
    "es2020",
    "es2021",
    "es2022",
    "es2023",
    "es2024",
    "es2025",
    "esnext",
    "dom",
    "dom.iterable",
    "dom.asynciterable",
    "webworker",
    "webworker.importscripts",
    "webworker.iterable",
    "webworker.asynciterable",
    "scripthost",
    "decorators",
    "decorators.legacy",
];
const WATCH_FILE: &[&str] = &[
    "fixedpollinginterval",
    "prioritypollinginterval",
    "dynamicprioritypolling",
    "fixedchunksizepolling",
    "usefsevents",
    "usefseventsonparentdirectory",
];
const WATCH_DIRECTORY: &[&str] = &[
    "usefsevents",
    "fixedpollinginterval",
    "dynamicprioritypolling",
    "fixedchunksizepolling",
];
const FALLBACK_POLLING: &[&str] = &[
    "fixedinterval",
    "priorityinterval",
    "dynamicpriority",
    "fixedchunksize",
];

const COMMON: &[OptionSpec] = &[
    flag("help", Some("h")),
    flag("help", Some("?")),
    flag("watch", Some("w")),
    flag("preserveWatchOutput", None),
    flag("listFiles", None),
    flag("explainFiles", None),
    flag("listEmittedFiles", None),
    flag("pretty", None),
    flag("traceResolution", None),
    flag("diagnostics", None),
    flag("extendedDiagnostics", None),
    string_opt("generateCpuProfile", None),
    string_opt("generateTrace", None),
    flag("incremental", Some("i")),
    flag("declaration", Some("d")),
    flag("declarationMap", None),
    flag("emitDeclarationOnly", None),
    flag("sourceMap", None),
    flag("inlineSourceMap", None),
    flag("noCheck", None),
    flag("deduplicatePackages", None),
    flag("noEmit", None),
    flag("assumeChangesOnlyAffectDirectDependencies", None),
    string_opt("locale", None),
    flag("quiet", Some("q")),
    flag("singleThreaded", None),
    string_opt("pprofDir", None),
    number_opt("checkers", 1),
    flag("runExternalCode", None),
];

const COMPILER: &[OptionSpec] = &[
    flag("all", None),
    flag("version", Some("v")),
    flag("init", None),
    string_opt("project", Some("p")),
    flag("showConfig", None),
    flag("listFilesOnly", None),
    flag("ignoreConfig", None),
    enum_opt("target", Some("t"), TARGETS),
    enum_opt("module", Some("m"), MODULES),
    list_opt("lib", LIBS),
    flag("allowJs", None),
    flag("checkJs", None),
    enum_opt("jsx", None, JSX),
    string_opt("outFile", None),
    string_opt("out", None),
    string_opt("outDir", None),
    string_opt("rootDir", None),
    tsconfig_flag("composite"),
    string_opt("tsBuildInfoFile", None),
    flag("removeComments", None),
    flag("importHelpers", None),
    flag("downlevelIteration", None),
    flag("isolatedModules", None),
    flag("verbatimModuleSyntax", None),
    flag("isolatedDeclarations", None),
    flag("erasableSyntaxOnly", None),
    flag("libReplacement", None),
    flag("strict", None),
    flag("noImplicitAny", None),
    flag("strictNullChecks", None),
    flag("strictFunctionTypes", None),
    flag("strictBindCallApply", None),
    flag("strictPropertyInitialization", None),
    flag("noImplicitThis", None),
    flag("useUnknownInCatchVariables", None),
    flag("alwaysStrict", None),
    flag("noUnusedLocals", None),
    flag("noUnusedParameters", None),
    flag("exactOptionalPropertyTypes", None),
    flag("noImplicitReturns", None),
    flag("noFallthroughCasesInSwitch", None),
    flag("noUncheckedIndexedAccess", None),
    flag("noImplicitOverride", None),
    flag("noPropertyAccessFromIndexSignature", None),
    enum_opt("moduleResolution", None, MODULE_RESOLUTION),
    string_opt("baseUrl", None),
    list_opt("rootDirs", &[]),
    list_opt("typeRoots", &[]),
    list_opt("types", &[]),
    flag("allowSyntheticDefaultImports", None),
    flag("esModuleInterop", None),
    flag("preserveSymlinks", None),
    flag("allowUmdGlobalAccess", None),
    list_opt("moduleSuffixes", &[]),
    flag("allowImportingTsExtensions", None),
    flag("rewriteRelativeImportExtensions", None),
    flag("resolvePackageJsonExports", None),
    flag("resolvePackageJsonImports", None),
    list_opt("customConditions", &[]),
    flag("noUncheckedSideEffectImports", None),
    string_opt("sourceRoot", None),
    string_opt("mapRoot", None),
    flag("inlineSources", None),
    flag("experimentalDecorators", None),
    flag("emitDecoratorMetadata", None),
    string_opt("jsxFactory", None),
    string_opt("jsxFragmentFactory", None),
    string_opt("jsxImportSource", None),
    flag("resolveJsonModule", None),
    flag("allowArbitraryExtensions", None),
    string_opt("reactNamespace", None),
    flag("skipDefaultLibCheck", None),
    flag("emitBOM", None),
    enum_opt("newLine", None, NEW_LINE),
    flag("noErrorTruncation", None),
    flag("noLib", None),
    flag("noResolve", None),
    flag("stripInternal", None),
    flag("disableSizeLimit", None),
    tsconfig_flag("disableSourceOfProjectReferenceRedirect"),
    tsconfig_flag("disableSolutionSearching"),
    tsconfig_flag("disableReferencedProjectLoad"),
    flag("noEmitHelpers", None),
    flag("noEmitOnError", None),
    flag("preserveConstEnums", None),
    string_opt("declarationDir", None),
    flag("skipLibCheck", None),
    flag("allowUnusedLabels", None),
    flag("allowUnreachableCode", None),
    flag("forceConsistentCasingInFileNames", None),
    number_opt("maxNodeModuleJsDepth", 0),
    flag("useDefineForClassFields", None),
    OptionSpec {
        name: "plugins",
        short: None,
        kind: OptionKind::List,
        tsconfig_only: true,
        min_value: 0,
        enum_values: &[],
    },
    enum_opt("moduleDetection", None, MODULE_DETECTION),
    string_opt("ignoreDeprecations", None),
    enum_opt("watchFile", None, WATCH_FILE),
    enum_opt("watchDirectory", None, WATCH_DIRECTORY),
    enum_opt("fallbackPolling", None, FALLBACK_POLLING),
    flag("synchronousWatchDirectory", None),
    list_opt("excludeDirectories", &[]),
    list_opt("excludeFiles", &[]),
];

const BUILD: &[OptionSpec] = &[
    flag("build", Some("b")),
    flag("verbose", Some("v")),
    flag("dry", Some("d")),
    flag("force", Some("f")),
    flag("clean", None),
    number_opt("builders", 1),
    flag("stopBuildOnErrors", None),
];

/// Looks up the canonical table spelling of one parsed option name. The
/// parser stores canonical names already, so this exists for the showConfig
/// reporting route to confirm a name is parser-validated ('static spelling).
#[must_use]
pub fn canonical_option_name(name: &str) -> Option<&'static str> {
    option_table(false)
        .find(|spec| spec.name == name)
        .map(|spec| spec.name)
}

fn option_table(is_build: bool) -> impl Iterator<Item = OptionSpec> {
    let extra: &[OptionSpec] = if is_build { BUILD } else { COMPILER };
    extra.iter().copied().chain(COMMON.iter().copied())
}

fn lookup_option(input: &str, is_build: bool) -> Option<OptionSpec> {
    let lowered = input.to_ascii_lowercase();
    option_table(is_build).find(|spec| {
        spec.name.eq_ignore_ascii_case(&lowered)
            || spec
                .short
                .is_some_and(|short| short.eq_ignore_ascii_case(&lowered))
    })
}

/// Converts a driver [`ArgsError`] into a TypeScript-shaped usage failure.
#[must_use]
pub fn args_error_to_tsc(error: &ArgsError) -> TscArgError {
    TscArgError::new(5023, error.to_string())
}

/// F2.1 seam: an exact `--api` token selects the persistent JSON-RPC transport
/// (`bamts_cli::api_server`) instead of a compilation. Detected before option
/// parsing so the child process's stdout stays protocol-only.
#[must_use]
pub fn api_transport_requested<I, S>(args: I) -> bool
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    args.into_iter().any(|token| token.as_ref() == "--api")
}

/// An exact `--lsp` token selects the stdio Language Server Protocol transport
/// (`bamts_cli::lsp`) instead of a compilation. Detected before option parsing
/// so the loop's stdout stays protocol-only.
#[must_use]
pub fn lsp_transport_requested<I, S>(args: I) -> bool
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    args.into_iter().any(|token| token.as_ref() == "--lsp")
}

#[cfg(test)]
mod lsp_transport_tests {
    use super::lsp_transport_requested;

    #[test]
    fn lsp_token_selects_transport_anywhere() {
        assert!(lsp_transport_requested(["--lsp"]));
        assert!(lsp_transport_requested([
            "--project",
            "tsconfig.json",
            "--lsp"
        ]));
        assert!(!lsp_transport_requested(["--project", "tsconfig.json"]));
        assert!(!lsp_transport_requested(["--lspish"]));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(args: &[&str]) -> ParsedTscCommand {
        parse_tsc_args(args.iter().copied()).expect("argv should parse")
    }

    fn parse_err(args: &[&str]) -> TscArgErrors {
        parse_tsc_args(args.iter().copied()).expect_err("argv should fail")
    }

    #[test]
    fn pretty_false_canonical_argv() {
        let command = parse(&[
            "tsc",
            "--noEmit",
            "--pretty",
            "false",
            "--allowJs",
            "--jsx",
            "preserve",
            "main.ts",
        ]);
        assert!(!command.pretty());
        assert_eq!(command.diagnostics_format(), DiagnosticsFormat::Text);
        assert!(command.flag("noEmit"));
        assert!(command.flag("allowJs"));
        assert_eq!(command.option_str("jsx"), Some("preserve"));
        let cli = command.to_cli_args();
        assert_eq!(cli.mode, Mode::Check);
        assert!(cli.js_compat.allow_js);
        assert!(cli.js_compat.jsx_preserve);
        assert_eq!(cli.entrypoint.as_deref(), Some("main.ts"));
        assert_eq!(cli.error_limit, usize::MAX);
        assert_eq!(cli.diagnostics_format, DiagnosticsFormat::Text);
        assert_eq!(command.parse_exit_status(), TscExitStatus::Success);
    }

    #[test]
    fn pretty_true_and_bare_flag() {
        assert!(parse(&["--pretty", "true", "a.ts"]).pretty());
        assert!(parse(&["--pretty", "a.ts"]).pretty());
        assert!(!parse(&["--pretty", "false", "a.ts"]).pretty());
        assert!(!parse(&["a.ts"]).pretty());
    }

    #[test]
    fn pretty_false_is_case_sensitive() {
        let command = parse(&["--pretty", "False", "a.ts"]);
        assert!(command.pretty());
        assert_eq!(
            command.file_names,
            vec!["False".to_owned(), "a.ts".to_owned()]
        );
    }

    #[test]
    fn equals_form_is_unknown() {
        let text = parse_err(&["--pretty=false", "a.ts"]).pretty_false();
        assert!(text.contains("error TS5023:"));
        assert!(text.contains("Unknown compiler option '--pretty=false'."));
    }

    #[test]
    fn unknown_option_fails_precisely() {
        let errors = parse_err(&["--not-a-real-flag", "a.ts"]);
        assert_eq!(
            errors.exit_status(),
            TscExitStatus::DiagnosticsPresentOutputsSkipped
        );
        let text = errors.pretty_false();
        assert!(text.contains("error TS5023:"));
        assert!(text.contains("Unknown compiler option '--not-a-real-flag'."));
        assert!(!text.contains("unknown option"));
    }

    #[test]
    fn did_you_mean_for_near_miss() {
        let text = parse_err(&["--allwJs", "a.ts"]).pretty_false();
        assert!(text.contains("TS5025"));
        assert!(text.contains("Did you mean 'allowJs'"));
    }

    #[test]
    fn invalid_enum_lists_allowed_values() {
        let text = parse_err(&["--target", "es99", "a.ts"]).pretty_false();
        assert!(text.contains("TS6046"));
        assert!(text.contains("Argument for '--target'"));
        assert!(text.contains("'es6'"));
        assert!(text.contains("'esnext'"));
    }

    #[test]
    fn removed_es3_target_reports_its_dedicated_diagnostic() {
        let errors = parse_err(&["--target", "es3", "a.ts"]);
        let text = errors.pretty_false();
        assert_eq!(
            errors.exit_status(),
            TscExitStatus::DiagnosticsPresentOutputsGenerated
        );
        assert!(text.contains("TS5108"));
        assert!(text.contains("Option 'target=ES3' has been removed."));
        assert!(!text.contains("TS6046"));
    }

    #[test]
    fn es5_target_parses_case_insensitively() {
        let lower = parse(&["--target", "es5", "a.ts"]);
        assert_eq!(lower.option_str("target"), Some("es5"));
        let upper = parse(&["--target", "ES5", "a.ts"]);
        assert_eq!(upper.option_str("target"), Some("es5"));
    }

    #[test]
    fn previously_failing_flags_parse_and_yield_expected_values() {
        let target = parse(&["--target", "es2015", "a.ts"]);
        assert_eq!(target.option_str("target"), Some("es2015"));

        let module = parse(&["--module", "commonjs", "a.ts"]);
        assert_eq!(module.option_str("module"), Some("commonjs"));

        let lib = parse(&["--lib", "es2015", "a.ts"]);
        assert_eq!(
            lib.options.get("lib"),
            Some(&TscOptionValue::List(vec!["es2015".to_owned()]))
        );

        let jsx = parse(&["--jsx", "react", "a.ts"]);
        assert_eq!(jsx.option_str("jsx"), Some("react"));

        let emit = parse(&["--emitDeclarationOnly", "a.ts"]);
        assert_eq!(
            emit.options.get("emitDeclarationOnly"),
            Some(&TscOptionValue::Bool(true))
        );
    }

    #[test]
    fn enum_values_are_case_insensitive() {
        assert_eq!(
            parse(&["--target", "ES2015", "a.ts"]).option_str("target"),
            Some("es2015")
        );
        assert_eq!(
            parse(&["--module", "CommonJS", "a.ts"]).option_str("module"),
            Some("commonjs")
        );
        assert_eq!(
            parse(&["--jsx", "react-jsx", "a.ts"]).option_str("jsx"),
            Some("react-jsx")
        );
    }

    #[test]
    fn missing_project_value_fails() {
        let text = parse_err(&["--project"]).pretty_false();
        assert!(text.contains("TS6044"));
        assert!(text.contains("Compiler option 'project' expects an argument."));
    }

    #[test]
    fn project_cannot_mix_with_files() {
        let errors = parse_err(&["--bogus", "-p", "tsconfig.json", "extra.ts"]);
        let text = errors.pretty_false();
        assert!(text.contains("TS5023"));
        assert!(text.contains("TS5042"));
        assert_eq!(errors.errors().len(), 2);
    }

    #[test]
    fn tsconfig_only_composite_true_fails() {
        let text = parse_err(&["--composite", "true", "a.ts"]).pretty_false();
        assert!(text.contains("TS5093"));
        assert!(text.contains("tsconfig.json"));
    }

    #[test]
    fn tsconfig_only_composite_false_is_allowed() {
        let command = parse(&["--composite", "false", "a.ts"]);
        assert_eq!(
            command.options.get("composite"),
            Some(&TscOptionValue::Bool(false))
        );
    }

    #[test]
    fn build_mode_parses_and_rejects_compiler_only_flags() {
        let command = parse(&["-b"]);
        assert!(command.is_build);
        assert!(command.flag("build"));
        let text = parse_err(&["-b", "--init"]).pretty_false();
        assert!(text.contains("error TS6387:"));
        assert!(text.contains("may not be used with '--build'"));
    }

    #[test]
    fn init_ignores_compile_options() {
        let command = parse(&["--init", "--target", "es5", "--pretty", "true", "main.ts"]);
        assert!(command.flag("init"));
        assert_eq!(command.file_names, ["main.ts"]);
    }

    #[test]
    fn late_build_flag_is_unknown() {
        let text = parse_err(&["a.ts", "--build"]).pretty_false();
        assert!(text.contains("error TS5023:"));
        assert!(text.contains("Unknown compiler option '--build'."));
    }

    #[test]
    fn build_only_flag_without_build_mode() {
        let text = parse_err(&["--verbose", "a.ts"]).pretty_false();
        assert!(text.contains("error TS6388:"));
        assert!(text.contains("may only be used with '--build'"));
    }

    #[test]
    fn clean_and_force_cannot_combine() {
        let text = parse_err(&["-b", "--clean", "--force"]).pretty_false();
        assert!(text.contains("error TS6370:"));
        assert!(text.contains("cannot be combined"));
    }

    #[test]
    fn watch_and_list_files_only_cannot_combine() {
        let text = parse_err(&["--watch", "--listFilesOnly", "a.ts"]).pretty_false();
        assert!(text.contains("Options 'watch' and 'listFilesOnly' cannot be combined."));
    }

    #[test]
    fn short_names_and_lib_list() {
        let command = parse(&[
            "-t",
            "ES2022",
            "-m",
            "nodenext",
            "--lib",
            "es2022,dom",
            "a.ts",
        ]);
        assert_eq!(command.option_str("target"), Some("es2022"));
        assert_eq!(command.option_str("module"), Some("nodenext"));
        assert_eq!(
            command.options.get("lib"),
            Some(&TscOptionValue::List(vec![
                "es2022".to_owned(),
                "dom".to_owned()
            ]))
        );
    }

    #[test]
    fn short_d_and_v_depend_on_mode() {
        let compile = parse(&["-d", "-v", "a.ts"]);
        assert!(compile.flag("declaration"));
        assert!(compile.flag("version"));
        let build = parse(&["-b", "-d", "-v"]);
        assert!(build.flag("dry"));
        assert!(build.flag("verbose"));
        assert!(!build.flag("declaration"));
        assert!(!build.flag("version"));
    }

    #[test]
    fn lib_missing_value_fails() {
        let text = parse_err(&["--lib"]).pretty_false();
        assert!(text.contains("TS6044"));
        assert!(text.contains("Compiler option 'lib' expects an argument."));
    }

    #[test]
    fn response_file_expands_tokens() {
        let command = parse_tsc_args_with(["@flags.txt", "main.ts"], |path| {
            assert_eq!(path, "flags.txt");
            Ok("--pretty false --noEmit --allowJs".to_owned())
        })
        .expect("response file");
        assert!(!command.pretty());
        assert!(command.flag("noEmit"));
        assert!(command.flag("allowJs"));
        assert_eq!(command.file_names, vec!["main.ts"]);
    }

    #[test]
    fn unterminated_response_quote_fails() {
        let text = parse_tsc_args_with(["@bad.txt"], |_| Ok("\"unterminated".to_owned()))
            .expect_err("unterminated")
            .pretty_false();
        assert!(text.contains("TS5004"));
    }

    #[test]
    fn unreadable_response_file_fails() {
        let text = parse_tsc_args_with(["@missing.txt"], |_| Err("nope".to_owned()))
            .expect_err("missing")
            .pretty_false();
        assert!(text.contains("error TS5012:"));
        assert!(text.contains("Cannot read file 'missing.txt'."));
    }

    #[test]
    fn multiple_files_are_retained() {
        let command = parse(&["--noEmit", "--pretty", "false", "a.ts", "b.ts", "c.ts"]);
        let cli = command.to_cli_args();
        assert_eq!(cli.entrypoint.as_deref(), Some("a.ts"));
        assert_eq!(cli.extra_inputs, vec!["b.ts", "c.ts"]);
        assert_eq!(cli.error_limit, usize::MAX);
    }

    #[test]
    fn empty_argv_is_valid_tsconfig_cwd() {
        let command = parse(&["tsc"]);
        assert!(command.file_names.is_empty());
        assert!(!command.pretty());
        assert_eq!(command.to_cli_args().entrypoint, None);
        assert_eq!(command.project(), None);
    }

    #[test]
    fn project_is_not_an_entrypoint() {
        let command = parse(&["-p", "tsconfig.json"]);
        assert_eq!(command.project(), Some("tsconfig.json"));
        assert!(command.file_names.is_empty());
        assert_eq!(command.to_cli_args().entrypoint, None);
    }

    #[test]
    fn exit_status_vectors() {
        assert_eq!(TscExitStatus::Success.code(), 0);
        assert_eq!(TscExitStatus::from_compilation(false, false).code(), 0);
        assert_eq!(TscExitStatus::from_compilation(true, false).code(), 1);
        assert_eq!(TscExitStatus::from_compilation(true, true).code(), 2);
        assert_eq!(TscExitStatus::InvalidProjectOutputsSkipped.code(), 3);
        assert_eq!(TscExitStatus::ProjectReferenceCycleOutputsSkipped.code(), 4);
        assert_eq!(TscExitStatus::NotImplemented.code(), 5);
    }

    #[test]
    fn declaration_and_source_map_map_to_driver_output() {
        let cli = parse(&["-d", "--sourceMap", "--outDir", "dist", "a.ts"]).to_cli_args();
        assert!(cli.output.emit_declarations);
        assert!(cli.output.source_maps);
        assert_eq!(cli.output.dir.as_deref(), Some("dist"));
        assert_eq!(cli.mode, Mode::Compile);
    }

    #[test]
    fn out_alias_maps_to_output_file() {
        let cli = parse(&["--out", "bundle.js", "a.ts"]).to_cli_args();
        assert_eq!(cli.output.file.as_deref(), Some("bundle.js"));
    }

    #[test]
    fn args_error_maps_to_typescript_shape() {
        let error = args_error_to_tsc(&ArgsError::UnknownOption {
            option: "--json".to_owned(),
        });
        assert_eq!(error.code, 5023);
        assert_eq!(
            error.pretty_false_line(),
            "error TS5023: unknown option '--json'"
        );
    }

    #[test]
    fn json_is_not_a_tsc_flag() {
        let text = parse_err(&["--json", "a.ts"]).pretty_false();
        assert!(text.contains("Unknown compiler option '--json'."));
    }

    #[test]
    fn api_transport_flag_is_detected_before_parsing() {
        assert!(api_transport_requested(["tsc", "--api"]));
        assert!(api_transport_requested(["--api"]));
        assert!(!api_transport_requested([
            "tsc", "--pretty", "false", "a.ts"
        ]));
        assert!(!api_transport_requested(["tsc", "--apidx"]));
        assert!(!api_transport_requested([] as [&str; 0]));
    }

    #[test]
    fn mode_classification_covers_representative_options() {
        use TscDispatchMode::{Build, Direct, Project};
        assert_eq!(
            classify_option("outDir", Project),
            ModeOptionClassification::Consumed
        );
        assert_eq!(
            classify_option("target", Project),
            ModeOptionClassification::Consumed
        );
        assert_eq!(
            classify_option("verbose", Build),
            ModeOptionClassification::Consumed
        );
        assert_eq!(
            classify_option("noEmit", Build),
            ModeOptionClassification::Unsupported
        );
        assert_eq!(
            classify_option("ignoreConfig", Direct),
            ModeOptionClassification::Consumed
        );
        assert_eq!(
            classify_option("ignoreConfig", Project),
            ModeOptionClassification::Unsupported
        );
        assert_eq!(
            classify_option("strict", Direct),
            ModeOptionClassification::Consumed
        );
    }

    #[test]
    fn import_helpers_is_consumed_in_direct_and_project_modes() {
        // tsc accepts `--importHelpers`; the baselines import the helpers from
        // `tslib` (importHelpers(target=es5).js emits `require("tslib")`), so
        // both argv dispatch modes must consume the flag instead of failing
        // with TS5047.
        use TscDispatchMode::{Direct, Project};
        assert_eq!(
            classify_option("importHelpers", Direct),
            ModeOptionClassification::Consumed
        );
        assert_eq!(
            classify_option("importHelpers", Project),
            ModeOptionClassification::Consumed
        );
    }

    #[test]
    fn first_unsupported_option_reports_the_stable_first_failure() {
        let command = parse(&["--watch", "--incremental"]);
        assert_eq!(
            command.first_unsupported_option(TscDispatchMode::Direct),
            Some("watch")
        );
    }

    #[test]
    fn direct_mode_classifies_even_unset_null_options() {
        let command = parse(&["--watch", "null"]);
        assert_eq!(
            command.first_unsupported_option(TscDispatchMode::Direct),
            Some("watch")
        );
    }

    #[test]
    fn consumed_sets_only_reference_parser_table_names() {
        for name in DIRECT_CONSUMED
            .iter()
            .chain(PROJECT_CONSUMED.iter())
            .chain(BUILD_CONSUMED.iter())
        {
            assert!(
                lookup_option(name, false).is_some() || lookup_option(name, true).is_some(),
                "consumed name `{name}` is missing from the parse table"
            );
        }
    }
}
