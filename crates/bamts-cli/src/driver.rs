use bamts::discover_project;
use bamts_compiler::CancellationToken;
use bamts_compiler::lower::LowerOptions;
use bamts_compiler::pipeline::{
    FrontendMode, ProgramFrontendOutput, compile_program_frontend_with_cancel,
};
use bamts_compiler::program::{
    ProgramLoadError, ProgramLoader, ProgramLowerError, ResolvedProgram, lower_program,
    lower_program_with_cancel,
};
use bamts_compiler::{
    diagnostic::{Diagnostic, DiagnosticReport, DiagnosticSeverity},
    diagnostics_parser::map_parse_diagnostics,
    lint::{LintOverride, LintProfile, LintTable},
    project::{
        JsonObject, JsonValue, ProjectConfig, ProjectRoot,
        build_mode::BuildInfo,
        effective::{
            EffectiveProject, MaterializeError, ProjectBuildOptions, ProjectCompileError,
            ProjectCompileOptions, ProjectCompileResult, ProjectLoadRequest,
            ProjectOptionOverrides, compile_project, compile_project_references,
            load_reference_closure,
        },
        parse_bamts_toml,
        references::resolve_config_file_name,
    },
    service::filesystem::OsFileSystem,
};
use bamts_runtime::{Limits, run_linked_program_with_cancel};
use serde::{
    Serialize,
    ser::{SerializeMap, SerializeSeq, Serializer},
};
use std::error::Error;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output, Stdio};
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
    mpsc::{self, Receiver, TryRecvError},
};
use std::{thread, time::Duration};

use crate::args::{ArgsError, CliArgs, ExecutionTarget, Mode};
use crate::cli::{
    diagnostic_format::{self as tsc_diagnostics, TscDiagnosticFormat},
    tsc_args::{ParsedTscCommand, TscDispatchMode, TscExitStatus, TscOptionValue},
};
use crate::context::ExecutionContext;
use crate::diagnostics::{self, DiagnosticSource, TruncationNotice};
use crate::output::{StdAtomicFs, publish_atomic};

const NODE_STATICLIB: &[u8] = include_bytes!(env!("BAMTS_NODE_STATICLIB"));
const HOST_TARGET: &str = env!("BAMTS_HOST_TARGET");
const BUILD_TARGET: &str = env!("BAMTS_BUILD_TARGET");
static NEXT_CACHE_TEMP_ID: AtomicUsize = AtomicUsize::new(0);

/// Bytes and process status produced by one successful CLI command.
#[derive(Debug, Default, Eq, PartialEq)]
pub struct CommandOutcome {
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub exit_code: i32,
    pub truncation: Option<TruncationNotice>,
}

/// A typed failure from compilation, execution, artifact publication, or linking.
#[derive(Debug)]
pub enum DriverError {
    Cancelled,
    ReadSource {
        path: PathBuf,
        source: io::Error,
    },
    UnsupportedSourceExtension {
        path: PathBuf,
    },
    Diagnostics {
        rendered: String,
        truncation: Option<TruncationNotice>,
    },
    Usage(ArgsError),
    NonUnicodeEnvironmentName,
    NonUnicodeEnvironmentValue {
        name: String,
    },
    LintConfig {
        path: PathBuf,
        message: String,
    },
    ProjectConfig {
        path: PathBuf,
        message: String,
    },
    ProgramLoad(ProgramLoadError),
    Lower(ProgramLowerError),
    Jit(bamts_codegen::JitError),
    Native(bamts_runtime::NativeError),
    Aot(bamts_codegen::AotError),
    MissingEntrypoint,
    MultipleCompileInputs,
    UnsupportedCompileTarget(ExecutionTarget),
    UnsupportedOutputOption(&'static str),
    CreateDirectory {
        path: PathBuf,
        source: io::Error,
    },
    CacheArchive {
        path: PathBuf,
        source: io::Error,
    },
    WriteObject {
        path: PathBuf,
        source: io::Error,
    },
    WriteTscConfig {
        path: PathBuf,
        source: io::Error,
    },
    ShowConfigRender {
        source: io::Error,
    },
    ToolchainMissing {
        program: OsString,
    },
    ToolchainProbe {
        program: OsString,
        source: io::Error,
    },
    ToolchainRejected {
        program: OsString,
        status: ExitStatus,
    },
    LinkStart {
        program: OsString,
        source: io::Error,
    },
    LinkFailed {
        program: OsString,
        status: ExitStatus,
        stderr: String,
    },
    PublishExecutable {
        path: PathBuf,
        source: io::Error,
    },
    CrossTargetLink {
        host: &'static str,
        target: &'static str,
    },
    UnsafeFallbackCacheRoot {
        path: PathBuf,
    },
}

impl DriverError {
    #[must_use]
    pub const fn rendered_diagnostic(&self) -> Option<&str> {
        match self {
            Self::Diagnostics { rendered, .. } => Some(rendered.as_str()),
            _ => None,
        }
    }
    #[must_use]
    pub const fn truncation_notice(&self) -> Option<TruncationNotice> {
        match self {
            Self::Diagnostics { truncation, .. } => *truncation,
            _ => None,
        }
    }

    #[must_use]
    pub const fn is_usage_error(&self) -> bool {
        matches!(self, Self::Usage(_))
    }
}

impl fmt::Display for DriverError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cancelled => formatter.write_str("operation cancelled"),
            Self::ReadSource { path, source } => {
                write!(formatter, "could not read `{}`: {source}", path.display())
            }
            Self::UnsupportedSourceExtension { path } => write!(
                formatter,
                "source file `{}` has an unsupported extension",
                path.display()
            ),
            Self::Diagnostics { .. } => formatter.write_str("source contains error diagnostics"),
            Self::Usage(error) => error.fmt(formatter),
            Self::NonUnicodeEnvironmentName => {
                formatter.write_str("process environment contains a non-Unicode name")
            }
            Self::NonUnicodeEnvironmentValue { name } => write!(
                formatter,
                "process environment variable {name} contains a non-Unicode value"
            ),
            Self::LintConfig { path, message } => {
                write!(
                    formatter,
                    "could not load lint configuration `{}`: {message}",
                    path.display()
                )
            }
            Self::ProjectConfig { path, message } => write!(
                formatter,
                "could not load project configuration `{}`: {message}",
                path.display()
            ),
            Self::ProgramLoad(error) => write!(formatter, "could not load program: {error}"),
            Self::Lower(error) => write!(formatter, "source cannot be lowered: {error}"),
            Self::Jit(error) => write!(formatter, "JIT compilation failed: {error}"),
            Self::Native(error) => write!(formatter, "program execution failed: {error}"),
            Self::Aot(error) => write!(formatter, "AOT object emission failed: {error}"),
            Self::MissingEntrypoint => formatter.write_str("command requires an entrypoint"),
            Self::MultipleCompileInputs => {
                formatter.write_str("program commands accept exactly one entrypoint")
            }
            Self::UnsupportedCompileTarget(target) => write!(
                formatter,
                "compile target `{target}` does not produce a persistent artifact"
            ),
            Self::UnsupportedOutputOption(option) => {
                write!(
                    formatter,
                    "{option} is not supported for native compilation"
                )
            }
            Self::CreateDirectory { path, source } => write!(
                formatter,
                "could not create output directory `{}`: {source}",
                path.display()
            ),
            Self::CacheArchive { path, source } => write!(
                formatter,
                "could not materialize the embedded runtime at `{}`: {source}",
                path.display()
            ),
            Self::WriteObject { path, source } => {
                write!(
                    formatter,
                    "could not write native object `{}`: {source}",
                    path.display()
                )
            }
            Self::WriteTscConfig { path, source } => write!(
                formatter,
                "could not write TypeScript config `{}`: {source}",
                path.display()
            ),
            Self::ShowConfigRender { source } => {
                write!(formatter, "could not render showConfig output: {source}")
            }
            Self::ToolchainMissing { program } => write!(
                formatter,
                "system C toolchain `{}` was not found",
                Path::new(program).display()
            ),
            Self::ToolchainProbe { program, source } => write!(
                formatter,
                "could not inspect system C toolchain `{}`: {source}",
                Path::new(program).display()
            ),
            Self::ToolchainRejected { program, status } => write!(
                formatter,
                "system C toolchain `{}` is unavailable ({status})",
                Path::new(program).display()
            ),
            Self::LinkStart { program, source } => write!(
                formatter,
                "could not start linker `{}`: {source}",
                Path::new(program).display()
            ),
            Self::LinkFailed {
                program,
                status,
                stderr,
            } => write!(
                formatter,
                "linker `{}` failed ({status}): {}",
                Path::new(program).display(),
                stderr.trim()
            ),
            Self::PublishExecutable { path, source } => write!(
                formatter,
                "could not publish executable `{}`: {source}",
                path.display()
            ),
            Self::CrossTargetLink { host, target } => write!(
                formatter,
                "native linking for Cargo target `{target}` is unsupported from host `{host}`"
            ),
            Self::UnsafeFallbackCacheRoot { path } => write!(
                formatter,
                "fallback cache root `{}` is not a private directory owned by the current user",
                path.display()
            ),
        }
    }
}

impl Error for DriverError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Cancelled => None,
            Self::ReadSource { source, .. }
            | Self::CreateDirectory { source, .. }
            | Self::CacheArchive { source, .. }
            | Self::WriteObject { source, .. }
            | Self::WriteTscConfig { source, .. }
            | Self::ShowConfigRender { source, .. }
            | Self::ToolchainProbe { source, .. }
            | Self::LinkStart { source, .. }
            | Self::PublishExecutable { source, .. } => Some(source),
            Self::Lower(error) => Some(error),
            Self::ProgramLoad(error) => Some(error),
            Self::Jit(error) => Some(error),
            Self::Native(error) => Some(error),
            Self::Aot(error) => Some(error),
            Self::Usage(error) => Some(error),
            Self::MissingEntrypoint
            | Self::UnsupportedSourceExtension { .. }
            | Self::Diagnostics { .. }
            | Self::NonUnicodeEnvironmentName
            | Self::NonUnicodeEnvironmentValue { .. }
            | Self::LintConfig { .. }
            | Self::ProjectConfig { .. }
            | Self::MultipleCompileInputs
            | Self::UnsupportedCompileTarget(_)
            | Self::UnsupportedOutputOption(_)
            | Self::ToolchainMissing { .. }
            | Self::ToolchainRejected { .. }
            | Self::LinkFailed { .. }
            | Self::CrossTargetLink { .. }
            | Self::UnsafeFallbackCacheRoot { .. } => None,
        }
    }
}

/// Executes one already-parsed CLI command.
pub fn execute(args: &CliArgs) -> Result<CommandOutcome, DriverError> {
    let context = ExecutionContext::ambient()?;
    execute_in_context(args, &context)
}

/// Executes one already-parsed command against explicit process inputs.
pub fn execute_in_context(
    args: &CliArgs,
    context: &ExecutionContext,
) -> Result<CommandOutcome, DriverError> {
    execute_in_context_with_cancel(args, context, CancellationToken::new())
}

/// [`execute`] with caller-controlled cooperative cancellation.
pub fn execute_with_cancel(
    args: &CliArgs,
    cancel: CancellationToken,
) -> Result<CommandOutcome, DriverError> {
    cancel.check().map_err(|_| DriverError::Cancelled)?;
    let context = ExecutionContext::ambient()?;
    execute_in_context_with_cancel(args, &context, cancel)
}

/// The canonical CLI execution seam with explicit process inputs and cancellation.
pub fn execute_in_context_with_cancel(
    args: &CliArgs,
    context: &ExecutionContext,
    cancel: CancellationToken,
) -> Result<CommandOutcome, DriverError> {
    cancel.check().map_err(|_| DriverError::Cancelled)?;
    match args.mode {
        Mode::Check | Mode::Compile | Mode::Run => {
            let frontend = load_program_frontend_in_context_with_cancel(args, context, &cancel)?;
            match args.mode {
                Mode::Check => check(args, &frontend),
                Mode::Compile => compile_in_context_with_cancel(args, &frontend, context, &cancel),
                Mode::Run => run_in_context_with_cancel(args, &frontend, context, &cancel),
                Mode::Explain => unreachable!("explain handled without a program"),
            }
        }
        Mode::Explain => {
            let rule = args
                .explain_rule
                .as_deref()
                .ok_or(DriverError::Usage(ArgsError::MissingExplainRule))?;
            let explanation = crate::args::explain_rule(rule).map_err(DriverError::Usage)?;
            Ok(CommandOutcome {
                stdout: explanation.into_bytes(),
                ..CommandOutcome::default()
            })
        }
    }
}

const TSC_HELP: &str = "\
tsc: The TypeScript Compiler - Version 7.0.2

COMMON COMMANDS

  tsc
  Compiles the current project (tsconfig.json in the working directory).

  tsc app.ts util.ts
  Ignoring tsconfig.json, compiles the specified files with default compiler options.

  tsc -b
  Build a composite project in the working directory.

  tsc --init
  Creates a tsconfig.json with the recommended settings in the working directory.

  tsc -p ./path/to/tsconfig.json
  Compiles the TypeScript project located at the specified path.

  tsc --help --all
  An expanded version of this information, showing all possible compiler options.

  tsc --noEmit
  tsc --target esnext
  Compiles the current project, with additional settings.

COMMAND LINE FLAGS

--help, -h
Print this message.

--version, -v
Print the compiler's version.

--build, -b
Build one or more projects and their dependencies, if out of date.
";

const TSC_INIT_CREATED: &str =
    "\nCreated a new tsconfig.json\n\nYou can learn more at https://aka.ms/tsconfig\n";
const TSC_INIT_CONFIG: &str = r#"{
  // Visit https://aka.ms/tsconfig to read more about this file
  "compilerOptions": {
    // File Layout
    // "rootDir": "./src",
    // "outDir": "./dist",

    // Environment Settings
    // See also https://aka.ms/tsconfig/module
    "module": "nodenext",
    "target": "esnext",
    "types": [],
    // For nodejs:
    // "lib": ["esnext"],
    // "types": ["node"],
    // and npm install -D @types/node

    // Other Outputs
    "sourceMap": true,
    "declaration": true,
    "declarationMap": true,

    // Stricter Typechecking Options
    "noUncheckedIndexedAccess": true,
    "exactOptionalPropertyTypes": true,

    // Style Options
    // "noImplicitReturns": true,
    // "noImplicitOverride": true,
    // "noUnusedLocals": true,
    // "noUnusedParameters": true,
    // "noFallthroughCasesInSwitch": true,
    // "noPropertyAccessFromIndexSignature": true,

    // Recommended Options
    "strict": true,
    "jsx": "react-jsx",
    "verbatimModuleSyntax": true,
    "isolatedModules": true,
    "noUncheckedSideEffectImports": true,
    "moduleDetection": "force",
    "skipLibCheck": true,
  }
}
"#;

/// Executes a command parsed by the TypeScript-compatible argv parser.
pub fn execute_tsc(command: &ParsedTscCommand) -> Result<CommandOutcome, DriverError> {
    let context = ExecutionContext::ambient()?;
    execute_tsc_in_context(command, &context)
}

fn execute_tsc_in_context(
    command: &ParsedTscCommand,
    context: &ExecutionContext,
) -> Result<CommandOutcome, DriverError> {
    let cwd = context.cwd();
    if command.flag("help") {
        return Ok(CommandOutcome {
            stdout: TSC_HELP.as_bytes().to_vec(),
            ..CommandOutcome::default()
        });
    }
    if command.flag("version") {
        return Ok(CommandOutcome {
            stdout: b"Version 7.0.2\n".to_vec(),
            ..CommandOutcome::default()
        });
    }
    if command.flag("init") {
        return initialize_tsc_config(context);
    }
    if command.is_build {
        return execute_tsc_build(command, cwd);
    }
    if command.project().is_some() || command.file_names.is_empty() {
        return execute_tsc_project(command, cwd);
    }
    if !command.flag("ignoreConfig") && context.resolve_path("tsconfig.json").is_file() {
        return Ok(CommandOutcome {
            stdout: b"error TS5112: tsconfig.json is present but will not be loaded if files are specified on commandline. Use '--ignoreConfig' to skip this error.\n".to_vec(),
            exit_code: TscExitStatus::DiagnosticsPresentOutputsSkipped.code(),
            ..CommandOutcome::default()
        });
    }
    // TypeScript 7.0.2 prints the final configuration after ordinary argument
    // validation and the files-plus-config conflict, but before the direct
    // compile-mode unsupported-option gate and before any parsing, binding,
    // checking, code generation, or writes. Ordinary direct compilation keeps
    // rejecting options it does not apply.
    if command.flag("showConfig") {
        // TypeScript prints argv file names relative to the process working
        // directory with a leading `./` (probe-verified).
        return show_config_outcome(&DirectShowConfig { command, cwd });
    }
    if let Some(option) = command.first_unsupported_option(TscDispatchMode::Direct) {
        return Ok(unsupported_option_outcome(option));
    }
    // JavaScript-artifact emission — declarations, source maps, and
    // multi-root programs — routes through the canonical project pipeline
    // over one inferred configuration-free project. The remaining
    // single-root compile keeps the native executable driver, which only
    // maps '--jsx preserve'.
    let artifact_route = command.file_names.len() > 1
        || (!command.flag("noEmit") && (command.flag("declaration") || command.flag("sourceMap")));
    if !artifact_route
        && command
            .option_str("jsx")
            .is_some_and(|jsx| jsx != "preserve")
    {
        return Ok(not_implemented(
            "Only '--jsx preserve' has a canonical native driver mapping.",
        ));
    }
    if !artifact_route {
        return compile_tsc_native_roots(command, context);
    }
    compile_tsc_artifacts(command, cwd, context)
}

/// The native executable direct route: one entrypoint, lowered and linked
/// without JavaScript-artifact emission.
fn compile_tsc_native_roots(
    command: &ParsedTscCommand,
    context: &ExecutionContext,
) -> Result<CommandOutcome, DriverError> {
    let mut stdout = Vec::new();
    let mut has_errors = false;
    let mut outputs_generated = false;
    for file_name in &command.file_names {
        let mut args = command.to_cli_args();
        args.entrypoint = Some(file_name.clone());
        args.extra_inputs.clear();
        let frontend = load_program_frontend_in_context_with_cancel(
            &args,
            context,
            &CancellationToken::new(),
        )?;
        let (rendered, file_has_errors) = render_tsc_program_diagnostics(command, &frontend);
        stdout.extend_from_slice(rendered.as_bytes());
        has_errors |= file_has_errors;
        if args.mode == Mode::Compile && (!file_has_errors || !command.flag("noEmitOnError")) {
            let outcome = compile_in_context_with_cancel(
                &args,
                &frontend,
                context,
                &CancellationToken::new(),
            )?;
            outputs_generated = true;
            stdout.extend_from_slice(&outcome.stdout);
        }
    }
    Ok(CommandOutcome {
        stdout,
        exit_code: TscExitStatus::from_compilation(has_errors, outputs_generated).code(),
        ..CommandOutcome::default()
    })
}

/// The JavaScript-artifact direct route: all argv roots in one inferred
/// project compiled through [`compile_project`]. Missing roots print
/// TypeScript's TS6053 diagnostic with the argv spelling and the remaining
/// roots still compile, matching TypeScript 7.0.2.
fn compile_tsc_artifacts(
    command: &ParsedTscCommand,
    cwd: &Path,
    context: &ExecutionContext,
) -> Result<CommandOutcome, DriverError> {
    let mut missing = Vec::new();
    let mut roots = Vec::new();
    for name in &command.file_names {
        if context.resolve_path(name).is_file() {
            roots.push(PathBuf::from(name));
        } else {
            missing.push(name.clone());
        }
    }
    let mut stdout = Vec::new();
    for name in &missing {
        writeln!(
            stdout,
            "error TS6053: File '{name}' not found.\n  The file is in the program because:\n    Root file specified for compilation"
        )
        .expect("writing to Vec cannot fail");
    }
    if roots.is_empty() {
        return Ok(CommandOutcome {
            stdout,
            exit_code: TscExitStatus::DiagnosticsPresentOutputsGenerated.code(),
            ..CommandOutcome::default()
        });
    }
    let filesystem = match OsFileSystem::new(cwd) {
        Ok(filesystem) => filesystem,
        Err(error) => return Ok(project_error_outcome(error.to_string())),
    };
    let request = ProjectLoadRequest {
        config_path: None,
        cwd: cwd.to_path_buf(),
        overrides: project_overrides(command),
        allow_missing_config: true,
        source_files: Some(roots),
    };
    let project = match EffectiveProject::load(&request, &filesystem) {
        Ok(project) => project,
        Err(error) => return Ok(project_compile_error_outcome(error, command, cwd)),
    };
    let result = match compile_project(&project, &ProjectCompileOptions::default(), &filesystem) {
        Ok(result) => result,
        Err(error) => return Ok(project_compile_error_outcome(error, command, cwd)),
    };
    if !result.up_to_date {
        publish_project_result(&result)?;
    }
    let mut outcome = project_result_outcome(command, &result);
    let mut merged = std::mem::take(&mut stdout);
    merged.append(&mut outcome.stdout);
    outcome.stdout = merged;
    if !missing.is_empty() {
        outcome.exit_code = TscExitStatus::DiagnosticsPresentOutputsGenerated.code();
    }
    Ok(outcome)
}

fn initialize_tsc_config(context: &ExecutionContext) -> Result<CommandOutcome, DriverError> {
    let path = context.resolve_path("tsconfig.json");
    let mut file = match OpenOptions::new().write(true).create_new(true).open(&path) {
        Ok(file) => file,
        Err(source) if source.kind() == io::ErrorKind::AlreadyExists => {
            return Ok(CommandOutcome {
                stdout: format!(
                    "error TS5054: A 'tsconfig.json' file is already defined at: '{}'.\n",
                    path.display()
                )
                .into_bytes(),
                ..CommandOutcome::default()
            });
        }
        Err(source) => return Err(DriverError::WriteTscConfig { path, source }),
    };
    if let Err(source) = file
        .write_all(TSC_INIT_CONFIG.as_bytes())
        .and_then(|()| file.sync_all())
    {
        return Err(DriverError::WriteTscConfig { path, source });
    }
    Ok(CommandOutcome {
        stdout: TSC_INIT_CREATED.as_bytes().to_vec(),
        ..CommandOutcome::default()
    })
}

#[cfg(test)]
fn execute_tsc_in(command: &ParsedTscCommand, cwd: &Path) -> Result<CommandOutcome, DriverError> {
    let environment = std::env::vars_os().collect();
    let context = ExecutionContext::new(cwd, environment)?;
    execute_tsc_in_context(command, &context)
}

fn execute_tsc_project(
    command: &ParsedTscCommand,
    cwd: &Path,
) -> Result<CommandOutcome, DriverError> {
    if let Some(option) = command.first_unsupported_option(TscDispatchMode::Project) {
        return Ok(unsupported_option_outcome(option));
    }
    let filesystem = match OsFileSystem::new(cwd) {
        Ok(filesystem) => filesystem,
        Err(error) => return Ok(project_error_outcome(error.to_string())),
    };
    let request = ProjectLoadRequest {
        config_path: Some(project_config_path(
            cwd,
            command.project().unwrap_or("tsconfig.json"),
        )),
        cwd: cwd.to_path_buf(),
        overrides: project_overrides(command),
        allow_missing_config: false,
        source_files: None,
    };
    let project = match EffectiveProject::load(&request, &filesystem) {
        Ok(project) => project,
        Err(error) => return Ok(project_compile_error_outcome(error, command, cwd)),
    };
    // TypeScript 7.0.2 prints the final merged configuration instead of
    // compiling: no project compilation, reference compilation, emit, or
    // writes happen on this route. The project was loaded exactly once above.
    if command.flag("showConfig") {
        return show_config_outcome(&ProjectShowConfig::new(&project));
    }
    let compile_options = ProjectCompileOptions {
        emit: !command.flag("listFilesOnly"),
        ..ProjectCompileOptions::default()
    };
    let result = match compile_project(&project, &compile_options, &filesystem) {
        Ok(result) => result,
        Err(error) => return Ok(project_compile_error_outcome(error, command, cwd)),
    };
    if !result.up_to_date {
        publish_project_result(&result)?;
    }
    Ok(project_result_outcome(command, &result))
}

fn execute_tsc_build(
    command: &ParsedTscCommand,
    cwd: &Path,
) -> Result<CommandOutcome, DriverError> {
    if let Some(option) = command.first_unsupported_option(TscDispatchMode::Build) {
        return Ok(unsupported_option_outcome(option));
    }
    let filesystem = match OsFileSystem::new(cwd) {
        Ok(filesystem) => filesystem,
        Err(error) => return Ok(project_error_outcome(error.to_string())),
    };
    let root = match ProjectRoot::new(cwd) {
        Ok(root) => root,
        Err(error) => return Ok(project_error_outcome(error.to_string())),
    };
    let configs = if command.file_names.is_empty() {
        vec![project_config_path(cwd, "tsconfig.json")]
    } else {
        command
            .file_names
            .iter()
            .map(|path| project_config_path(cwd, path))
            .collect()
    };
    if command.flag("clean") {
        let (_, graph) = match load_reference_closure(&root, &configs, &filesystem) {
            Ok(closure) => closure,
            Err(error) => return Ok(project_error_outcome(error.to_string())),
        };
        let mut order = match graph.topological_order() {
            Ok(order) => order,
            Err(error) => return Ok(project_error_outcome(error.to_string())),
        };
        order.reverse();
        for path in order {
            let Some(info_path) = graph
                .node(&path)
                .and_then(|node| node.build_info_path.as_deref())
            else {
                continue;
            };
            let Ok(bytes) = fs::read(info_path) else {
                continue;
            };
            let Ok(info) = BuildInfo::decode(&bytes) else {
                continue;
            };
            if !command.flag("dry") {
                for output in info.outputs {
                    if let Err(source) = fs::remove_file(&output)
                        && source.kind() != io::ErrorKind::NotFound
                    {
                        return Err(DriverError::ProjectConfig {
                            path: output,
                            message: source.to_string(),
                        });
                    }
                }
                let _ = fs::remove_file(info_path);
            }
        }
        return Ok(CommandOutcome::default());
    }

    let stop_on_error = command
        .options
        .get("stopBuildOnErrors")
        .and_then(|value| value.as_bool())
        .unwrap_or(true);
    let report = match compile_project_references(
        &root,
        &configs,
        cwd,
        ProjectBuildOptions {
            force: command.flag("force"),
            stop_on_error,
        },
        &filesystem,
    ) {
        Ok(report) => report,
        Err(error) => return Ok(project_error_outcome(error.to_string())),
    };
    let mut stdout = Vec::new();
    let mut has_errors = false;
    let mut outputs_generated = false;
    for project in report.projects {
        if command.flag("verbose") && !command.flag("dry") {
            if project.result.up_to_date {
                writeln!(
                    stdout,
                    "Project '{}' is up to date",
                    project.config_path.display()
                )
                .expect("writing to Vec cannot fail");
            } else {
                writeln!(
                    stdout,
                    "Building project '{}'...",
                    project.config_path.display()
                )
                .expect("writing to Vec cannot fail");
            }
        }
        let outcome = project_result_outcome(command, &project.result);
        stdout.extend_from_slice(&outcome.stdout);
        has_errors |= outcome.exit_code != TscExitStatus::Success.code();
        if command.flag("dry") {
            writeln!(stdout, "Would build {}", project.config_path.display())
                .expect("writing to Vec cannot fail");
        } else if !project.result.up_to_date {
            publish_project_result(&project.result)?;
            outputs_generated |= project.result.emitted;
        }
    }
    has_errors |= !report.blocked.is_empty();
    Ok(CommandOutcome {
        stdout,
        stderr: Vec::new(),
        exit_code: TscExitStatus::from_compilation(has_errors, outputs_generated).code(),
        truncation: None,
    })
}

fn project_overrides(command: &ParsedTscCommand) -> ProjectOptionOverrides {
    let boolean = |name: &str| command.options.get(name).and_then(|value| value.as_bool());
    let string = |name: &str| command.option_str(name).map(Arc::<str>::from);
    ProjectOptionOverrides {
        no_emit: boolean("noEmit"),
        no_emit_on_error: boolean("noEmitOnError"),
        declaration: boolean("declaration"),
        declaration_map: boolean("declarationMap"),
        source_map: boolean("sourceMap"),
        inline_source_map: boolean("inlineSourceMap"),
        inline_sources: boolean("inlineSources"),
        out_dir: command.option_str("outDir").map(PathBuf::from),
        root_dir: command.option_str("rootDir").map(PathBuf::from),
        map_root: command.option_str("mapRoot").map(Arc::from),
        out_file: command
            .option_str("outFile")
            .or_else(|| command.option_str("out"))
            .map(PathBuf::from),
        always_strict: boolean("alwaysStrict"),
        ts_build_info_file: command.option_str("tsBuildInfoFile").map(PathBuf::from),
        strict: boolean("strict"),
        no_implicit_any: boolean("noImplicitAny"),
        strict_null_checks: boolean("strictNullChecks"),
        strict_property_initialization: boolean("strictPropertyInitialization"),
        allow_js: boolean("allowJs"),
        check_js: boolean("checkJs"),
        jsx: command.option_str("jsx").map(Arc::from),
        source_root: command.option_str("sourceRoot").map(Arc::from),
        target: string("target"),
        module: string("module"),
        module_resolution: string("moduleResolution"),
        module_detection: string("moduleDetection"),
        new_line: string("newLine"),
        jsx_factory: string("jsxFactory"),
        jsx_fragment_factory: string("jsxFragmentFactory"),
        jsx_import_source: string("jsxImportSource"),
        resolve_json_module: boolean("resolveJsonModule"),
        declaration_dir: command.option_str("declarationDir").map(PathBuf::from),
        base_url: command.option_str("baseUrl").map(PathBuf::from),
        emit_declaration_only: boolean("emitDeclarationOnly"),
        incremental: boolean("incremental"),
        composite: boolean("composite"),
        es_module_interop: boolean("esModuleInterop"),
        isolated_modules: boolean("isolatedModules"),
        verbatim_module_syntax: boolean("verbatimModuleSyntax"),
        trace_resolution: boolean("traceResolution"),
        lib: command
            .options
            .get("lib")
            .and_then(|value| value.as_list())
            .map(|items| Arc::from(items.to_vec())),
    }
}

fn project_config_path(cwd: &Path, path: &str) -> PathBuf {
    let path = PathBuf::from(path);
    let path = if path.is_absolute() {
        path
    } else {
        cwd.join(path)
    };
    resolve_config_file_name(path)
}

fn publish_project_result(result: &ProjectCompileResult) -> Result<(), DriverError> {
    let mut atomic = StdAtomicFs;
    for (path, bytes) in &result.outputs.files {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|source| DriverError::CreateDirectory {
                path: parent.to_path_buf(),
                source,
            })?;
        }
        publish_atomic(&mut atomic, path, bytes).map_err(|error| DriverError::ProjectConfig {
            path: path.clone(),
            message: error.to_string(),
        })?;
    }
    if let Some((path, info)) = &result.build_info {
        let bytes = info.encode().map_err(|error| DriverError::ProjectConfig {
            path: path.clone(),
            message: error.to_string(),
        })?;
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|source| DriverError::CreateDirectory {
                path: parent.to_path_buf(),
                source,
            })?;
        }
        publish_atomic(&mut atomic, path, &bytes).map_err(|error| DriverError::ProjectConfig {
            path: path.clone(),
            message: error.to_string(),
        })?;
    }
    Ok(())
}

fn project_result_outcome(
    command: &ParsedTscCommand,
    result: &ProjectCompileResult,
) -> CommandOutcome {
    let diagnostics = map_parse_diagnostics(&result.diagnostics);
    let has_errors = diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error);
    let names = result
        .sources
        .iter()
        .map(|source| source.path.to_string_lossy())
        .collect::<Vec<_>>();
    let sources = result
        .sources
        .iter()
        .zip(&names)
        .map(|(source, name)| DiagnosticSource {
            id: source.id,
            name,
            text: &source.text,
        })
        .collect::<Vec<_>>();
    let format = if command.pretty() {
        TscDiagnosticFormat::Pretty
    } else {
        TscDiagnosticFormat::PrettyFalse
    };
    let mut stdout = if command.flag("listFilesOnly") {
        Vec::new()
    } else {
        tsc_diagnostics::render(format, &diagnostics, &sources).into_bytes()
    };
    if command.flag("listFiles") || command.flag("listFilesOnly") {
        for name in &names {
            writeln!(stdout, "{name}").expect("writing to Vec cannot fail");
        }
    }
    CommandOutcome {
        stdout,
        exit_code: if command.flag("listFilesOnly") {
            TscExitStatus::Success.code()
        } else {
            TscExitStatus::from_compilation(has_errors, result.emitted).code()
        },
        ..CommandOutcome::default()
    }
}

fn project_compile_error_outcome(
    error: ProjectCompileError,
    command: &ParsedTscCommand,
    cwd: &Path,
) -> CommandOutcome {
    match error {
        unsupported @ ProjectCompileError::UnsupportedOption { .. } => {
            not_implemented(&unsupported.to_string())
        }
        ProjectCompileError::ConfigNotFound { path } => {
            config_not_found_outcome(command, cwd, &path)
        }
        ProjectCompileError::Materialize(
            materialize @ (MaterializeError::FilesListEmpty { .. }
            | MaterializeError::NoInputs { .. }),
        ) => project_diagnostic_outcome(materialize.to_string()),
        other => project_error_outcome(other.to_string()),
    }
}

fn config_not_found_outcome(
    command: &ParsedTscCommand,
    cwd: &Path,
    config_path: &Path,
) -> CommandOutcome {
    let Some(project) = command.project() else {
        return tsc_error_outcome(
            "TS5081",
            format!(
                "Cannot find a tsconfig.json file at the current directory: {}.",
                config_path.display()
            ),
        );
    };
    let project_path = Path::new(project);
    if project_path
        .extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| extension.eq_ignore_ascii_case("json"))
    {
        return tsc_error_outcome(
            "TS5083",
            format!("Cannot read file '{}'.", config_path.display()),
        );
    }
    let directory = if project_path.is_absolute() {
        project_path.to_path_buf()
    } else {
        cwd.join(project_path)
    };
    tsc_error_outcome(
        "TS5057",
        format!(
            "Cannot find a tsconfig.json file at the specified directory: '{}'.",
            directory.display()
        ),
    )
}

fn project_diagnostic_outcome(message: String) -> CommandOutcome {
    CommandOutcome {
        stdout: format!("error {message}\n").into_bytes(),
        exit_code: TscExitStatus::DiagnosticsPresentOutputsSkipped.code(),
        ..CommandOutcome::default()
    }
}

fn project_error_outcome(message: String) -> CommandOutcome {
    tsc_error_outcome("TS5083", message)
}

fn tsc_error_outcome(code: &str, message: String) -> CommandOutcome {
    CommandOutcome {
        stdout: format!("error {code}: {message}\n").into_bytes(),
        exit_code: TscExitStatus::DiagnosticsPresentOutputsSkipped.code(),
        ..CommandOutcome::default()
    }
}

fn not_implemented(message: &str) -> CommandOutcome {
    CommandOutcome {
        stderr: format!("error TS5047: {message}\n").into_bytes(),
        exit_code: TscExitStatus::NotImplemented.code(),
        ..CommandOutcome::default()
    }
}

fn unsupported_option_outcome(option: &str) -> CommandOutcome {
    not_implemented(&format!(
        "Compiler option '--{option}' has no canonical native driver mapping."
    ))
}

// ---------------------------------------------------------------------------
// `--showConfig`: borrowed TypeScript 7.0.2 configuration serialization.
//
// The document is a `serde::Serialize` view over the immutable
// `bamts_compiler::project::JsonValue` graph. Nothing is cloned into
// `serde_json::Value`; rendering walks the borrowed entries in declaration
// order so the output is byte-deterministic. Serialization failure is typed,
// not unwrapped: [`DriverError::ShowConfigRender`] carries the io error.
// ---------------------------------------------------------------------------

/// Renders one borrowed effective-configuration document as TypeScript
/// `--showConfig` bytes: four-space `serde_json` indentation plus exactly one
/// trailing newline. The writer failure is the io error itself, and a JSON
/// serialization failure (non-finite number) is reported as io::InvalidData
/// through the same typed [`DriverError::ShowConfigRender`] channel.
fn render_show_config_document<T: Serialize>(document: &T) -> Result<Vec<u8>, DriverError> {
    let mut buffer = Vec::new();
    let mut serializer = serde_json::Serializer::with_formatter(
        &mut buffer,
        serde_json::ser::PrettyFormatter::with_indent(b"    "),
    );
    document
        .serialize(&mut serializer)
        .map_err(|error| DriverError::ShowConfigRender {
            source: io::Error::new(io::ErrorKind::InvalidData, error.to_string()),
        })?;
    buffer.push(b'\n');
    Ok(buffer)
}

/// One typed key/value slot of the direct-route `--showConfig` document.
/// Direct dispatch emits only options explicitly supplied on the command
/// line, in the lexical order of the parsed `BTreeMap` — which matches
/// TypeScript 7.0.2's observed output order (verified by probe: `strict`
/// precedes `target` regardless of argv order). Enum values were already
/// canonicalized to lower case by the argv parser.
enum DirectCompilerOption<'a> {
    Bool(bool),
    Text(&'a str),
    Items(&'a [String]),
    Number(i32),
}

impl Serialize for DirectCompilerOption<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Bool(value) => serializer.serialize_bool(*value),
            Self::Text(value) => serializer.serialize_str(value),
            Self::Items(values) => serializer.collect_seq(values.iter()),
            Self::Number(value) => serializer.serialize_i32(*value),
        }
    }
}

/// The direct-route `--showConfig` document: effective CLI compiler options
/// plus the argv file list, rendered relative to the process working
/// directory with TypeScript's `./` prefix (probe-verified).
struct DirectShowConfig<'a> {
    command: &'a ParsedTscCommand,
    cwd: &'a Path,
}

impl Serialize for DirectShowConfig<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let options: Vec<(&'static str, DirectCompilerOption<'_>)> =
            direct_compiler_options(self.command).collect();
        let files: Vec<String> = self
            .command
            .file_names
            .iter()
            .map(|name| {
                let path = self.cwd.join(name);
                ProjectShowConfig::relative_path(self.cwd, &path)
            })
            .collect();
        let mut state = serializer.serialize_map(Some(2))?;
        state.serialize_entry("compilerOptions", &SerializeMapEntries(options.iter()))?;
        state.serialize_entry("files", &files)?;
        state.end()
    }
}

/// Serializes a borrowed compiler-option sequence as a JSON object so the
/// document keeps TypeScript's key order instead of a struct field order.
struct SerializeMapEntries<I>(I);

impl<'a> Serialize
    for SerializeMapEntries<std::slice::Iter<'a, (&'static str, DirectCompilerOption<'a>)>>
{
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut state = serializer.serialize_map(Some(self.0.len()))?;
        for (key, value) in self.0.clone() {
            state.serialize_entry(key, value)?;
        }
        state.end()
    }
}

/// Borrowed compiler-options serializer: emits the canonical explicit
/// `JsonObject` entries first, then the synthesized implied entries,
/// inside one `compilerOptions` map — matching TypeScript 7.0.2, which
/// nests implied options inside `compilerOptions` rather than emitting
/// them as top-level document keys.
struct CompilerOptionsView<'a> {
    canonical: &'a JsonValue,
    implied: &'a [(String, JsonValue)],
}

impl Serialize for CompilerOptionsView<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.canonical {
            JsonValue::Object(explicit) => {
                let mut state = serializer
                    .serialize_map(Some(explicit.entries().len() + self.implied.len()))?;
                for (key, value) in explicit.entries() {
                    state.serialize_entry(key.as_ref(), &JsonViewRef(value))?;
                }
                for (name, value) in self.implied {
                    state.serialize_entry(name.as_str(), &JsonViewRef(value))?;
                }
                state.end()
            }
            other => JsonViewRef(other).serialize(serializer),
        }
    }
}

struct ProjectShowConfig<'a> {
    project: &'a EffectiveProject,
}

impl<'a> ProjectShowConfig<'a> {
    fn new(project: &'a EffectiveProject) -> Self {
        Self { project }
    }

    /// Lexical relative path from `base` to `path` in TypeScript showConfig
    /// form: descendants and equal paths get a leading `./`, parents and
    /// siblings use `../` components. Both inputs are absolute; incompatible
    /// Windows prefixes or roots fall back to the absolute path text rather
    /// than producing a meaningless cross-root traversal.
    fn relative_path(base: &Path, path: &Path) -> String {
        /// Splits an absolute path into its filesystem root (prefix +
        /// rootdir) and the remaining normal components. Non-normal
        /// components (`.`, `..`) cause `None` so the caller falls back
        /// to the absolute text instead of mis-rendering.
        fn split_absolute(p: &Path) -> Option<(String, Vec<String>)> {
            let mut root = String::new();
            let mut normals = Vec::new();
            for component in p.components() {
                match component {
                    std::path::Component::Prefix(prefix) => {
                        root.push_str(&prefix.as_os_str().to_string_lossy());
                    }
                    std::path::Component::RootDir => {
                        root.push('/');
                    }
                    std::path::Component::Normal(segment) => {
                        normals.push(
                            segment
                                .to_string_lossy()
                                .replace(std::path::MAIN_SEPARATOR, "/"),
                        );
                    }
                    std::path::Component::CurDir | std::path::Component::ParentDir => return None,
                }
            }
            if root.is_empty() {
                return None;
            }
            Some((root, normals))
        }
        let Some((base_root, base_normals)) = split_absolute(base) else {
            return path
                .to_string_lossy()
                .replace(std::path::MAIN_SEPARATOR, "/");
        };
        let Some((path_root, path_normals)) = split_absolute(path) else {
            return path
                .to_string_lossy()
                .replace(std::path::MAIN_SEPARATOR, "/");
        };
        if base_root != path_root {
            return path
                .to_string_lossy()
                .replace(std::path::MAIN_SEPARATOR, "/");
        }
        let shared = base_normals
            .iter()
            .zip(path_normals.iter())
            .take_while(|(from, to)| from == to)
            .count();
        let mut relative = String::new();
        for _ in shared..base_normals.len() {
            relative.push_str("../");
        }
        if relative.is_empty() {
            relative.push_str("./");
        }
        relative.push_str(&path_normals[shared..].join("/"));
        relative
    }
}

impl Serialize for ProjectShowConfig<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let raw = self.project.config().config().raw();
        let config_directory = self
            .project
            .config_path()
            .parent()
            .expect("config path always has a parent directory");

        let mut state = serializer.serialize_map(None)?;
        let empty_object = JsonValue::Object(JsonObject::from_entries(Vec::new()));
        let compiler_options = raw.get("compilerOptions").unwrap_or(&empty_object);
        let canonical = canonicalize_compiler_options(compiler_options, config_directory);
        // TypeScript 7.0.2 nests the implied options it reports for the
        // supported target/module surface inside `compilerOptions`, appended
        // after the explicit entries. Each implication applies only when the
        // user did not set the option explicitly.
        let implied: Vec<(String, JsonValue)> = implied_compiler_options(raw);
        state.serialize_entry(
            "compilerOptions",
            &CompilerOptionsView {
                canonical: &canonical,
                implied: &implied,
            },
        )?;
        let references: Vec<SerializeReferenceEntry> = self
            .project
            .references()
            .iter()
            .map(|reference| SerializeReferenceEntry {
                base: config_directory,
                path: reference.path(),
            })
            .collect();
        if !references.is_empty() {
            state.serialize_entry("references", &references)?;
        }
        let files: Vec<String> = self
            .project
            .source_files()
            .iter()
            .map(|path| Self::relative_path(config_directory, path))
            .collect();
        if !files.is_empty() {
            state.serialize_entry("files", &files)?;
        }
        if let Some(include) = raw.get("include") {
            let paths: Vec<String> = include
                .as_array()
                .into_iter()
                .flatten()
                .map(|value| {
                    Self::relative_path(
                        config_directory,
                        Path::new(value.as_str().expect("include entry is a string")),
                    )
                })
                .collect();
            state.serialize_entry("include", &paths)?;
        }
        if let Some(exclude) = raw.get("exclude") {
            let paths: Vec<String> = exclude
                .as_array()
                .into_iter()
                .flatten()
                .map(|value| {
                    Self::relative_path(
                        config_directory,
                        Path::new(value.as_str().expect("exclude entry is a string")),
                    )
                })
                .collect();
            state.serialize_entry("exclude", &paths)?;
        }

        state.end()
    }
}

/// Rewrites compiler-option values onto their canonical TypeScript form:
/// enum values are lower-cased (`ES2022` → `es2022`, `NODE16` →
/// `node16`, …), and path-like fields that the effective-config loader
/// rewrote to absolute form are relativized back against the config
/// directory so the output matches TypeScript's `--showConfig` text.
fn canonicalize_compiler_options(options: &JsonValue, config_directory: &Path) -> JsonValue {
    const ENUM_OPTIONS: &[&str] = &[
        "target",
        "module",
        "jsx",
        "moduleResolution",
        "moduleDetection",
        "newLine",
    ];
    const PATH_FIELDS: &[&str] = &[
        "baseUrl",
        "rootDir",
        "outDir",
        "declarationDir",
        "outFile",
        "tsBuildInfoFile",
    ];
    let Some(object) = options.as_object() else {
        return options.clone();
    };
    let base_url = object
        .get("baseUrl")
        .and_then(JsonValue::as_str)
        .map(PathBuf::from)
        .unwrap_or_else(|| config_directory.to_path_buf());
    let entries = object
        .entries()
        .iter()
        .map(|(key, value)| {
            let key_str = key.as_ref();
            let value = if ENUM_OPTIONS.contains(&key_str) {
                match value {
                    JsonValue::String(text) => {
                        JsonValue::String(Arc::from(text.to_ascii_lowercase().as_str()))
                    }
                    other => other.clone(),
                }
            } else if PATH_FIELDS.contains(&key_str) {
                match value {
                    JsonValue::String(text) => JsonValue::String(Arc::from(
                        ProjectShowConfig::relative_path(config_directory, Path::new(&**text))
                            .as_str(),
                    )),
                    other => other.clone(),
                }
            } else if key_str == "typeRoots" {
                match value {
                    JsonValue::Array(items) => {
                        let relativized: Vec<JsonValue> = items
                            .iter()
                            .map(|item| {
                                let text = item.as_str().expect("typeRoots entry is a string");
                                JsonValue::String(Arc::from(
                                    ProjectShowConfig::relative_path(
                                        config_directory,
                                        Path::new(text),
                                    )
                                    .as_str(),
                                ))
                            })
                            .collect();
                        JsonValue::Array(Arc::from(relativized))
                    }
                    other => other.clone(),
                }
            } else if key_str == "paths" {
                match value {
                    JsonValue::Object(mappings) => {
                        let rewritten: Vec<(Arc<str>, JsonValue)> = mappings
                            .entries()
                            .iter()
                            .map(|(pattern, targets)| {
                                let relativized = match targets {
                                    JsonValue::Array(items) => {
                                        let relativized: Vec<JsonValue> = items
                                            .iter()
                                            .map(|item| {
                                                let text = item
                                                    .as_str()
                                                    .expect("paths target is a string");
                                                JsonValue::String(Arc::from(
                                                    ProjectShowConfig::relative_path(
                                                        &base_url,
                                                        Path::new(text),
                                                    )
                                                    .as_str(),
                                                ))
                                            })
                                            .collect();
                                        JsonValue::Array(Arc::from(relativized))
                                    }
                                    other => other.clone(),
                                };
                                (Arc::clone(pattern), relativized)
                            })
                            .collect();
                        JsonValue::Object(JsonObject::from_entries(rewritten))
                    }
                    other => other.clone(),
                }
            } else {
                match value {
                    JsonValue::Object(nested) => canonicalize_compiler_options(
                        &JsonValue::Object(nested.clone()),
                        config_directory,
                    ),
                    other => other.clone(),
                }
            };
            (key.clone(), value)
        })
        .collect();
    JsonValue::Object(JsonObject::from_entries(entries))
}

/// Computes the implied compiler options TypeScript 7.0.2 appends to a
/// project `--showConfig` document, derived from observable CLI probes:
/// - `module` implies `moduleResolution` (node16/node18 → "node16",
///   node20/nodenext → that module) and `moduleDetection: "force"`;
///   node16/node18 also imply `resolveJsonModule: false`.
/// - `target` implies `module` (pre-es2022 targets → "es6"/"es2020",
///   esnext → "esnext") and `useDefineForClassFields: false` for
///   pre-es2022 targets.
///
/// Every implication applies only when the option is not explicitly set.
fn implied_compiler_options(raw: &JsonObject) -> Vec<(String, JsonValue)> {
    let Some(options) = raw.get("compilerOptions").and_then(JsonValue::as_object) else {
        return Vec::new();
    };
    let text = |name: &str| options.get(name).and_then(JsonValue::as_str);
    let set = |name: &str| options.get(name).is_some();
    let mut implied: Vec<(String, JsonValue)> = Vec::new();

    if let Some(module) = text("module") {
        if !set("moduleResolution") {
            let resolution = match module {
                "node16" | "node18" => Some("node16"),
                "node20" | "nodenext" => Some(module),
                _ => None,
            };
            if let Some(resolution) = resolution {
                implied.push((
                    "moduleResolution".to_owned(),
                    JsonValue::String(Arc::from(resolution)),
                ));
            }
        }
        if !set("moduleDetection") && matches!(module, "node16" | "node18" | "node20" | "nodenext")
        {
            implied.push((
                "moduleDetection".to_owned(),
                JsonValue::String(Arc::from("force")),
            ));
        }
        if !set("resolveJsonModule") && matches!(module, "node16" | "node18") {
            implied.push(("resolveJsonModule".to_owned(), JsonValue::Bool(false)));
        }
    }

    if let Some(target) = text("target") {
        if !set("module") {
            let module = match target {
                "es6" | "es2015" | "es2016" | "es2017" | "es2018" | "es2019" => Some("es6"),
                "es2020" | "es2021" => Some("es2020"),
                "esnext" => Some("esnext"),
                _ => None,
            };
            if let Some(module) = module {
                implied.push(("module".to_owned(), JsonValue::String(Arc::from(module))));
            }
        }
        if !set("useDefineForClassFields")
            && matches!(
                target,
                "es6" | "es2015" | "es2016" | "es2017" | "es2018" | "es2019" | "es2020" | "es2021"
            )
        {
            implied.push(("useDefineForClassFields".to_owned(), JsonValue::Bool(false)));
        }
    }

    implied
}

/// One `references` entry serialized relative to the config directory.
struct SerializeReferenceEntry<'a> {
    base: &'a Path,
    path: &'a Path,
}

impl Serialize for SerializeReferenceEntry<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut state = serializer.serialize_map(Some(1))?;
        state.serialize_entry(
            "path",
            &ProjectShowConfig::relative_path(self.base, self.path),
        )?;
        state.end()
    }
}

/// Renders a showConfig document and wraps it in a success outcome.
fn show_config_outcome<T: Serialize>(document: &T) -> Result<CommandOutcome, DriverError> {
    Ok(CommandOutcome {
        stdout: render_show_config_document(document)?,
        exit_code: TscExitStatus::Success.code(),
        ..CommandOutcome::default()
    })
}

/// Iterates the parsed direct command in the lexical order of the
/// `BTreeMap`, which matches TypeScript 7.0.2's observed output order
/// (verified by probe: `strict` precedes `target` for both argv orders).
/// Only parser-validated option names are emitted.
fn direct_compiler_options(
    command: &ParsedTscCommand,
) -> impl Iterator<Item = (&'static str, DirectCompilerOption<'_>)> {
    command.options.iter().filter_map(|(name, value)| {
        // Dispatch controls are consumed by routing, not compiler state.
        if matches!(
            name.as_str(),
            "help" | "version" | "init" | "showConfig" | "ignoreConfig" | "pretty" | "project"
        ) {
            return None;
        }
        let name = crate::cli::tsc_args::canonical_option_name(name)?;
        let value = match value {
            TscOptionValue::Bool(value) => DirectCompilerOption::Bool(*value),
            TscOptionValue::String(value) => DirectCompilerOption::Text(value.as_str()),
            TscOptionValue::Number(value) => DirectCompilerOption::Number(*value),
            TscOptionValue::List(values) => DirectCompilerOption::Items(values.as_slice()),
            TscOptionValue::Null => return None,
        };
        Some((name, value))
    })
}

/// Shared serializer body over any referenced JSON value.
struct JsonViewRef<'a>(&'a JsonValue);

impl Serialize for JsonViewRef<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.0 {
            JsonValue::Null => serializer.serialize_none(),
            JsonValue::Bool(value) => serializer.serialize_bool(*value),
            JsonValue::Number(value) => {
                if let Ok(number) = value.parse::<i64>() {
                    serializer.serialize_i64(number)
                } else if let Ok(number) = value.parse::<u64>() {
                    serializer.serialize_u64(number)
                } else if let Ok(number) = value.parse::<f64>() {
                    serializer.serialize_f64(number)
                } else {
                    Err(serde::ser::Error::custom(format!(
                        "invalid JSON number {value:?}"
                    )))
                }
            }
            JsonValue::String(value) => serializer.serialize_str(value),
            JsonValue::Array(values) => {
                let mut state = serializer.serialize_seq(Some(values.len()))?;
                for value in values.iter() {
                    state.serialize_element(&JsonViewRef(value))?;
                }
                state.end()
            }
            JsonValue::Object(object) => {
                let mut state = serializer.serialize_map(Some(object.entries().len()))?;
                for (key, value) in object.entries() {
                    state.serialize_entry(key.as_ref(), &JsonViewRef(value))?;
                }
                state.end()
            }
        }
    }
}

fn levels(args: &CliArgs, project_root: &Path) -> Result<LintTable, DriverError> {
    let profile = if args.pedantic {
        LintProfile::Pedantic
    } else if args.strict {
        LintProfile::Strict
    } else {
        LintProfile::Default
    };
    let mut levels = LintTable::new(profile);
    let path = project_root.join("bamts.toml");
    if path.is_file() {
        let source = fs::read_to_string(&path).map_err(|source| DriverError::ReadSource {
            path: path.clone(),
            source,
        })?;
        let config = parse_bamts_toml(&source).map_err(|error| DriverError::LintConfig {
            path: path.clone(),
            message: error.to_string(),
        })?;
        levels
            .apply_config(&config)
            .map_err(forbidden_lint_override)?;
    }
    let overrides = args.lint_overrides.iter().map(|override_arg| {
        let flag = match override_arg.level {
            bamts_compiler::lint::LintLevel::Allow => "-A",
            bamts_compiler::lint::LintLevel::Warn => "-W",
            bamts_compiler::lint::LintLevel::Deny => "-D",
            bamts_compiler::lint::LintLevel::Forbid => "-F",
        };
        LintOverride::new(
            override_arg.selector.as_str(),
            override_arg.level,
            format!("{flag} {}", override_arg.selector),
        )
    });
    levels
        .apply_cli(overrides)
        .map_err(forbidden_lint_override)?;
    Ok(levels)
}

fn forbidden_lint_override(error: bamts_compiler::lint::ForbidOverrideError) -> DriverError {
    DriverError::Usage(ArgsError::ForbiddenLintOverride {
        rule: error.rule().slug().to_string(),
        forbidden_by: error.forbidden_by().to_string(),
        lowered_by: error.lowered_by().to_string(),
    })
}

fn lower_options(args: &CliArgs) -> LowerOptions {
    LowerOptions {
        javascript_compatibility: args.js_compat.enabled,
    }
}

fn check(args: &CliArgs, frontend: &LoadedProgramFrontend) -> Result<CommandOutcome, DriverError> {
    let diagnostics = render_program_diagnostics(args, frontend);
    if frontend
        .output
        .modules()
        .iter()
        .any(|module| module.has_errors())
    {
        return Err(DriverError::Diagnostics {
            rendered: diagnostics.text,
            truncation: diagnostics.truncation,
        });
    }
    Ok(CommandOutcome {
        stderr: diagnostics.text.into_bytes(),
        truncation: diagnostics.truncation,
        ..CommandOutcome::default()
    })
}

fn compile_in_context_with_cancel(
    args: &CliArgs,
    frontend: &LoadedProgramFrontend,
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<CommandOutcome, DriverError> {
    if !args.extra_inputs.is_empty() {
        return Err(DriverError::MultipleCompileInputs);
    }
    if args.target != ExecutionTarget::Aot {
        return Err(DriverError::UnsupportedCompileTarget(args.target));
    }
    if args.output.emit_declarations {
        return Err(DriverError::UnsupportedOutputOption("--emit-declarations"));
    }
    if args.output.source_maps {
        return Err(DriverError::UnsupportedOutputOption("--source-maps"));
    }

    let entrypoint = required_entrypoint(args)?;
    let warnings = require_clean_frontend(args, frontend)?;
    let executable = lower_program_with_cancel(
        &frontend.program,
        &frontend.output,
        lower_options(args),
        cancel,
    )
    .map_err(DriverError::Lower)?;
    if BUILD_TARGET != HOST_TARGET {
        return Err(DriverError::CrossTargetLink {
            host: HOST_TARGET,
            target: BUILD_TARGET,
        });
    }
    let object = bamts_codegen::compile_aot_with_cancel(executable.wire(), HOST_TARGET, cancel)
        .map_err(|error| match error {
            bamts_codegen::AotError::Cancelled => DriverError::Cancelled,
            error => DriverError::Aot(error),
        })?;
    let destination = output_path(args, entrypoint, context)?;
    link_executable(&object.bytes, &destination, context, cancel)?;
    Ok(CommandOutcome {
        stderr: warnings.text.into_bytes(),
        truncation: warnings.truncation,
        ..CommandOutcome::default()
    })
}

fn run_in_context_with_cancel(
    args: &CliArgs,
    frontend: &LoadedProgramFrontend,
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<CommandOutcome, DriverError> {
    let entrypoint = required_entrypoint(args)?;
    let warnings = require_clean_frontend(args, frontend)?;
    let executable = lower_program_with_cancel(
        &frontend.program,
        &frontend.output,
        lower_options(args),
        cancel,
    )
    .map_err(DriverError::Lower)?;
    match args.target {
        ExecutionTarget::Jit => run_jit(args, entrypoint, warnings, &executable, context, cancel),
        ExecutionTarget::Aot => run_aot(args, entrypoint, warnings, &executable, context, cancel),
    }
}

fn run_jit(
    args: &CliArgs,
    entrypoint: &Path,
    warnings: RenderedDiagnostics,
    executable: &bamts_compiler::program::ExecutableProgram,
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<CommandOutcome, DriverError> {
    let program =
        bamts_codegen::compile_jit_with_cancel(executable.wire(), cancel).map_err(|error| {
            match error {
                bamts_codegen::JitError::Cancelled => DriverError::Cancelled,
                error => DriverError::Jit(error),
            }
        })?;
    let mut host = bamts_node::NodeHost::new();
    populate_node_environment(&mut host, context)?;
    host.set_script_compiler(Box::new(bamts::ScriptCompiler));
    host.set_argv(
        ["bamts".to_owned(), entrypoint.display().to_string()]
            .into_iter()
            .chain(args.program_args.iter().cloned()),
    );
    let outcome = run_linked_program_with_cancel(
        executable.wire(),
        &program,
        &mut host,
        &Limits::default(),
        cancel.clone(),
    )
    .map_err(DriverError::Native)?;
    let mut stdout = host.stdout().to_vec();
    stdout.extend_from_slice(&outcome.stdout);
    let exit_code = host.completion_exit_code(outcome.exit_code);
    let mut stderr = warnings.text.into_bytes();
    stderr.extend_from_slice(host.stderr());
    Ok(CommandOutcome {
        stdout,
        stderr,
        exit_code,
        truncation: warnings.truncation,
    })
}

fn run_aot(
    args: &CliArgs,
    entrypoint: &Path,
    warnings: RenderedDiagnostics,
    executable: &bamts_compiler::program::ExecutableProgram,
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<CommandOutcome, DriverError> {
    if BUILD_TARGET != HOST_TARGET {
        return Err(DriverError::CrossTargetLink {
            host: HOST_TARGET,
            target: BUILD_TARGET,
        });
    }
    let object = bamts_codegen::compile_aot_with_cancel(executable.wire(), HOST_TARGET, cancel)
        .map_err(|error| match error {
            bamts_codegen::AotError::Cancelled => DriverError::Cancelled,
            error => DriverError::Aot(error),
        })?;
    let id = NEXT_CACHE_TEMP_ID.fetch_add(1, Ordering::Relaxed);
    let root = cache_root(context)?;
    let destination = root.join("run").join(format!(
        "bamts-run-{}-{id}{}",
        std::process::id(),
        std::env::consts::EXE_SUFFIX
    ));
    require_within_cache_root(&destination, &root)?;
    link_executable(&object.bytes, &destination, context, cancel)?;
    let _published = claim_published_executable(&destination, cancel)?;
    require_within_cache_root(&destination, &root)?;
    let launch_token = format!("{}-{id}", std::process::id());
    let mut command = Command::new(&destination);
    command
        .current_dir(context.cwd())
        .env_clear()
        .envs(context.envs())
        .env(bamts_node::AOT_ENTRYPOINT_ENV, entrypoint.as_os_str())
        .env(bamts_node::AOT_LAUNCH_TOKEN_ENV, &launch_token)
        .arg(launch_token)
        .args(&args.program_args);
    let output = capture_process_with_cancel(&mut command, cancel);
    let output = output
        .map_err(|source| DriverError::LinkStart {
            program: destination.into_os_string(),
            source,
        })?
        .ok_or(DriverError::Cancelled)?;
    let mut stderr = warnings.text.into_bytes();
    stderr.extend_from_slice(&output.stderr);
    Ok(CommandOutcome {
        stdout: output.stdout,
        stderr,
        exit_code: output.status.code().unwrap_or(1),
        truncation: warnings.truncation,
    })
}
#[derive(Debug)]
struct PublishedExecutable {
    path: PathBuf,
}

impl Drop for PublishedExecutable {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn claim_published_executable(
    destination: &Path,
    cancel: &CancellationToken,
) -> Result<PublishedExecutable, DriverError> {
    let published = PublishedExecutable {
        path: destination.to_owned(),
    };
    cancel.check().map_err(|_| DriverError::Cancelled)?;
    Ok(published)
}

fn populate_node_environment(
    host: &mut bamts_node::NodeHost,
    context: &ExecutionContext,
) -> Result<(), DriverError> {
    for (name, value) in context.envs() {
        let name = name
            .to_str()
            .ok_or(DriverError::NonUnicodeEnvironmentName)?;
        let value = value
            .to_str()
            .ok_or_else(|| DriverError::NonUnicodeEnvironmentValue {
                name: name.to_owned(),
            })?;
        host.set_env(name, value);
    }
    Ok(())
}

fn capture_process_with_cancel(
    command: &mut Command,
    cancel: &CancellationToken,
) -> io::Result<Option<Output>> {
    configure_managed_process(command);
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let Some(stdout) = child.stdout.take() else {
        let _ = terminate_managed_process(&mut child);
        return Err(io::Error::other("managed child stdout was not piped"));
    };
    let Some(stderr) = child.stderr.take() else {
        let _ = terminate_managed_process(&mut child);
        return Err(io::Error::other("managed child stderr was not piped"));
    };
    let (stdout_reader, stdout_completion) = spawn_child_pipe_reader(stdout);
    let (stderr_reader, stderr_completion) = spawn_child_pipe_reader(stderr);

    let mut status = None;
    let mut stdout_complete = false;
    let mut stderr_complete = false;
    loop {
        if cancel.is_cancelled() {
            let _ = terminate_managed_process(&mut child);
            let _ = join_child_pipe(stdout_reader);
            let _ = join_child_pipe(stderr_reader);
            return Ok(None);
        }
        for (completion, complete) in [
            (&stdout_completion, &mut stdout_complete),
            (&stderr_completion, &mut stderr_complete),
        ] {
            if !*complete {
                match completion.try_recv() {
                    Ok(Ok(())) => *complete = true,
                    Ok(Err(error)) => {
                        let _ = terminate_managed_process(&mut child);
                        let _ = join_child_pipe(stdout_reader);
                        let _ = join_child_pipe(stderr_reader);
                        return Err(error);
                    }
                    Err(TryRecvError::Disconnected) => {
                        let _ = terminate_managed_process(&mut child);
                        let stdout = join_child_pipe(stdout_reader);
                        let stderr = join_child_pipe(stderr_reader);
                        return stdout.and(stderr).map(|_| None);
                    }
                    Err(TryRecvError::Empty) => {}
                }
            }
        }
        if status.is_none() {
            match child.try_wait() {
                Ok(child_status) => status = child_status,
                Err(error) => {
                    let _ = terminate_managed_process(&mut child);
                    let _ = join_child_pipe(stdout_reader);
                    let _ = join_child_pipe(stderr_reader);
                    return Err(error);
                }
            }
        }
        if status.is_some() && stdout_complete && stderr_complete {
            break;
        }
        thread::sleep(Duration::from_millis(5));
    }
    Ok(Some(Output {
        status: status.expect("managed child status is present after loop"),
        stdout: join_child_pipe(stdout_reader)?,
        stderr: join_child_pipe(stderr_reader)?,
    }))
}

fn spawn_child_pipe_reader(
    mut pipe: impl Read + Send + 'static,
) -> (
    thread::JoinHandle<io::Result<Vec<u8>>>,
    Receiver<io::Result<()>>,
) {
    let (completion_sender, completion_receiver) = mpsc::channel();
    let reader = thread::spawn(move || {
        let mut bytes = Vec::new();
        let result = pipe.read_to_end(&mut bytes);
        let completion = result
            .as_ref()
            .map(|_| ())
            .map_err(|error| io::Error::new(error.kind(), error.to_string()));
        let _ = completion_sender.send(completion);
        result.map(|_| bytes)
    });
    (reader, completion_receiver)
}

#[cfg(unix)]
fn configure_managed_process(command: &mut Command) {
    use std::os::unix::process::CommandExt;
    command.process_group(0);
}

#[cfg(not(unix))]
fn configure_managed_process(_command: &mut Command) {}

#[cfg(unix)]
fn terminate_managed_process(child: &mut std::process::Child) -> io::Result<()> {
    let group = rustix::process::Pid::from_child(child);
    let terminated = rustix::process::kill_process_group(group, rustix::process::Signal::KILL)
        .map_err(|source| {
            io::Error::other(format!(
                "cannot terminate managed process group {group}: {source}"
            ))
        });
    if terminated.is_err() {
        let _ = child.kill();
    }
    let waited = child.wait().map(|_| ());
    terminated.and(waited)
}

#[cfg(windows)]
fn terminate_managed_process(child: &mut std::process::Child) -> io::Result<()> {
    let pid = child.id().to_string();
    let terminated = Command::new("taskkill")
        .args(["/PID", &pid, "/T", "/F"])
        .status()
        .and_then(|status| {
            if status.success() {
                Ok(())
            } else {
                Err(io::Error::other(format!(
                    "cannot terminate managed process tree {pid}: taskkill exited with {status}"
                )))
            }
        });
    if terminated.is_err() {
        let _ = child.kill();
    }
    let waited = child.wait().map(|_| ());
    terminated.and(waited)
}

#[cfg(all(not(unix), not(windows)))]
fn terminate_managed_process(child: &mut std::process::Child) -> io::Result<()> {
    child.kill()?;
    child.wait().map(|_| ())
}

fn join_child_pipe(reader: thread::JoinHandle<io::Result<Vec<u8>>>) -> io::Result<Vec<u8>> {
    reader
        .join()
        .map_err(|_| io::Error::other("managed child pipe reader panicked"))?
}

fn required_entrypoint(args: &CliArgs) -> Result<&Path, DriverError> {
    args.entrypoint
        .as_deref()
        .map(Path::new)
        .ok_or(DriverError::MissingEntrypoint)
}

fn output_path(
    args: &CliArgs,
    entrypoint: &Path,
    context: &ExecutionContext,
) -> Result<PathBuf, DriverError> {
    if let Some(file) = &args.output.file {
        return Ok(context.resolve_path(file));
    }
    let file_name = entrypoint
        .file_stem()
        .filter(|name| !name.is_empty())
        .unwrap_or_else(|| OsStr::new("a"));
    let mut file_name = file_name.to_os_string();
    file_name.push(std::env::consts::EXE_SUFFIX);
    if let Some(directory) = &args.output.dir {
        let directory = context.resolve_path(directory);
        fs::create_dir_all(&directory).map_err(|source| DriverError::CreateDirectory {
            path: directory.clone(),
            source,
        })?;
        return Ok(directory.join(file_name));
    }
    Ok(entrypoint.with_file_name(file_name))
}

fn link_executable(
    object: &[u8],
    destination: &Path,
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<(), DriverError> {
    let destination = context.resolve_path(destination);
    let parent = destination.parent().unwrap_or_else(|| Path::new("."));
    fs::create_dir_all(parent).map_err(|source| DriverError::CreateDirectory {
        path: parent.to_owned(),
        source,
    })?;
    let archive = cached_node_archive(context)?;
    let compiler = discover_toolchain(context, cancel)?;
    let temporary = TemporaryLinkFiles::create(parent, &destination)?;
    fs::write(&temporary.object, object).map_err(|source| DriverError::WriteObject {
        path: temporary.object.clone(),
        source,
    })?;

    let mut command = Command::new(&compiler);
    command
        .current_dir(context.cwd())
        .env_clear()
        .envs(context.envs())
        .arg(&temporary.object)
        .arg(&archive)
        .arg("-o")
        .arg(&temporary.executable);
    if cfg!(target_os = "linux") {
        command.args(["-ldl", "-lpthread", "-lm"]);
    }
    let output = capture_process_with_cancel(&mut command, cancel)
        .map_err(|source| DriverError::LinkStart {
            program: compiler.clone(),
            source,
        })?
        .ok_or(DriverError::Cancelled)?;
    if !output.status.success() {
        return Err(DriverError::LinkFailed {
            program: compiler,
            status: output.status,
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        });
    }
    publish_linked_executable(&temporary.executable, &destination)
}

fn discover_toolchain(
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<OsString, DriverError> {
    let program = context
        .env("CC")
        .map_or_else(|| OsString::from("cc"), OsStr::to_os_string);
    probe_toolchain_in_context(program, context, cancel)
}

fn probe_toolchain_in_context(
    program: OsString,
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<OsString, DriverError> {
    let mut command = Command::new(&program);
    command
        .current_dir(context.cwd())
        .env_clear()
        .envs(context.envs())
        .arg("--version");
    match capture_process_with_cancel(&mut command, cancel) {
        Ok(Some(output)) if output.status.success() => Ok(program),
        Ok(Some(output)) => Err(DriverError::ToolchainRejected {
            program,
            status: output.status,
        }),
        Ok(None) => Err(DriverError::Cancelled),
        Err(source) if source.kind() == io::ErrorKind::NotFound => {
            Err(DriverError::ToolchainMissing { program })
        }
        Err(source) => Err(DriverError::ToolchainProbe { program, source }),
    }
}

#[cfg(test)]
fn probe_toolchain(program: OsString) -> Result<OsString, DriverError> {
    let context = ExecutionContext::ambient()?;
    probe_toolchain_in_context(program, &context, &CancellationToken::new())
}
fn cached_node_archive(context: &ExecutionContext) -> Result<PathBuf, DriverError> {
    let cache_dir = cache_root(context)?.join("runtime");
    fs::create_dir_all(&cache_dir).map_err(|source| DriverError::CacheArchive {
        path: cache_dir.clone(),
        source,
    })?;
    let extension = if cfg!(target_env = "msvc") {
        "lib"
    } else {
        "a"
    };
    let path = cache_dir.join(format!(
        "bamts-node-{:016x}.{extension}",
        content_hash(NODE_STATICLIB)
    ));
    if path.is_file() {
        return Ok(path);
    }
    let (temporary, mut file) = loop {
        let id = NEXT_CACHE_TEMP_ID.fetch_add(1, Ordering::Relaxed);
        let temporary =
            path.with_extension(format!("{extension}.{}.{}.tmp", std::process::id(), id));
        match OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)
        {
            Ok(file) => break (temporary, file),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(source) => {
                return Err(DriverError::CacheArchive {
                    path: temporary,
                    source,
                });
            }
        }
    };
    if let Err(error) = write_cached_archive(&mut file, &temporary) {
        drop(file);
        let _ = fs::remove_file(&temporary);
        return Err(error);
    }
    drop(file);
    match fs::rename(&temporary, &path) {
        Ok(()) => Ok(path),
        Err(_error) if path.is_file() => {
            let _ = fs::remove_file(&temporary);
            Ok(path)
        }
        Err(source) => {
            let _ = fs::remove_file(&temporary);
            Err(DriverError::CacheArchive { path, source })
        }
    }
}

fn write_cached_archive(file: &mut File, path: &Path) -> Result<(), DriverError> {
    file.write_all(NODE_STATICLIB)
        .and_then(|()| file.sync_all())
        .map_err(|source| DriverError::CacheArchive {
            path: path.to_owned(),
            source,
        })
}

fn cache_root(context: &ExecutionContext) -> Result<PathBuf, DriverError> {
    if let Some(path) = context.env("BAMTS_CACHE_DIR") {
        return Ok(context.resolve_path(path));
    }
    if let Some(path) = context.env("XDG_CACHE_HOME") {
        return Ok(context.resolve_path(path).join("bamts"));
    }
    if let Some(path) = context.env("HOME") {
        return Ok(context.resolve_path(path).join(".cache/bamts"));
    }
    ensure_private_fallback_cache_root_in_context(
        fallback_cache_root_path_in_context(context)?,
        context,
    )
}

#[cfg(unix)]
fn fallback_cache_root_path_in_context(context: &ExecutionContext) -> Result<PathBuf, DriverError> {
    let parent = validate_fallback_parent_chain_in_context(context.temp_dir(), context)?;
    Ok(parent.join(format!(
        "bamts-cache-{}",
        fallback_cache_user_key_in_context(context)?
    )))
}

#[cfg(not(unix))]
fn fallback_cache_root_path_in_context(context: &ExecutionContext) -> Result<PathBuf, DriverError> {
    Ok(context.temp_dir().join(format!(
        "bamts-cache-{}",
        fallback_cache_user_key_in_context(context)?
    )))
}

#[cfg(unix)]
fn fallback_cache_user_key_in_context(context: &ExecutionContext) -> Result<String, DriverError> {
    Ok(effective_uid_in_context(context)?.to_string())
}

#[cfg(not(unix))]
fn fallback_cache_user_key_in_context(context: &ExecutionContext) -> Result<String, DriverError> {
    Ok(context
        .env("USERNAME")
        .or_else(|| context.env("USER"))
        .map(|value| value.to_string_lossy().into_owned())
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| "default".to_owned()))
}

#[cfg(all(test, unix))]
fn fallback_cache_root_path() -> Result<PathBuf, DriverError> {
    let context = ExecutionContext::ambient()?;
    fallback_cache_root_path_in_context(&context)
}

fn ensure_private_fallback_cache_root_in_context(
    path: PathBuf,
    context: &ExecutionContext,
) -> Result<PathBuf, DriverError> {
    #[cfg(unix)]
    let path = {
        let parent = path
            .parent()
            .ok_or_else(|| DriverError::UnsafeFallbackCacheRoot { path: path.clone() })?;
        let name = path
            .file_name()
            .ok_or_else(|| DriverError::UnsafeFallbackCacheRoot { path: path.clone() })?;
        validate_fallback_parent_chain_in_context(parent, context)?.join(name)
    };
    match create_private_fallback_dir(&path) {
        Ok(()) => {}
        Err(source) if source.kind() == io::ErrorKind::AlreadyExists => {}
        Err(source) => {
            return Err(DriverError::CreateDirectory { path, source });
        }
    }
    validate_private_fallback_dir_in_context(&path, context)?;
    Ok(path)
}

#[cfg(unix)]
fn create_private_fallback_dir(path: &Path) -> io::Result<()> {
    use std::os::unix::fs::DirBuilderExt;
    fs::DirBuilder::new().mode(0o700).create(path)
}

#[cfg(not(unix))]
fn create_private_fallback_dir(path: &Path) -> io::Result<()> {
    fs::create_dir(path)
}

#[cfg(unix)]
fn validate_fallback_parent_chain_in_context(
    path: &Path,
    context: &ExecutionContext,
) -> Result<PathBuf, DriverError> {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    let canonical = fs::canonicalize(path).map_err(|source| DriverError::CreateDirectory {
        path: path.to_owned(),
        source,
    })?;
    let euid = effective_uid_in_context(context)?;
    for ancestor in canonical.ancestors() {
        let metadata =
            fs::symlink_metadata(ancestor).map_err(|source| DriverError::CreateDirectory {
                path: ancestor.to_owned(),
                source,
            })?;
        let mode = metadata.permissions().mode();
        let writable = mode & 0o022 != 0;
        let owner = metadata.uid();
        let protected_by_sticky_owner = mode & 0o1000 != 0 && (owner == 0 || owner == euid);
        if !metadata.is_dir() || (writable && !protected_by_sticky_owner) {
            return Err(DriverError::UnsafeFallbackCacheRoot {
                path: ancestor.to_owned(),
            });
        }
    }
    Ok(canonical)
}

#[cfg(unix)]
fn validate_private_fallback_dir_in_context(
    path: &Path,
    context: &ExecutionContext,
) -> Result<(), DriverError> {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    let metadata = fs::symlink_metadata(path).map_err(|source| DriverError::CreateDirectory {
        path: path.to_owned(),
        source,
    })?;
    let euid = effective_uid_in_context(context)?;
    let permissions = metadata.permissions().mode() & 0o777;
    if metadata.file_type().is_symlink()
        || !metadata.is_dir()
        || metadata.uid() != euid
        || permissions & 0o077 != 0
    {
        return Err(DriverError::UnsafeFallbackCacheRoot {
            path: path.to_owned(),
        });
    }
    Ok(())
}

#[cfg(not(unix))]
fn validate_private_fallback_dir_in_context(
    path: &Path,
    _context: &ExecutionContext,
) -> Result<(), DriverError> {
    let metadata = fs::metadata(path).map_err(|source| DriverError::CreateDirectory {
        path: path.to_owned(),
        source,
    })?;
    if !metadata.is_dir() {
        return Err(DriverError::UnsafeFallbackCacheRoot {
            path: path.to_owned(),
        });
    }
    Ok(())
}

#[cfg(test)]
fn ensure_private_fallback_cache_root(path: PathBuf) -> Result<PathBuf, DriverError> {
    let context = ExecutionContext::ambient()?;
    ensure_private_fallback_cache_root_in_context(path, &context)
}

#[cfg(all(test, unix))]
fn validate_fallback_parent_chain(path: &Path) -> Result<PathBuf, DriverError> {
    let context = ExecutionContext::ambient()?;
    validate_fallback_parent_chain_in_context(path, &context)
}
/// Probe the effective user id without `unsafe` through an atomic random file.
#[cfg(unix)]
fn effective_uid_in_context(context: &ExecutionContext) -> Result<u32, DriverError> {
    use std::os::unix::fs::MetadataExt;

    let parent = context.temp_dir().to_owned();
    let probe = tempfile::Builder::new()
        .prefix(".bamts-euid-")
        .tempfile_in(&parent)
        .map_err(|source| DriverError::CreateDirectory {
            path: parent,
            source,
        })?;
    probe
        .as_file()
        .metadata()
        .map(|metadata| metadata.uid())
        .map_err(|source| DriverError::CreateDirectory {
            path: probe.path().to_owned(),
            source,
        })
}

#[cfg(test)]
fn effective_uid() -> Result<u32, DriverError> {
    let context = ExecutionContext::ambient()?;
    effective_uid_in_context(&context)
}

fn require_within_cache_root(path: &Path, root: &Path) -> Result<(), DriverError> {
    if path.starts_with(root) {
        Ok(())
    } else {
        Err(DriverError::UnsafeFallbackCacheRoot {
            path: path.to_owned(),
        })
    }
}

const fn content_hash(bytes: &[u8]) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64;
    let mut index = 0;
    while index < bytes.len() {
        hash ^= bytes[index] as u64;
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        index += 1;
    }
    hash
}

struct TemporaryLinkFiles {
    object: PathBuf,
    executable: PathBuf,
}

impl TemporaryLinkFiles {
    fn create(parent: &Path, destination: &Path) -> Result<Self, DriverError> {
        let stem = destination
            .file_name()
            .unwrap_or_else(|| OsStr::new("bamts-output"))
            .to_string_lossy();
        for attempt in 0_u32..128 {
            let prefix = format!(".{stem}.bamts-{}-{attempt}", std::process::id());
            let object = parent.join(format!("{prefix}.o"));
            match OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&object)
            {
                Ok(_) => {
                    return Ok(Self {
                        object,
                        executable: parent.join(format!("{prefix}.out")),
                    });
                }
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(source) => {
                    return Err(DriverError::WriteObject {
                        path: object,
                        source,
                    });
                }
            }
        }
        Err(DriverError::WriteObject {
            path: parent.to_owned(),
            source: io::Error::new(
                io::ErrorKind::AlreadyExists,
                "temporary-name attempts exhausted",
            ),
        })
    }
}

impl Drop for TemporaryLinkFiles {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.object);
        let _ = fs::remove_file(&self.executable);
    }
}

fn publish_linked_executable(temporary: &Path, destination: &Path) -> Result<(), DriverError> {
    match fs::rename(temporary, destination) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            fs::remove_file(destination).map_err(|source| DriverError::PublishExecutable {
                path: destination.to_owned(),
                source,
            })?;
            fs::rename(temporary, destination).map_err(|source| DriverError::PublishExecutable {
                path: destination.to_owned(),
                source,
            })
        }
        Err(source) => Err(DriverError::PublishExecutable {
            path: destination.to_owned(),
            source,
        }),
    }
}

struct LoadedProgramFrontend {
    program: ResolvedProgram,
    output: ProgramFrontendOutput,
}

fn load_program_frontend(args: &CliArgs) -> Result<LoadedProgramFrontend, DriverError> {
    let context = ExecutionContext::ambient()?;
    load_program_frontend_in_context_with_cancel(args, &context, &CancellationToken::new())
}

fn load_program_frontend_in_context_with_cancel(
    args: &CliArgs,
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<LoadedProgramFrontend, DriverError> {
    if !args.extra_inputs.is_empty() {
        return Err(DriverError::MultipleCompileInputs);
    }
    let entrypoint = required_entrypoint(args)?;
    let current_directory = context.cwd().to_owned();
    let absolute_entrypoint = if entrypoint.is_absolute() {
        entrypoint.to_path_buf()
    } else {
        current_directory.join(entrypoint)
    };
    let absolute_entrypoint =
        fs::canonicalize(&absolute_entrypoint).map_err(|source| DriverError::ReadSource {
            path: absolute_entrypoint,
            source,
        })?;
    let fallback_root = if absolute_entrypoint.starts_with(&current_directory) {
        current_directory
    } else {
        absolute_entrypoint
            .parent()
            .unwrap_or_else(|| Path::new("/"))
            .to_path_buf()
    };
    let project = discover_project(&absolute_entrypoint, fallback_root);
    let canonical_root = fs::canonicalize(project.root())
        .map_err(|error| DriverError::ProgramLoad(ProgramLoadError::InvalidRoot(error)))?;
    let root = ProjectRoot::new(canonical_root).map_err(|error| {
        DriverError::ProgramLoad(ProgramLoadError::InvalidRoot(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            error,
        )))
    })?;
    let config_path = project.config().to_owned();
    let config_source = if config_path.is_file() {
        fs::read_to_string(&config_path).map_err(|source| DriverError::ReadSource {
            path: config_path.clone(),
            source,
        })?
    } else {
        "{}".to_owned()
    };
    let config = ProjectConfig::parse(&root, &config_path, &config_source).map_err(|error| {
        DriverError::ProjectConfig {
            path: config_path,
            message: error.to_string(),
        }
    })?;
    let loader = ProgramLoader::new(&root, config.options()).map_err(DriverError::ProgramLoad)?;
    let program = loader
        .load_with_cancel(&absolute_entrypoint, cancel)
        .map_err(DriverError::ProgramLoad)?;
    let levels = levels(args, root.path())?;
    let output =
        compile_program_frontend_with_cancel(&program, FrontendMode::Check, &levels, cancel)
            .map_err(|_| DriverError::Cancelled)?;
    Ok(LoadedProgramFrontend { program, output })
}

struct RenderedDiagnostics {
    text: String,
    truncation: Option<TruncationNotice>,
}
fn render_program_diagnostics(
    args: &CliArgs,
    frontend: &LoadedProgramFrontend,
) -> RenderedDiagnostics {
    let diagnostics = frontend
        .output
        .modules()
        .iter()
        .flat_map(|module| module.diagnostics().iter().cloned())
        .collect::<Vec<_>>();
    let names = frontend
        .program
        .modules()
        .iter()
        .map(|module| module.path().to_string_lossy())
        .collect::<Vec<_>>();
    let sources = frontend
        .program
        .modules()
        .iter()
        .zip(&names)
        .map(|(module, name)| DiagnosticSource {
            id: module.source_id(),
            name,
            text: module.source(),
        })
        .collect::<Vec<_>>();
    let (text, truncation) = diagnostics::render_report(
        args.diagnostics_format,
        &DiagnosticReport::new(&diagnostics),
        &sources,
        args.error_limit,
    );
    RenderedDiagnostics { text, truncation }
}

fn render_tsc_program_diagnostics(
    command: &ParsedTscCommand,
    frontend: &LoadedProgramFrontend,
) -> (String, bool) {
    let native = frontend
        .output
        .modules()
        .iter()
        .flat_map(|module| module.diagnostics().iter().cloned())
        .collect::<Vec<Diagnostic>>();
    let diagnostics = map_parse_diagnostics(&native);
    let has_errors = diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error);
    let names = frontend
        .program
        .modules()
        .iter()
        .map(|module| module.path().to_string_lossy())
        .collect::<Vec<_>>();
    let sources = frontend
        .program
        .modules()
        .iter()
        .zip(&names)
        .map(|(module, name)| DiagnosticSource {
            id: module.source_id(),
            name,
            text: module.source(),
        })
        .collect::<Vec<_>>();
    let format = if command.pretty() {
        TscDiagnosticFormat::Pretty
    } else {
        TscDiagnosticFormat::PrettyFalse
    };
    (
        tsc_diagnostics::render(format, &diagnostics, &sources),
        has_errors,
    )
}

fn require_clean_frontend(
    args: &CliArgs,
    frontend: &LoadedProgramFrontend,
) -> Result<RenderedDiagnostics, DriverError> {
    Ok(render_program_diagnostics(args, frontend))
}

/// Compiles a source entrypoint through the same frontend, lint, and lowering
/// pipeline as [`execute`], returning the lowered executable program without
/// running or linking it.  This is the in-process interpreter seam used by the
/// corpus differential harness so that CLI-supplied lint overrides and
/// JavaScript-compatibility flags reach the lowering stage.
///
/// Type diagnostics do not block lowering. That matches TypeScript's default
/// emit-on-error policy; `check` still fail-closes on error diagnostics.
pub fn compile_program(
    args: &CliArgs,
) -> Result<bamts_compiler::program::ExecutableProgram, DriverError> {
    let frontend = load_program_frontend(args)?;
    let _diagnostics = require_clean_frontend(args, &frontend)?;
    lower_program(&frontend.program, &frontend.output, lower_options(args))
        .map_err(DriverError::Lower)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::ffi::OsString;
    use std::path::{Path, PathBuf};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::{Duration, Instant};
    use std::{fs, process, thread};

    use bamts_compiler::{
        CancellationToken,
        lint::{LintLevel, SourceDialect, rule_by_name},
    };

    use crate::args::{ArgsError, parse_args};
    use crate::cli::tsc_args::{TscExitStatus, parse_tsc_args};
    use crate::context::ExecutionContext;

    use super::{
        CommandOutcome, DriverError, capture_process_with_cancel, content_hash, execute_in_context,
        execute_tsc, execute_tsc_in, levels, link_executable, lower_options, probe_toolchain,
        probe_toolchain_in_context,
    };

    #[cfg(unix)]
    #[test]
    fn hanging_toolchain_probe_maps_cancellation_to_driver_cancelled()
    -> Result<(), Box<dyn std::error::Error>> {
        use std::os::unix::fs::PermissionsExt;

        let directory = std::env::temp_dir().join(format!(
            "bamts-cli-toolchain-probe-cancel-{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory)?;
        let compiler = directory.join("fake-cc");
        fs::write(
            &compiler,
            "#!/bin/sh
printf started > probe-started
/bin/sleep 30
",
        )?;
        fs::set_permissions(&compiler, fs::Permissions::from_mode(0o700))?;
        let context = ExecutionContext::new(&directory, BTreeMap::new())?;
        let cancel = CancellationToken::new();
        let trigger = cancel.clone();
        let marker = directory.join("probe-started");
        let canceller = thread::spawn(move || {
            let deadline = Instant::now() + Duration::from_secs(2);
            while !marker.is_file() && Instant::now() < deadline {
                thread::sleep(Duration::from_millis(5));
            }
            let started = marker.is_file();
            trigger.cancel();
            started
        });

        let started = Instant::now();
        let error = probe_toolchain_in_context(compiler.into_os_string(), &context, &cancel)
            .expect_err("cancelled compiler probe must fail as cancellation");
        assert!(matches!(error, DriverError::Cancelled));
        assert!(
            canceller
                .join()
                .expect("probe cancellation thread completes")
        );
        assert!(
            started.elapsed() < Duration::from_secs(3),
            "managed probe cancellation must be bounded"
        );
        fs::remove_dir_all(directory)?;
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn hanging_toolchain_link_maps_cancellation_to_driver_cancelled()
    -> Result<(), Box<dyn std::error::Error>> {
        use std::os::unix::fs::PermissionsExt;

        let directory = std::env::temp_dir().join(format!(
            "bamts-cli-toolchain-link-cancel-{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory)?;
        let compiler = directory.join("fake-cc");
        fs::write(
            &compiler,
            r#"#!/bin/sh
if [ "$1" = "--version" ]; then exit 0; fi
printf started > link-started
/bin/sleep 30
"#,
        )?;
        fs::set_permissions(&compiler, fs::Permissions::from_mode(0o700))?;
        let context = ExecutionContext::new(
            &directory,
            BTreeMap::from([
                (OsString::from("CC"), compiler.into_os_string()),
                (
                    OsString::from("XDG_CACHE_HOME"),
                    directory.join("cache").into_os_string(),
                ),
            ]),
        )?;
        let cancel = CancellationToken::new();
        let trigger = cancel.clone();
        let marker = directory.join("link-started");
        // Wait for the linker to actually start rather than for a fixed
        // slice of wall clock: a loaded runner can take longer to spawn
        // the process than a short deadline allows. The cap only breaks a
        // genuine hang, and the returned instant dates the cancel so the
        // bound below measures cancellation, not process startup.
        let canceller = thread::spawn(move || {
            let deadline = Instant::now() + Duration::from_secs(60);
            while !marker.is_file() && Instant::now() < deadline {
                thread::sleep(Duration::from_millis(5));
            }
            let started = marker.is_file();
            trigger.cancel();
            started.then(Instant::now)
        });

        let error = link_executable(&[], &directory.join("output"), &context, &cancel)
            .expect_err("cancelled linker must fail as cancellation");
        assert!(matches!(error, DriverError::Cancelled));
        let cancelled_at = canceller
            .join()
            .expect("link cancellation thread completes")
            .expect("the linker must start before it is cancelled");
        assert!(
            cancelled_at.elapsed() < Duration::from_secs(3),
            "managed link cancellation must be bounded"
        );
        fs::remove_dir_all(directory)?;
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn relative_cc_uses_explicit_cwd_and_environment_for_probe_and_link()
    -> Result<(), Box<dyn std::error::Error>> {
        use std::os::unix::fs::PermissionsExt;

        let directory = std::env::temp_dir().join(format!(
            "bamts-cli-relative-toolchain-{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory)?;
        let compiler = directory.join("fake-cc");
        fs::write(
            &compiler,
            r#"#!/bin/sh
printf '%s|%s
' "$PWD" "$BAMTS_TOOLCHAIN_CONTEXT" >> toolchain.log
if [ "$1" = "--version" ]; then exit 0; fi
while [ "$#" -gt 0 ]; do
    if [ "$1" = "-o" ]; then
        shift
        printf '#!/bin/sh
exit 0
' > "$1"
        exit 0
    fi
    shift
done
exit 2
"#,
        )?;
        fs::set_permissions(&compiler, fs::Permissions::from_mode(0o700))?;
        let context = ExecutionContext::new(
            &directory,
            BTreeMap::from([
                (OsString::from("CC"), OsString::from("./fake-cc")),
                (
                    OsString::from("BAMTS_TOOLCHAIN_CONTEXT"),
                    OsString::from("from-explicit-context"),
                ),
                (
                    OsString::from("XDG_CACHE_HOME"),
                    directory.join("cache").into_os_string(),
                ),
            ]),
        )?;

        link_executable(
            &[],
            Path::new("linked-output"),
            &context,
            &CancellationToken::new(),
        )?;
        let expected = format!("{}|from-explicit-context", directory.display());
        let observations = fs::read_to_string(directory.join("toolchain.log"))?
            .lines()
            .map(str::to_owned)
            .collect::<Vec<_>>();
        assert_eq!(observations, vec![expected.clone(), expected]);
        assert!(directory.join("linked-output").is_file());
        fs::remove_dir_all(directory)?;
        Ok(())
    }

    static NEXT_TSC_TEST_ID: AtomicUsize = AtomicUsize::new(0);

    struct TscFixture(PathBuf);

    impl TscFixture {
        fn new() -> Self {
            let id = NEXT_TSC_TEST_ID.fetch_add(1, Ordering::Relaxed);
            let root =
                std::env::temp_dir().join(format!("bamts-tsc-project-{}-{id}", process::id()));
            fs::create_dir_all(&root).expect("create TSC fixture");
            Self(root)
        }

        fn write(&self, path: &str, contents: &str) {
            let path = self.0.join(path);
            fs::create_dir_all(path.parent().expect("fixture file parent"))
                .expect("create fixture parent");
            fs::write(path, contents).expect("write fixture file");
        }
    }

    impl Drop for TscFixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).ok();
        }
    }

    #[test]
    fn tsc_help_and_version_are_driver_commands() {
        let help =
            execute_tsc(&parse_tsc_args(["--help"]).expect("help parses")).expect("help executes");
        assert_eq!(help.exit_code, TscExitStatus::Success.code());
        assert!(
            String::from_utf8(help.stdout)
                .expect("UTF-8 help")
                .starts_with("tsc: The TypeScript Compiler - Version 7.0.2")
        );

        let version = execute_tsc(&parse_tsc_args(["--version"]).expect("version parses"))
            .expect("version executes");
        assert_eq!(version.exit_code, TscExitStatus::Success.code());
        assert_eq!(version.stdout, b"Version 7.0.2\n");
    }

    #[test]
    fn tsc_init_creates_canonical_config_without_overwriting() {
        let fixture = TscFixture::new();
        let init = execute_tsc_in(
            &parse_tsc_args(["--init", "--target", "es5", "--pretty", "true", "main.ts"])
                .expect("init parses"),
            &fixture.0,
        )
        .expect("init executes");
        assert_eq!(init.exit_code, TscExitStatus::Success.code());
        assert_eq!(init.stdout, super::TSC_INIT_CREATED.as_bytes());
        assert!(init.stderr.is_empty());

        let config = fixture.0.join("tsconfig.json");
        let original = fs::read(&config).expect("init writes config");
        assert_eq!(original, super::TSC_INIT_CONFIG.as_bytes());

        let existing = execute_tsc_in(
            &parse_tsc_args(["--init"]).expect("second init parses"),
            &fixture.0,
        )
        .expect("second init executes");
        assert_eq!(existing.exit_code, TscExitStatus::Success.code());
        assert!(existing.stderr.is_empty());
        assert_eq!(
            String::from_utf8(existing.stdout).expect("UTF-8 TS5054"),
            format!(
                "error TS5054: A 'tsconfig.json' file is already defined at: '{}'.\n",
                config.display()
            )
        );
        assert_eq!(fs::read(config).expect("read unchanged config"), original);
    }

    #[test]
    fn tsc_project_load_errors_keep_their_typescript_diagnostics() {
        let fixture = TscFixture::new();
        let assert_error = |outcome: CommandOutcome, expected: String| {
            assert_eq!(
                outcome.exit_code,
                TscExitStatus::DiagnosticsPresentOutputsSkipped.code()
            );
            assert!(outcome.stderr.is_empty());
            assert_eq!(String::from_utf8(outcome.stdout).unwrap(), expected);
        };

        let current = execute_tsc_in(
            &parse_tsc_args(std::iter::empty::<&str>()).expect("default project parses"),
            &fixture.0,
        )
        .expect("default project executes");
        assert_error(
            current,
            format!(
                "error TS5081: Cannot find a tsconfig.json file at the current directory: {}.\n",
                fixture.0.join("tsconfig.json").display()
            ),
        );

        let directory = fixture.0.join("missing-project");
        fs::create_dir_all(&directory).unwrap();
        let explicit_directory = execute_tsc_in(
            &parse_tsc_args(["--project", "missing-project"]).expect("directory project parses"),
            &fixture.0,
        )
        .expect("directory project executes");
        assert_error(
            explicit_directory,
            format!(
                "error TS5057: Cannot find a tsconfig.json file at the specified directory: '{}'.\n",
                directory.display()
            ),
        );

        let config = fixture.0.join("missing.json");
        let explicit_file = execute_tsc_in(
            &parse_tsc_args(["--project", "missing.json"]).expect("file project parses"),
            &fixture.0,
        )
        .expect("file project executes");
        assert_error(
            explicit_file,
            format!("error TS5083: Cannot read file '{}'.\n", config.display()),
        );

        fixture.write("empty.json", r#"{"files":[]}"#);
        let empty = execute_tsc_in(
            &parse_tsc_args(["--project", "empty.json"]).expect("empty project parses"),
            &fixture.0,
        )
        .expect("empty project executes");
        assert_error(
            empty,
            format!(
                "error TS18002: The 'files' list in config file '{}' is empty.\n",
                fixture.0.join("empty.json").display()
            ),
        );

        fixture.write(
            "none.json",
            r#"{"include":["src/**/*.ts"],"exclude":["build"]}"#,
        );
        let none = execute_tsc_in(
            &parse_tsc_args(["--project", "none.json"]).expect("no-input project parses"),
            &fixture.0,
        )
        .expect("no-input project executes");
        assert_error(
            none,
            format!(
                "error TS18003: No inputs were found in config file '{}'. Specified 'include' paths were '[\"src/**/*.ts\"]' and 'exclude' paths were '[\"build\"]'.\n",
                fixture.0.join("none.json").display()
            ),
        );

        let absolute_pattern = fixture.0.join("absolute/**/*.ts");
        fixture.write(
            "absolute.json",
            &format!(r#"{{"include":["{}"]}}"#, absolute_pattern.display()),
        );
        let absolute = execute_tsc_in(
            &parse_tsc_args(["--project", "absolute.json"]).expect("absolute project parses"),
            &fixture.0,
        )
        .expect("absolute project executes");
        assert_error(
            absolute,
            format!(
                "error TS18003: No inputs were found in config file '{}'. Specified 'include' paths were '[\"{}\"]' and 'exclude' paths were '[]'.\n",
                fixture.0.join("absolute.json").display(),
                absolute_pattern.display()
            ),
        );

        fixture.write(
            "base/base.json",
            r#"{"include":["src/**/*.ts"],"exclude":["build"]}"#,
        );
        fixture.write("app/tsconfig.json", r#"{"extends":"../base/base.json"}"#);
        let inherited = execute_tsc_in(
            &parse_tsc_args(["--project", "app/tsconfig.json"]).expect("inherited project parses"),
            &fixture.0,
        )
        .expect("inherited project executes");
        assert_error(
            inherited,
            format!(
                "error TS18003: No inputs were found in config file '{}'. Specified 'include' paths were '[\"../base/src/**/*.ts\"]' and 'exclude' paths were '[\"../base/build\"]'.\n",
                fixture.0.join("app/tsconfig.json").display()
            ),
        );
    }
    #[test]
    fn tsc_project_lists_loaded_files_and_list_only_suppresses_emit() {
        let fixture = TscFixture::new();
        fixture.write(
            "src/a.ts",
            "import { b } from './b';\nexport const a = b;\n",
        );
        fixture.write("src/b.ts", "export const b = 1;\n");
        fixture.write(
            "list.json",
            r#"{"files":["src/a.ts"],"compilerOptions":{"outDir":"list-dist"}}"#,
        );
        let listed = execute_tsc_in(
            &parse_tsc_args(["--project", "list.json", "--listFiles"])
                .expect("listFiles project parses"),
            &fixture.0,
        )
        .expect("listFiles project executes");
        assert_eq!(listed.exit_code, TscExitStatus::Success.code());
        assert!(listed.stderr.is_empty());
        assert!(fixture.0.join("list-dist/a.js").is_file());
        assert!(fixture.0.join("list-dist/b.js").is_file());
        let listed = String::from_utf8(listed.stdout).unwrap();
        let dependency = fixture.0.join("src/b.ts").display().to_string();
        let root = fixture.0.join("src/a.ts").display().to_string();
        assert!(listed.contains(&dependency), "{listed}");
        assert!(listed.contains(&root), "{listed}");

        fixture.write(
            "only.json",
            r#"{"files":["src/a.ts"],"compilerOptions":{"outDir":"only-dist"}}"#,
        );
        let only = execute_tsc_in(
            &parse_tsc_args(["--project", "only.json", "--listFilesOnly"])
                .expect("listFilesOnly project parses"),
            &fixture.0,
        )
        .expect("listFilesOnly project executes");
        assert_eq!(only.exit_code, TscExitStatus::Success.code());
        assert!(only.stderr.is_empty());
        assert!(!fixture.0.join("only-dist").exists());
        assert_eq!(
            String::from_utf8(only.stdout).unwrap(),
            format!("{dependency}\n{root}\n")
        );

        fixture.write("bad.ts", "export const broken = ;\n");
        fixture.write("bad.json", r#"{"files":["bad.ts"]}"#);
        let bad = execute_tsc_in(
            &parse_tsc_args(["--project", "bad.json", "--listFilesOnly"])
                .expect("bad listFilesOnly project parses"),
            &fixture.0,
        )
        .expect("bad listFilesOnly project executes");
        assert_eq!(bad.exit_code, TscExitStatus::Success.code());
        assert_eq!(
            String::from_utf8(bad.stdout).unwrap(),
            format!("{}\n", fixture.0.join("bad.ts").display())
        );
    }

    #[test]
    fn tsc_direct_source_requires_ignore_config() {
        let fixture = TscFixture::new();
        fixture.write("tsconfig.json", "{}\n");
        fixture.write("main.ts", "export const value = 1;\n");

        let blocked = execute_tsc_in(
            &parse_tsc_args(["--noEmit", "main.ts"]).expect("direct parse"),
            &fixture.0,
        )
        .expect("direct config guard executes");
        assert_eq!(
            blocked.exit_code,
            TscExitStatus::DiagnosticsPresentOutputsSkipped.code()
        );
        assert!(blocked.stderr.is_empty());
        assert_eq!(
            blocked.stdout,
            b"error TS5112: tsconfig.json is present but will not be loaded if files are specified on commandline. Use '--ignoreConfig' to skip this error.\n"
        );

        let ignored = execute_tsc_in(
            &parse_tsc_args(["--noEmit", "--ignoreConfig", "main.ts"])
                .expect("ignoreConfig parses"),
            &fixture.0,
        )
        .expect("ignored config executes");
        assert_eq!(ignored.exit_code, TscExitStatus::Success.code());
        assert!(ignored.stderr.is_empty());
        assert!(!String::from_utf8_lossy(&ignored.stdout).contains("TS5112"));
    }

    #[test]
    fn tsc_direct_check_maps_parse_diagnostics_once() {
        let id = NEXT_TSC_TEST_ID.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("bamts-tsc-direct-{}-{id}.ts", std::process::id()));
        std::fs::write(&path, "const value = ;\n").expect("write source");
        let command = parse_tsc_args([
            "--noEmit",
            "--pretty",
            "false",
            path.to_str().expect("UTF-8 path"),
        ])
        .expect("direct command parses");
        let outcome = execute_tsc(&command).expect("direct check executes");
        let stdout = String::from_utf8(outcome.stdout).expect("UTF-8 diagnostics");
        assert_eq!(
            outcome.exit_code,
            TscExitStatus::DiagnosticsPresentOutputsSkipped.code()
        );
        assert!(outcome.stderr.is_empty());
        assert!(stdout.contains("error TS1109: Expression expected."));
        assert!(!stdout.contains("BAMTS-P002"));
        let _ = std::fs::remove_file(path);
    }

    #[test]
    fn tsc_type_error_emits_with_status_2() {
        let id = NEXT_TSC_TEST_ID.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("bamts-tsc-emit-{}-{id}.ts", std::process::id()));
        let emitted = path.with_extension("");
        std::fs::write(&path, "const value: number = \"text\";\n").expect("write source");

        let outcome = execute_tsc(
            &parse_tsc_args([path.to_str().expect("UTF-8 path")]).expect("default emit parses"),
        )
        .expect("default emit executes");
        let stdout = String::from_utf8(outcome.stdout).expect("UTF-8 diagnostics");
        assert_eq!(
            outcome.exit_code,
            TscExitStatus::DiagnosticsPresentOutputsGenerated.code()
        );
        assert!(outcome.stderr.is_empty());
        assert_eq!(stdout.matches("BAMTS-C004").count(), 1);
        assert!(emitted.is_file(), "error-tolerant compilation emits output");
        let _ = std::fs::remove_file(emitted);
        let _ = std::fs::remove_file(path);
    }

    #[test]
    fn tsc_direct_multi_root_checks_and_native_jsx_fails_closed() {
        let fixture = TscFixture::new();
        fixture.write("a.ts", "export const value = 1;\n");
        fixture.write(
            "b.ts",
            "import { value } from \"./a\";\nexport const doubled = value * 2;\n",
        );
        let multi_root = execute_tsc_in(
            &parse_tsc_args(["--noEmit", "--pretty", "false", "a.ts", "b.ts"])
                .expect("multi-root parses"),
            &fixture.0,
        )
        .expect("multi-root returns a typed outcome");
        assert_eq!(multi_root.exit_code, TscExitStatus::Success.code());
        assert!(!String::from_utf8_lossy(&multi_root.stdout).contains("error TS"));

        fixture.write("component.tsx", "export const view = <div />;\n");
        let jsx = execute_tsc_in(
            &parse_tsc_args(["--noEmit", "--jsx", "react", "component.tsx"])
                .expect("JSX command parses"),
            &fixture.0,
        )
        .expect("JSX command returns a typed outcome");
        assert_eq!(jsx.exit_code, TscExitStatus::NotImplemented.code());
    }

    #[test]
    fn tsc_project_emits_artifacts_and_honors_no_emit_on_error() {
        let fixture = TscFixture::new();
        fixture.write("src/main.ts", "export const answer = 42;\n");
        fixture.write(
            "tsconfig.json",
            r#"{"files":["src/main.ts"],"compilerOptions":{"rootDir":"src","outDir":"dist","declaration":true}}"#,
        );
        let project = execute_tsc_in(
            &parse_tsc_args(["-p", "tsconfig.json", "--pretty", "false"]).expect("project parses"),
            &fixture.0,
        )
        .expect("project executes");
        assert_eq!(project.exit_code, TscExitStatus::Success.code());
        assert!(fixture.0.join("dist/main.js").is_file());
        assert!(fixture.0.join("dist/main.d.ts").is_file());

        fixture.write("src/main.ts", "const value = ;\n");
        let gated = execute_tsc_in(
            &parse_tsc_args([
                "--project",
                "tsconfig.json",
                "--noEmitOnError",
                "--outDir",
                "gated",
                "--pretty",
                "false",
            ])
            .expect("gated project parses"),
            &fixture.0,
        )
        .expect("gated project executes");
        assert_eq!(
            gated.exit_code,
            TscExitStatus::DiagnosticsPresentOutputsSkipped.code()
        );
        assert!(!fixture.0.join("gated/main.js").exists());
        assert!(gated.stderr.is_empty());
        assert!(
            String::from_utf8_lossy(&gated.stdout).contains("error TS1109: Expression expected.")
        );
    }

    #[test]
    fn tsc_build_orders_references_and_stops_after_error() {
        let fixture = TscFixture::new();
        fixture.write("lib/src/lib.ts", "export const lib = 1;\n");
        fixture.write(
            "lib/tsconfig.json",
            r#"{"files":["src/lib.ts"],"compilerOptions":{"composite":true,"rootDir":"src","outDir":"dist","noEmitOnError":true}}"#,
        );
        fixture.write("app/src/app.ts", "export const app = 1;\n");
        fixture.write(
            "app/tsconfig.json",
            r#"{"files":["src/app.ts"],"references":[{"path":"../lib"}],"compilerOptions":{"composite":true,"rootDir":"src","outDir":"dist"}}"#,
        );
        let dry = execute_tsc_in(
            &parse_tsc_args(["--build", "app", "--dry"]).expect("dry build parses"),
            &fixture.0,
        )
        .expect("dry build executes");
        assert_eq!(dry.exit_code, TscExitStatus::Success.code());
        let dry = String::from_utf8(dry.stdout).expect("UTF-8 dry report");
        assert!(dry.find("lib/tsconfig.json").unwrap() < dry.find("app/tsconfig.json").unwrap());
        assert!(!fixture.0.join("lib/dist/lib.js").exists());

        let built = execute_tsc_in(
            &parse_tsc_args(["--build", "app"]).expect("build parses"),
            &fixture.0,
        )
        .expect("build executes");
        assert_eq!(built.exit_code, TscExitStatus::Success.code());
        assert!(fixture.0.join("lib/dist/lib.js").is_file());
        assert!(fixture.0.join("lib/dist/lib.d.ts").is_file());
        assert!(fixture.0.join("app/dist/app.js").is_file());
        assert!(fixture.0.join("app/dist/app.d.ts").is_file());
        fs::remove_dir_all(fixture.0.join("app/dist")).expect("clear app outputs");

        fixture.write("lib/src/lib.ts", "const value = ;\n");
        let failed = execute_tsc_in(
            &parse_tsc_args(["--build", "app", "--force"]).expect("build parses"),
            &fixture.0,
        )
        .expect("build executes");
        assert_eq!(
            failed.exit_code,
            TscExitStatus::DiagnosticsPresentOutputsSkipped.code()
        );
        assert!(!fixture.0.join("app/dist/app.js").exists());
        assert!(failed.stderr.is_empty());
        assert!(
            String::from_utf8_lossy(&failed.stdout).contains("error TS1109: Expression expected.")
        );
    }

    #[test]
    fn content_hash_is_stable_and_sensitive() {
        assert_eq!(content_hash(b"bamts"), 0xd301_9081_dac2_4a42);
        assert_ne!(content_hash(b"bamts"), content_hash(b"bamti"));
    }

    #[test]
    fn missing_toolchain_is_typed() {
        let error = probe_toolchain("/definitely/not/a/c/compiler".into())
            .expect_err("missing compiler must fail");
        assert!(matches!(error, DriverError::ToolchainMissing { .. }));
    }

    #[test]
    fn cross_target_link_has_actionable_error() {
        let error = DriverError::CrossTargetLink {
            host: "x86_64-unknown-linux-gnu",
            target: "aarch64-unknown-linux-gnu",
        };
        assert_eq!(
            error.to_string(),
            "native linking for Cargo target `aarch64-unknown-linux-gnu` is unsupported from host `x86_64-unknown-linux-gnu`"
        );
    }

    #[test]
    fn cli_rule_override_beats_a_later_group_override() {
        let args = parse_args([
            "check",
            "-A",
            "explicit-any",
            "-D",
            "escape-hatches",
            "main.ts",
        ])
        .expect("arguments parse");
        let table =
            levels(&args, Path::new("/definitely/no/bamts/config")).expect("overrides resolve");
        let explicit_any = rule_by_name("explicit-any").expect("registered rule").id();
        let implicit_any = rule_by_name("implicit-any").expect("registered rule").id();
        assert_eq!(table.level(explicit_any), LintLevel::Allow);
        assert_eq!(table.level(implicit_any), LintLevel::Deny);
    }

    #[test]
    fn lowering_forbid_is_a_typed_usage_error() {
        let args = parse_args([
            "check",
            "-F",
            "explicit-any",
            "-A",
            "explicit-any",
            "main.ts",
        ])
        .expect("arguments parse");
        assert!(matches!(
            levels(&args, Path::new("/definitely/no/bamts/config")),
            Err(DriverError::Usage(ArgsError::ForbiddenLintOverride { .. }))
        ));
    }

    #[test]
    fn lowering_options_follow_javascript_compatibility_selection() {
        let disabled = parse_args(["compile", "main.ts"]).expect("arguments parse");
        let enabled =
            parse_args(["compile", "--compat", "strict", "main.ts"]).expect("arguments parse");

        assert!(!lower_options(&disabled).javascript_compatibility);
        assert!(lower_options(&enabled).javascript_compatibility);
    }

    #[test]
    fn strict_cli_profile_keeps_javascript_rules_nonfatal() {
        let args = parse_args(["check", "--strict", "vendored.js"]).expect("arguments parse");
        let table =
            levels(&args, Path::new("/definitely/no/bamts/config")).expect("profile resolves");
        let footgun = rule_by_name("invalid-number-formatting-options")
            .expect("registered footgun")
            .id();
        let typescript_only = rule_by_name("explicit-any").expect("registered rule").id();
        assert_eq!(
            table.level_for_source(footgun, SourceDialect::JavaScript),
            LintLevel::Warn
        );
        assert_eq!(
            table.level_for_source(typescript_only, SourceDialect::JavaScript),
            LintLevel::Allow
        );
    }

    #[cfg(unix)]
    #[test]
    fn fallback_cache_root_has_stable_per_user_path() {
        let parent = super::validate_fallback_parent_chain(&std::env::temp_dir()).unwrap();
        let expected = parent.join(format!("bamts-cache-{}", super::effective_uid().unwrap()));
        assert_eq!(super::fallback_cache_root_path().unwrap(), expected);
    }

    #[cfg(unix)]
    #[test]
    fn private_fallback_cache_root_creates_owner_only_directory() {
        use std::os::unix::fs::PermissionsExt;
        use std::sync::atomic::Ordering;

        let path = std::env::temp_dir().join(format!(
            "bamts-cli-private-cache-create-{}-{}",
            std::process::id(),
            super::NEXT_CACHE_TEMP_ID.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = std::fs::remove_dir_all(&path);
        let root = super::ensure_private_fallback_cache_root(path.clone())
            .expect("private fallback root should be created");
        let metadata = std::fs::symlink_metadata(&root).expect("metadata");
        assert!(metadata.is_dir());
        assert_eq!(metadata.permissions().mode() & 0o777, 0o700);
        let _ = std::fs::remove_dir_all(&path);
    }

    #[cfg(unix)]
    #[test]
    fn private_fallback_cache_root_rejects_group_or_other_bits() {
        use std::os::unix::fs::PermissionsExt;
        use std::sync::atomic::Ordering;

        let path = std::env::temp_dir().join(format!(
            "bamts-cli-private-cache-unsafe-{}-{}",
            std::process::id(),
            super::NEXT_CACHE_TEMP_ID.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir(&path).expect("create fixture root");
        let mut permissions = std::fs::metadata(&path).expect("metadata").permissions();
        permissions.set_mode(0o710);
        std::fs::set_permissions(&path, permissions).expect("chmod");
        let error = super::ensure_private_fallback_cache_root(path.clone())
            .expect_err("group/other bits must be rejected");
        assert!(matches!(error, DriverError::UnsafeFallbackCacheRoot { .. }));
        let _ = std::fs::remove_dir_all(&path);
    }

    #[cfg(unix)]
    #[test]
    fn private_fallback_cache_root_rejects_replaceable_parent() {
        use std::os::unix::fs::PermissionsExt;
        use std::sync::atomic::Ordering;

        let parent = std::env::temp_dir().join(format!(
            "bamts-cli-replaceable-parent-{}-{}",
            std::process::id(),
            super::NEXT_CACHE_TEMP_ID.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = std::fs::remove_dir_all(&parent);
        std::fs::create_dir(&parent).expect("create fixture parent");
        let mut permissions = std::fs::metadata(&parent).expect("metadata").permissions();
        permissions.set_mode(0o777);
        std::fs::set_permissions(&parent, permissions).expect("chmod");

        let error = super::ensure_private_fallback_cache_root(parent.join("cache"))
            .expect_err("replaceable parent must be rejected");

        assert!(matches!(error, DriverError::UnsafeFallbackCacheRoot { .. }));
        let _ = std::fs::remove_dir_all(&parent);
    }

    #[cfg(unix)]
    #[test]
    fn symlinked_entrypoint_uses_one_canonical_config_root()
    -> Result<(), Box<dyn std::error::Error>> {
        use std::os::unix::fs::symlink;

        let directory =
            std::env::temp_dir().join(format!("bamts-cli-symlink-root-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        let real = directory.join("real");
        let alias = directory.join("alias");
        std::fs::create_dir_all(real.join("src"))?;
        std::fs::create_dir_all(&alias)?;
        std::fs::write(real.join("bamts.toml"), "")?;
        std::fs::write(real.join("src/main.ts"), "let answer = 42;")?;
        std::fs::write(alias.join("bamts.toml"), "this is not valid TOML = [")?;
        symlink(real.join("src/main.ts"), alias.join("main.ts"))?;

        let alias_entrypoint = alias.join("main.ts");
        let args = parse_args(["check", alias_entrypoint.to_str().expect("UTF-8 temp path")])?;
        let outcome = super::execute(&args)?;
        assert_eq!(outcome.exit_code, 0);

        std::fs::remove_dir_all(directory)?;
        Ok(())
    }
    #[test]
    fn check_keeps_truncation_notice_after_limited_diagnostics()
    -> Result<(), Box<dyn std::error::Error>> {
        let directory =
            std::env::temp_dir().join(format!("bamts-cli-truncation-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory)?;
        let entrypoint = directory.join("main.ts");
        std::fs::write(
            &entrypoint,
            "const first: string = 1;\nconst second: string = 2;\n",
        )?;

        let args = parse_args([
            "check",
            "--error-limit",
            "1",
            entrypoint.to_str().expect("UTF-8 temp path"),
        ])?;
        let error = super::execute(&args).expect_err("type errors must fail check mode");
        let rendered = error
            .rendered_diagnostic()
            .expect("diagnostic failure carries rendered output");
        let first_diagnostic = rendered
            .find("error[")
            .expect("one diagnostic is rendered before the limit");
        let notice = rendered
            .find("diagnostic(s) elided after limit 1")
            .expect("truncation notice is preserved");
        assert_eq!(rendered.matches("error[").count(), 1);
        assert!(
            first_diagnostic < notice,
            "notice follows rendered diagnostics"
        );

        std::fs::remove_dir_all(directory)?;
        Ok(())
    }

    #[test]
    fn jit_uses_the_complete_explicit_execution_context() -> Result<(), Box<dyn std::error::Error>>
    {
        let directory =
            std::env::temp_dir().join(format!("bamts-cli-jit-context-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory)?;
        let entrypoint = directory.join("main.ts");
        std::fs::write(
            &entrypoint,
            "process.stdout.write(process.env.BAMTS_EXPLICIT_CONTEXT);",
        )?;
        let context = ExecutionContext::new(
            &directory,
            BTreeMap::from([(
                OsString::from("BAMTS_EXPLICIT_CONTEXT"),
                OsString::from("from-explicit-context"),
            )]),
        )?;
        let args = parse_args([
            "run",
            "--target",
            "jit",
            entrypoint.to_str().expect("UTF-8 temp path"),
        ])?;

        let outcome = execute_in_context(&args, &context)?;

        assert_eq!(outcome.stdout, b"from-explicit-context");
        assert_eq!(outcome.exit_code, 0);
        std::fs::remove_dir_all(directory)?;
        Ok(())
    }

    #[test]
    fn jit_compile_cancellation_maps_to_driver_cancelled() -> Result<(), Box<dyn std::error::Error>>
    {
        let directory =
            std::env::temp_dir().join(format!("bamts-cli-jit-cancel-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory)?;
        let entrypoint = directory.join("main.ts");
        std::fs::write(&entrypoint, "process.stdout.write('unreachable');")?;
        let context = ExecutionContext::new(&directory, BTreeMap::new())?;
        let args = parse_args([
            "run",
            "--target",
            "jit",
            entrypoint.to_str().expect("UTF-8 temp path"),
        ])?;
        let frontend = super::load_program_frontend_in_context_with_cancel(
            &args,
            &context,
            &CancellationToken::new(),
        )?;
        let warnings = super::require_clean_frontend(&args, &frontend)?;
        let executable = bamts_compiler::program::lower_program(
            &frontend.program,
            &frontend.output,
            super::lower_options(&args),
        )?;
        let cancel = CancellationToken::new();
        cancel.cancel();

        let error = super::run_jit(&args, &entrypoint, warnings, &executable, &context, &cancel)
            .expect_err("cancelled JIT compilation must not become a backend error");

        assert!(matches!(error, DriverError::Cancelled));
        std::fs::remove_dir_all(directory)?;
        Ok(())
    }

    #[test]
    fn cancelled_aot_codegen_maps_to_driver_cancelled() -> Result<(), Box<dyn std::error::Error>> {
        let directory = std::env::temp_dir().join(format!(
            "bamts-cli-aot-codegen-cancel-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory)?;
        let entrypoint = directory.join("main.ts");
        std::fs::write(&entrypoint, "process.stdout.write('unreachable');")?;
        let context = ExecutionContext::new(&directory, BTreeMap::new())?;
        let args = parse_args([
            "run",
            "--target",
            "aot",
            entrypoint.to_str().expect("UTF-8 temp path"),
        ])?;
        let frontend = super::load_program_frontend_in_context_with_cancel(
            &args,
            &context,
            &CancellationToken::new(),
        )?;
        let warnings = super::require_clean_frontend(&args, &frontend)?;
        let executable = bamts_compiler::program::lower_program(
            &frontend.program,
            &frontend.output,
            super::lower_options(&args),
        )?;
        let cancel = CancellationToken::new();
        cancel.cancel();

        let error = super::run_aot(&args, &entrypoint, warnings, &executable, &context, &cancel)
            .expect_err("cancelled AOT compilation must not become a backend error");

        assert!(matches!(error, DriverError::Cancelled));
        std::fs::remove_dir_all(directory)?;
        Ok(())
    }

    #[test]
    fn post_link_cancellation_removes_published_executable()
    -> Result<(), Box<dyn std::error::Error>> {
        let directory = std::env::temp_dir().join(format!(
            "bamts-cli-aot-published-cancel-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory)?;
        let destination = directory.join("published-aot");
        std::fs::write(&destination, b"published")?;
        assert!(
            destination.is_file(),
            "test requires a published destination"
        );
        let cancel = CancellationToken::new();
        cancel.cancel();

        let error = super::claim_published_executable(&destination, &cancel)
            .expect_err("post-link cancellation must abort before spawn");

        assert!(matches!(error, DriverError::Cancelled));
        assert!(
            !destination.exists(),
            "published destination must be removed on cancellation"
        );
        std::fs::remove_dir_all(directory)?;
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn aot_children_run_in_the_explicit_context_cwd() -> Result<(), Box<dyn std::error::Error>> {
        use std::os::unix::fs::PermissionsExt;

        let directory =
            std::env::temp_dir().join(format!("bamts-cli-aot-cwd-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory)?;
        let entrypoint = directory.join("main.ts");
        let compiler = directory.join("fake-cc");
        std::fs::write(&entrypoint, "process.stdout.write('unreachable');")?;
        std::fs::write(
            &compiler,
            r#"#!/bin/sh
if [ "$1" = "--version" ]; then exit 0; fi
output=
while [ "$#" -gt 0 ]; do
  if [ "$1" = "-o" ]; then output=$2; break; fi
  shift
done
printf '#!/bin/sh\npwd\n' > "$output"
/bin/chmod 700 "$output"
"#,
        )?;
        let mut permissions = std::fs::metadata(&compiler)?.permissions();
        permissions.set_mode(0o700);
        std::fs::set_permissions(&compiler, permissions)?;
        let context = ExecutionContext::new(
            &directory,
            BTreeMap::from([
                (OsString::from("CC"), compiler.into_os_string()),
                (
                    OsString::from("XDG_CACHE_HOME"),
                    directory.join("cache").into_os_string(),
                ),
            ]),
        )?;
        let args = parse_args([
            "run",
            "--target",
            "aot",
            entrypoint.to_str().expect("UTF-8 temp path"),
        ])?;

        let outcome = execute_in_context(&args, &context)?;

        assert_eq!(
            outcome.stdout,
            format!("{}\n", directory.display()).as_bytes()
        );
        std::fs::remove_dir_all(directory)?;
        Ok(())
    }

    #[test]
    fn json_diagnostics_return_a_typed_truncation_notice() -> Result<(), Box<dyn std::error::Error>>
    {
        let directory =
            std::env::temp_dir().join(format!("bamts-cli-json-truncation-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory)?;
        let entrypoint = directory.join("main.ts");
        std::fs::write(
            &entrypoint,
            "const first: string = 1;\nconst second: string = 2;\n",
        )?;
        let args = parse_args([
            "check",
            "--json",
            "--error-limit",
            "1",
            entrypoint.to_str().expect("UTF-8 temp path"),
        ])?;

        let error = super::execute(&args).expect_err("type errors must fail check mode");
        let rendered = error
            .rendered_diagnostic()
            .expect("diagnostic failure carries JSON output");
        let parsed: serde_json::Value = serde_json::from_str(rendered)?;
        assert_eq!(parsed.as_array().map(Vec::len), Some(1));
        assert!(!rendered.contains("diagnostic(s) elided"));
        let notice = error
            .truncation_notice()
            .expect("structured formats carry typed elision metadata");
        assert_eq!(notice.limit(), 1);
        assert!(notice.elided() > 0);

        std::fs::remove_dir_all(directory)?;
        Ok(())
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn managed_capture_kills_descendant_without_external_kill_before_reader_join()
    -> Result<(), Box<dyn std::error::Error>> {
        let directory = std::env::temp_dir().join(format!(
            "bamts-cli-managed-descendant-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory)?;
        let empty_path = directory.join("empty-path");
        std::fs::create_dir(&empty_path)?;
        let pid_file = directory.join("descendant.pid");
        let cancel = CancellationToken::new();
        let trigger = cancel.clone();
        let cancellation_pid_file = pid_file.clone();
        let canceller = thread::spawn(move || {
            let deadline = Instant::now() + Duration::from_secs(2);
            while !cancellation_pid_file.is_file() && Instant::now() < deadline {
                thread::sleep(Duration::from_millis(5));
            }
            trigger.cancel();
        });
        let mut command = process::Command::new("/bin/sh");
        command
            .args([
                "-c",
                r#"/bin/sleep 30 & child=$!; printf '%s' "$child" > "$1"; wait"#,
                "bamts-managed-child",
                pid_file.to_str().expect("UTF-8 PID path"),
            ])
            .env("PATH", empty_path);
        let started = Instant::now();

        let output = capture_process_with_cancel(&mut command, &cancel)?;

        canceller.join().expect("cancellation thread completes");
        assert!(output.is_none(), "cancellation has exit precedence");
        assert!(
            started.elapsed() < Duration::from_secs(2),
            "managed process-tree shutdown must be bounded"
        );
        let pid = std::fs::read_to_string(&pid_file)?.trim().parse::<u32>()?;
        let deadline = Instant::now() + Duration::from_secs(2);
        loop {
            let alive = std::fs::read_to_string(format!("/proc/{pid}/stat"))
                .ok()
                .and_then(|stat| stat.split_whitespace().nth(2).map(str::to_owned))
                .is_some_and(|state| state != "Z");
            if !alive {
                break;
            }
            assert!(
                Instant::now() < deadline,
                "descendant PID {pid} survived cancellation"
            );
            thread::sleep(Duration::from_millis(5));
        }
        std::fs::remove_dir_all(directory)?;
        Ok(())
    }
    #[test]
    fn run_executes_node_vm_scripts_with_the_linked_backend()
    -> Result<(), Box<dyn std::error::Error>> {
        let cases = [
            (
                "default-import",
                "import vm from 'node:vm'; process.stdout.write(String(vm.runInThisContext('1+1')) + '\\n');",
                b"2\n".as_slice(),
                0,
            ),
            (
                "named-import",
                "import { runInThisContext } from 'node:vm'; process.stdout.write(String(runInThisContext('1+1')) + '\\n');",
                b"2\n".as_slice(),
                0,
            ),
            (
                "syntax-error",
                "import vm from 'node:vm'; try { new vm.Script('('); } catch (error) { process.stdout.write(error.name + '\\n'); }",
                b"SyntaxError\n".as_slice(),
                0,
            ),
            (
                "escaped-function",
                "import vm from 'node:vm'; const script = new vm.Script('(function(){ return 42; })'); const f = script.runInThisContext(); process.stdout.write(String(f()) + '\\n');",
                b"42\n".as_slice(),
                0,
            ),
            (
                "construct-runner",
                "import vm from 'node:vm'; const runner = vm.runInThisContext; const before = runner.prototype; const after = {}; const options = { get filename() { runner.prototype = after; return 'changed.js'; } }; const fallback = new runner('1', options); const result = new runner('({ answer: 42 })'); process.stdout.write(String(Object.getPrototypeOf(fallback) === before) + ',' + String(runner.prototype === after) + ',' + String(result.answer) + '\\n');",
                b"true,true,42\n".as_slice(),
                0,
            ),
            (
                "host-exit-override",
                "process.exit(23);",
                b"".as_slice(),
                23,
            ),
        ];

        for (name, source, expected_stdout, expected_exit_code) in cases {
            let directory =
                std::env::temp_dir().join(format!("bamts-cli-vm-{name}-{}", std::process::id()));
            let _ = std::fs::remove_dir_all(&directory);
            std::fs::create_dir_all(&directory)?;
            let entrypoint = directory.join("main.ts");
            std::fs::write(&entrypoint, source)?;

            let args = parse_args(["run", entrypoint.to_str().expect("UTF-8 temp path")])?;
            let outcome = super::execute(&args)?;
            assert_eq!(outcome.stdout, expected_stdout, "{name}");
            assert_eq!(outcome.exit_code, expected_exit_code, "{name}");
            std::fs::remove_dir_all(directory)?;
        }
        Ok(())
    }
}
