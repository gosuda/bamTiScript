use crate::args::{ArgsError, CliArgs, ExecutionTarget, Mode};
use crate::cli::{
    diagnostic_format::{self as tsc_diagnostics, TscDiagnosticFormat},
    tsc_args::ParsedTscCommand,
};
use crate::context::ExecutionContext;
use crate::diagnostics::{self, DiagnosticSource, TruncationNotice};
use bamts::discover_project;
use bamts_compiler::CancellationToken;
use bamts_compiler::lower::LowerOptions;
use bamts_compiler::pipeline::{
    FrontendMode, ProgramFrontendOutput, compile_program_frontend_with_cancel,
};
use bamts_compiler::program::{
    ProgramLoadError, ProgramLoader, ProgramLowerError, ResolvedProgram,
};
use bamts_compiler::{
    diagnostic::{Diagnostic, DiagnosticReport, DiagnosticSeverity},
    diagnostics_parser::map_parse_diagnostics,
    lint::{LintOverride, LintProfile, LintTable},
    project::{ProjectConfig, ProjectRoot, canonical::canonicalize, parse_bamts_toml},
};
use bamts_runtime::Limits;
use std::error::Error;
use std::ffi::OsString;
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::ExitStatus;
use std::sync::atomic::AtomicUsize;

mod native;
mod process;
mod project;
mod tsc;

pub use native::compile_program;
#[cfg(any(test, target_env = "msvc"))]
pub(crate) use process::capture_process_with_cancel;
pub use tsc::execute_tsc;

#[cfg(all(test, windows))]
use native::fallback_cache_root_path_in_context;
#[cfg(test)]
use native::{
    RunInputs, claim_published_executable, content_hash, probe_toolchain, run_aot, run_jit,
};
#[cfg(all(test, unix))]
use native::{
    effective_uid, ensure_private_fallback_cache_root, fallback_cache_root_path, link_executable,
    probe_toolchain_in_context, validate_fallback_parent_chain,
};
#[cfg(test)]
use project::project_overrides;
#[cfg(test)]
use tsc::{TSC_INIT_CONFIG, TSC_INIT_CREATED, execute_tsc_in};

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
    /// The system did not start the thread that runs a program in the JIT.
    ProgramThread(io::Error),
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
            Self::ProgramThread(source) => {
                write!(
                    formatter,
                    "could not start the thread of the program: {source}"
                )
            }
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
            | Self::PublishExecutable { source, .. }
            | Self::ProgramThread(source) => Some(source),
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
    execute_in_context_with_cancel(args, context, CancellationToken::new(), Limits::program())
}

/// [`execute`] with caller-controlled cooperative cancellation.
pub fn execute_with_cancel(
    args: &CliArgs,
    cancel: CancellationToken,
) -> Result<CommandOutcome, DriverError> {
    cancel.check().map_err(|_| DriverError::Cancelled)?;
    let context = ExecutionContext::ambient()?;
    execute_in_context_with_cancel(args, &context, cancel, Limits::program())
}

/// The canonical CLI execution seam with explicit process inputs and cancellation.
///
/// `limits` is the caller's execution budget for the JIT run: the CLI run path
/// passes [`Limits::program`], which lets a program run for as long as it runs,
/// and a host that waits synchronously for one request, such as the `--api`
/// execute method, passes a finite fuel so a runaway loop answers `fuel
/// exhausted` instead of hanging the host. The AOT image runs in its own
/// process with [`Limits::program`]; `cancel` is its bound and terminates it.
pub fn execute_in_context_with_cancel(
    args: &CliArgs,
    context: &ExecutionContext,
    cancel: CancellationToken,
    limits: Limits,
) -> Result<CommandOutcome, DriverError> {
    cancel.check().map_err(|_| DriverError::Cancelled)?;
    match args.mode {
        Mode::Check | Mode::Compile | Mode::Run => {
            let frontend = load_program_frontend_in_context_with_cancel(args, context, &cancel)?;
            match args.mode {
                Mode::Check => native::check(args, &frontend),
                Mode::Compile => {
                    native::compile_in_context_with_cancel(args, &frontend, context, &cancel)
                }
                Mode::Run => {
                    native::run_in_context_with_cancel(args, &frontend, context, &cancel, &limits)
                }
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
        ..LowerOptions::default()
    }
}

fn required_entrypoint(args: &CliArgs) -> Result<&Path, DriverError> {
    args.entrypoint
        .as_deref()
        .map(Path::new)
        .ok_or(DriverError::MissingEntrypoint)
}

struct LoadedProgramFrontend {
    pub(super) program: ResolvedProgram,
    pub(super) output: ProgramFrontendOutput,
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
        canonicalize(&absolute_entrypoint).map_err(|source| DriverError::ReadSource {
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
    let canonical_root = canonicalize(project.root())
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
    pub(super) text: String,
    pub(super) truncation: Option<TruncationNotice>,
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
    render_diagnostics(args, frontend, &diagnostics)
}

fn render_diagnostics(
    args: &CliArgs,
    frontend: &LoadedProgramFrontend,
    diagnostics: &[Diagnostic],
) -> RenderedDiagnostics {
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
        &DiagnosticReport::new(diagnostics),
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

/// Renders the diagnostics of a program about to run or compile. Node does not load
/// a JavaScript module that breaks an early error, so one of those stops it.
fn require_clean_frontend(
    args: &CliArgs,
    frontend: &LoadedProgramFrontend,
) -> Result<RenderedDiagnostics, DriverError> {
    let early = bamts::early_errors(&frontend.program, false);
    if !early.is_empty() {
        let rendered = render_diagnostics(args, frontend, &early);
        return Err(DriverError::Diagnostics {
            rendered: rendered.text,
            truncation: rendered.truncation,
        });
    }
    Ok(render_program_diagnostics(args, frontend))
}

/// Renders the diagnostics of a program about to run. Modules reachable only
/// through `import()` reject that `import()` at run time instead of failing
/// the run, so this applies the facade's run rule through the same function
/// rather than the whole-program check the compile path uses.
fn require_runnable_frontend(
    args: &CliArgs,
    frontend: &LoadedProgramFrontend,
) -> Result<RenderedDiagnostics, DriverError> {
    let failures = bamts::run_blocking_diagnostics(&frontend.program, &frontend.output, false);
    if !failures.is_empty() {
        let rendered = render_diagnostics(args, frontend, &failures);
        return Err(DriverError::Diagnostics {
            rendered: rendered.text,
            truncation: rendered.truncation,
        });
    }
    Ok(render_program_diagnostics(args, frontend))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::ffi::OsString;
    use std::path::{Path, PathBuf};
    use std::sync::atomic::{AtomicUsize, Ordering};
    #[cfg(unix)]
    use std::thread;
    #[cfg(unix)]
    use std::time::{Duration, Instant};
    use std::{fs, process};

    use bamts_compiler::{
        CancellationToken,
        lint::{LintLevel, SourceDialect, rule_by_name},
        project::canonical::slash_text,
    };

    use crate::args::{ArgsError, parse_args};
    use crate::cli::tsc_args::{TscExitStatus, parse_tsc_args};
    use crate::context::ExecutionContext;

    use super::{
        CommandOutcome, DriverError, Limits, content_hash, execute_in_context,
        execute_in_context_with_cancel, execute_tsc, execute_tsc_in, levels, lower_options,
        probe_toolchain,
    };
    #[cfg(unix)]
    use super::{capture_process_with_cancel, link_executable, probe_toolchain_in_context};

    /// The JIT gives a program a stack of its own. A caller on a thread with the
    /// 2 MiB that Rust gives a new thread, as the worker of the npm package is,
    /// still sees `RangeError` for builtins that call builtins without end.
    #[test]
    fn the_jit_runs_a_program_on_a_stack_of_its_own() -> Result<(), Box<dyn std::error::Error>> {
        let directory = std::env::temp_dir().join(format!("bamts-cli-jit-stack-{}", process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory)?;
        fs::write(
            directory.join("main.ts"),
            "const cycle: any = [];\n\
             cycle.join = Array.prototype.toString;\n\
             try { String(cycle); } catch (error) { console.log((error as Error).name); }\n\
             console.log(\"ok\");\n",
        )?;
        let context = ExecutionContext::new(&directory, BTreeMap::new())?;
        let args = parse_args(["run", "--jit", "main.ts"])?;
        let outcome = std::thread::Builder::new()
            .stack_size(2 << 20)
            .spawn(move || execute_in_context(&args, &context))?
            .join()
            .expect("the calling thread does not panic")?;
        assert_eq!(outcome.stdout, b"RangeError\nok\n");
        assert_eq!(outcome.exit_code, 0);
        fs::remove_dir_all(directory)?;
        Ok(())
    }

    #[test]
    fn the_jit_runs_a_program_past_the_default_fuel() -> Result<(), Box<dyn std::error::Error>> {
        let directory = std::env::temp_dir().join(format!("bamts-cli-jit-fuel-{}", process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory)?;
        fs::write(
            directory.join("main.ts"),
            "let sum = 0;\n\
             for (let i = 0; i < 200000; i++) { sum = (sum + i) | 0; }\n\
             console.log(sum);\n",
        )?;
        let context = ExecutionContext::new(&directory, BTreeMap::new())?;
        let args = parse_args(["run", "--jit", "main.ts"])?;
        let outcome = execute_in_context(&args, &context)?;
        assert_eq!(outcome.stdout, b"-1474936480\n");
        assert_eq!(outcome.exit_code, 0);
        fs::remove_dir_all(directory)?;
        Ok(())
    }

    #[test]
    fn the_run_path_is_not_bounded_by_the_api_fuel() -> Result<(), Box<dyn std::error::Error>> {
        let directory =
            std::env::temp_dir().join(format!("bamts-cli-jit-unbounded-{}", process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory)?;
        fs::write(
            directory.join("main.ts"),
            "let sum = 0;\n\
             for (let i = 0; i < 1000000; i++) { sum = (sum + i) | 0; }\n\
             console.log(sum);\n",
        )?;
        let context = ExecutionContext::new(&directory, BTreeMap::new())?;
        let args = parse_args(["run", "--jit", "main.ts"])?;
        let three_api_budgets = Limits {
            fuel: 3_000_000,
            ..Limits::program()
        };
        let bounded = execute_in_context_with_cancel(
            &args,
            &context,
            CancellationToken::new(),
            three_api_budgets,
        )
        .expect_err("the loop needs more than three API budgets");
        assert!(bounded.to_string().contains("fuel exhausted"), "{bounded}");
        let outcome = execute_in_context(&args, &context)?;
        assert_eq!(outcome.stdout, b"1783293664\n");
        assert_eq!(outcome.exit_code, 0);
        fs::remove_dir_all(directory)?;
        Ok(())
    }

    #[test]
    fn cli_run_defers_dynamic_only_early_error_to_import_rejection()
    -> Result<(), Box<dyn std::error::Error>> {
        let directory =
            std::env::temp_dir().join(format!("bamts-cli-dynamic-only-{}", process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory)?;
        fs::write(
            directory.join("main.ts"),
            "console.log(\"before\");\n\
             const pending = import(\"./early-error_FIXTURE.js\");\n\
             pending.then(\n\
             () => console.log(\"fulfilled\"),\n\
             (error) => console.log(\"rejected:\" + error.name),\n\
             );\n\
             console.log(\"after\");\n",
        )?;
        fs::write(
            directory.join("early-error_FIXTURE.js"),
            "let wired = 1;\nlet wired = 2;\n",
        )?;
        let context = ExecutionContext::new(&directory, BTreeMap::new())?;
        let args = parse_args(["run", "--jit", "--js-compat", "main.ts"])?;
        let outcome = execute_in_context(&args, &context)?;
        assert_eq!(outcome.exit_code, 0);
        assert_eq!(outcome.stdout, b"before\nafter\nrejected:SyntaxError\n");
        fs::remove_dir_all(directory)?;
        Ok(())
    }

    #[cfg(unix)]
    fn cancel_after_readiness<T>(
        marker: &Path,
        cancel: &CancellationToken,
        capture: impl FnOnce() -> T,
    ) -> (T, std::io::Result<String>) {
        use std::io;

        thread::scope(|scope| {
            let (capture_finished, finished) = std::sync::mpsc::channel::<()>();
            let readiness = scope.spawn(move || {
                loop {
                    match fs::read_to_string(marker) {
                        Ok(message) if message.ends_with('\n') => {
                            cancel.cancel();
                            return Ok(message);
                        }
                        Ok(_) => {}
                        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                        Err(error) => {
                            cancel.cancel();
                            return Err(error);
                        }
                    }
                    if !matches!(
                        finished.recv_timeout(Duration::from_millis(5)),
                        Err(std::sync::mpsc::RecvTimeoutError::Timeout)
                    ) {
                        return Err(io::Error::other(
                            "fixture exited before reporting readiness",
                        ));
                    }
                }
            });
            let outcome = capture();
            drop(capture_finished);
            (
                outcome,
                readiness.join().expect("readiness watcher completes"),
            )
        })
    }

    #[cfg(unix)]
    #[test]
    fn hanging_toolchain_probe_maps_cancellation_to_driver_cancelled()
    -> Result<(), Box<dyn std::error::Error>> {
        use std::os::unix::fs::PermissionsExt;

        let directory = tempfile::tempdir()?;
        let compiler = directory.path().join("fake-cc");
        fs::write(
            &compiler,
            "#!/bin/sh
printf 'started\\n' > probe-started
/bin/sleep 30
: > probe-returned
",
        )?;
        fs::set_permissions(&compiler, fs::Permissions::from_mode(0o700))?;
        let context = ExecutionContext::new(directory.path(), BTreeMap::new())?;
        let cancel = CancellationToken::new();
        let (outcome, ready) =
            cancel_after_readiness(&directory.path().join("probe-started"), &cancel, || {
                probe_toolchain_in_context(compiler.into_os_string(), &context, &cancel)
            });
        assert_eq!(ready?, "started\n");
        let error = outcome.expect_err("cancelled compiler probe must fail as cancellation");
        assert!(matches!(error, DriverError::Cancelled));
        assert!(
            !directory.path().join("probe-returned").exists(),
            "compiler probe reached its natural exit"
        );
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
    fn import_helpers_on_the_command_line_reaches_the_project_overrides() {
        let with = parse_tsc_args(["--importHelpers", "--target", "es5"]).expect("flag parses");
        assert_eq!(super::project_overrides(&with).import_helpers, Some(true));
        let without = parse_tsc_args(["--target", "es5"]).expect("flags parse");
        assert_eq!(super::project_overrides(&without).import_helpers, None);
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
                slash_text(&config)
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
                slash_text(&fixture.0.join("tsconfig.json"))
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
                slash_text(&directory)
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
            format!(
                "error TS5083: Cannot read file '{}'.\n",
                slash_text(&config)
            ),
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
                slash_text(&fixture.0.join("empty.json"))
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
                slash_text(&fixture.0.join("none.json"))
            ),
        );

        let absolute_pattern = fixture.0.join("absolute/**/*.ts");
        fixture.write(
            "absolute.json",
            &format!(r#"{{"include":["{}"]}}"#, slash_text(&absolute_pattern)),
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
                slash_text(&fixture.0.join("absolute.json")),
                slash_text(&absolute_pattern)
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
                slash_text(&fixture.0.join("app/tsconfig.json"))
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
        let dependency = slash_text(&fixture.0.join("src/b.ts"));
        let root = slash_text(&fixture.0.join("src/a.ts"));
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
            format!("{}\n", slash_text(&fixture.0.join("bad.ts")))
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
        // The emitted executable has the platform's executable extension: none on
        // Unix, `exe` on Windows.
        let emitted = path.with_extension(std::env::consts::EXE_EXTENSION);
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
    fn tsc_project_out_file_reports_positioned_ts5102_and_emits_per_file() {
        let fixture = TscFixture::new();
        fixture.write("src/main.ts", "export const answer = 42;\n");
        fixture.write(
            "tsconfig.json",
            r#"{"files":["src/main.ts"],"compilerOptions":{"outFile":"dist/bundle.js"}}"#,
        );
        let outcome = execute_tsc_in(
            &parse_tsc_args(["-p", "tsconfig.json", "--pretty", "false"]).expect("project parses"),
            &fixture.0,
        )
        .expect("project executes");
        assert_eq!(
            outcome.exit_code,
            TscExitStatus::DiagnosticsPresentOutputsGenerated.code()
        );
        let stdout = String::from_utf8(outcome.stdout).expect("UTF-8 diagnostics");
        assert!(
            stdout.contains("tsconfig.json(1,45): error TS5102:"),
            "positioned at the outFile key: {stdout}"
        );
        assert!(
            stdout.contains("Option 'outFile' has been removed."),
            "{stdout}"
        );
        assert!(
            fixture.0.join("src/main.js").is_file(),
            "per-file output still emits"
        );
        assert!(
            !fixture.0.join("dist/bundle.js").exists(),
            "no bundle is produced"
        );
    }

    #[test]
    fn tsc_project_out_file_via_extends_is_unpositioned() {
        let fixture = TscFixture::new();
        fixture.write("src/main.ts", "export const answer = 42;\n");
        fixture.write("base.json", r#"{"compilerOptions":{"outFile":"out.js"}}"#);
        fixture.write(
            "tsconfig.json",
            r#"{"extends":"./base.json","files":["src/main.ts"]}"#,
        );
        let outcome = execute_tsc_in(
            &parse_tsc_args(["-p", "tsconfig.json", "--pretty", "false"]).expect("project parses"),
            &fixture.0,
        )
        .expect("project executes");
        assert_eq!(
            outcome.exit_code,
            TscExitStatus::DiagnosticsPresentOutputsGenerated.code()
        );
        let stdout = String::from_utf8(outcome.stdout).expect("UTF-8 diagnostics");
        assert!(stdout.contains("error TS5102:"), "{stdout}");
        assert!(
            stdout.lines().any(|line| line.starts_with("error TS5102:")),
            "no file position: {stdout}"
        );
        assert!(fixture.0.join("src/main.js").is_file());
    }

    #[test]
    fn tsc_direct_out_file_reports_ts5102_and_emits_per_file() {
        let fixture = TscFixture::new();
        fixture.write("a.ts", "export const x = 1;\n");
        let outcome = execute_tsc_in(
            &parse_tsc_args([
                "--outFile",
                "x.js",
                "--ignoreConfig",
                "--pretty",
                "false",
                "a.ts",
            ])
            .expect("direct parses"),
            &fixture.0,
        )
        .expect("direct executes");
        assert_eq!(
            outcome.exit_code,
            TscExitStatus::DiagnosticsPresentOutputsGenerated.code()
        );
        let stdout = String::from_utf8(outcome.stdout).expect("UTF-8 diagnostics");
        assert!(stdout.contains("error TS5102:"), "{stdout}");
        assert!(
            stdout.lines().any(|line| line.starts_with("error TS5102:")),
            "TS5102 is unpositioned: {stdout}"
        );
        assert!(
            fixture.0.join("a.js").is_file(),
            "per-file output still emits"
        );
        assert!(!fixture.0.join("x.js").exists(), "no bundle is produced");
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

    #[cfg(windows)]
    #[test]
    fn fallback_cache_root_refuses_the_temporary_directory_of_windows() {
        let root = |variables: &[(&str, &str)]| {
            let env = variables
                .iter()
                .map(|(name, value)| (OsString::from(name), OsString::from(value)))
                .collect();
            let context = ExecutionContext::new(std::env::temp_dir(), env).expect("context");
            super::fallback_cache_root_path_in_context(&context)
        };
        let refused = |variables: &[(&str, &str)]| {
            matches!(
                root(variables),
                Err(DriverError::UnsafeFallbackCacheRoot { .. })
            )
        };

        // Nothing names a directory of the user.
        assert!(refused(&[]));
        assert!(refused(&[("SystemRoot", r"D:\Windows")]));
        assert!(refused(&[("WINDIR", r"D:\Windows")]));
        // The SYSTEM account names it, in any spelling.
        assert!(refused(&[
            ("SystemRoot", r"C:\Windows"),
            ("TEMP", r"c:\windows\TEMP\")
        ]));
        assert!(refused(&[
            ("SystemRoot", r"D:\Windows"),
            ("TEMP", "D:/Windows/Temp/")
        ]));
        let windows = std::env::var("SystemRoot").expect("SystemRoot");
        for spelling in [
            format!("{windows}/Temp").replace('\\', "/"),
            format!(r"\\?\{windows}\Temp"),
            format!(r"{windows}\.\Temp"),
            format!(r"{windows}\System32\..\Temp"),
        ] {
            assert!(
                refused(&[("SystemRoot", &windows), ("TEMP", &spelling)]),
                "{spelling}"
            );
        }
        // A directory below it is as open to other users, and it need not exist yet.
        for below in [
            format!(r"{windows}\Temp\bamts-missing"),
            format!("{windows}/Temp/bamts-missing/deeper/"),
        ] {
            assert!(
                refused(&[("SystemRoot", &windows), ("TEMP", &below)]),
                "{below}"
            );
        }
        // A name that only starts the same way is another directory.
        assert!(!refused(&[
            ("SystemRoot", &windows),
            ("TEMP", &format!(r"{windows}\Temporary"))
        ]));
        // A junction is a directory that any user can make, and it leads there too.
        let junction = std::env::temp_dir().join(format!("bamts-temp-link-{}", std::process::id()));
        let made = std::process::Command::new("cmd")
            .args(["/C", "mklink", "/J"])
            .arg(&junction)
            .arg(format!(r"{windows}\Temp"))
            .output()
            .expect("run mklink");
        assert!(made.status.success(), "{made:?}");
        let through_junction = refused(&[
            ("SystemRoot", &windows),
            ("TEMP", junction.to_str().expect("a UTF-8 path")),
        ]);
        std::fs::remove_dir(&junction).expect("remove the junction");
        assert!(through_junction);

        assert_eq!(
            root(&[
                ("SystemRoot", r"C:\Windows"),
                ("TMP", r"D:\Temp"),
                ("USERNAME", "builder")
            ])
            .expect("a directory of the user"),
            PathBuf::from(r"D:\Temp\bamts-cache-builder")
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

        let error = super::run_jit(
            super::RunInputs {
                args: &args,
                entrypoint: &entrypoint,
                warnings,
                executable: &executable,
                context: &context,
            },
            &cancel,
            &bamts_runtime::Limits::program(),
        )
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

        let error = super::run_aot(
            super::RunInputs {
                args: &args,
                entrypoint: &entrypoint,
                warnings,
                executable: &executable,
                context: &context,
            },
            &cancel,
        )
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

    #[cfg(unix)]
    #[test]
    fn managed_capture_kills_descendant_without_external_kill_before_reader_join()
    -> Result<(), Box<dyn std::error::Error>> {
        let directory = tempfile::tempdir()?;
        let empty_path = directory.path().join("empty-path");
        std::fs::create_dir(&empty_path)?;
        let pid_file = directory.path().join("descendant.pid");
        let cancel = CancellationToken::new();
        let mut command = process::Command::new("/bin/sh");
        command
            .args([
                "-c",
                r#"(/bin/sleep 30; : > descendant-returned) & child=$!; printf '%s\n' "$child" > descendant.pid; wait"#,
            ])
            .current_dir(directory.path())
            .env("PATH", empty_path);
        let (output, ready) = cancel_after_readiness(&pid_file, &cancel, || {
            capture_process_with_cancel(&mut command, &cancel)
        });
        let output = output?;
        assert!(output.is_none(), "cancellation has exit precedence");
        assert!(
            !directory.path().join("descendant-returned").exists(),
            "the descendant closed its pipes without being killed"
        );
        let pid = ready?.trim_end().parse::<u32>()?;
        let deadline = Instant::now() + Duration::from_secs(2);
        loop {
            let alive = process::Command::new("/bin/ps")
                .args(["-o", "stat=", "-p", &pid.to_string()])
                .output()
                .ok()
                .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_owned())
                .is_some_and(|state| !state.is_empty() && !state.starts_with('Z'));
            if !alive {
                break;
            }
            assert!(
                Instant::now() < deadline,
                "descendant PID {pid} survived cancellation"
            );
            thread::sleep(Duration::from_millis(5));
        }
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
