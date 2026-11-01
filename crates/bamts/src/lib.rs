//! The supported public entry point for compiling and running BamTS programs.
//!
//! The component crates remain available through the modules re-exported here;
//! applications can depend on `bamts` without coupling to the internal native
//! ABI crate.

#![forbid(unsafe_code)]

use std::error::Error as StdError;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

use bamts_cancel::{CancellationToken, Cancelled};
use bamts_compiler::diagnostic::{Diagnostic, DiagnosticSeverity};
use bamts_compiler::lint::{LintProfile, LintTable};
use bamts_compiler::lower::LowerOptions;
use bamts_compiler::parser::parse;
use bamts_compiler::pipeline::{FrontendMode, compile_program_frontend_with_cancel};
use bamts_compiler::program::{
    ProgramLoadError, ProgramLoader, ProgramLowerError, ResolvedProgram, lower_program_with_cancel,
};
use bamts_compiler::project::{ConfigError, ProjectConfig, ProjectRoot};
use bamts_compiler::scanner::scan;
use bamts_compiler::source::ScriptKind;

pub use bamts_bytecode as bytecode;
pub use bamts_compiler as compiler;
#[cfg(feature = "node-host")]
pub use bamts_node as node;
#[cfg(feature = "node-host")]
pub use bamts_node::ScriptCompiler;
pub use bamts_runtime as runtime;

/// Native-code backends, available only when either native-code feature is enabled.
#[cfg(any(feature = "aot", feature = "host-jit"))]
pub use bamts_codegen as codegen;

/// The output observable to a program embedding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramOutput {
    /// Bytes written to standard output by the program.
    pub stdout: Vec<u8>,
    /// The program's requested process exit code.
    pub exit_code: i32,
}

/// A failure at the facade boundary.
///
/// This enum is `#[non_exhaustive]`. Downstream matches must include a
/// wildcard arm so that future variants can be added without a major bump.
///
/// ```compile_fail
/// fn classify(err: bamts::Error) -> &'static str {
///     match err {
///         bamts::Error::ReadConfig { .. } => "read",
///         bamts::Error::ProjectConfig { .. } => "project",
///         bamts::Error::ProgramLoad(_) => "load",
///         bamts::Error::Diagnostics { .. } => "diagnostics",
///         bamts::Error::Lower(_) => "lower",
///         bamts::Error::Runtime(_) => "runtime",
///     }
/// }
/// ```
#[derive(Debug)]
#[non_exhaustive]
pub enum Error {
    /// The operation was cancelled.
    Cancelled(Cancelled),
    /// The project configuration could not be read.
    ReadConfig {
        path: PathBuf,
        source: std::io::Error,
    },
    /// The project configuration is invalid.
    ProjectConfig { path: PathBuf, source: ConfigError },
    /// The entrypoint or one of its dependencies could not be loaded.
    ProgramLoad(ProgramLoadError),
    /// The complete program frontend produced one or more error diagnostics.
    Diagnostics { diagnostics: Vec<Diagnostic> },
    /// The checked program cannot be represented in verified BamTS bytecode.
    Lower(ProgramLowerError),
    /// The verified program did not execute successfully.
    Runtime(bamts_runtime::RuntimeError),
    /// Native object emission failed.
    #[cfg(feature = "aot")]
    Aot(bamts_codegen::AotError),
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cancelled(error) => error.fmt(formatter),
            Self::ReadConfig { path, source } => write!(
                formatter,
                "could not read project configuration `{}`: {source}",
                path.display()
            ),
            Self::ProjectConfig { path, source } => write!(
                formatter,
                "invalid project configuration `{}`: {source}",
                path.display()
            ),
            Self::ProgramLoad(error) => write!(formatter, "could not load program: {error}"),
            Self::Diagnostics { diagnostics } => write!(
                formatter,
                "program has {} error diagnostic(s)",
                diagnostics.len()
            ),
            Self::Lower(error) => write!(formatter, "could not compile program: {error}"),
            Self::Runtime(error) => write!(formatter, "program execution failed: {error}"),
            #[cfg(feature = "aot")]
            Self::Aot(error) => write!(formatter, "could not emit native object: {error}"),
        }
    }
}

impl StdError for Error {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Cancelled(error) => Some(error),
            Self::ReadConfig { source, .. } => Some(source),
            Self::ProjectConfig { source, .. } => Some(source),
            Self::ProgramLoad(error) => Some(error),
            Self::Diagnostics { .. } => None,
            Self::Lower(error) => Some(error),
            Self::Runtime(error) => Some(error),
            #[cfg(feature = "aot")]
            Self::Aot(error) => Some(error),
        }
    }
}

impl From<ProgramLoadError> for Error {
    fn from(error: ProgramLoadError) -> Self {
        Self::ProgramLoad(error)
    }
}

impl From<Cancelled> for Error {
    fn from(error: Cancelled) -> Self {
        Self::Cancelled(error)
    }
}

impl From<ProgramLowerError> for Error {
    fn from(error: ProgramLowerError) -> Self {
        Self::Lower(error)
    }
}

impl From<bamts_runtime::RuntimeError> for Error {
    fn from(error: bamts_runtime::RuntimeError) -> Self {
        Self::Runtime(error)
    }
}

/// Result type returned by facade convenience entry points.
pub type Result<T, E = Error> = std::result::Result<T, E>;

/// Compiles an entrypoint and its complete local module graph into one executable program.
///
/// This convenience API enables JavaScript compatibility for `.js` and `.jsx`
/// entrypoints. The CLI remains strict by default and requires `--js-compat`.
///
/// ```
/// # fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
/// let directory = std::env::temp_dir().join(format!(
///     "bamts-facade-compile-{}",
///     std::process::id(),
/// ));
/// std::fs::create_dir_all(&directory)?;
/// let path = directory.join("main.ts");
/// std::fs::write(&path, "let answer = 42;")?;
/// let executable = bamts::compile_source_file(&path)?;
/// std::fs::remove_dir_all(directory)?;
/// assert_eq!(executable.wire().modules().len(), 1);
/// # Ok(())
/// # }
/// ```
pub fn compile_source_file(
    path: impl AsRef<Path>,
) -> Result<bamts_compiler::program::ExecutableProgram> {
    compile_source_file_with_cancel(path, &CancellationToken::new())
}

/// Compiles an entrypoint and its complete local module graph with cancellation.
pub fn compile_source_file_with_cancel(
    path: impl AsRef<Path>,
    cancel: &CancellationToken,
) -> Result<bamts_compiler::program::ExecutableProgram> {
    compile_source_file_with_lints(path, &LintTable::new(LintProfile::Default), cancel)
}

/// Compiles an entrypoint and its complete local module graph under `lints`.
pub fn compile_source_file_with_lints(
    path: impl AsRef<Path>,
    lints: &LintTable,
    cancel: &CancellationToken,
) -> Result<bamts_compiler::program::ExecutableProgram> {
    compile_entry(path.as_ref(), lints, false, cancel)
}

/// Compiles an entrypoint the host runs as an ECMAScript Script. Its top-level
/// `var` and function names live on the global object, and module syntax in it
/// is an error. A file cannot say this of itself, which is why it is a separate
/// entry: Node runs the same bytes as a CommonJS module.
pub fn compile_script_file(
    path: impl AsRef<Path>,
    lints: &LintTable,
    cancel: &CancellationToken,
) -> Result<bamts_compiler::program::ExecutableProgram> {
    compile_entry(path.as_ref(), lints, true, cancel)
}

fn compile_entry(
    path: &Path,
    lints: &LintTable,
    script_entry: bool,
    cancel: &CancellationToken,
) -> Result<bamts_compiler::program::ExecutableProgram> {
    let path = canonical_entrypoint_with_cancel(path, cancel)?;
    let fallback_root = path.parent().map(Path::to_path_buf).ok_or_else(|| {
        Error::ProgramLoad(ProgramLoadError::InvalidRoot(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "entrypoint has no parent directory",
        )))
    })?;
    let resolved = resolve_project_with_cancel(&path, fallback_root, cancel)?;
    let frontend = compile_program_frontend_with_cancel(
        &resolved.program,
        FrontendMode::Check,
        lints,
        cancel,
    )?;
    let diagnostics = frontend
        .modules()
        .iter()
        .flat_map(|module| module.diagnostics().iter())
        .filter(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error)
        .cloned()
        .collect::<Vec<_>>();
    if !diagnostics.is_empty() {
        return Err(Error::Diagnostics { diagnostics });
    }
    let diagnostics = early_errors(&resolved.program, script_entry);
    if !diagnostics.is_empty() {
        return Err(Error::Diagnostics { diagnostics });
    }
    lower_program_with_cancel(
        &resolved.program,
        &frontend,
        LowerOptions {
            javascript_compatibility: true,
            script_entry,
        },
        cancel,
    )
    .map_err(Error::from)
}

/// The early errors of every JavaScript module about to run. TypeScript sources
/// answer to the checker instead.
fn early_errors(program: &ResolvedProgram, script_entry: bool) -> Vec<Diagnostic> {
    let entrypoint = program.entrypoint().source_id();
    program
        .modules()
        .iter()
        .filter(|module| {
            matches!(
                module.script_kind(),
                ScriptKind::JavaScript | ScriptKind::JavaScriptReact
            )
        })
        .flat_map(|module| {
            let scanned = scan(
                module.source_id(),
                module.script_kind(),
                module.source().clone(),
            );
            let parsed = parse(scanned);
            if script_entry && module.source_id() == entrypoint {
                bamts_compiler::early_errors::check_script(parsed.product())
            } else {
                bamts_compiler::early_errors::check(parsed.product())
            }
        })
        .collect()
}

/// Runs an entrypoint and its complete local module graph with the deterministic
/// Node-compatible host.
///
/// ```
/// # fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
/// let path = std::env::temp_dir().join(format!(
///     "bamts-facade-run-{}.ts",
///     std::process::id(),
/// ));
/// std::fs::write(&path, "console.log(42);")?;
/// let output = bamts::run_program(&path)?;
/// std::fs::remove_file(path)?;
/// assert_eq!(output.stdout, b"42\n");
/// assert_eq!(output.exit_code, 0);
/// # Ok(())
/// # }
/// ```
#[cfg(feature = "node-host")]
pub fn run_program(path: impl AsRef<Path>) -> Result<ProgramOutput> {
    let executable = compile_source_file_with_cancel(path, &CancellationToken::new())?;
    let mut host = bamts_node::NodeHost::new();
    host.set_script_compiler(Box::new(ScriptCompiler));
    let outcome = bamts_runtime::run(
        executable.wire(),
        &mut host,
        &bamts_runtime::Limits::default(),
    )?;

    Ok(ProgramOutput {
        stdout: host.stdout().to_vec(),
        exit_code: host.completion_exit_code(outcome.exit_code),
    })
}

/// Compiles an entrypoint and its complete local module graph into a relocatable
/// native object.
///
/// This entry point requires the `aot` feature because object emission is not
/// part of the default interpreter-only dependency closure.
///
/// ```no_run
/// # fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
/// let path = std::env::temp_dir().join(format!(
///     "bamts-facade-aot-{}.ts",
///     std::process::id(),
/// ));
/// std::fs::write(&path, "let answer = 42;")?;
/// let object = bamts::compile_native_object(&path, "x86_64")?;
/// std::fs::remove_file(path)?;
/// assert!(!object.bytes.is_empty());
/// # Ok(())
/// # }
/// ```
#[cfg(feature = "aot")]
pub fn compile_native_object(
    path: impl AsRef<Path>,
    target: &str,
) -> Result<bamts_codegen::AotObject> {
    let executable = compile_source_file_with_cancel(path, &CancellationToken::new())?;
    bamts_codegen::compile_aot(executable.wire(), target).map_err(Error::Aot)
}

#[cfg(feature = "aot")]
impl From<bamts_codegen::AotError> for Error {
    fn from(error: bamts_codegen::AotError) -> Self {
        Self::Aot(error)
    }
}

/// Resolves an entrypoint path with cancellation.
pub fn canonical_entrypoint_with_cancel(
    path: &Path,
    cancel: &CancellationToken,
) -> Result<PathBuf> {
    let absolute = if path.is_absolute() {
        path.to_owned()
    } else {
        std::env::current_dir()
            .map(|directory| directory.join(path))
            .map_err(|error| Error::ProgramLoad(ProgramLoadError::InvalidRoot(error)))?
    };
    cancel.check()?;
    let canonical = fs::canonicalize(&absolute).map_err(|source| {
        Error::ProgramLoad(ProgramLoadError::Read {
            path: absolute,
            source,
        })
    })?;
    cancel.check()?;
    Ok(canonical)
}

/// The root and compiler configuration selected for a canonical entrypoint.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectDiscovery {
    root: PathBuf,
    config: PathBuf,
}

impl ProjectDiscovery {
    #[must_use]
    pub fn root(&self) -> &Path {
        &self.root
    }

    #[must_use]
    pub fn config(&self) -> &Path {
        &self.config
    }
}

/// Selects one project root and `tsconfig.json` for a canonical entrypoint.
///
/// A `bamts.toml` ancestor takes precedence over every `tsconfig.json`
/// ancestor. When neither exists, `fallback_root` defines the project.
#[must_use]
pub fn discover_project(entrypoint: &Path, fallback_root: PathBuf) -> ProjectDiscovery {
    discover_project_with_cancel(entrypoint, fallback_root, &CancellationToken::new())
        .expect("a fresh cancellation token cannot be cancelled")
}

/// Selects a project root and configuration with cancellation.
pub fn discover_project_with_cancel(
    entrypoint: &Path,
    fallback_root: PathBuf,
    cancel: &CancellationToken,
) -> std::result::Result<ProjectDiscovery, Cancelled> {
    let ancestors = || entrypoint.parent().into_iter().flat_map(Path::ancestors);
    let mut root = None;
    for directory in ancestors() {
        cancel.check()?;
        if directory.join("bamts.toml").is_file() {
            root = Some(directory.to_path_buf());
            break;
        }
    }
    if root.is_none() {
        for directory in ancestors() {
            cancel.check()?;
            if directory.join("tsconfig.json").is_file() {
                root = Some(directory.to_path_buf());
                break;
            }
        }
    }
    let root = root.unwrap_or(fallback_root);
    let mut config = None;
    for directory in ancestors().take_while(|directory| directory.starts_with(&root)) {
        cancel.check()?;
        let candidate = directory.join("tsconfig.json");
        if candidate.is_file() {
            config = Some(candidate);
            break;
        }
    }
    Ok(ProjectDiscovery {
        config: config.unwrap_or_else(|| root.join("tsconfig.json")),
        root,
    })
}

/// The project root and loaded module graph selected for a canonical entrypoint.
#[derive(Debug)]
pub struct ResolvedProject {
    /// The canonicalized, validated project root.
    pub root: ProjectRoot,
    /// The loaded entrypoint and its complete local module graph.
    pub program: ResolvedProgram,
}

/// Selects a project root, reads its configuration, and loads the complete
/// module graph for a canonical entrypoint.
///
/// `fallback_root` is used only when no `bamts.toml` or `tsconfig.json`
/// ancestor exists; the caller chooses it (the CLI uses the current directory
/// when the entrypoint is inside it, the facade uses the entrypoint's parent).
pub fn resolve_project(entrypoint: &Path, fallback_root: PathBuf) -> Result<ResolvedProject> {
    resolve_project_with_cancel(entrypoint, fallback_root, &CancellationToken::new())
}

/// Selects a project, reads its configuration, and loads it with cancellation.
pub fn resolve_project_with_cancel(
    entrypoint: &Path,
    fallback_root: PathBuf,
    cancel: &CancellationToken,
) -> Result<ResolvedProject> {
    let project = discover_project_with_cancel(entrypoint, fallback_root, cancel)?;
    cancel.check()?;
    let canonical_root = fs::canonicalize(project.root())
        .map_err(|error| Error::ProgramLoad(ProgramLoadError::InvalidRoot(error)))?;
    cancel.check()?;
    let root = ProjectRoot::new(canonical_root).map_err(|error| {
        Error::ProgramLoad(ProgramLoadError::InvalidRoot(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            error,
        )))
    })?;
    let config_path = project.config().to_owned();
    let config_source = if config_path.is_file() {
        cancel.check()?;
        let source = fs::read_to_string(&config_path).map_err(|source| Error::ReadConfig {
            path: config_path.clone(),
            source,
        })?;
        cancel.check()?;
        source
    } else {
        "{}".to_owned()
    };
    let config = ProjectConfig::parse(&root, &config_path, &config_source).map_err(|source| {
        Error::ProjectConfig {
            path: config_path,
            source,
        }
    })?;
    let loader = ProgramLoader::new(&root, config.options()).map_err(Error::ProgramLoad)?;
    let program = loader
        .load_with_cancel(entrypoint, cancel)
        .map_err(Error::ProgramLoad)?;
    Ok(ResolvedProject { root, program })
}

#[cfg(test)]
mod tests {
    use super::compile_source_file;
    #[cfg(feature = "node-host")]
    use super::run_program;
    use std::error::Error;
    use std::path::{Path, PathBuf};

    fn fixture(name: &str) -> Result<(PathBuf, PathBuf), Box<dyn Error>> {
        let directory =
            std::env::temp_dir().join(format!("bamts-facade-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory)?;
        std::fs::write(
            directory.join("dependency.ts"),
            "export let value = 1; value = 2;",
        )?;
        let entrypoint = directory.join("main.ts");
        std::fs::write(
            &entrypoint,
            "import { value } from './dependency.js'; console.log(value);",
        )?;
        Ok((directory, entrypoint))
    }

    fn remove_fixture(directory: &Path) -> Result<(), Box<dyn Error>> {
        std::fs::remove_dir_all(directory)?;
        Ok(())
    }

    fn tree_fixture(name: &str) -> Result<PathBuf, Box<dyn Error>> {
        let directory = std::env::temp_dir().join(format!(
            "bamts-facade-discovery-{name}-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(directory.join("sub"))?;
        Ok(directory)
    }

    #[test]
    fn bamts_toml_root_wins_over_a_closer_tsconfig() -> Result<(), Box<dyn Error>> {
        let directory = tree_fixture("toml-precedence")?;
        std::fs::write(directory.join("bamts.toml"), "")?;
        std::fs::write(directory.join("shared.ts"), "export let value = 1;")?;
        std::fs::write(directory.join("sub/tsconfig.json"), "{}")?;
        let entrypoint = directory.join("sub/main.ts");
        std::fs::write(
            &entrypoint,
            "import { value } from '../shared.js'; let answer = value;",
        )?;

        // The root is the nearest bamts.toml directory, so the `..` import
        // stays inside the project and compiles.
        let executable = compile_source_file(&entrypoint)?;
        assert_eq!(executable.wire().modules().len(), 2);

        // Without bamts.toml the tsconfig.json directory becomes the root and
        // the same import escapes it.
        std::fs::remove_file(directory.join("bamts.toml"))?;
        let error = compile_source_file(&entrypoint)
            .expect_err("the import must escape the tsconfig-only root");
        assert!(matches!(error, super::Error::ProgramLoad(_)));

        remove_fixture(&directory)?;
        Ok(())
    }

    #[test]
    fn nearest_tsconfig_within_the_root_wins() -> Result<(), Box<dyn Error>> {
        let directory = tree_fixture("tsconfig-chain")?;
        std::fs::write(directory.join("bamts.toml"), "")?;
        std::fs::write(directory.join("tsconfig.json"), "this is not json")?;
        std::fs::write(directory.join("sub/tsconfig.json"), "{}")?;
        let entrypoint = directory.join("sub/main.ts");
        std::fs::write(&entrypoint, "let answer = 42;")?;

        // The nearest tsconfig.json between the entrypoint and the root wins,
        // so the malformed root-level file is never read.
        compile_source_file(&entrypoint)?;

        // With no closer tsconfig.json the root's own file becomes the project
        // configuration and its parse failure names that exact path.
        std::fs::remove_file(directory.join("sub/tsconfig.json"))?;
        let error =
            compile_source_file(&entrypoint).expect_err("the root tsconfig.json must be parsed");
        let expected = std::fs::canonicalize(directory.join("tsconfig.json"))?;
        assert!(matches!(
            error,
            super::Error::ProjectConfig { ref path, .. } if *path == expected
        ));

        remove_fixture(&directory)?;
        Ok(())
    }

    #[cfg(feature = "node-host")]
    fn script_fixture(name: &str, source: &str) -> Result<(PathBuf, PathBuf), Box<dyn Error>> {
        let directory =
            std::env::temp_dir().join(format!("bamts-facade-script-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory)?;
        let entrypoint = directory.join("main.ts");
        std::fs::write(&entrypoint, source)?;
        Ok((directory, entrypoint))
    }

    #[cfg(feature = "node-host")]
    fn run_microtask_checkpoint(
        name: &str,
        source: &str,
    ) -> Result<(Vec<u8>, bamts_runtime::MicrotaskDrain), Box<dyn Error>> {
        let (directory, entrypoint) = script_fixture(name, source)?;
        let executable = compile_source_file(&entrypoint)?;
        let mut host = bamts_node::NodeHost::new();
        host.set_script_compiler(Box::new(super::ScriptCompiler));
        let mut machine = bamts_runtime::Machine::new(
            executable.wire(),
            &mut host,
            bamts_runtime::Limits::default(),
        );
        machine.evaluate()?;
        let drain = machine.drain_microtasks()?;
        drop(machine);
        let stdout = host.stdout().to_vec();
        remove_fixture(&directory)?;
        Ok((stdout, drain))
    }

    #[cfg(feature = "node-host")]
    struct TimerCheckpoint {
        stdout: Vec<u8>,
        waited: bool,
        timer: bamts_runtime::TimerRun,
        before_timer: bamts_runtime::MicrotaskDrain,
        after_timer: bamts_runtime::MicrotaskDrain,
    }

    #[cfg(feature = "node-host")]
    fn run_timer_checkpoint(name: &str, source: &str) -> Result<TimerCheckpoint, Box<dyn Error>> {
        let (directory, entrypoint) = script_fixture(name, source)?;
        let executable = compile_source_file(&entrypoint)?;
        let mut host = bamts_node::NodeHost::new();
        host.set_script_compiler(Box::new(super::ScriptCompiler));
        let mut machine = bamts_runtime::Machine::new(
            executable.wire(),
            &mut host,
            bamts_runtime::Limits::default(),
        );
        machine.evaluate()?;
        let before_timer = machine.drain_microtasks()?;
        let waited = machine.wait_for_timer_expiry()?;
        let timer = machine.run_one_expired_timer()?;
        let after_timer = machine.drain_microtasks()?;
        drop(machine);
        let stdout = host.stdout().to_vec();
        remove_fixture(&directory)?;
        Ok(TimerCheckpoint {
            stdout,
            waited,
            timer,
            before_timer,
            after_timer,
        })
    }

    #[test]
    fn compiles_complete_program_with_module_local_function_ids() -> Result<(), Box<dyn Error>> {
        let (directory, entrypoint) = fixture("compile")?;
        let executable = compile_source_file(&entrypoint)?;

        assert_eq!(executable.wire().modules().len(), 2);
        assert!(
            executable
                .wire()
                .modules()
                .iter()
                .all(|module| module.code().entry().get() == 0)
        );
        remove_fixture(&directory)
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn runs_qualified_import_equals_namespace_alias() -> Result<(), Box<dyn Error>> {
        let source = r#"
            declare namespace A { export namespace B { export const value: number; } }
            import X = A.B;
            type Alias = X;
            const erased: Alias | undefined = undefined;
            process.stdout.write(String(erased === undefined) + "\n");
        "#;
        let (directory, entrypoint) = script_fixture("qualified-import-equals", source)?;
        let output = run_program(&entrypoint)?;

        assert_eq!(output.stdout, b"true\n");
        assert_eq!(output.exit_code, 0);
        remove_fixture(&directory)
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn runs_nested_ambient_qualified_import_equals_namespace_alias() -> Result<(), Box<dyn Error>> {
        let source = r#"
            declare namespace A {
                export namespace B {
                    export namespace C {
                        export const value: number;
                    }
                }
            }
            import X = A.B.C;
            type Alias = X;
            const erased: Alias | undefined = undefined;
            process.stdout.write(String(erased === undefined) + "\n");
        "#;
        let (directory, entrypoint) = script_fixture("nested-qualified-import-equals", source)?;
        let output = run_program(&entrypoint)?;

        assert_eq!(output.stdout, b"true\n");
        assert_eq!(output.exit_code, 0);
        remove_fixture(&directory)
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn runs_merged_export_namespace_value_export() -> Result<(), Box<dyn Error>> {
        let directory = std::env::temp_dir().join(format!(
            "bamts-facade-merged-export-namespace-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory)?;
        std::fs::write(
            directory.join("ns.ts"),
            r#"
                export class C {}
                export namespace C {
                    export const tag = "ns";
                }
                export namespace N {
                    export const x = 1;
                }
                export namespace N {
                    export const y = 2;
                }
                export function F() {
                    return "fn";
                }
                export namespace F {
                    export const z = 3;
                }
            "#,
        )?;
        let entrypoint = directory.join("main.ts");
        std::fs::write(
            &entrypoint,
            r#"
                import { C, N, F } from "./ns.ts";
                process.stdout.write(String(C.tag) + "\n");
                process.stdout.write(String(N.x + N.y) + "\n");
                process.stdout.write(String(F() + F.z) + "\n");
            "#,
        )?;
        let output = run_program(&entrypoint)?;
        assert_eq!(output.stdout, b"ns\n3\nfn3\n");
        assert_eq!(output.exit_code, 0);
        remove_fixture(&directory)
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn runs_two_module_program_with_live_imported_mutation() -> Result<(), Box<dyn Error>> {
        let (directory, entrypoint) = fixture("run")?;
        let output = run_program(&entrypoint)?;

        assert_eq!(output.stdout, b"2\n");
        assert_eq!(output.exit_code, 0);
        remove_fixture(&directory)
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn runs_commonjs_export_equals_import_require() -> Result<(), Box<dyn Error>> {
        let directory = std::env::temp_dir().join(format!(
            "bamts-facade-export-equals-require-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory)?;
        std::fs::write(
            directory.join("dep.ts"),
            r#"
                function run() {
                    process.stdout.write("executed\n");
                }
                export = run;
            "#,
        )?;
        let entrypoint = directory.join("main.ts");
        std::fs::write(
            &entrypoint,
            r#"
                import run = require("./dep.js");
                run();
            "#,
        )?;
        let output = run_program(&entrypoint)?;

        assert_eq!(output.stdout, b"executed\n");
        assert_eq!(output.exit_code, 0);
        remove_fixture(&directory)
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn object_reflection_cannot_transfer_private_fields() -> Result<(), Box<dyn Error>> {
        let source = r#"
            class Secret {
                #value = {
                    value: 7,
                    enumerable: true,
                    configurable: true,
                    writable: true,
                };

                probe(target: object) {
                    try {
                        return target.#value;
                    } catch {
                        return "missing";
                    }
                }
            }

            const source = new Secret();
            const target = {};
            const before = source.probe(target);
            Object.defineProperties(target, source);
            const after = source.probe(target);
            process.stdout.write(String(before === after) + "\n");
        "#;
        let (directory, entrypoint) = script_fixture("private-field-reflection", source)?;
        let output = run_program(&entrypoint)?;

        assert_eq!(output.stdout, b"true\n");
        assert_eq!(output.exit_code, 0);
        remove_fixture(&directory)
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn runs_node_vm_scripts() -> Result<(), Box<dyn Error>> {
        let cases = [
            (
                "default-import",
                "import vm from 'node:vm'; process.stdout.write(String(vm.runInThisContext('1+1')) + '\\n');",
                b"2\n".as_slice(),
            ),
            (
                "named-import",
                "import { runInThisContext } from 'node:vm'; process.stdout.write(String(runInThisContext('1+1')) + '\\n');",
                b"2\n".as_slice(),
            ),
            (
                "syntax-error",
                "import vm from 'node:vm'; try { new vm.Script('('); } catch (error) { process.stdout.write(error.name + '\\n'); }",
                b"SyntaxError\n".as_slice(),
            ),
            (
                "escaped-function",
                "import vm from 'node:vm'; const script = new vm.Script('(function(){ return 42; })'); const f = script.runInThisContext(); process.stdout.write(String(f()) + '\\n');",
                b"42\n".as_slice(),
            ),
            (
                "construct-runner",
                "import vm from 'node:vm'; const runner = vm.runInThisContext; const before = runner.prototype; const after = {}; const options = { get filename() { runner.prototype = after; return 'changed.js'; } }; const fallback = new runner('1', options); const result = new runner('({ answer: 42 })'); process.stdout.write(String(Object.getPrototypeOf(fallback) === before) + ',' + String(runner.prototype === after) + ',' + String(result.answer) + '\\n');",
                b"true,true,42\n".as_slice(),
            ),
        ];

        for (name, source, expected_stdout) in cases {
            let (directory, entrypoint) = script_fixture(name, source)?;
            let output = run_program(&entrypoint)?;
            assert_eq!(output.stdout, expected_stdout, "{name}");
            assert_eq!(output.exit_code, 0, "{name}");
            remove_fixture(&directory)?;
        }
        Ok(())
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn classic_script_completion_matches_node_24() -> Result<(), Box<dyn Error>> {
        let cases = [
            ("expression", "1+1", b"2\n".as_slice()),
            ("declaration", "var x=5", b"undefined\n".as_slice()),
            ("if-value", "if(true){42}", b"42\n".as_slice()),
            ("if-empty", "1;if(true){}", b"undefined\n".as_slice()),
            ("block", "{7}", b"7\n".as_slice()),
            ("for", "for(let i=0;i<3;i++){i}", b"2\n".as_slice()),
            (
                "while-empty",
                "1;while(false){2}",
                b"undefined\n".as_slice(),
            ),
            ("finally", "try{1}finally{2}", b"1\n".as_slice()),
            (
                "catch-empty",
                "try{1;throw 2}catch(e){}",
                b"undefined\n".as_slice(),
            ),
            ("catch-value", "try{throw 1}catch(e){4}", b"4\n".as_slice()),
            (
                "catch-empty-finally",
                "try{1;throw 2}catch(e){}finally{3}",
                b"undefined\n".as_slice(),
            ),
            (
                "try-value-finally",
                "try{1}catch(e){}finally{3}",
                b"1\n".as_slice(),
            ),
            ("switch", "switch(1){case 1:5}", b"5\n".as_slice()),
            ("function", "function f(){}", b"undefined\n".as_slice()),
        ];

        for (name, script, expected_stdout) in cases {
            let source = format!(
                "import vm from 'node:vm'; process.stdout.write(String(vm.runInThisContext({script:?})) + '\\n');"
            );
            let (directory, entrypoint) = script_fixture(&format!("completion-{name}"), &source)?;
            let output = run_program(&entrypoint)?;
            assert_eq!(output.stdout, expected_stdout, "{name}");
            assert_eq!(output.exit_code, 0, "{name}");
            remove_fixture(&directory)?;
        }
        Ok(())
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn classic_script_dynamic_import_resolves_external_namespaces() -> Result<(), Box<dyn Error>> {
        let cases = [
            (
                "external-namespace",
                "import('node:util').then(function(ns) { process.stdout.write(String(typeof ns.parseArgs) + '\\n'); })",
                b"function\n".as_slice(),
            ),
            (
                "computed-specifier",
                "const name = 'node:util'; import(name).then(function(ns) { process.stdout.write(String(typeof ns.parseArgs) + '\\n'); })",
                b"function\n".as_slice(),
            ),
        ];

        for (name, script, expected_stdout) in cases {
            let source = format!("import vm from 'node:vm'; vm.runInThisContext({script:?});");
            let (directory, entrypoint) =
                script_fixture(&format!("classic-import-{name}"), &source)?;
            let output = run_program(&entrypoint)?;
            assert_eq!(output.stdout, expected_stdout, "{name}");
            assert_eq!(output.exit_code, 0, "{name}");
            remove_fixture(&directory)?;
        }
        Ok(())
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn promise_static_methods_chain_at_an_explicit_microtask_checkpoint()
    -> Result<(), Box<dyn Error>> {
        let source = r#"
            const seen: number[] = [];
            const first = Promise.resolve(1).then(value => { seen.push(value); });
            const second = Promise.reject(2).catch(reason => { seen.push(reason); });
            const third = Promise.all([Promise.resolve(3), 4]).then(values => {
                seen.push(values[0] + values[1]);
            });
            const fourth = Promise.resolve(5).finally(() => {}).then(value => {
                seen.push(value);
            });
            Promise.all([first, second, third, fourth]).then(() => {
                process.stdout.write(seen.join(",") + "\n");
            });
        "#;
        let (stdout, drain) = run_microtask_checkpoint("promise-checkpoint", source)?;
        assert!(drain.executed > 0);
        assert!(drain.uncaught.is_empty());
        assert_eq!(stdout, b"1,2,7,5\n");
        Ok(())
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn promise_finally_waits_and_all_keeps_input_order() -> Result<(), Box<dyn Error>> {
        let source = r#"
            const seen: string[] = [];
            let releaseCleanup;
            const cleanup = new Promise(resolve => { releaseCleanup = resolve; });
            const waited = Promise.resolve(10)
                .finally(() => cleanup)
                .then(value => { seen.push("value:" + value); });
            queueMicrotask(() => { seen.push("checkpoint"); });
            queueMicrotask(() => { releaseCleanup(); });

            const replaced = Promise.reject(20)
                .finally(() => Promise.reject(30))
                .catch(reason => { seen.push("reason:" + reason); });
            const empty = Promise.all([]).then(values => {
                seen.push("empty:" + values.length);
            });

            let resolveFirst;
            let resolveSecond;
            const first = new Promise(resolve => { resolveFirst = resolve; });
            const second = new Promise(resolve => { resolveSecond = resolve; });
            const ordered = Promise.all([first, second]).then(values => {
                seen.push("order:" + values.join(":"));
            });
            resolveSecond(2);
            resolveFirst(1);

            Promise.all([waited, replaced, empty, ordered]).then(() => {
                process.stdout.write(seen.join(",") + "\n");
            });
        "#;
        let (stdout, drain) = run_microtask_checkpoint("promise-edges", source)?;
        assert!(drain.executed > 0);
        assert!(drain.uncaught.is_empty());
        assert_eq!(stdout, b"checkpoint,empty:0,order:1:2,value:10,reason:30\n");
        Ok(())
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn promise_all_closes_an_abrupt_iterator_and_keeps_the_original_throw()
    -> Result<(), Box<dyn Error>> {
        let source = r#"
            let closed = false;
            const iterable = {
                [Symbol.iterator]() {
                    return {
                        next() { throw 7; },
                        return() {
                            closed = true;
                            throw 8;
                        },
                    };
                },
            };
            Promise.all(iterable).catch(reason => {
                process.stdout.write(reason + "|" + closed + "\n");
            });

            const lookupFailure = {
                [Symbol.iterator]() {
                    return {
                        next() { throw 7; },
                        get return() { throw 8; },
                    };
                },
            };
            Promise.all(lookupFailure).catch(reason => {
                process.stdout.write("lookup:" + reason + "\n");
            });
        "#;
        let (stdout, drain) = run_microtask_checkpoint("promise-iterator-close", source)?;
        assert!(drain.executed > 0);
        assert!(drain.uncaught.is_empty());
        assert_eq!(stdout, b"7|true\nlookup:7\n");
        Ok(())
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn promise_thenable_getter_is_sync_and_body_is_queued() -> Result<(), Box<dyn Error>> {
        let source = r#"
            let gets = 0;
            let calls = 0;
            const thenable = {
                get then() {
                    gets += 1;
                    return resolve => {
                        calls += 1;
                        resolve(7);
                    };
                },
            };
            const promise = Promise.resolve(thenable);
            process.stdout.write(gets + "|" + calls + "|");
            promise.then(value => {
                process.stdout.write(gets + "|" + calls + "|" + value + "\n");
            });
        "#;
        let (stdout, drain) = run_microtask_checkpoint("promise-thenable-getter", source)?;
        assert!(drain.executed > 0);
        assert!(drain.uncaught.is_empty());
        assert_eq!(stdout, b"1|0|1|1|7\n");
        Ok(())
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn promise_reactions_keep_registration_order_across_settlement() -> Result<(), Box<dyn Error>> {
        let source = r#"
            const seen: string[] = [];
            let resolve;
            const promise = new Promise(settle => { resolve = settle; });
            promise.then(() => { seen.push("A"); });
            promise.then(() => { seen.push("B"); });
            resolve();
            promise.then(() => { seen.push("C"); });
            queueMicrotask(() => {
                process.stdout.write(seen.join("") + "\n");
            });
        "#;
        let (stdout, drain) = run_microtask_checkpoint("promise-reaction-order", source)?;
        assert_eq!(drain.executed, 4);
        assert!(drain.uncaught.is_empty());
        assert_eq!(stdout, b"ABC\n");
        Ok(())
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn promise_self_resolution_rejects() -> Result<(), Box<dyn Error>> {
        let source = r#"
            let resolve;
            const promise = new Promise(settle => { resolve = settle; });
            resolve(promise);
            promise.catch(() => {
                process.stdout.write("self-rejected\n");
            });
        "#;
        let (stdout, drain) = run_microtask_checkpoint("promise-self-resolution", source)?;
        assert!(drain.executed > 0);
        assert!(drain.uncaught.is_empty());
        assert_eq!(stdout, b"self-rejected\n");
        Ok(())
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn promise_surface_has_node_tags_brands_and_lengths() -> Result<(), Box<dyn Error>> {
        let source = r#"
            const checks = [Object.prototype.toString.call(Promise.resolve())];
            try {
                Promise.prototype.then.call({}, () => {});
                checks.push("bad-brand");
            } catch (error) {
                checks.push("brand-error");
            }
            try {
                queueMicrotask(1);
                checks.push("bad-callback");
            } catch (error) {
                checks.push("callback-error");
            }
            try {
                const detached = Promise.resolve;
                detached(1);
                checks.push("bad-static");
            } catch (error) {
                checks.push("static-error");
            }
            checks.push(
                Promise.length,
                Promise.resolve.length,
                Promise.reject.length,
                Promise.all.length,
                Promise.prototype.then.length,
                Promise.prototype.catch.length,
                Promise.prototype.finally.length,
                queueMicrotask.length,
            );
            process.stdout.write(checks.join("|") + "\n");
        "#;
        let (directory, entrypoint) = script_fixture("promise-surface", source)?;
        let output = run_program(&entrypoint)?;

        assert_eq!(
            output.stdout,
            b"[object Promise]|brand-error|callback-error|static-error|1|1|1|1|2|1|1|1\n"
        );
        assert_eq!(output.exit_code, 0);
        remove_fixture(&directory)
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn async_await_resumes_in_node_microtask_order() -> Result<(), Box<dyn Error>> {
        let source = r#"
            const seen: string[] = [];
            async function run() {
                seen.push("start");
                await Promise.resolve();
                seen.push("A");
            }
            run();
            Promise.resolve()
                .then(() => { seen.push("B1"); })
                .then(() => { seen.push("B2"); })
                .then(() => { process.stdout.write(seen.join(",") + "\n"); });
        "#;
        let (stdout, drain) = run_microtask_checkpoint("async-order", source)?;
        assert!(drain.executed >= 4);
        assert!(drain.uncaught.is_empty());
        assert_eq!(stdout, b"start,A,B1,B2\n");
        Ok(())
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn async_function_awaits_a_timeout_at_explicit_checkpoints() -> Result<(), Box<dyn Error>> {
        let source = r#"
            async function run() {
                const value = await new Promise(resolve => {
                    const handle = setTimeout(function (value) {
                        process.stdout.write(String(this === handle) + "|");
                        resolve(value);
                    }, 1, 42);
                });
                process.stdout.write(String(value) + "\n");
            }
            run();
        "#;
        let checkpoint = run_timer_checkpoint("async-timeout", source)?;
        assert!(checkpoint.waited);
        assert_eq!(checkpoint.timer.executed, 1);
        assert!(checkpoint.timer.uncaught.is_empty());
        assert!(checkpoint.before_timer.uncaught.is_empty());
        assert!(checkpoint.after_timer.executed > 0);
        assert!(checkpoint.after_timer.uncaught.is_empty());
        assert_eq!(checkpoint.stdout, b"true|42\n");
        Ok(())
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn clear_timeout_suppresses_only_its_own_callback() -> Result<(), Box<dyn Error>> {
        let source = r#"
            const canceled = setTimeout(() => {
                process.stdout.write("canceled\n");
            }, 1);
            clearTimeout(canceled);
            setTimeout(() => {
                process.stdout.write("kept\n");
            }, 1);
        "#;
        let checkpoint = run_timer_checkpoint("clear-timeout", source)?;
        assert!(checkpoint.waited);
        assert_eq!(checkpoint.timer.executed, 1);
        assert!(checkpoint.timer.uncaught.is_empty());
        assert!(checkpoint.before_timer.uncaught.is_empty());
        assert!(checkpoint.after_timer.uncaught.is_empty());
        assert_eq!(checkpoint.stdout, b"kept\n");
        Ok(())
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn rejected_await_enters_its_catch_and_preserves_later_resumes() -> Result<(), Box<dyn Error>> {
        let source = r#"
            async function caught() {
                try {
                    await Promise.reject(7);
                    process.stdout.write("missed\n");
                } catch (reason) {
                    process.stdout.write("caught:" + reason + "\n");
                }
                let total = 1 + await Promise.resolve(2);
                return total + await Promise.resolve(3);
            }
            async function uncaught() {
                await Promise.reject(8);
            }
            caught().then(value => {
                process.stdout.write("return:" + value + "\n");
            });
            uncaught().catch(reason => {
                process.stdout.write("uncaught:" + reason + "\n");
            });
        "#;
        let (stdout, drain) = run_microtask_checkpoint("async-rejection", source)?;
        assert!(drain.executed >= 6);
        assert!(drain.uncaught.is_empty());
        assert_eq!(stdout, b"caught:7\nuncaught:8\nreturn:6\n");
        Ok(())
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn run_program_drains_microtasks_and_timers_to_quiescence_in_phase_order()
    -> Result<(), Box<dyn Error>> {
        let source = r#"
            process.stdout.write("sync\n");
            Promise.resolve().then(() => {
                process.stdout.write("promise\n");
            });
            setTimeout(() => {
                process.stdout.write("timer\n");
                Promise.resolve().then(() => {
                    process.stdout.write("timer-promise\n");
                });
            }, 1);
        "#;
        let (directory, entrypoint) = script_fixture("quiescence-phase-order", source)?;
        let output = run_program(&entrypoint)?;

        assert_eq!(output.stdout, b"sync\npromise\ntimer\ntimer-promise\n");
        assert_eq!(output.exit_code, 0);
        remove_fixture(&directory)
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn run_program_keeps_alive_for_a_future_timer() -> Result<(), Box<dyn Error>> {
        let source = r#"
            process.stdout.write("start\n");
            setTimeout(() => {
                process.stdout.write("fired\n");
            }, 2);
        "#;
        let (directory, entrypoint) = script_fixture("future-timer", source)?;
        let output = run_program(&entrypoint)?;

        assert_eq!(output.stdout, b"start\nfired\n");
        assert_eq!(output.exit_code, 0);
        remove_fixture(&directory)
    }

    #[cfg(feature = "node-host")]
    #[test]
    fn run_program_maps_the_first_uncaught_timer_throw() -> Result<(), Box<dyn Error>> {
        let source = r#"
            setTimeout(() => {
                throw 7;
            }, 1);
            setTimeout(() => {
                throw 99;
            }, 2);
        "#;
        let (directory, entrypoint) = script_fixture("uncaught-timer", source)?;
        let error = run_program(&entrypoint).expect_err("an uncaught timer callback fails the run");
        let super::Error::Runtime(runtime) = error else {
            panic!("expected a runtime error, got {error:?}");
        };
        match runtime.kind {
            bamts_runtime::RuntimeErrorKind::UncaughtThrow { value, .. } => {
                assert_eq!(
                    value,
                    bamts_runtime::constant_value(&bamts_bytecode::Constant::Int32(7)).unwrap(),
                    "expected the first timer's uncaught throw (7)"
                );
            }
            other => panic!("expected UncaughtThrow, got {other:?}"),
        }
        remove_fixture(&directory)
    }

    #[cfg(feature = "aot")]
    #[test]
    fn compiles_complete_program_to_native_object() -> Result<(), Box<dyn Error>> {
        let (directory, entrypoint) = fixture("aot")?;
        let object = super::compile_native_object(&entrypoint, "x86_64")?;

        assert!(!object.bytes.is_empty());
        remove_fixture(&directory)
    }
}
