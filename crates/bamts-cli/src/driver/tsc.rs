use super::*;
use super::native::*;
use super::project::*;
use bamts_compiler::project::canonical::slash_text;
use bamts_compiler::project::effective::compile_project;
use bamts_compiler::project::effective::EffectiveProject;
use bamts_compiler::project::effective::ProjectCompileOptions;
use bamts_compiler::project::effective::ProjectLoadRequest;
use bamts_compiler::service::filesystem::OsFileSystem;
use crate::cli::tsc_args::TscDispatchMode;
use crate::cli::tsc_args::TscExitStatus;
use std::fs::OpenOptions;
use std::io::Write;

pub(super) const TSC_HELP: &str = "\
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

pub(super) const TSC_INIT_CREATED: &str =
    "\nCreated a new tsconfig.json\n\nYou can learn more at https://aka.ms/tsconfig\n";
pub(super) const TSC_INIT_CONFIG: &str = r#"{
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

pub(super) fn execute_tsc_in_context(
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
    // over one inferred configuration-free project. TypeScript 7.0.2 removed
    // `outFile`: a direct `--outFile` still compiles per-file through that
    // pipeline so the TS5102 diagnostic flows from `compile_project`. The
    // remaining single-root compile keeps the native executable driver, which
    // only maps '--jsx preserve'.
    let artifact_route = command.file_names.len() > 1
        || command.option_str("outFile").is_some()
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
pub(super) fn compile_tsc_native_roots(
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
pub(super) fn compile_tsc_artifacts(
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

pub(super) fn initialize_tsc_config(context: &ExecutionContext) -> Result<CommandOutcome, DriverError> {
    let path = context.resolve_path("tsconfig.json");
    let mut file = match OpenOptions::new().write(true).create_new(true).open(&path) {
        Ok(file) => file,
        Err(source) if source.kind() == io::ErrorKind::AlreadyExists => {
            return Ok(CommandOutcome {
                stdout: format!(
                    "error TS5054: A 'tsconfig.json' file is already defined at: '{}'.\n",
                    slash_text(&path)
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
pub(super) fn execute_tsc_in(command: &ParsedTscCommand, cwd: &Path) -> Result<CommandOutcome, DriverError> {
    let environment = std::env::vars_os().collect();
    let context = ExecutionContext::new(cwd, environment)?;
    execute_tsc_in_context(command, &context)
}
