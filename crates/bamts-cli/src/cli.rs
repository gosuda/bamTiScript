pub mod diagnostic_format;
pub mod tsc_args;
use crate::args::{CliArgs, help_message, load_error_message, parse_args, version_message};
use crate::context::ExecutionContext;
use crate::driver::{
    CommandOutcome, DriverError, execute, execute_in_context, execute_in_context_with_cancel,
    execute_with_cancel,
};
use bamts_compiler::CancellationToken;
use bamts_runtime::Limits;

/// Runs one CLI invocation against the ambient process context.
#[must_use]
pub fn cli_outcome(argv: impl IntoIterator<Item = String>) -> CommandOutcome {
    cli_outcome_with(argv, execute)
}

/// Runs one CLI invocation against explicit process inputs.
#[must_use]
pub fn cli_outcome_in_context(
    argv: impl IntoIterator<Item = String>,
    context: &ExecutionContext,
) -> CommandOutcome {
    cli_outcome_with(argv, |args| execute_in_context(args, context))
}

/// [`cli_outcome`] with a caller-supplied cancellation token.
#[must_use]
pub fn cli_outcome_with_cancel(
    argv: impl IntoIterator<Item = String>,
    cancel: CancellationToken,
) -> CommandOutcome {
    cli_outcome_with(argv, |args| execute_with_cancel(args, cancel.clone()))
}

/// [`cli_outcome_in_context`] with a caller-supplied cancellation token.
#[must_use]
pub fn cli_outcome_in_context_with_cancel(
    argv: impl IntoIterator<Item = String>,
    context: &ExecutionContext,
    cancel: CancellationToken,
) -> CommandOutcome {
    cli_outcome_with(argv, |args| {
        execute_in_context_with_cancel(args, context, cancel.clone(), Limits::program())
    })
}

fn cli_outcome_with(
    argv: impl IntoIterator<Item = String>,
    execute: impl FnOnce(&CliArgs) -> Result<CommandOutcome, DriverError>,
) -> CommandOutcome {
    match parse_args(argv) {
        Ok(args) if args.help => CommandOutcome {
            stdout: help_message().as_bytes().to_vec(),
            ..CommandOutcome::default()
        },
        Ok(args) if args.version => CommandOutcome {
            stdout: format!("{}\n", version_message()).into_bytes(),
            ..CommandOutcome::default()
        },
        Ok(args) => execute(&args).unwrap_or_else(|error| driver_error_outcome(&error)),
        Err(error) => CommandOutcome {
            stderr: format!("error: {error}\n\n{}", help_message()).into_bytes(),
            exit_code: 2,
            ..CommandOutcome::default()
        },
    }
}

/// Whether any argument selects the native execution front.
///
/// The tsc-compatible front rejects `--run`, `-r`, `--jit`, and `--aot` as
/// unknown compiler options, so their presence routes the whole invocation
/// to the native parser that documents them. `--target` is deliberately
/// excluded: tsc owns it as the ECMAScript target flag.
pub fn native_execution_requested<I, S>(args: I) -> bool
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    args.into_iter()
        .any(|token| matches!(token.as_ref(), "--run" | "-r" | "--jit" | "--aot"))
}

fn driver_error_outcome(error: &DriverError) -> CommandOutcome {
    let (stderr, truncation) = match error {
        DriverError::ProgramLoad(error) => (
            format!("{}\n", load_error_message(error)).into_bytes(),
            None,
        ),
        DriverError::Diagnostics {
            rendered,
            truncation,
        } => (rendered.as_bytes().to_vec(), *truncation),
        DriverError::Usage(error) => (
            format!("error: {error}\n\n{}", help_message()).into_bytes(),
            None,
        ),
        error => (format!("error: {error}\n").into_bytes(), None),
    };
    CommandOutcome {
        stderr,
        exit_code: if error.is_usage_error() { 2 } else { 1 },
        truncation,
        ..CommandOutcome::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context() -> (tempfile::TempDir, ExecutionContext) {
        let directory = tempfile::tempdir().expect("temporary project");
        let context =
            ExecutionContext::new(directory.path(), Default::default()).expect("execution context");
        (directory, context)
    }

    #[test]
    fn help_version_and_usage_are_buffered() {
        let (_directory, context) = context();
        let help = cli_outcome_in_context(["bamts".to_owned(), "--help".to_owned()], &context);
        assert_eq!(help.exit_code, 0);
        assert_eq!(help.stdout, help_message().as_bytes());
        assert!(help.stderr.is_empty());

        let version =
            cli_outcome_in_context(["bamts".to_owned(), "--version".to_owned()], &context);
        assert_eq!(version.exit_code, 0);
        assert_eq!(
            version.stdout,
            format!("{}\n", version_message()).as_bytes()
        );
        assert!(version.stderr.is_empty());

        let explanation = cli_outcome([
            "bamts".to_owned(),
            "explain".to_owned(),
            "BAMTS-W017".to_owned(),
        ]);
        assert_eq!(explanation.exit_code, 0);
        assert!(
            explanation
                .stdout
                .windows(b"rationale:".len())
                .any(|window| window == b"rationale:")
        );
        assert!(explanation.stderr.is_empty());

        let usage = cli_outcome_in_context(
            ["bamts".to_owned(), "--definitely-invalid".to_owned()],
            &context,
        );
        assert_eq!(usage.exit_code, 2);
        assert!(usage.stdout.is_empty());
        assert!(usage.stderr.starts_with(b"error: "));
        assert!(usage.stderr.ends_with(help_message().as_bytes()));
    }

    #[test]
    fn native_execution_routing_matches_only_native_flags() {
        assert!(native_execution_requested(["--run"]));
        assert!(native_execution_requested(["-r", "app.ts"]));
        assert!(native_execution_requested(["--jit"]));
        assert!(native_execution_requested(["--aot"]));
        assert!(!native_execution_requested([
            "--target", "es2020", "app.ts"
        ]));
        assert!(!native_execution_requested(["--build", "src"]));
        assert!(!native_execution_requested(["app.ts"]));
        assert!(!native_execution_requested(["--watch"]));
    }
    #[test]
    fn driver_failures_keep_cli_bytes_and_exit_code() {
        let (directory, context) = context();
        std::fs::write(
            directory.path().join("main.ts"),
            "const value: number = 'wrong';",
        )
        .expect("write fixture");
        let outcome = cli_outcome_in_context(
            ["bamts".to_owned(), "check".to_owned(), "main.ts".to_owned()],
            &context,
        );
        assert_eq!(outcome.exit_code, 1);
        assert!(outcome.stdout.is_empty());
        assert!(
            outcome
                .stderr
                .windows(b"BAMTS-C".len())
                .any(|window| window == b"BAMTS-C")
        );
    }

    #[test]
    fn pre_cancelled_context_invocation_stops_before_entrypoint_work() {
        let (_directory, context) = context();
        let cancel = CancellationToken::new();
        cancel.cancel();
        let outcome = cli_outcome_in_context_with_cancel(
            [
                "bamts".to_owned(),
                "check".to_owned(),
                "does-not-exist.ts".to_owned(),
            ],
            &context,
            cancel,
        );
        assert_eq!(
            outcome,
            CommandOutcome {
                stderr: b"error: operation cancelled\n".to_vec(),
                exit_code: 1,
                ..CommandOutcome::default()
            }
        );
    }
}
