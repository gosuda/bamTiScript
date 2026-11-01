#[cfg(unix)]
use std::{
    env,
    ffi::OsString,
    io::{self, Write},
    path::PathBuf,
    process,
};

#[cfg(unix)]
use bamts_verification::jit_runner::{
    Attempt, HeadSha, JitError, ProvisionArgs, PullRequestNumber, RepoName, Result, RunId,
    RunnerGroupId, provision, run_internal_launcher,
};

#[cfg(unix)]
const USAGE: &str = "usage: bh1_jit provision --repo owner/name --pr N --run ID --attempt N --head-sha 40hex --runner-group-id ID [--runner-parent PATH]";

#[cfg(unix)]
enum Command {
    Provision(ProvisionArgs),
    InternalLaunch,
}

#[cfg(unix)]
fn main() {
    if let Err(error) = run() {
        let _ = writeln!(io::stderr().lock(), "{error}");
        process::exit(error.code.exit_code());
    }
}

#[cfg(unix)]
fn run() -> Result<()> {
    match parse_command(env::args_os())? {
        Command::Provision(args) => {
            let outcome = provision(&args)?;
            println!(
                "jit_runner_ok job_id={} runner_id={} conclusion={}",
                outcome.job_id, outcome.runner_id, outcome.conclusion
            );
        }
        Command::InternalLaunch => run_internal_launcher()?,
    }
    Ok(())
}

#[cfg(unix)]
fn parse_command(mut arguments: impl Iterator<Item = OsString>) -> Result<Command> {
    let _program = arguments.next();
    let command = next_utf8(&mut arguments, "command")?;
    match command.as_str() {
        "provision" => parse_provision(&mut arguments).map(Command::Provision),
        "__launch-jit-from-stdin" if arguments.next().is_none() => Ok(Command::InternalLaunch),
        _ if command.starts_with('-') => Err(JitError::usage(format!(
            "unknown flag `{command}`; {USAGE}"
        ))),
        _ => Err(JitError::usage(format!(
            "unknown command `{command}`; {USAGE}"
        ))),
    }
}

#[cfg(unix)]
fn parse_provision(arguments: &mut impl Iterator<Item = OsString>) -> Result<ProvisionArgs> {
    let mut repo: Option<RepoName> = None;
    let mut pull_request: Option<PullRequestNumber> = None;
    let mut run_id: Option<RunId> = None;
    let mut attempt: Option<Attempt> = None;
    let mut head_sha: Option<HeadSha> = None;
    let mut runner_group_id: Option<RunnerGroupId> = None;
    let mut runner_parent: Option<PathBuf> = None;

    while let Some(raw_flag) = arguments.next() {
        let flag = raw_flag
            .into_string()
            .map_err(|_| JitError::usage(format!("flag is not valid UTF-8; {USAGE}")))?;
        if !flag.starts_with("--") {
            return Err(JitError::usage(format!(
                "unexpected argument `{flag}`; {USAGE}"
            )));
        }
        let value = next_utf8(arguments, &format!("value for {flag}"))?;
        if value.starts_with("--") {
            return Err(JitError::usage(format!(
                "missing value for `{flag}`; {USAGE}"
            )));
        }
        match flag.as_str() {
            "--repo" => set_once(&mut repo, value.parse()?, &flag)?,
            "--pr" => set_once(&mut pull_request, value.parse()?, &flag)?,
            "--run" => set_once(&mut run_id, value.parse()?, &flag)?,
            "--attempt" => set_once(&mut attempt, value.parse()?, &flag)?,
            "--head-sha" => set_once(&mut head_sha, value.parse()?, &flag)?,
            "--runner-group-id" => set_once(&mut runner_group_id, value.parse()?, &flag)?,
            "--runner-parent" => set_once(&mut runner_parent, PathBuf::from(value), &flag)?,
            _ => return Err(JitError::usage(format!("unknown flag `{flag}`; {USAGE}"))),
        }
    }

    Ok(ProvisionArgs {
        repo: required(repo, "--repo")?,
        pull_request: required(pull_request, "--pr")?,
        run_id: required(run_id, "--run")?,
        attempt: required(attempt, "--attempt")?,
        head_sha: required(head_sha, "--head-sha")?,
        runner_group_id: required(runner_group_id, "--runner-group-id")?,
        runner_parent,
    })
}

#[cfg(unix)]
fn next_utf8(arguments: &mut impl Iterator<Item = OsString>, subject: &str) -> Result<String> {
    arguments
        .next()
        .ok_or_else(|| JitError::usage(format!("missing {subject}; {USAGE}")))?
        .into_string()
        .map_err(|_| JitError::usage(format!("{subject} is not valid UTF-8; {USAGE}")))
}

#[cfg(unix)]
fn set_once<T>(slot: &mut Option<T>, value: T, flag: &str) -> Result<()> {
    if slot.replace(value).is_some() {
        return Err(JitError::usage(format!("duplicate flag `{flag}`; {USAGE}")));
    }
    Ok(())
}

#[cfg(unix)]
fn required<T>(value: Option<T>, flag: &str) -> Result<T> {
    value.ok_or_else(|| JitError::usage(format!("missing required flag `{flag}`; {USAGE}")))
}

#[cfg(unix)]
#[cfg(test)]
mod tests {
    use super::*;

    fn valid() -> Vec<OsString> {
        [
            "bh1_jit",
            "provision",
            "--repo",
            "owner/repo",
            "--pr",
            "7",
            "--run",
            "41",
            "--attempt",
            "2",
            "--head-sha",
            "0123456789abcdef0123456789abcdef01234567",
            "--runner-group-id",
            "9",
        ]
        .into_iter()
        .map(OsString::from)
        .collect()
    }

    fn parse_provision(arguments: Vec<OsString>) -> ProvisionArgs {
        match parse_command(arguments.into_iter()).unwrap() {
            Command::Provision(args) => args,
            Command::InternalLaunch => panic!("expected provision command"),
        }
    }

    #[test]
    fn accepts_complete_provision_command() {
        let args = parse_provision(valid());
        assert_eq!(args.run_id, RunId(41));
        assert_eq!(args.attempt, Attempt(2));
        assert_eq!(args.runner_parent, None);
    }

    #[test]
    fn accepts_optional_runner_parent() {
        let mut arguments = valid();
        arguments.extend([
            OsString::from("--runner-parent"),
            OsString::from("/var/tmp/bh1"),
        ]);
        let args = parse_provision(arguments);
        assert_eq!(args.runner_parent, Some(PathBuf::from("/var/tmp/bh1")));
    }

    #[test]
    fn rejects_every_missing_required_flag() {
        for flag in [
            "--repo",
            "--pr",
            "--run",
            "--attempt",
            "--head-sha",
            "--runner-group-id",
        ] {
            let mut arguments = valid();
            let index = arguments
                .iter()
                .position(|argument| argument == flag)
                .unwrap();
            arguments.drain(index..=index + 1);
            let error = parse_command(arguments.into_iter()).err().unwrap();
            assert_eq!(
                error.code,
                bamts_verification::jit_runner::JitErrorCode::Usage,
                "{flag}"
            );
        }
    }

    #[test]
    fn rejects_duplicate_unknown_and_positional_arguments() {
        let mut duplicate = valid();
        duplicate.extend([OsString::from("--run"), OsString::from("42")]);
        assert!(parse_command(duplicate.into_iter()).is_err());

        let mut unknown = valid();
        unknown.extend([OsString::from("--surprise"), OsString::from("x")]);
        assert!(parse_command(unknown.into_iter()).is_err());

        let mut positional = valid();
        positional.push(OsString::from("extra"));
        assert!(parse_command(positional.into_iter()).is_err());
    }

    #[test]
    fn accepts_only_argument_free_internal_launcher_command() {
        let command = parse_command(
            ["bh1_jit", "__launch-jit-from-stdin"]
                .into_iter()
                .map(OsString::from),
        )
        .unwrap();
        assert!(matches!(command, Command::InternalLaunch));
        assert!(
            parse_command(
                ["bh1_jit", "__launch-jit-from-stdin", "extra"]
                    .into_iter()
                    .map(OsString::from),
            )
            .is_err()
        );
    }
}

/// The JIT runner provisioning drives unix process groups, file modes, and
/// locks, so it exists only on unix hosts.
#[cfg(not(unix))]
fn main() {
    eprintln!("bh1_jit is not supported on this platform: it needs a unix host");
    std::process::exit(1);
}
