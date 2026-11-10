use std::{
    env,
    ffi::OsString,
    io::{self, Write},
    path::PathBuf,
    process,
};

use bamts_verification::{
    ErrorCode, Result, VerificationError,
    suite::{
        BackendFilter, CiMode, CiOptions, FailureClass, RunFilterOptions, StatusFilter,
        SuiteRunReport, SyncOptions, audit_ledger, parse_shards, run_ci, run_suite, sync_suite,
        write_suite_ledger,
    },
    ts_ledger::Backend,
};

enum Command {
    Sync {
        verify_pin: bool,
        write_snapshot: bool,
        workspace_root: PathBuf,
        snapshot_root: PathBuf,
    },
    Classify {
        workspace_root: PathBuf,
        snapshot_root: PathBuf,
        ledger_out: PathBuf,
    },
    SyncAndClassify {
        verify_pin: bool,
        write_snapshot: bool,
        workspace_root: PathBuf,
        snapshot_root: PathBuf,
        ledger_out: PathBuf,
    },
    AuditLedger {
        require_complete: bool,
        ledger: Option<PathBuf>,
        workspace_root: PathBuf,
        snapshot_root: PathBuf,
    },
    Run {
        filters: RunFilterOptions,
        workspace_root: PathBuf,
        snapshot_root: PathBuf,
    },
    Ci {
        mode: CiMode,
        filters: RunFilterOptions,
        workspace_root: PathBuf,
        snapshot_root: PathBuf,
    },
}

enum ClassifySync {
    SnapshotIfMissing,
    Always {
        verify_pin: bool,
        write_snapshot: bool,
    },
}

fn classify_suite(
    workspace_root: PathBuf,
    snapshot_root: PathBuf,
    ledger_out: PathBuf,
    sync: ClassifySync,
) -> Result<()> {
    match sync {
        ClassifySync::SnapshotIfMissing => {
            if !snapshot_root.join("snapshot.sha256").exists() {
                sync_suite(&SyncOptions {
                    verify_pin: true,
                    write_snapshot: true,
                    workspace_root,
                    snapshot_root: snapshot_root.clone(),
                    extracted_suite_root: None,
                })?;
            }
        }
        ClassifySync::Always {
            verify_pin,
            write_snapshot,
        } => {
            sync_suite(&SyncOptions {
                verify_pin,
                write_snapshot,
                workspace_root,
                snapshot_root: snapshot_root.clone(),
                extracted_suite_root: None,
            })?;
        }
    }
    let ledger = write_suite_ledger(&snapshot_root, &ledger_out)?;
    println!(
        "ledger_written path={} entries={} included={} deferred={} excluded={}",
        ledger_out.display(),
        ledger.entries.len(),
        ledger.totals.included,
        ledger.totals.deferred,
        ledger.totals.excluded,
    );
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        let _ = writeln!(io::stderr().lock(), "{error}");
        process::exit(1);
    }
}

fn run() -> Result<()> {
    let command = parse_command(env::args_os())?;
    match command {
        Command::Sync {
            verify_pin,
            write_snapshot,
            workspace_root,
            snapshot_root,
        } => {
            let snapshot = sync_suite(&SyncOptions {
                verify_pin,
                write_snapshot,
                workspace_root,
                snapshot_root,
                extracted_suite_root: None,
            })?;
            println!("snapshot.sha256={}", snapshot.digest);
            Ok(())
        }
        Command::Classify {
            workspace_root,
            snapshot_root,
            ledger_out,
        } => classify_suite(
            workspace_root,
            snapshot_root,
            ledger_out,
            ClassifySync::SnapshotIfMissing,
        ),
        Command::SyncAndClassify {
            verify_pin,
            write_snapshot,
            workspace_root,
            snapshot_root,
            ledger_out,
        } => classify_suite(
            workspace_root,
            snapshot_root,
            ledger_out,
            ClassifySync::Always {
                verify_pin,
                write_snapshot,
            },
        ),
        Command::AuditLedger {
            require_complete,
            ledger,
            workspace_root,
            snapshot_root,
        } => {
            let committed_ledger = workspace_root.join("verification/ts-suite-ledger.json");
            let ledger_path = ledger.unwrap_or_else(|| {
                if committed_ledger.is_file() {
                    committed_ledger
                } else {
                    snapshot_root.join("ledger.json")
                }
            });
            let index_path = snapshot_root.join("index.json");
            let discovered = discovered_inputs_from_index(&index_path)?;
            let audited = audit_ledger(&ledger_path, require_complete, &discovered)?;
            println!(
                "ledger_ok entries={} inputs={}",
                audited.entries.len(),
                audited.snapshot.input_count
            );
            Ok(())
        }
        Command::Run {
            filters,
            workspace_root,
            snapshot_root,
        } => {
            if !snapshot_root.join("snapshot.sha256").exists() {
                sync_suite(&SyncOptions {
                    verify_pin: true,
                    write_snapshot: true,
                    workspace_root: workspace_root.clone(),
                    snapshot_root: snapshot_root.clone(),
                    extracted_suite_root: None,
                })?;
            }
            let report = run_suite(&workspace_root, &snapshot_root, &filters)?;
            print_run_report(&report);
            Ok(())
        }
        Command::Ci {
            mode,
            filters,
            workspace_root,
            snapshot_root,
        } => {
            let report = run_ci(&CiOptions {
                mode,
                filters,
                workspace_root,
                snapshot_root,
            })?;
            println!(
                "ci state={} results={}",
                report.state_reached.as_str(),
                report.results.len()
            );
            Ok(())
        }
    }
}

fn print_run_report(report: &SuiteRunReport) {
    println!(
        "state={} results={}",
        report.state_reached.as_str(),
        report.results.len()
    );
    for (class, count) in &report.rollups {
        println!("rollup {}={count}", class.as_str());
    }
    for result in &report.results {
        if !matches!(result.class, FailureClass::Pass) {
            println!(
                "result entry={} backend={:?} class={} detail={}",
                result.entry_id,
                result.backend,
                result.class.as_str(),
                result.detail.replace('\n', "\\n")
            );
        }
    }
}

fn discovered_inputs_from_index(
    path: &std::path::Path,
) -> Result<std::collections::BTreeSet<String>> {
    let bytes = std::fs::read(path).map_err(|error| {
        VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
    })?;
    let index: bamts_verification::suite::SuiteIndex = serde_json::from_slice(&bytes)
        .map_err(|error| VerificationError::new(ErrorCode::Json, format!("index.json: {error}")))?;
    Ok(index
        .entries
        .values()
        .filter(|entry| {
            matches!(
                entry.asset_kind,
                bamts_verification::suite::AssetKind::CaseInput
            )
        })
        .map(|entry| entry.logical_path.clone())
        .collect())
}

fn parse_command(mut arguments: impl Iterator<Item = OsString>) -> Result<Command> {
    let _ = arguments.next();
    let command = required_argument(&mut arguments, "command")?;
    let cwd = env::current_dir().map_err(|error| {
        VerificationError::new(
            ErrorCode::Io,
            format!("cannot determine current directory: {error}"),
        )
    })?;

    match command.as_str() {
        "sync" => parse_sync(&mut arguments, cwd),
        "classify" => parse_classify(&mut arguments, cwd),
        "sync-and-classify" => parse_sync_and_classify(&mut arguments, cwd),
        "audit-ledger" => parse_audit_ledger(&mut arguments, cwd),
        "run" => parse_run(&mut arguments, cwd),
        "ci" => parse_ci(&mut arguments, cwd),
        _ if command.starts_with("--") => Err(usage(format!("unknown flag `{command}`"))),
        _ => Err(usage(format!("unknown command `{command}`"))),
    }
}

fn parse_classify(arguments: &mut impl Iterator<Item = OsString>, cwd: PathBuf) -> Result<Command> {
    let mut write_ledger = false;
    let mut workspace_root = cwd.clone();
    let mut snapshot_root = cwd.join("verification/ts-suite");
    let mut ledger_out = cwd.join("verification/ts-suite-ledger.json");

    while let Some(raw) = arguments.next() {
        let flag = raw
            .into_string()
            .map_err(|_| usage("flag must be valid UTF-8"))?;
        match flag.as_str() {
            "--write-ledger" => write_ledger = true,
            "--workspace" => {
                workspace_root = PathBuf::from(flag_value_from(&mut *arguments, "--workspace")?)
            }
            "--snapshot" => {
                snapshot_root = PathBuf::from(flag_value_from(&mut *arguments, "--snapshot")?)
            }
            "--ledger-out" => {
                ledger_out = PathBuf::from(flag_value_from(&mut *arguments, "--ledger-out")?)
            }
            _ if flag.starts_with("--") => return Err(usage(format!("unknown flag `{flag}`"))),
            _ => return Err(usage(format!("unexpected argument `{flag}`"))),
        }
    }

    if !write_ledger {
        return Err(usage("classify requires `--write-ledger`"));
    }
    Ok(Command::Classify {
        workspace_root,
        snapshot_root,
        ledger_out,
    })
}

fn parse_sync_and_classify(
    arguments: &mut impl Iterator<Item = OsString>,
    cwd: PathBuf,
) -> Result<Command> {
    let mut verify_pin = false;
    let mut write_snapshot = false;
    let mut workspace_root = cwd.clone();
    let mut snapshot_root = cwd.join("verification/ts-suite");
    let mut ledger_out = cwd.join("verification/ts-suite-ledger.json");

    while let Some(raw) = arguments.next() {
        let flag = raw
            .into_string()
            .map_err(|_| usage("flag must be valid UTF-8"))?;
        match flag.as_str() {
            "--verify-pin" => verify_pin = true,
            "--write-snapshot" => write_snapshot = true,
            "--workspace" => {
                workspace_root = PathBuf::from(flag_value_from(&mut *arguments, "--workspace")?)
            }
            "--snapshot" => {
                snapshot_root = PathBuf::from(flag_value_from(&mut *arguments, "--snapshot")?)
            }
            "--ledger-out" => {
                ledger_out = PathBuf::from(flag_value_from(&mut *arguments, "--ledger-out")?)
            }
            _ if flag.starts_with("--") => return Err(usage(format!("unknown flag `{flag}`"))),
            _ => return Err(usage(format!("unexpected argument `{flag}`"))),
        }
    }

    if !verify_pin {
        return Err(usage("sync-and-classify requires `--verify-pin`"));
    }
    if !write_snapshot {
        return Err(usage("sync-and-classify requires `--write-snapshot`"));
    }
    Ok(Command::SyncAndClassify {
        verify_pin,
        write_snapshot,
        workspace_root,
        snapshot_root,
        ledger_out,
    })
}

fn parse_sync(arguments: &mut impl Iterator<Item = OsString>, cwd: PathBuf) -> Result<Command> {
    let mut verify_pin = false;
    let mut write_snapshot = false;
    let mut workspace_root = cwd.clone();
    let mut snapshot_root = cwd.join("verification/ts-suite");

    while let Some(raw) = arguments.next() {
        let flag = raw
            .into_string()
            .map_err(|_| usage("flag must be valid UTF-8"))?;
        match flag.as_str() {
            "--verify-pin" => verify_pin = true,
            "--write-snapshot" => write_snapshot = true,
            "--workspace" => {
                workspace_root = PathBuf::from(flag_value_from(&mut *arguments, "--workspace")?)
            }
            "--snapshot" => {
                snapshot_root = PathBuf::from(flag_value_from(&mut *arguments, "--snapshot")?)
            }
            _ if flag.starts_with("--") => return Err(usage(format!("unknown flag `{flag}`"))),
            _ => return Err(usage(format!("unexpected argument `{flag}`"))),
        }
    }

    if !verify_pin {
        return Err(usage("sync requires `--verify-pin`"));
    }
    if !write_snapshot {
        return Err(usage("sync requires `--write-snapshot`"));
    }
    Ok(Command::Sync {
        verify_pin,
        write_snapshot,
        workspace_root,
        snapshot_root,
    })
}

fn parse_audit_ledger(
    arguments: &mut impl Iterator<Item = OsString>,
    cwd: PathBuf,
) -> Result<Command> {
    let mut require_complete = false;
    let mut ledger = None;
    let mut snapshot_root = cwd.join("verification/ts-suite");

    while let Some(raw) = arguments.next() {
        let flag = raw
            .into_string()
            .map_err(|_| usage("flag must be valid UTF-8"))?;
        match flag.as_str() {
            "--require-complete" => require_complete = true,
            "--ledger" => {
                ledger = Some(PathBuf::from(flag_value_from(&mut *arguments, "--ledger")?))
            }
            "--snapshot" => {
                snapshot_root = PathBuf::from(flag_value_from(&mut *arguments, "--snapshot")?)
            }
            _ if flag.starts_with("--") => return Err(usage(format!("unknown flag `{flag}`"))),
            _ => return Err(usage(format!("unexpected argument `{flag}`"))),
        }
    }

    if !require_complete {
        return Err(usage("audit-ledger requires `--require-complete`"));
    }
    Ok(Command::AuditLedger {
        require_complete,
        ledger,
        workspace_root: cwd,
        snapshot_root,
    })
}

fn parse_run(arguments: &mut impl Iterator<Item = OsString>, cwd: PathBuf) -> Result<Command> {
    let (filters, workspace_root, snapshot_root) = parse_filters(arguments, cwd)?;
    Ok(Command::Run {
        filters,
        workspace_root,
        snapshot_root,
    })
}

fn parse_ci(arguments: &mut impl Iterator<Item = OsString>, cwd: PathBuf) -> Result<Command> {
    expect_flag(arguments, "--mode")?;
    let mode_value = flag_value(arguments, "--mode")?;
    let mode = parse_ci_mode(&mode_value)?;
    let (filters, workspace_root, snapshot_root) = parse_filters(arguments, cwd)?;
    Ok(Command::Ci {
        mode,
        filters,
        workspace_root,
        snapshot_root,
    })
}

fn parse_filters(
    arguments: &mut impl Iterator<Item = OsString>,
    cwd: PathBuf,
) -> Result<(RunFilterOptions, PathBuf, PathBuf)> {
    let mut status = None;
    let mut slice = None;
    let mut backend = None;
    let mut shards = None;
    let mut workspace_root = cwd.clone();
    let mut snapshot_root = cwd.join("verification/ts-suite");

    while let Some(raw) = arguments.next() {
        let flag = raw
            .into_string()
            .map_err(|_| usage("flag must be valid UTF-8"))?;
        match flag.as_str() {
            "--status" => {
                status = Some(parse_status_filter(&flag_value_from(
                    &mut *arguments,
                    "--status",
                )?)?)
            }
            "--slice" => slice = Some(flag_value_from(&mut *arguments, "--slice")?),
            "--backend" => {
                backend = Some(parse_backend_filter(&flag_value_from(
                    &mut *arguments,
                    "--backend",
                )?)?)
            }
            "--shards" => {
                shards = Some(parse_shards(&flag_value_from(
                    &mut *arguments,
                    "--shards",
                )?)?)
            }
            "--workspace" => {
                workspace_root = PathBuf::from(flag_value_from(&mut *arguments, "--workspace")?)
            }
            "--snapshot" => {
                snapshot_root = PathBuf::from(flag_value_from(&mut *arguments, "--snapshot")?)
            }
            _ if flag.starts_with("--") => return Err(usage(format!("unknown flag `{flag}`"))),
            _ => return Err(usage(format!("unexpected argument `{flag}`"))),
        }
    }

    Ok((
        RunFilterOptions {
            status: status.unwrap_or(StatusFilter::All),
            slice,
            backends: backend.unwrap_or(BackendFilter::All),
            shards,
        },
        workspace_root,
        snapshot_root,
    ))
}

fn parse_status_filter(value: &str) -> Result<StatusFilter> {
    match value {
        "included" => Ok(StatusFilter::Included),
        "deferred" => Ok(StatusFilter::Deferred),
        "excluded" => Ok(StatusFilter::Excluded),
        "all" => Ok(StatusFilter::All),
        _ => Err(usage(format!(
            "unsupported --status `{value}`; expected included|deferred|excluded|all"
        ))),
    }
}

fn parse_backend_filter(value: &str) -> Result<BackendFilter> {
    match value {
        "all" => Ok(BackendFilter::All),
        "check" => Ok(BackendFilter::One(Backend::Check)),
        "interpreter" => Ok(BackendFilter::One(Backend::Interpreter)),
        "jit" => Ok(BackendFilter::One(Backend::Jit)),
        "aot" => Ok(BackendFilter::One(Backend::Aot)),
        _ => Err(usage(format!(
            "unsupported --backend `{value}`; expected check|interpreter|jit|aot|all"
        ))),
    }
}

fn parse_ci_mode(value: &str) -> Result<CiMode> {
    match value {
        "pr" => Ok(CiMode::Pr),
        "nightly" => Ok(CiMode::Nightly),
        _ => Err(usage(format!(
            "unsupported --mode `{value}`; expected pr|nightly"
        ))),
    }
}

fn required_argument(
    arguments: &mut impl Iterator<Item = OsString>,
    description: &str,
) -> Result<String> {
    let argument = arguments
        .next()
        .ok_or_else(|| usage(format!("missing {description}")))?;
    argument
        .into_string()
        .map_err(|_| usage(format!("{description} must be valid UTF-8")))
}

fn expect_flag(arguments: &mut impl Iterator<Item = OsString>, flag: &str) -> Result<()> {
    let value = required_argument(arguments, &format!("flag `{flag}`"))?;
    if value == flag {
        return Ok(());
    }
    if value.starts_with("--") {
        return Err(usage(format!("unknown flag `{value}`")));
    }
    Err(usage(format!("expected flag `{flag}`, found `{value}`")))
}

fn flag_value(arguments: &mut impl Iterator<Item = OsString>, flag: &str) -> Result<String> {
    let value = required_argument(arguments, &format!("value for `{flag}`"))?;
    if !value.starts_with("--") {
        return Ok(value);
    }
    if value == flag {
        return Err(usage(format!("duplicate flag `{flag}`")));
    }
    Err(usage(format!("unknown flag `{value}`")))
}

fn flag_value_from(arguments: &mut impl Iterator<Item = OsString>, flag: &str) -> Result<String> {
    flag_value(arguments, flag)
}

fn usage(detail: impl Into<String>) -> VerificationError {
    VerificationError::new(ErrorCode::Usage, detail)
}
