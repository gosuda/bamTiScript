use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    ffi::OsString,
    io::{self, Write},
    path::{Path, PathBuf},
    process,
};

use bamts_verification::{
    ErrorCode, Gate, GateReport, Result, VerificationError,
    authority::verify_authority,
    catalog::{extract_catalog_cells, regenerate_manifest, write_catalog_json},
    completion::{
        CompletionAspect, CompletionReport, CompletionScope, RegenerateMode, RegenerateOutcome,
        regenerate_completion_program, verify_completion,
    },
    diagnostic_catalog::{self, CatalogError},
    evidence::{ExecutionBinding, PublishMode},
    formal_bridge::{
        LaneStatus, audit_formal_artifacts, qualify_replay_canary, ready_lane_records,
        regenerate_canonical_fixture, run_replay_canary_child,
    },
    formal_gates::audit_formal_gates,
    leaf_evidence::generate as generate_leaf_evidence,
    ledger::verify_ledger_g0,
    perf_guard::{self, Verdict},
    perf_jit, perf_stage0,
    rebuild::{RebuildMode, discover_receipts, rebuild_ledger},
    shard::ShardSpec,
    source_fetch::{CommandBackend, materialize_named},
    suite::completion::{SuiteMergeRequest, SuiteRunRequest, merge_suite, run_suite},
    sweep_report::{DiffRequest, FamiliesRequest, diff as diff_receipts, families},
    toolchain_schema::{
        blocking_obligations, catalog_identifiers, emit_probe_object, load_target_cells,
    },
    unicode,
    workspace_guard::audit_workspace,
};

/// Repo-relative pinned diagnostic source; doubles as its source label so the
/// generated module stays host-independent.
const DIAGNOSTIC_SOURCE: &str =
    "target/authority/typescript-7.0.2-tests/src/compiler/diagnosticMessages.json";
/// Repo-relative destination of the generated diagnostic catalog module.
const DIAGNOSTIC_GENERATED: &str = "crates/bamts-compiler/src/generated/diagnostic_messages.rs";

#[derive(Debug, PartialEq, Eq)]
enum Command {
    AuthorityVerify {
        release: String,
    },
    CatalogExtract {
        catalog: String,
    },
    CatalogRegenerate {
        release: String,
        check: bool,
    },
    LedgerVerify,
    LedgerRebuild {
        check: bool,
    },
    LeafEvidenceGenerate {
        leaf: String,
        aspect: String,
        out: PathBuf,
    },
    CompletionVerify {
        scope: CompletionScope,
        aspect: CompletionAspect,
    },
    CompletionEvidence {
        scope: CompletionScope,
        aspect: CompletionAspect,
    },
    CompletionRegenerate {
        check: bool,
    },
    DiagnosticsRegenerate {
        check: bool,
    },
    ToolchainEvidence,
    ToolchainObject {
        target: String,
        out: PathBuf,
    },
    PerfStage0,
    PerfJit,
    PerfCompare {
        rules: PathBuf,
        baseline: PathBuf,
        scorecard: PathBuf,
    },
    FormalAudit(Vec<Gate>),
    RegenerateFixtures,
    SourceFetch {
        name: String,
        destination: PathBuf,
    },
    UnicodeFetch,
    UnicodeEmit {
        destination: Option<PathBuf>,
    },
    UnicodeVerify,
    ReplayCanary {
        faulty: bool,
    },
    SuiteRun(SuiteRunRequest),
    SuiteMerge(SuiteMergeRequest),
    SuiteFamilies(FamiliesRequest),
    SuiteDiff(DiffRequest),
}

fn main() {
    if let Err(error) = run() {
        let _ = writeln!(io::stderr().lock(), "{error}");
        process::exit(1);
    }
}

fn run() -> Result<()> {
    let command = parse_command(env::args_os())?;
    let root = env::current_dir().map_err(|error| {
        VerificationError::new(
            ErrorCode::Io,
            format!("cannot determine current directory: {error}"),
        )
    })?;
    dispatch(&root, command)
}

fn dispatch(root: &Path, command: Command) -> Result<()> {
    match command {
        Command::AuthorityVerify { release } => verify_authority_command(root, &release),
        Command::CatalogExtract { catalog } => extract_catalog(root, &catalog),
        Command::CatalogRegenerate { release, check } => regenerate_catalog(root, &release, check),
        Command::LedgerVerify => verify_g0(root),
        Command::LedgerRebuild { check } => rebuild_ledger_command(root, check),
        Command::LeafEvidenceGenerate { leaf, aspect, out } => {
            let evidence = generate_leaf_evidence(root, &leaf, &aspect, &out)?;
            writeln!(io::stdout().lock(), "{evidence}").map_err(|error| {
                VerificationError::new(
                    ErrorCode::Io,
                    format!("cannot write receipt evidence: {error}"),
                )
            })
        }
        Command::CompletionVerify { scope, aspect } => {
            verify_completion_command(root, &scope, aspect)
        }
        Command::CompletionEvidence { scope, aspect } => {
            completion_evidence_command(root, &scope, aspect)
        }
        Command::CompletionRegenerate { check } => regenerate_completion_command(root, check),
        Command::DiagnosticsRegenerate { check } => regenerate_diagnostics(root, check),
        Command::ToolchainEvidence => audit_toolchain_evidence(root),
        Command::ToolchainObject { target, out } => emit_toolchain_object(&target, &out),
        Command::PerfStage0 => run_perf_stage0(),
        Command::PerfJit => run_perf_jit(),
        Command::PerfCompare {
            rules,
            baseline,
            scorecard,
        } => compare_perf(&rules, &baseline, &scorecard),
        Command::FormalAudit(gates) => audit_formal(root, &gates),
        Command::RegenerateFixtures => regenerate_fixtures(root),
        Command::SourceFetch { name, destination } => fetch_source(root, &name, &destination),
        Command::UnicodeFetch => fetch_unicode(root),
        Command::UnicodeEmit { destination } => emit_unicode(root, destination.as_deref()),
        Command::UnicodeVerify => verify_unicode(root),
        Command::ReplayCanary { faulty } => run_replay_canary_child(root, faulty),
        Command::SuiteRun(request) => run_suite(root, &request).map(|_| ()),
        Command::SuiteMerge(request) => merge_suite(root, &request).map(|_| ()),
        Command::SuiteFamilies(request) => print_report(&families(&request)?),
        Command::SuiteDiff(request) => {
            let (report, regressions) = diff_receipts(&request)?;
            print_report(&report)?;
            if request.fail_on_regression && regressions > 0 {
                return Err(VerificationError::new(
                    ErrorCode::Transition,
                    format!("{regressions} row(s) regressed from PASS"),
                ));
            }
            Ok(())
        }
    }
}

fn print_report(report: &str) -> Result<()> {
    write!(io::stdout().lock(), "{report}").map_err(|error| {
        VerificationError::new(ErrorCode::Io, format!("cannot write report: {error}"))
    })
}

fn parse_command(mut arguments: impl Iterator<Item = OsString>) -> Result<Command> {
    let _ = arguments.next();
    let command = required_argument(&mut arguments, "command")?;

    match command.as_str() {
        "authority" => parse_authority_command(&mut arguments),
        "catalog" => parse_catalog_command(&mut arguments),
        "ledger" => parse_ledger_command(&mut arguments),
        "leaf-evidence" => parse_leaf_evidence_command(&mut arguments),
        "completion" => parse_completion_command(&mut arguments),
        "diagnostics" => parse_diagnostics_command(&mut arguments),
        "toolchain" => parse_toolchain_command(&mut arguments),
        "perf" => parse_perf_command(&mut arguments),
        "formal" => parse_formal_command(&mut arguments),
        "source" => parse_source_command(&mut arguments),
        "unicode" => parse_unicode_command(&mut arguments),
        "suite" => parse_suite_command(&mut arguments),
        "--formal-canary-replay" => {
            reject_extra_arguments(&mut arguments, &[])?;
            Ok(Command::ReplayCanary { faulty: false })
        }
        "--formal-canary-replay-faulty" => {
            reject_extra_arguments(&mut arguments, &[])?;
            Ok(Command::ReplayCanary { faulty: true })
        }
        _ if command.starts_with("--") => Err(usage(format!("unknown flag `{command}`"))),
        _ => Err(usage(format!("unknown command `{command}`"))),
    }
}
fn parse_leaf_evidence_command(arguments: &mut impl Iterator<Item = OsString>) -> Result<Command> {
    expect_literal(arguments, "generate", "leaf-evidence subcommand")?;
    let flags = parse_flags(arguments, &["--leaf", "--aspect", "--out"], &[])?;
    Ok(Command::LeafEvidenceGenerate {
        leaf: required_flag(&flags.values, "--leaf", "leaf-evidence generate")?,
        aspect: required_flag(&flags.values, "--aspect", "leaf-evidence generate")?,
        out: PathBuf::from(required_flag(
            &flags.values,
            "--out",
            "leaf-evidence generate",
        )?),
    })
}

fn parse_suite_command(arguments: &mut impl Iterator<Item = OsString>) -> Result<Command> {
    let subcommand = required_argument(arguments, "suite subcommand")?;
    match subcommand.as_str() {
        "run" => {
            let flags = parse_flags(
                arguments,
                &[
                    "--catalog",
                    "--shard",
                    "--receipt",
                    "--runner",
                    "--platform",
                    "--workflow",
                    "--run-id",
                    "--run-attempt",
                    "--source-sha",
                    "--job",
                    "--host",
                    "--runtime",
                ],
                &[],
            )?;
            let shard = parse_shard(&required_flag(&flags.values, "--shard", "suite run")?)?;
            let run_attempt = required_flag(&flags.values, "--run-attempt", "suite run")?
                .parse::<u32>()
                .map_err(|_| usage("suite run --run-attempt must be an unsigned integer"))?;
            let execution = ExecutionBinding::new(
                required_flag(&flags.values, "--workflow", "suite run")?,
                required_flag(&flags.values, "--run-id", "suite run")?,
                run_attempt,
                required_flag(&flags.values, "--source-sha", "suite run")?,
                required_flag(&flags.values, "--job", "suite run")?,
                required_flag(&flags.values, "--host", "suite run")?,
                required_flag(&flags.values, "--runtime", "suite run")?,
            )
            .map_err(|error| usage(error.to_string()))?;
            Ok(Command::SuiteRun(SuiteRunRequest {
                catalog: required_flag(&flags.values, "--catalog", "suite run")?,
                shard,
                receipt: PathBuf::from(required_flag(&flags.values, "--receipt", "suite run")?),
                runner: required_flag(&flags.values, "--runner", "suite run")?,
                platform: required_flag(&flags.values, "--platform", "suite run")?,
                execution,
            }))
        }
        "merge" => {
            let flags = parse_flags(
                arguments,
                &["--catalog", "--receipts", "--out"],
                &["--check"],
            )?;
            Ok(Command::SuiteMerge(SuiteMergeRequest {
                catalog: required_flag(&flags.values, "--catalog", "suite merge")?,
                receipts: PathBuf::from(required_flag(&flags.values, "--receipts", "suite merge")?),
                out: PathBuf::from(required_flag(&flags.values, "--out", "suite merge")?),
                publish: if flags.switches.contains("--check") {
                    PublishMode::Check
                } else {
                    PublishMode::Replace
                },
            }))
        }
        "families" => {
            let receipt = path_argument(arguments, "suite families receipt")?;
            let flags = parse_flags(arguments, &["--top", "--family", "--root"], &[])?;
            Ok(Command::SuiteFamilies(FamiliesRequest {
                receipt,
                top: count_flag(&flags.values, "--top", 20)?,
                family: flags.values.get("--family").cloned(),
                root: flags.values.get("--root").map(PathBuf::from),
            }))
        }
        "diff" => {
            let a = path_argument(arguments, "first receipt of suite diff")?;
            let b = path_argument(arguments, "second receipt of suite diff")?;
            let flags = parse_flags(arguments, &["--limit"], &["--fail-on-regression"])?;
            Ok(Command::SuiteDiff(DiffRequest {
                a,
                b,
                limit: count_flag(&flags.values, "--limit", 20)?,
                fail_on_regression: flags.switches.contains("--fail-on-regression"),
            }))
        }
        _ if subcommand.starts_with("--") => Err(usage(format!("unknown flag `{subcommand}`"))),
        _ => Err(usage(format!("unknown suite subcommand `{subcommand}`"))),
    }
}

/// A positional path. A word that looks like a flag is a missing path.
fn path_argument(
    arguments: &mut impl Iterator<Item = OsString>,
    description: &str,
) -> Result<PathBuf> {
    let value = required_argument(arguments, description)?;
    if value.starts_with("--") {
        return Err(usage(format!(
            "missing {description}, found flag `{value}`"
        )));
    }
    Ok(PathBuf::from(value))
}

fn count_flag(values: &BTreeMap<String, String>, flag: &str, default: usize) -> Result<usize> {
    values.get(flag).map_or(Ok(default), |value| {
        value
            .parse::<usize>()
            .map_err(|_| usage(format!("`{flag}` must be an unsigned integer")))
    })
}

/// Parses low-level suite coordinates as zero-based `<index>/<count>`.
/// `ts_conformance --shards` is intentionally a separate one-based surface.
fn parse_shard(value: &str) -> Result<ShardSpec> {
    let (index, count) = value
        .split_once('/')
        .ok_or_else(|| usage("`--shard` must use zero-based `<index>/<count>`"))?;
    let index = index
        .parse::<u32>()
        .map_err(|_| usage("`--shard` index must be an unsigned integer"))?;
    let count = count
        .parse::<u32>()
        .map_err(|_| usage("`--shard` count must be an unsigned integer"))?;
    ShardSpec::new(index, count).map_err(|error| usage(error.to_string()))
}

fn parse_authority_command(arguments: &mut impl Iterator<Item = OsString>) -> Result<Command> {
    expect_literal(arguments, "verify", "authority subcommand")?;
    expect_flag(arguments, "--release")?;
    let release = flag_value(arguments, "--release")?;
    reject_extra_arguments(arguments, &["--release"])?;
    Ok(Command::AuthorityVerify { release })
}

fn parse_catalog_command(arguments: &mut impl Iterator<Item = OsString>) -> Result<Command> {
    let subcommand = required_argument(arguments, "catalog subcommand")?;
    match subcommand.as_str() {
        "extract" => {
            expect_flag(arguments, "--catalog")?;
            let catalog = flag_value(arguments, "--catalog")?;
            reject_extra_arguments(arguments, &["--catalog"])?;
            Ok(Command::CatalogExtract { catalog })
        }
        "regenerate" => {
            expect_flag(arguments, "--release")?;
            let release = flag_value(arguments, "--release")?;
            let check = match arguments.next() {
                None => false,
                Some(value) => {
                    let value = value
                        .into_string()
                        .map_err(|_| usage("catalog flag must be valid UTF-8"))?;
                    if value != "--check" {
                        return Err(if value.starts_with("--") {
                            usage(format!("unknown flag `{value}`"))
                        } else {
                            usage(format!("unexpected argument `{value}`"))
                        });
                    }
                    reject_extra_arguments(arguments, &["--check"])?;
                    true
                }
            };
            Ok(Command::CatalogRegenerate { release, check })
        }
        _ if subcommand.starts_with("--") => Err(usage(format!("unknown flag `{subcommand}`"))),
        _ => Err(usage(format!("unknown catalog subcommand `{subcommand}`"))),
    }
}

fn parse_source_command(arguments: &mut impl Iterator<Item = OsString>) -> Result<Command> {
    expect_literal(arguments, "fetch", "source subcommand")?;
    let name = required_argument(arguments, "source name")?;
    expect_flag(arguments, "--dest")?;
    let destination = PathBuf::from(flag_value(arguments, "--dest")?);
    reject_extra_arguments(arguments, &["--dest"])?;
    Ok(Command::SourceFetch { name, destination })
}

fn parse_unicode_command(arguments: &mut impl Iterator<Item = OsString>) -> Result<Command> {
    let subcommand = required_argument(arguments, "unicode subcommand")?;
    match subcommand.as_str() {
        "fetch" => {
            reject_extra_arguments(arguments, &[])?;
            Ok(Command::UnicodeFetch)
        }
        "emit" => {
            let flags = parse_flags(arguments, &["--dest"], &[])?;
            Ok(Command::UnicodeEmit {
                destination: flags.values.get("--dest").map(PathBuf::from),
            })
        }
        "verify" => {
            reject_extra_arguments(arguments, &[])?;
            Ok(Command::UnicodeVerify)
        }
        _ if subcommand.starts_with("--") => Err(usage(format!("unknown flag `{subcommand}`"))),
        _ => Err(usage(format!("unknown unicode subcommand `{subcommand}`"))),
    }
}

fn parse_ledger_command(arguments: &mut impl Iterator<Item = OsString>) -> Result<Command> {
    let subcommand = required_argument(arguments, "ledger subcommand")?;
    match subcommand.as_str() {
        "verify" => {
            expect_flag(arguments, "--gate")?;
            let value = flag_value(arguments, "--gate")?;
            let gate = Gate::parse(&value)?;
            if gate != Gate::G0 {
                return Err(usage(format!(
                    "ledger verify requires `--gate G0`, found `{value}`"
                )));
            }
            reject_extra_arguments(arguments, &["--gate"])?;
            Ok(Command::LedgerVerify)
        }
        "rebuild" => {
            let flags = parse_flags(arguments, &[], &["--check", "--write"])?;
            if flags.switches.contains("--check") && flags.switches.contains("--write") {
                return Err(usage(
                    "ledger rebuild accepts `--check` or `--write`, not both",
                ));
            }
            let check = flags.switches.contains("--check");
            Ok(Command::LedgerRebuild { check })
        }
        _ if subcommand.starts_with("--") => Err(usage(format!("unknown flag `{subcommand}`"))),
        _ => Err(usage(format!("unknown ledger subcommand `{subcommand}`"))),
    }
}

/// Accepted `--aspect` values, for the unknown-aspect usage detail.
const COMPLETION_ASPECTS: &str = "contract, evidence, coverage, regression, mutation, aggregate";

fn parse_completion_command(arguments: &mut impl Iterator<Item = OsString>) -> Result<Command> {
    let subcommand = required_argument(arguments, "completion subcommand")?;
    match subcommand.as_str() {
        "verify" => parse_completion_request(arguments)
            .map(|(scope, aspect)| Command::CompletionVerify { scope, aspect }),
        "evidence" => parse_completion_request(arguments)
            .map(|(scope, aspect)| Command::CompletionEvidence { scope, aspect }),
        "regenerate" => {
            let flags = parse_flags(arguments, &[], &["--check"])?;
            let check = flags.switches.contains("--check");
            Ok(Command::CompletionRegenerate { check })
        }
        _ if subcommand.starts_with("--") => Err(usage(format!("unknown flag `{subcommand}`"))),
        _ => Err(usage(format!(
            "unknown completion subcommand `{subcommand}`"
        ))),
    }
}

fn parse_completion_request(
    arguments: &mut impl Iterator<Item = OsString>,
) -> Result<(CompletionScope, CompletionAspect)> {
    let flags = parse_flags(
        arguments,
        &[
            "--leaf",
            "--cluster",
            "--track",
            "--wave",
            "--root",
            "--aspect",
        ],
        &[],
    )?;
    Ok((
        completion_scope(&flags.values)?,
        completion_aspect(&flags.values)?,
    ))
}

fn completion_scope(values: &BTreeMap<String, String>) -> Result<CompletionScope> {
    let found: Vec<CompletionScope> = [
        (
            "--leaf",
            CompletionScope::Leaf as fn(String) -> CompletionScope,
        ),
        ("--cluster", CompletionScope::Cluster),
        ("--track", CompletionScope::Track),
        ("--wave", CompletionScope::Wave),
        ("--root", CompletionScope::Root),
    ]
    .into_iter()
    .filter_map(|(flag, wrap)| values.get(flag).map(|value| wrap(value.clone())))
    .collect();
    match found.as_slice() {
        [scope] => Ok(scope.clone()),
        [] => Err(usage(
            "completion verify requires exactly one of --leaf, --cluster, --track, --wave, or --root",
        )),
        _ => Err(usage(
            "completion scope flags are mutually exclusive; pass exactly one of --leaf, --cluster, --track, --wave, or --root",
        )),
    }
}

fn completion_aspect(values: &BTreeMap<String, String>) -> Result<CompletionAspect> {
    match values.get("--aspect") {
        None => Ok(CompletionAspect::Aggregate),
        Some(value) => CompletionAspect::parse(value).ok_or_else(|| {
            usage(format!(
                "unknown aspect `{value}`; expected one of {COMPLETION_ASPECTS}"
            ))
        }),
    }
}

/// Parses `<index>/<count>` into a validated shard. Out-of-matrix coordinates
/// are rejected by [`ShardSpec::new`] itself.
fn parse_diagnostics_command(arguments: &mut impl Iterator<Item = OsString>) -> Result<Command> {
    expect_literal(arguments, "regenerate", "diagnostics subcommand")?;
    let flags = parse_flags(arguments, &[], &["--check"])?;
    let check = flags.switches.contains("--check");
    Ok(Command::DiagnosticsRegenerate { check })
}

fn parse_toolchain_command(arguments: &mut impl Iterator<Item = OsString>) -> Result<Command> {
    let subcommand = required_argument(arguments, "toolchain subcommand")?;
    match subcommand.as_str() {
        "evidence" => {
            reject_extra_arguments(arguments, &[])?;
            Ok(Command::ToolchainEvidence)
        }
        "object" => {
            let flags = parse_flags(arguments, &["--target", "--out"], &[])?;
            let target = required_flag(&flags.values, "--target", "toolchain object")?;
            let out = PathBuf::from(required_flag(&flags.values, "--out", "toolchain object")?);
            Ok(Command::ToolchainObject { target, out })
        }
        _ => Err(usage(format!(
            "unknown toolchain subcommand `{subcommand}`"
        ))),
    }
}
fn parse_perf_command(arguments: &mut impl Iterator<Item = OsString>) -> Result<Command> {
    let subcommand = required_argument(arguments, "perf subcommand")?;
    match subcommand.as_str() {
        "stage0" => {
            reject_extra_arguments(arguments, &[])?;
            Ok(Command::PerfStage0)
        }
        "jit" => {
            reject_extra_arguments(arguments, &[])?;
            Ok(Command::PerfJit)
        }
        "compare" => {
            let flags = parse_flags(arguments, &["--rules", "--baseline", "--scorecard"], &[])?;
            let rules = PathBuf::from(required_flag(&flags.values, "--rules", "perf compare")?);
            let baseline =
                PathBuf::from(required_flag(&flags.values, "--baseline", "perf compare")?);
            let scorecard =
                PathBuf::from(required_flag(&flags.values, "--scorecard", "perf compare")?);
            Ok(Command::PerfCompare {
                rules,
                baseline,
                scorecard,
            })
        }
        _ if subcommand.starts_with("--") => Err(usage(format!("unknown flag `{subcommand}`"))),
        _ => Err(usage(format!("unknown perf subcommand `{subcommand}`"))),
    }
}

/// Parsed `--flag value` pairs and bare `--flag` switches, in any order.
struct FlagSet {
    values: BTreeMap<String, String>,
    switches: BTreeSet<String>,
}

/// Drains the remaining argv, accepting exactly the declared flags and
/// failing closed on anything else.
fn parse_flags(
    arguments: &mut impl Iterator<Item = OsString>,
    value_flags: &[&str],
    switch_flags: &[&str],
) -> Result<FlagSet> {
    let mut values = BTreeMap::new();
    let mut switches = BTreeSet::new();
    while let Some(argument) = arguments.next() {
        let flag = argument
            .into_string()
            .map_err(|_| usage("flag must be valid UTF-8"))?;
        if !flag.starts_with("--") {
            return Err(usage(format!("unexpected argument `{flag}`")));
        }
        if switch_flags.contains(&flag.as_str()) {
            if !switches.insert(flag.clone()) {
                return Err(usage(format!("duplicate flag `{flag}`")));
            }
            continue;
        }
        if value_flags.contains(&flag.as_str()) {
            if values.contains_key(&flag) {
                return Err(usage(format!("duplicate flag `{flag}`")));
            }
            let value = arguments
                .next()
                .ok_or_else(|| usage(format!("missing value for `{flag}`")))?;
            let value = value
                .into_string()
                .map_err(|_| usage(format!("value for `{flag}` must be valid UTF-8")))?;
            if value.starts_with("--") {
                return Err(usage(format!(
                    "missing value for `{flag}`, found flag `{value}`"
                )));
            }
            values.insert(flag, value);
            continue;
        }
        return Err(usage(format!("unknown flag `{flag}`")));
    }
    Ok(FlagSet { values, switches })
}

fn required_flag(values: &BTreeMap<String, String>, flag: &str, context: &str) -> Result<String> {
    values
        .get(flag)
        .cloned()
        .ok_or_else(|| usage(format!("{context} requires `{flag}`")))
}

fn parse_formal_command(arguments: &mut impl Iterator<Item = OsString>) -> Result<Command> {
    let subcommand = required_argument(arguments, "formal subcommand")?;
    match subcommand.as_str() {
        "audit" => {
            expect_flag(arguments, "--gates")?;
            let gates = parse_formal_gates(&flag_value(arguments, "--gates")?)?;
            reject_extra_arguments(arguments, &["--gates"])?;
            Ok(Command::FormalAudit(gates))
        }
        "regenerate-fixtures" => {
            reject_extra_arguments(arguments, &[])?;
            Ok(Command::RegenerateFixtures)
        }
        _ if subcommand.starts_with("--") => Err(usage(format!("unknown flag `{subcommand}`"))),
        _ => Err(usage(format!("unknown formal subcommand `{subcommand}`"))),
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

fn expect_literal(
    arguments: &mut impl Iterator<Item = OsString>,
    expected: &str,
    description: &str,
) -> Result<()> {
    let value = required_argument(arguments, description)?;
    if value == expected {
        return Ok(());
    }
    if value.starts_with("--") {
        return Err(usage(format!("unknown flag `{value}`")));
    }
    Err(usage(format!(
        "expected {description} `{expected}`, found `{value}`"
    )))
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

fn reject_extra_arguments(
    arguments: &mut impl Iterator<Item = OsString>,
    known_flags: &[&str],
) -> Result<()> {
    let Some(value) = arguments.next() else {
        return Ok(());
    };
    let value = value
        .into_string()
        .map_err(|_| usage("extra argument must be valid UTF-8"))?;
    if known_flags.contains(&value.as_str()) {
        return Err(usage(format!("duplicate flag `{value}`")));
    }
    if value.starts_with("--") {
        return Err(usage(format!("unknown flag `{value}`")));
    }
    Err(usage(format!("unexpected argument `{value}`")))
}

fn parse_formal_gates(value: &str) -> Result<Vec<Gate>> {
    if value.is_empty() {
        return Err(usage("`--gates` must not be empty"));
    }

    let mut gates = Vec::new();
    for name in value.split(',') {
        if name.is_empty() {
            return Err(usage("`--gates` contains an empty gate"));
        }
        let gate = Gate::parse(name)?;
        if gates.contains(&gate) {
            return Err(usage(format!("duplicate gate `{name}`")));
        }
        gates.push(gate);
    }

    let dependency_order = Gate::FORMAL_ORDER;
    if gates.len() > dependency_order.len()
        || gates
            .iter()
            .zip(dependency_order)
            .any(|(actual, expected)| *actual != expected)
    {
        let expected = dependency_order.map(gate_name).join(",");
        return Err(VerificationError::new(
            ErrorCode::GateDependency,
            format!("formal audit gates must be a dependency-respecting prefix of {expected}"),
        ));
    }

    Ok(gates)
}

fn verify_authority_command(root: &Path, release: &str) -> Result<()> {
    let report = verify_authority(root, release)?;
    emit(&format!(
        "AUTHORITY PASS release={} checks={}\n",
        report.release, report.checks
    ))
}

fn extract_catalog(root: &Path, catalog: &str) -> Result<()> {
    let cells = extract_catalog_cells(root, catalog)?;
    write_catalog_json(io::stdout().lock(), catalog, &cells)
}

fn regenerate_catalog(root: &Path, release: &str, check: bool) -> Result<()> {
    if release != "typescript-7.0.2" {
        return Err(usage(format!(
            "catalog regeneration requires `--release typescript-7.0.2`, found `{release}`"
        )));
    }
    let report = regenerate_manifest(root, check)?;
    let mode = if report.wrote_manifest {
        "write"
    } else {
        "check"
    };
    emit(&format!(
        "CATALOG PASS release={release} mode={mode} catalogs={} identifiers={}\n",
        report.catalogs, report.identifiers
    ))
}

fn fetch_source(root: &Path, name: &str, destination: &Path) -> Result<()> {
    let report = materialize_named(root, name, destination, &CommandBackend::default())?;
    emit(&format!(
        "SOURCE FETCH PASS name={} release={} destination={}\n",
        report.name,
        report.pin,
        report.destination.display()
    ))
}

fn fetch_unicode(root: &Path) -> Result<()> {
    let report = unicode::fetch(root, &CommandBackend::default())?;
    emit(&format!(
        "UNICODE FETCH PASS sources={} destination={}\n",
        report.source_count,
        report.destination.display()
    ))
}

fn emit_unicode(root: &Path, destination: Option<&Path>) -> Result<()> {
    let report = unicode::emit(root, destination)?;
    emit(&format!(
        "UNICODE EMIT PASS sources={} destination={}\n",
        report.source_count,
        report.destination.display()
    ))
}

fn verify_unicode(root: &Path) -> Result<()> {
    let report = unicode::verify(root)?;
    emit(&format!(
        "UNICODE VERIFY PASS sources={} destination={}\n",
        report.source_count,
        report.destination.display()
    ))
}

fn verify_g0(root: &Path) -> Result<()> {
    let workspace = audit_workspace(root)?;
    let ledger = verify_ledger_g0(root)?;
    let workspace_checks = report_checks(workspace, Gate::G0, "workspace G0 audit")?;
    let ledger_checks = report_checks(ledger, Gate::G0, "ledger G0 verification")?;
    let checks = ledger_checks
        .checked_add(workspace_checks)
        .ok_or_else(|| VerificationError::new(ErrorCode::Schema, "G0 check count overflow"))?;
    emit(&format!("G0 PASS checks={checks}\n"))
}

fn audit_formal(root: &Path, gates: &[Gate]) -> Result<()> {
    let formal_gates: Vec<_> = gates
        .iter()
        .copied()
        .filter(|gate| *gate != Gate::G6)
        .collect();
    let reports = audit_formal_gates(root, &formal_gates)?;
    let checks = ordered_report_checks(reports, &formal_gates)?;

    let mut output = String::new();
    for (gate, checks) in formal_gates.iter().zip(checks) {
        append_pass_line(&mut output, *gate, checks);
    }

    if gates.last() == Some(&Gate::G6) {
        let reports = audit_formal_artifacts(root, &[Gate::G6])?;
        let checks = ordered_report_checks(reports, &[Gate::G6])?
            .into_iter()
            .next()
            .ok_or_else(|| {
                VerificationError::new(ErrorCode::Schema, "G6 audit omitted its report")
            })?;
        qualify_replay_canary(root)?;
        append_g6_ready(&mut output, checks)?;
    }

    emit(&output)
}

fn regenerate_fixtures(root: &Path) -> Result<()> {
    let transitions = regenerate_canonical_fixture(root)?;
    emit(&format!("G6 FIXTURES transitions={transitions}\n"))
}
fn verify_completion_command(
    root: &Path,
    scope: &CompletionScope,
    aspect: CompletionAspect,
) -> Result<()> {
    let report = verified_completion_report(root, scope, aspect)?;
    let line = report.success_line().ok_or_else(|| {
        VerificationError::new(
            ErrorCode::Schema,
            "passing completion report omitted its success line",
        )
    })?;
    emit(&format!("{line}\n"))
}

fn completion_evidence_command(
    root: &Path,
    scope: &CompletionScope,
    aspect: CompletionAspect,
) -> Result<()> {
    let report = verified_completion_report(root, scope, aspect)?;
    let evidence = report.gate_evidence.ok_or_else(|| {
        VerificationError::new(
            ErrorCode::Schema,
            "canonical evidence is available only for direct leaf aspect checks",
        )
    })?;
    emit(&format!("{evidence}\n"))
}

fn verified_completion_report(
    root: &Path,
    scope: &CompletionScope,
    aspect: CompletionAspect,
) -> Result<CompletionReport> {
    let report = verify_completion(root, scope, aspect)?;
    if report.is_pass() {
        return Ok(report);
    }
    let shown = report
        .failures
        .iter()
        .take(10)
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    let extra = report.failures.len().saturating_sub(shown.len());
    let mut detail = shown.join("; ");
    if extra != 0 {
        detail.push_str(&format!("; +{extra} more"));
    }
    Err(VerificationError::new(
        ErrorCode::Workspace,
        format!(
            "completion verification failed for aspect `{}`: {detail}",
            aspect.as_str()
        ),
    ))
}

fn regenerate_completion_command(root: &Path, check: bool) -> Result<()> {
    let mode = if check {
        RegenerateMode::Check
    } else {
        RegenerateMode::Write
    };
    match regenerate_completion_program(root, mode)? {
        RegenerateOutcome::Identical => emit("COMPLETION PROGRAM PASS mode=check\n"),
        RegenerateOutcome::Written { bytes } => emit(&format!(
            "COMPLETION PROGRAM PASS mode=write bytes={bytes}\n"
        )),
    }
}

fn rebuild_ledger_command(root: &Path, check: bool) -> Result<()> {
    let receipts = discover_receipts(root)?;
    let mode = if check {
        RebuildMode::Check
    } else {
        RebuildMode::Write
    };
    let report = rebuild_ledger(root, &receipts, mode)?;
    if !report.is_clean() {
        let shown = report
            .rejections
            .iter()
            .take(5)
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        let extra = report.rejections.len().saturating_sub(shown.len());
        let mut detail = shown.join("; ");
        if extra != 0 {
            detail.push_str(&format!("; +{extra} more"));
        }
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!(
                "ledger rebuild rejected {} obligations: {detail}",
                report.rejections.len()
            ),
        ));
    }
    if check && report.changed {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "ledger rebuild check found drift in {}",
                report.ledger_path.display()
            ),
        ));
    }
    let mode = if check { "check" } else { "write" };
    emit(&format!(
        "LEDGER REBUILD PASS mode={mode} obligations={} receipts={} bytes={} changed={} digest={}\n",
        report.obligations,
        report.receipts_consumed,
        report.bytes,
        report.changed,
        report.ledger_digest
    ))
}

fn regenerate_diagnostics(root: &Path, check: bool) -> Result<()> {
    let json = root.join(DIAGNOSTIC_SOURCE);
    let generated = root.join(DIAGNOSTIC_GENERATED);
    if check {
        diagnostic_catalog::check(&json, DIAGNOSTIC_SOURCE, &generated)
            .map_err(diagnostic_catalog_error)?;
        emit(&format!(
            "DIAGNOSTICS PASS mode=check source={DIAGNOSTIC_SOURCE}\n"
        ))
    } else {
        diagnostic_catalog::write_generated(&json, DIAGNOSTIC_SOURCE, &generated)
            .map_err(diagnostic_catalog_error)?;
        emit(&format!(
            "DIAGNOSTICS PASS mode=write source={DIAGNOSTIC_SOURCE}\n"
        ))
    }
}

fn diagnostic_catalog_error(error: CatalogError) -> VerificationError {
    match error {
        CatalogError::Io(source) => {
            VerificationError::new(ErrorCode::Io, format!("diagnostic catalog: {source}"))
        }
        CatalogError::Json(source) => {
            VerificationError::new(ErrorCode::Json, format!("diagnostic catalog: {source}"))
        }
        CatalogError::Mismatch { path } => VerificationError::new(
            ErrorCode::SetMismatch,
            format!("generated diagnostic catalog drifted from {DIAGNOSTIC_SOURCE}: {path}"),
        ),
    }
}

fn audit_toolchain_evidence(root: &Path) -> Result<()> {
    let cells = load_target_cells(root)?;
    let blocked = blocking_obligations(&cells);
    if !blocked.is_empty() {
        let identifiers: Vec<&str> = blocked
            .iter()
            .map(|(identifier, _)| identifier.as_str())
            .collect();
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!(
                "toolchain evidence declares {} non-PASS obligations: {}",
                identifiers.len(),
                identifiers.join(", ")
            ),
        ));
    }
    emit(&format!(
        "TOOLCHAIN EVIDENCE PASS cells={} obligations={} blocking=0 external_blocked=0\n",
        cells.len(),
        catalog_identifiers().len(),
    ))
}
fn emit_toolchain_object(target: &str, out: &Path) -> Result<()> {
    let object = emit_probe_object(target, out)?;
    emit(&format!(
        "TOOLCHAIN OBJECT PASS target={} sha256={} bytes={} entry={} helpers={}\n",
        object.target,
        object.sha256,
        object.byte_len,
        object.entry_symbol,
        object.required_helpers.join(","),
    ))
}

fn run_perf_stage0() -> Result<()> {
    let receipt = perf_stage0::run();
    emit_perf_receipt("STAGE0", receipt)
}

fn run_perf_jit() -> Result<()> {
    let receipt = perf_jit::run().map_err(|error| {
        VerificationError::new(
            ErrorCode::ToolFailed,
            format!("perf jit measurement failed: {error:#}"),
        )
    })?;
    let receipt = serde_json::from_str(&receipt).map_err(|error| {
        VerificationError::new(
            ErrorCode::Json,
            format!("perf jit returned invalid JSON: {error}"),
        )
    })?;
    emit_perf_receipt("JIT", receipt)
}

fn emit_perf_receipt(name: &str, receipt: serde_json::Value) -> Result<()> {
    let state = receipt
        .get("state")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| {
            VerificationError::new(
                ErrorCode::Schema,
                format!("perf {} receipt omits `state`", name.to_ascii_lowercase()),
            )
        })?;
    if state != "ACCEPTED" {
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!(
                "perf {} receipt state={state}: {receipt}",
                name.to_ascii_lowercase()
            ),
        ));
    }
    let receipt = serde_json::to_string(&receipt).map_err(|error| {
        VerificationError::new(
            ErrorCode::Json,
            format!(
                "cannot encode perf {} receipt: {error}",
                name.to_ascii_lowercase()
            ),
        )
    })?;
    emit(&format!("PERF {name} PASS receipt={receipt}\n"))
}

fn compare_perf(rules: &Path, baseline: &Path, scorecard: &Path) -> Result<()> {
    match perf_guard::evaluate_stage1_guard_from_paths(rules, baseline, scorecard).map_err(
        |error| {
            VerificationError::new(
                ErrorCode::ToolFailed,
                format!("perf comparison failed: {error}"),
            )
        },
    )? {
        Verdict::Pass {
            current_median,
            bound,
        } => emit(&format!(
            "PERF COMPARE PASS current_median={current_median} bound={bound}\n"
        )),
        Verdict::Fail(detail) => Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!("perf comparison rejected: {detail}"),
        )),
    }
}

fn ordered_report_checks(reports: Vec<GateReport>, expected: &[Gate]) -> Result<Vec<usize>> {
    if reports.len() != expected.len() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "gate audit returned {} reports for {} requested gates",
                reports.len(),
                expected.len()
            ),
        ));
    }

    let mut checks_by_gate = BTreeMap::new();
    for report in reports {
        if !expected.contains(&report.gate) {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "gate audit returned unexpected report for {}",
                    gate_name(report.gate)
                ),
            ));
        }
        if checks_by_gate.insert(report.gate, report.checks).is_some() {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "gate audit returned duplicate report for {}",
                    gate_name(report.gate)
                ),
            ));
        }
    }

    expected
        .iter()
        .map(|gate| {
            checks_by_gate.get(gate).copied().ok_or_else(|| {
                VerificationError::new(
                    ErrorCode::Schema,
                    format!("gate audit omitted report for {}", gate_name(*gate)),
                )
            })
        })
        .collect()
}

fn report_checks(report: GateReport, expected: Gate, source: &str) -> Result<usize> {
    if report.gate == expected {
        return Ok(report.checks);
    }
    Err(VerificationError::new(
        ErrorCode::Schema,
        format!(
            "{source} returned {} instead of {}",
            gate_name(report.gate),
            gate_name(expected)
        ),
    ))
}

fn append_pass_line(output: &mut String, gate: Gate, checks: usize) {
    output.push_str(gate_name(gate));
    output.push_str(" PASS checks=");
    output.push_str(&checks.to_string());
    output.push('\n');
}

fn append_g6_ready(output: &mut String, checks: usize) -> Result<()> {
    let mut lanes = ready_lane_records();
    if lanes.len() != 6 {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "G6 READY registry contains {} lanes instead of 6",
                lanes.len()
            ),
        ));
    }
    if lanes.iter().any(|lane| lane.status != LaneStatus::Ready) {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            "G6 READY registry contains a non-READY lane",
        ));
    }

    lanes.sort_by(|left, right| left.lane.cmp(right.lane));
    if lanes.windows(2).any(|pair| pair[0].lane == pair[1].lane) {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            "G6 READY registry contains duplicate lane names",
        ));
    }

    output.push_str("G6 READY lanes=6 checks=");
    output.push_str(&checks.to_string());
    output.push('\n');
    for lane in lanes {
        output.push_str("G6 READY lane=");
        output.push_str(lane.lane);
        output.push_str(" model=");
        output.push_str(lane.formal_model);
        output.push('\n');
    }
    Ok(())
}

fn emit(output: &str) -> Result<()> {
    io::stdout()
        .lock()
        .write_all(output.as_bytes())
        .map_err(|error| {
            VerificationError::new(ErrorCode::Io, format!("cannot write output: {error}"))
        })
}

fn gate_name(gate: Gate) -> &'static str {
    match gate {
        Gate::G0 => "G0",
        Gate::G1 => "G1",
        Gate::G2 => "G2",
        Gate::G3 => "G3",
        Gate::G4 => "G4",
        Gate::G5 => "G5",
        Gate::G6 => "G6",
    }
}

fn usage(detail: impl Into<String>) -> VerificationError {
    VerificationError::new(ErrorCode::Usage, detail)
}
#[cfg(test)]
mod tests {
    use super::*;

    fn parse(arguments: &[&str]) -> Result<Command> {
        parse_command(arguments.iter().map(|argument| OsString::from(*argument)))
    }

    #[test]
    fn parses_leaf_evidence_generation_request() {
        let command = parse(&[
            "bamts-verification",
            "leaf-evidence",
            "generate",
            "--leaf",
            "B0.1",
            "--aspect",
            "mutation",
            "--out",
            ".outline/evidence/B0.1-mutation.json",
        ])
        .expect("leaf evidence generation command");
        assert_eq!(
            command,
            Command::LeafEvidenceGenerate {
                leaf: "B0.1".to_owned(),
                aspect: "mutation".to_owned(),
                out: PathBuf::from(".outline/evidence/B0.1-mutation.json"),
            }
        );
    }

    #[test]
    fn parses_completion_evidence_request() {
        let command = parse(&[
            "bamts-verification",
            "completion",
            "evidence",
            "--leaf",
            "B0.1",
            "--aspect",
            "contract",
        ])
        .expect("completion evidence command");
        assert_eq!(
            command,
            Command::CompletionEvidence {
                scope: CompletionScope::Leaf("B0.1".to_owned()),
                aspect: CompletionAspect::Contract,
            }
        );
    }

    #[test]
    fn parses_suite_run_into_canonical_request() {
        let command = parse(&[
            "bamts-verification",
            "suite",
            "run",
            "--catalog",
            "test262",
            "--shard",
            "2/4",
            "--receipt",
            "receipts/2.jsonl",
            "--runner",
            "jit",
            "--platform",
            "ubuntu-latest",
            "--workflow",
            ".github/workflows/ci.yml",
            "--run-id",
            "41",
            "--run-attempt",
            "2",
            "--source-sha",
            "0123456789abcdef0123456789abcdef01234567",
            "--job",
            "conformance",
            "--host",
            "GitHub Actions 1",
            "--runtime",
            "node-v24.18.0 rustc-1.91.0",
        ])
        .expect("suite run command");
        let Command::SuiteRun(request) = command else {
            panic!("suite run command variant")
        };
        assert_eq!(request.catalog, "test262");
        assert_eq!((request.shard.index(), request.shard.count()), (2, 4));
        assert_eq!(request.receipt, PathBuf::from("receipts/2.jsonl"));
        assert_eq!(request.runner, "jit");
        assert_eq!(request.platform, "ubuntu-latest");
        assert_eq!(
            request.execution.first_mismatch_field(
                &ExecutionBinding::new(
                    ".github/workflows/ci.yml",
                    "41",
                    2,
                    "0123456789abcdef0123456789abcdef01234567",
                    "conformance",
                    "GitHub Actions 1",
                    "node-v24.18.0 rustc-1.91.0",
                )
                .expect("binding")
            ),
            None
        );
    }

    #[test]
    fn parses_suite_merge_check_into_canonical_request() {
        let command = parse(&[
            "bamts-verification",
            "suite",
            "merge",
            "--catalog",
            "test262",
            "--receipts",
            "receipts",
            "--out",
            "merged.jsonl",
            "--check",
        ])
        .expect("suite merge command");
        let Command::SuiteMerge(request) = command else {
            panic!("suite merge command variant")
        };
        assert_eq!(request.catalog, "test262");
        assert_eq!(request.receipts, PathBuf::from("receipts"));
        assert_eq!(request.out, PathBuf::from("merged.jsonl"));
        assert_eq!(request.publish, PublishMode::Check);
    }

    #[test]
    fn parses_suite_families_with_its_optional_flags() {
        let Command::SuiteFamilies(plain) =
            parse(&["bamts-verification", "suite", "families", "merged.jsonl"]).expect("plain")
        else {
            panic!("suite families variant")
        };
        assert_eq!(plain.receipt, PathBuf::from("merged.jsonl"));
        assert_eq!(plain.top, 20);
        assert_eq!(plain.family, None);
        assert_eq!(plain.root, None);

        let Command::SuiteFamilies(one) = parse(&[
            "bamts-verification",
            "suite",
            "families",
            "merged.jsonl",
            "--top",
            "5",
            "--family",
            "types/mismatch",
            "--root",
            "target/authority/test262",
        ])
        .expect("flags") else {
            panic!("suite families variant")
        };
        assert_eq!(one.top, 5);
        assert_eq!(one.family.as_deref(), Some("types/mismatch"));
        assert_eq!(one.root, Some(PathBuf::from("target/authority/test262")));
    }

    #[test]
    fn parses_suite_diff_with_two_receipts_and_a_regression_switch() {
        let Command::SuiteDiff(request) = parse(&[
            "bamts-verification",
            "suite",
            "diff",
            "before.jsonl",
            "after.jsonl",
            "--limit",
            "3",
            "--fail-on-regression",
        ])
        .expect("diff") else {
            panic!("suite diff variant")
        };
        assert_eq!(request.a, PathBuf::from("before.jsonl"));
        assert_eq!(request.b, PathBuf::from("after.jsonl"));
        assert_eq!(request.limit, 3);
        assert!(request.fail_on_regression);

        let Command::SuiteDiff(defaults) =
            parse(&["bamts-verification", "suite", "diff", "a.jsonl", "b.jsonl"])
                .expect("defaults")
        else {
            panic!("suite diff variant")
        };
        assert_eq!(defaults.limit, 20);
        assert!(!defaults.fail_on_regression);
    }

    #[test]
    fn rejects_malformed_suite_report_arguments() {
        for arguments in [
            vec!["bamts-verification", "suite", "families"],
            vec!["bamts-verification", "suite", "families", "--top", "5"],
            vec![
                "bamts-verification",
                "suite",
                "families",
                "r.jsonl",
                "--top",
                "many",
            ],
            vec![
                "bamts-verification",
                "suite",
                "families",
                "r.jsonl",
                "--top",
            ],
            vec!["bamts-verification", "suite", "diff", "only-one.jsonl"],
            vec![
                "bamts-verification",
                "suite",
                "diff",
                "a.jsonl",
                "--limit",
                "2",
            ],
            vec![
                "bamts-verification",
                "suite",
                "diff",
                "a.jsonl",
                "b.jsonl",
                "--limit",
                "x",
            ],
            vec![
                "bamts-verification",
                "suite",
                "diff",
                "a.jsonl",
                "b.jsonl",
                "c.jsonl",
            ],
        ] {
            let error = parse(&arguments).expect_err(&format!("{arguments:?}"));
            assert_eq!(error.code(), ErrorCode::Usage, "{arguments:?}");
        }
    }

    #[test]
    fn rejects_malformed_suite_shard() {
        let error = parse(&[
            "bamts-verification",
            "suite",
            "run",
            "--catalog",
            "test262",
            "--shard",
            "4/4",
            "--receipt",
            "receipt.jsonl",
            "--runner",
            "jit",
            "--platform",
            "ubuntu-latest",
            "--workflow",
            ".github/workflows/ci.yml",
            "--run-id",
            "41",
            "--run-attempt",
            "2",
            "--source-sha",
            "0123456789abcdef0123456789abcdef01234567",
            "--job",
            "conformance",
            "--host",
            "GitHub Actions 1",
            "--runtime",
            "node-v24.18.0 rustc-1.91.0",
        ])
        .expect_err("out-of-range shard");
        assert_eq!(error.code(), ErrorCode::Usage);
        assert!(error.to_string().contains("outside matrix"));
    }

    #[test]
    fn rejects_missing_and_duplicate_suite_flags() {
        let missing = parse(&[
            "bamts-verification",
            "suite",
            "merge",
            "--catalog",
            "test262",
        ])
        .expect_err("missing receipts");
        assert_eq!(missing.code(), ErrorCode::Usage);
        assert!(missing.to_string().contains("--receipts"));

        let duplicate = parse(&[
            "bamts-verification",
            "suite",
            "merge",
            "--catalog",
            "test262",
            "--catalog",
            "benchmarks",
            "--receipts",
            "receipts",
            "--out",
            "out.jsonl",
        ])
        .expect_err("duplicate catalog");
        assert_eq!(duplicate.code(), ErrorCode::Usage);
        assert!(duplicate.to_string().contains("duplicate flag"));
    }

    #[test]
    fn rejects_missing_and_unknown_suite_subcommands() {
        let missing = parse(&["bamts-verification", "suite"]).expect_err("missing subcommand");
        assert_eq!(missing.code(), ErrorCode::Usage);
        assert!(missing.to_string().contains("missing suite subcommand"));

        let unknown =
            parse(&["bamts-verification", "suite", "snapshot"]).expect_err("unknown subcommand");
        assert_eq!(unknown.code(), ErrorCode::Usage);
        assert!(unknown.to_string().contains("unknown suite subcommand"));
    }
    #[test]
    fn dispatches_suite_variants_to_completion_engine() {
        let root = Path::new(".");
        let run_error = dispatch(
            root,
            Command::SuiteRun(SuiteRunRequest {
                catalog: "not-a-catalog".to_owned(),
                shard: ShardSpec::unsharded(),
                receipt: PathBuf::from("unused.jsonl"),
                runner: "compiler".to_owned(),
                platform: "ubuntu-latest".to_owned(),
                execution: ExecutionBinding::new(
                    "local-test",
                    "local-test",
                    1,
                    "0000000000000000000000000000000000000000",
                    "local-test",
                    "local-test",
                    "local-test",
                )
                .expect("binding"),
            }),
        )
        .expect_err("completion suite validates run catalog");
        assert_eq!(run_error.code(), ErrorCode::Usage);
        assert!(run_error.to_string().contains("unknown catalog"));

        let merge_error = dispatch(
            root,
            Command::SuiteMerge(SuiteMergeRequest {
                catalog: "not-a-catalog".to_owned(),
                receipts: PathBuf::from("unused"),
                out: PathBuf::from("unused.jsonl"),
                publish: PublishMode::Replace,
            }),
        )
        .expect_err("completion suite validates merge catalog");
        assert_eq!(merge_error.code(), ErrorCode::Usage);
        assert!(merge_error.to_string().contains("unknown catalog"));
    }
}
