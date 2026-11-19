use crate::{ErrorCode, Gate, GateReport, Result, VerificationError};
use quint_connect::{Config as DriverConfig, Driver, State, Step};
use serde::{Deserialize, Deserializer, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    ffi::OsString,
    fs,
    path::{Component, Path, PathBuf},
    process::Command,
};

const QUINT_VERSION: &str = "0.32.0";
const QUINT_ARCHIVE_DIGEST: &str =
    "9Yoji7DU6moRm1ofDaN+ftdxNcEGciiGbm7eN4MjlcCbfv7/Y/zchadcXXRmMZmN9oTPXUk9GmhjQOhADJsiSQ==";
const ITF_FORMAT_DESCRIPTION: &str = "https://apalache-mc.org/docs/adr/015adr-trace.html";
const MBT_ACTION: &str = "mbt::actionTaken";
const MBT_PICKS: &str = "mbt::nondetPicks";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CanonicalTransition {
    pub action: CanonicalAction,
    pub bounds: CanonicalBounds,
    pub formal_model: String,
    pub id: String,
    pub observable: CanonicalObject,
    pub post: CanonicalObject,
    pub pre: CanonicalObject,
    pub property: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CanonicalAction {
    pub name: String,
    pub picks: CanonicalObject,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CanonicalBounds {
    pub max_samples: u64,
    pub max_steps: u64,
    pub seed: String,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(untagged)]
pub enum CanonicalScalar {
    Boolean(bool),
    Integer(i64),
    Sequence(Vec<CanonicalScalar>),
    Record(BTreeMap<String, CanonicalScalar>),
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct CanonicalObject(pub BTreeMap<String, CanonicalScalar>);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LaneStatus {
    Ready,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LaneRecord {
    pub lane: &'static str,
    pub formal_model: &'static str,
    pub projection_version: &'static str,
    pub status: LaneStatus,
}

pub fn ready_lane_records() -> Vec<LaneRecord> {
    [
        ("DriverSystem", "driver/DriverSystem.qnt"),
        ("GC", "gc/model.qnt"),
        ("NodeLoop", "node_loop.qnt"),
        ("JIT", "jit_lifecycle.qnt"),
        ("NAPI", "napi_lifecycle.qnt"),
        ("BytecodeCache", "bytecode_cache_keys.qnt"),
    ]
    .into_iter()
    .map(|(lane, formal_model)| LaneRecord {
        lane,
        formal_model,
        projection_version: "bamti.g6-ready/v1",
        status: LaneStatus::Ready,
    })
    .collect()
}

pub fn audit_formal_artifacts(root: &Path, gates: &[Gate]) -> Result<Vec<GateReport>> {
    if gates.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::Usage,
            "formal artifact audit requires G6",
        ));
    }

    let mut requested = BTreeSet::new();
    for gate in gates {
        if !requested.insert(*gate) {
            return Err(VerificationError::new(
                ErrorCode::Usage,
                format!("formal artifact audit received duplicate gate {gate:?}"),
            ));
        }
    }
    if requested != BTreeSet::from([Gate::G6]) {
        return Err(VerificationError::new(
            ErrorCode::GateDependency,
            "formal artifact audit establishes G6 READY only; G1 through G5 require their own evidence gates",
        ));
    }

    Ok(vec![GateReport {
        gate: Gate::G6,
        checks: audit_g6_ready(root)?,
    }])
}

pub fn qualify_replay_canary(root: &Path) -> Result<()> {
    let launcher_dir = local_quint_bin_dir(root)?;
    let path = prepend_path(&launcher_dir)?;
    let executable = env::current_exe().map_err(|error| {
        VerificationError::new(
            ErrorCode::Io,
            format!("cannot resolve current executable for canary replay: {error}"),
        )
    })?;

    let correct = run_canary_child(&executable, root, &path, false)?;
    if !correct.status.success() {
        return Err(VerificationError::new(
            ErrorCode::Replay,
            format!(
                "correct replay canary failed: {}",
                child_output(&correct.stdout, &correct.stderr)
            ),
        ));
    }

    let faulty = run_canary_child(&executable, root, &path, true)?;
    if faulty.status.success() {
        return Err(VerificationError::new(
            ErrorCode::Replay,
            "faulty replay canary unexpectedly succeeded",
        ));
    }
    let faulty_output = child_output(&faulty.stdout, &faulty.stderr);
    if !faulty_output.contains(ErrorCode::Replay.as_str())
        || !faulty_output.contains("canary state comparison failed")
    {
        return Err(VerificationError::new(
            ErrorCode::Replay,
            format!("faulty replay canary did not fail from state comparison: {faulty_output}"),
        ));
    }

    Ok(())
}

pub fn run_replay_canary_child(root: &Path, faulty: bool) -> Result<()> {
    preflight_local_quint(root)?;

    let spec = root.join("crates/bamts-verification/fixtures/formal/canary.qnt");
    if !spec.is_file() {
        return Err(VerificationError::new(
            ErrorCode::ToolMissing,
            format!("missing replay canary specification: {}", spec.display()),
        ));
    }
    let spec = spec.to_string_lossy().into_owned();
    let result = quint_connect::runner::run_test(
        CanaryDriver {
            faulty,
            ..CanaryDriver::default()
        },
        quint_connect::runner::Config {
            test_name: if faulty {
                "bamti formal replay canary (faulty)".to_owned()
            } else {
                "bamti formal replay canary".to_owned()
            },
            gen_config: quint_connect::runner::RunConfig {
                spec,
                main: Some("formal_canary".to_owned()),
                init: Some("init".to_owned()),
                step: Some("step".to_owned()),
                max_samples: Some(4),
                max_steps: Some(6),
                seed: "9731".to_owned(),
            },
        },
    );

    match result {
        Ok(()) => Ok(()),
        Err(error) => {
            let detail = format!("{error:#}");
            let code = if detail.contains("State invariant failed") {
                ErrorCode::Replay
            } else {
                ErrorCode::ToolFailed
            };
            let prefix = if code == ErrorCode::Replay {
                "canary state comparison failed"
            } else {
                "canary Quint execution failed"
            };
            Err(VerificationError::new(code, format!("{prefix}: {detail}")))
        }
    }
}

fn audit_g6_ready(root: &Path) -> Result<usize> {
    let (manifest, normalized) = load_normalized_transitions(root)?;
    let fixture_path = root.join("verification/formal/trace-fixtures.jsonl");
    let fixture = parse_canonical_fixture(&fixture_path)?;
    validate_unique_transition_ids(&fixture, &fixture_path)?;
    compare_transitions(&normalized, &fixture)?;

    let lanes = ready_lane_records();
    if lanes.len() != manifest.runs.len()
        || lanes
            .iter()
            .zip(&manifest.runs)
            .any(|(lane, run)| lane.formal_model != run.model)
    {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            "the six READY lane records no longer match the six formal runs",
        ));
    }

    Ok(10 + manifest.runs.len() * 4 + fixture.len() + lanes.len())
}

fn load_normalized_transitions(root: &Path) -> Result<(RunManifest, Vec<CanonicalTransition>)> {
    let toolchains = read_toolchains(root)?;
    validate_toolchains(&toolchains)?;

    let manifest_path = root.join("verification/formal/quint/runs.json");
    let manifest: RunManifest = read_strict_json_file(&manifest_path)?;
    validate_run_manifest(root, &manifest, &toolchains.quint)?;

    let mut normalized = Vec::new();
    for (expected, run) in expected_runs().iter().zip(&manifest.runs) {
        if run.model != expected.model {
            return Err(VerificationError::new(
                ErrorCode::SetMismatch,
                format!(
                    "run order/model mismatch: expected `{}`, found `{}`",
                    expected.model, run.model
                ),
            ));
        }
        if run.init != "init"
            || run.main_module != expected.main_module
            || run.step != "step"
            || run.trace != expected.trace
            || run.seed != expected.seed
        {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "run `{}` differs from its canonical model/init/step/trace/seed contract",
                    run.model
                ),
            ));
        }
        if run.max_samples != 200 || run.max_steps != 12 {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "run `{}` must use max_samples=200 and max_steps=12",
                    run.model
                ),
            ));
        }

        let trace_path = rooted_path(root, &run.trace, "trace")?;
        let trace = read_bytes(&trace_path)?;
        verify_sha256(&trace_path, &run.trace_sha256, &trace)?;
        normalized.extend(normalize_itf(&trace_path, &trace, run)?);
    }
    validate_unique_transition_ids(&normalized, &manifest_path)?;
    normalized.sort_by(|left, right| left.id.cmp(&right.id));
    Ok((manifest, normalized))
}

fn validate_unique_transition_ids(
    transitions: &[CanonicalTransition],
    source: &Path,
) -> Result<()> {
    let mut ids = BTreeSet::new();
    for transition in transitions {
        if !ids.insert(transition.id.as_str()) {
            return Err(VerificationError::new(
                ErrorCode::Duplicate,
                format!(
                    "{} contains duplicate transition id `{}`",
                    source.display(),
                    transition.id
                ),
            ));
        }
    }
    Ok(())
}

#[derive(Debug, Deserialize)]
struct Toolchains {
    schema: String,
    quint: QuintToolchain,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct QuintToolchain {
    version: String,
    node_minimum: String,
    url: String,
    digest_algorithm: String,
    digest: String,
    commit: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RunManifest {
    schema: String,
    generator_backend: String,
    #[serde(default)]
    replay_backend: Option<String>,
    node_version: String,
    package_lock_sha256: String,
    runs: Vec<RunRecord>,
    tool: RunTool,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RunTool {
    archive_digest: String,
    archive_digest_algorithm: String,
    name: String,
    version: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RunRecord {
    init: String,
    invariants: Vec<String>,
    #[serde(default)]
    liveness_witness: Option<LivenessWitness>,
    main_module: String,
    max_samples: u64,
    max_steps: u64,
    model: String,
    seed: String,
    step: String,
    trace: String,
    trace_sha256: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct LivenessWitness {
    max_samples: u64,
    max_steps: u64,
    name: String,
    seed: String,
    witnessed: u64,
}

struct ExpectedRun {
    model: &'static str,
    main_module: &'static str,
    trace: &'static str,
    seed: &'static str,
}

fn expected_runs() -> [ExpectedRun; 6] {
    [
        ExpectedRun {
            model: "driver/DriverSystem.qnt",
            main_module: "DriverSystem",
            trace: "verification/formal/quint/driver_0.itf.json",
            seed: "101",
        },
        ExpectedRun {
            model: "gc/model.qnt",
            main_module: "model",
            trace: "verification/formal/quint/gc_0.itf.json",
            seed: "202",
        },
        ExpectedRun {
            model: "node_loop.qnt",
            main_module: "node_loop",
            trace: "verification/formal/quint/node_loop_0.itf.json",
            seed: "303",
        },
        ExpectedRun {
            model: "jit_lifecycle.qnt",
            main_module: "jit_lifecycle",
            trace: "verification/formal/quint/jit_0.itf.json",
            seed: "404",
        },
        ExpectedRun {
            model: "napi_lifecycle.qnt",
            main_module: "napi_lifecycle",
            trace: "verification/formal/quint/napi_0.itf.json",
            seed: "505",
        },
        ExpectedRun {
            model: "bytecode_cache_keys.qnt",
            main_module: "bytecode_cache_keys",
            trace: "verification/formal/quint/cache_0.itf.json",
            seed: "606",
        },
    ]
}

fn read_toolchains(root: &Path) -> Result<Toolchains> {
    let path = root.join("formal/toolchains.toml");
    let source = read_text(&path)?;
    toml::from_str(&source).map_err(|error| {
        VerificationError::new(ErrorCode::Toml, format!("{}: {error}", path.display()))
    })
}

fn validate_toolchains(toolchains: &Toolchains) -> Result<()> {
    if toolchains.schema != "bamti.formal-toolchains/v1" {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            "formal/toolchains.toml has an unsupported schema",
        ));
    }
    validate_quint_toolchain(&toolchains.quint)
}

fn validate_quint_toolchain(tool: &QuintToolchain) -> Result<()> {
    if tool.version != QUINT_VERSION
        || tool.node_minimum != "18"
        || tool.url != "https://registry.npmjs.org/@informalsystems/quint/-/quint-0.32.0.tgz"
        || tool.digest_algorithm != "sha512"
        || tool.digest != QUINT_ARCHIVE_DIGEST
        || tool.commit.is_empty()
    {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            "formal/toolchains.toml does not contain the approved Quint 0.32.0 pin",
        ));
    }
    Ok(())
}

fn validate_run_manifest(
    root: &Path,
    manifest: &RunManifest,
    toolchain: &QuintToolchain,
) -> Result<()> {
    if manifest.schema != "bamti.quint-runs/v1"
        || manifest.generator_backend != "quint"
        || manifest.replay_backend.is_some()
        || manifest.node_version != "24.18.0"
    {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            "runs.json must record Quint generation and no product replay in P0",
        ));
    }
    if manifest.tool.name != "@informalsystems/quint"
        || manifest.tool.version != toolchain.version
        || manifest.tool.archive_digest_algorithm != toolchain.digest_algorithm
        || manifest.tool.archive_digest != toolchain.digest
    {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            "runs.json Quint provenance does not match formal/toolchains.toml",
        ));
    }
    if manifest.runs.len() != expected_runs().len() {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!(
                "runs.json must contain exactly six runs, found {}",
                manifest.runs.len()
            ),
        ));
    }

    let lock_path = root.join("formal/quint/package-lock.json");
    let lock = read_bytes(&lock_path)?;
    verify_sha256(&lock_path, &manifest.package_lock_sha256, &lock)?;

    for run in &manifest.runs {
        if run.invariants.is_empty()
            || run.invariants.iter().any(|name| name.trim().is_empty())
            || run.invariants.iter().collect::<BTreeSet<_>>().len() != run.invariants.len()
        {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!("run `{}` has an invalid invariant set", run.model),
            ));
        }
        if let Some(witness) = &run.liveness_witness
            && (witness.max_samples == 0
                || witness.max_steps == 0
                || witness.witnessed == 0
                || witness.name.trim().is_empty()
                || !decimal_seed(&witness.seed))
        {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!("run `{}` has an invalid liveness witness", run.model),
            ));
        }
        if run.max_samples == 0 || run.max_steps == 0 || !decimal_seed(&run.seed) {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!("run `{}` has invalid bounds", run.model),
            ));
        }
        let model_path = rooted_path(root, &format!("formal/quint/{}", run.model), "model")?;
        if !model_path.is_file() {
            return Err(VerificationError::new(
                ErrorCode::Io,
                format!(
                    "run `{}` references missing model {}",
                    run.model,
                    model_path.display()
                ),
            ));
        }
    }
    Ok(())
}

fn parse_canonical_fixture(path: &Path) -> Result<Vec<CanonicalTransition>> {
    let bytes = read_bytes(path)?;
    if bytes.is_empty() || !bytes.ends_with(b"\n") {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("{} must be nonempty and newline terminated", path.display()),
        ));
    }

    let mut transitions = Vec::new();
    for (index, raw_line) in bytes.split_inclusive(|byte| *byte == b'\n').enumerate() {
        let line = &raw_line[..raw_line.len() - 1];
        if line.is_empty() || line.contains(&b'\r') {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "{} has a blank or CRLF line at {}",
                    path.display(),
                    index + 1
                ),
            ));
        }
        let line = std::str::from_utf8(line).map_err(|error| {
            VerificationError::new(
                ErrorCode::Json,
                format!(
                    "{} line {} is not UTF-8: {error}",
                    path.display(),
                    index + 1
                ),
            )
        })?;
        let value = parse_strict_json_value(line, path)?;
        let transition: CanonicalTransition = serde_json::from_value(value).map_err(|error| {
            VerificationError::new(
                ErrorCode::Schema,
                format!("{} line {}: {error}", path.display(), index + 1),
            )
        })?;
        validate_transition(&transition, path)?;
        let canonical = serde_json::to_string(&transition).map_err(|error| {
            VerificationError::new(
                ErrorCode::Json,
                format!(
                    "{} line {} cannot be serialized: {error}",
                    path.display(),
                    index + 1
                ),
            )
        })?;
        if line != canonical {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "{} line {} is not canonical JSON",
                    path.display(),
                    index + 1
                ),
            ));
        }
        transitions.push(transition);
    }
    Ok(transitions)
}

fn validate_transition(transition: &CanonicalTransition, source: &Path) -> Result<()> {
    if transition.id.trim().is_empty()
        || transition.formal_model.trim().is_empty()
        || transition.property != "bounded-transition"
        || transition.action.name.trim().is_empty()
        || transition.action.name == "step"
        || transition.bounds.max_samples == 0
        || transition.bounds.max_steps == 0
        || !decimal_seed(&transition.bounds.seed)
    {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "{} contains an invalid canonical transition",
                source.display()
            ),
        ));
    }
    validate_object(&transition.action.picks, source)?;
    validate_object(&transition.observable, source)?;
    validate_object(&transition.pre, source)?;
    validate_object(&transition.post, source)?;
    if transition.pre.0.keys().collect::<Vec<_>>() != transition.post.0.keys().collect::<Vec<_>>() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "{} transition `{}` changes its state shape",
                source.display(),
                transition.id
            ),
        ));
    }
    Ok(())
}

fn validate_object(object: &CanonicalObject, source: &Path) -> Result<()> {
    if object.0.keys().any(|key| key.trim().is_empty()) {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "{} contains an empty canonical object key",
                source.display()
            ),
        ));
    }
    Ok(())
}

#[derive(Debug)]
struct RawState {
    action: CanonicalAction,
    state: CanonicalObject,
}

fn normalize_itf(path: &Path, bytes: &[u8], run: &RunRecord) -> Result<Vec<CanonicalTransition>> {
    let text = std::str::from_utf8(bytes).map_err(|error| {
        VerificationError::new(
            ErrorCode::Json,
            format!("{} is not UTF-8: {error}", path.display()),
        )
    })?;
    let value = parse_strict_json_value(text, path)?;
    let root = json_object(&value, path, "ITF root")?;
    require_exact_keys(root, &["#meta", "states", "vars"], path, "ITF root")?;

    let meta = json_object(required(root, "#meta", path)?, path, "ITF metadata")?;
    require_exact_keys(
        meta,
        &[
            "description",
            "format",
            "format-description",
            "source",
            "status",
            "timestamp",
        ],
        path,
        "ITF metadata",
    )?;
    if json_string(required(meta, "format", path)?, path, "ITF metadata format")? != "ITF"
        || json_string(
            required(meta, "format-description", path)?,
            path,
            "ITF metadata format-description",
        )? != ITF_FORMAT_DESCRIPTION
        || json_string(required(meta, "source", path)?, path, "ITF metadata source")? != run.model
    {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "{} has ITF provenance inconsistent with `{}`",
                path.display(),
                run.model
            ),
        ));
    }
    let status = json_string(required(meta, "status", path)?, path, "ITF metadata status")?;
    if status != "ok" && status != "violation" {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("{} has invalid ITF status `{status}`", path.display()),
        ));
    }
    let _ = json_string(
        required(meta, "description", path)?,
        path,
        "ITF metadata description",
    )?;
    let _ = json_u64(
        required(meta, "timestamp", path)?,
        path,
        "ITF metadata timestamp",
    )?;

    let vars = json_array(required(root, "vars", path)?, path, "ITF vars")?;
    let mut model_vars = Vec::new();
    let mut seen_model_vars = BTreeSet::new();
    let mut action_metadata_count = 0;
    let mut picks_metadata_count = 0;
    for value in vars {
        let name = json_string(value, path, "ITF variable")?;
        match name.as_str() {
            MBT_ACTION => action_metadata_count += 1,
            MBT_PICKS => picks_metadata_count += 1,
            _ => {
                if !seen_model_vars.insert(name.clone()) {
                    return Err(VerificationError::new(
                        ErrorCode::Duplicate,
                        format!("{} has duplicate ITF variable `{name}`", path.display()),
                    ));
                }
                model_vars.push(name);
            }
        }
    }
    // Quint 0.32.0 emits each MBT metadata variable twice in `vars` under --mbt.
    if action_metadata_count != 2 || picks_metadata_count != 2 || model_vars.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("{} is not a pinned Quint --mbt ITF", path.display()),
        ));
    }

    let states = json_array(required(root, "states", path)?, path, "ITF states")?;
    if states.len() < 2 {
        return Err(VerificationError::new(
            ErrorCode::Transition,
            format!("{} must contain at least two ITF states", path.display()),
        ));
    }

    let mut parsed_states = Vec::with_capacity(states.len());
    let expected_state_keys = model_vars
        .iter()
        .map(String::as_str)
        .chain(["#meta", MBT_ACTION, MBT_PICKS])
        .collect::<BTreeSet<_>>();
    for (index, state_value) in states.iter().enumerate() {
        let state = json_object(state_value, path, "ITF state")?;
        let actual_state_keys = state.keys().map(String::as_str).collect::<BTreeSet<_>>();
        if actual_state_keys != expected_state_keys {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "{} state {index} does not match the ITF variable set",
                    path.display()
                ),
            ));
        }
        let state_meta = json_object(required(state, "#meta", path)?, path, "ITF state metadata")?;
        require_exact_keys(state_meta, &["index"], path, "ITF state metadata")?;
        if json_u64(
            required(state_meta, "index", path)?,
            path,
            "ITF state index",
        )? != index as u64
        {
            return Err(VerificationError::new(
                ErrorCode::Transition,
                format!("{} has noncontiguous ITF state indexes", path.display()),
            ));
        }
        let raw_action_name = json_string(required(state, MBT_ACTION, path)?, path, "MBT action")?;
        let action = CanonicalAction {
            name: normalize_action_name(index, raw_action_name, run, path)?,
            picks: parse_mbt_picks(required(state, MBT_PICKS, path)?, path)?,
        };
        let mut values = BTreeMap::new();
        for variable in &model_vars {
            values.insert(
                variable.clone(),
                canonical_scalar(required(state, variable, path)?, path, variable)?,
            );
        }
        parsed_states.push(RawState {
            action,
            state: CanonicalObject(values),
        });
    }

    Ok(parsed_states
        .windows(2)
        .enumerate()
        .map(|(index, pair)| CanonicalTransition {
            action: pair[1].action.clone(),
            bounds: CanonicalBounds {
                max_samples: run.max_samples,
                max_steps: run.max_steps,
                seed: run.seed.clone(),
            },
            formal_model: run.model.clone(),
            id: format!("quint/{}/{index:03}", run.main_module),
            observable: changed_values(&pair[0].state, &pair[1].state),
            post: pair[1].state.clone(),
            pre: pair[0].state.clone(),
            property: "bounded-transition".to_owned(),
        })
        .collect())
}

fn normalize_action_name(
    index: usize,
    action_name: String,
    run: &RunRecord,
    path: &Path,
) -> Result<String> {
    if action_name.trim().is_empty() {
        return Err(VerificationError::new(
            ErrorCode::Transition,
            format!(
                "{} state {index} has no concrete named action",
                path.display()
            ),
        ));
    }
    if index == 0 {
        if action_name == run.init || action_name == run.step {
            return Ok(run.init.clone());
        }
        return Err(VerificationError::new(
            ErrorCode::Transition,
            format!(
                "{} initial action must be `{}` or `{}`, found `{action_name}`",
                path.display(),
                run.init,
                run.step
            ),
        ));
    }
    if action_name == run.step {
        return Err(VerificationError::new(
            ErrorCode::Transition,
            format!(
                "{} state {index} has no concrete named action",
                path.display()
            ),
        ));
    }
    Ok(action_name)
}

fn parse_mbt_picks(value: &serde_json::Value, path: &Path) -> Result<CanonicalObject> {
    let record = json_object(value, path, "MBT nondeterministic picks")?;
    let mut picks = BTreeMap::new();
    for (name, value) in record {
        let option = json_object(value, path, "MBT nondeterministic pick")?;
        require_exact_keys(option, &["tag", "value"], path, "MBT nondeterministic pick")?;
        match json_string(
            required(option, "tag", path)?,
            path,
            "MBT nondeterministic pick tag",
        )?
        .as_str()
        {
            "None" => {
                let tuple = json_object(required(option, "value", path)?, path, "MBT None value")?;
                require_exact_keys(tuple, &["#tup"], path, "MBT None value")?;
                if !json_array(required(tuple, "#tup", path)?, path, "MBT None tuple")?.is_empty() {
                    return Err(VerificationError::new(
                        ErrorCode::Schema,
                        format!("{} has a nonempty MBT None tuple", path.display()),
                    ));
                }
            }
            "Some" => {
                picks.insert(
                    name.clone(),
                    canonical_scalar(required(option, "value", path)?, path, "MBT Some value")?,
                );
            }
            tag => {
                return Err(VerificationError::new(
                    ErrorCode::Schema,
                    format!("{} has unknown MBT pick tag `{tag}`", path.display()),
                ));
            }
        }
    }
    Ok(CanonicalObject(picks))
}

fn changed_values(pre: &CanonicalObject, post: &CanonicalObject) -> CanonicalObject {
    CanonicalObject(
        post.0
            .iter()
            .filter(|(name, value)| pre.0.get(*name) != Some(*value))
            .map(|(name, value)| (name.clone(), value.clone()))
            .collect(),
    )
}

fn compare_transitions(
    expected: &[CanonicalTransition],
    actual: &[CanonicalTransition],
) -> Result<()> {
    let expected_set = expected
        .iter()
        .map(|transition| transition.id.as_str())
        .collect::<BTreeSet<_>>();
    let actual_set = actual
        .iter()
        .map(|transition| transition.id.as_str())
        .collect::<BTreeSet<_>>();
    if expected_set != actual_set || expected.len() != actual.len() {
        let missing = expected_set
            .difference(&actual_set)
            .copied()
            .collect::<Vec<_>>();
        let extra = actual_set
            .difference(&expected_set)
            .copied()
            .collect::<Vec<_>>();
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!("canonical transition set mismatch; missing={missing:?}, extra={extra:?}"),
        ));
    }
    for (index, (left, right)) in expected.iter().zip(actual).enumerate() {
        if left != right {
            let field = transition_difference(left, right);
            return Err(VerificationError::new(
                ErrorCode::Transition,
                format!(
                    "canonical transition mismatch at index {index}, expected `{}`, actual `{}`; field={field}",
                    left.id, right.id
                ),
            ));
        }
    }
    Ok(())
}

fn transition_difference(left: &CanonicalTransition, right: &CanonicalTransition) -> &'static str {
    if left.id != right.id {
        "id"
    } else if left.formal_model != right.formal_model {
        "formal_model"
    } else if left.property != right.property {
        "property"
    } else if left.bounds != right.bounds {
        "bounds"
    } else if left.action != right.action {
        "action"
    } else if left.pre != right.pre {
        "pre"
    } else if left.post != right.post {
        "post"
    } else {
        "observable"
    }
}

fn preflight_local_quint(root: &Path) -> Result<()> {
    let toolchains = read_toolchains(root)?;
    validate_toolchains(&toolchains)?;

    let lock_path = root.join("formal/quint/package-lock.json");
    let lock = parse_strict_json_file(&lock_path)?;
    let packages = json_object(
        required(
            json_object(&lock, &lock_path, "package lock")?,
            "packages",
            &lock_path,
        )?,
        &lock_path,
        "package lock packages",
    )?;
    let package = json_object(
        required(packages, "node_modules/@informalsystems/quint", &lock_path)?,
        &lock_path,
        "Quint package lock entry",
    )?;
    if json_string(
        required(package, "version", &lock_path)?,
        &lock_path,
        "Quint package version",
    )? != QUINT_VERSION
        || json_string(
            required(package, "integrity", &lock_path)?,
            &lock_path,
            "Quint package integrity",
        )? != format!("sha512-{QUINT_ARCHIVE_DIGEST}")
    {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            "local package lock does not pin Quint 0.32.0",
        ));
    }

    let package_path = root.join("formal/quint/node_modules/@informalsystems/quint/package.json");
    let package_json = parse_strict_json_file(&package_path)?;
    let package = json_object(&package_json, &package_path, "installed Quint package")?;
    if json_string(
        required(package, "version", &package_path)?,
        &package_path,
        "installed Quint version",
    )? != QUINT_VERSION
    {
        return Err(VerificationError::new(
            ErrorCode::ToolMissing,
            "installed Quint package is not version 0.32.0",
        ));
    }

    let launcher = local_quint_launcher(root)?;
    let output = Command::new(&launcher)
        .arg("--version")
        .output()
        .map_err(|error| {
            VerificationError::new(
                ErrorCode::ToolMissing,
                format!(
                    "cannot execute local Quint launcher {}: {error}",
                    launcher.display()
                ),
            )
        })?;
    if !output.status.success() || String::from_utf8_lossy(&output.stdout).trim() != QUINT_VERSION {
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!(
                "local Quint launcher did not report {QUINT_VERSION}: {}",
                child_output(&output.stdout, &output.stderr)
            ),
        ));
    }
    Ok(())
}

fn run_canary_child(
    executable: &Path,
    root: &Path,
    path: &OsString,
    faulty: bool,
) -> Result<std::process::Output> {
    let flag = if faulty {
        "--formal-canary-replay-faulty"
    } else {
        "--formal-canary-replay"
    };
    Command::new(executable)
        .arg(flag)
        .current_dir(root)
        .env("PATH", path)
        .output()
        .map_err(|error| {
            VerificationError::new(
                ErrorCode::Io,
                format!("cannot spawn replay canary child: {error}"),
            )
        })
}

fn local_quint_bin_dir(root: &Path) -> Result<PathBuf> {
    let directory = root.join("formal/quint/node_modules/.bin");
    if !directory.is_dir() {
        return Err(VerificationError::new(
            ErrorCode::ToolMissing,
            format!(
                "missing repository-local Quint bin directory: {}",
                directory.display()
            ),
        ));
    }
    Ok(directory)
}

fn local_quint_launcher(root: &Path) -> Result<PathBuf> {
    let launcher =
        local_quint_bin_dir(root)?.join(if cfg!(windows) { "quint.cmd" } else { "quint" });
    if !launcher.is_file() {
        return Err(VerificationError::new(
            ErrorCode::ToolMissing,
            format!(
                "missing repository-local Quint launcher: {}",
                launcher.display()
            ),
        ));
    }
    Ok(launcher)
}

fn prepend_path(prefix: &Path) -> Result<OsString> {
    let inherited = env::var_os("PATH").unwrap_or_default();
    let mut paths = Vec::from([prefix.to_path_buf()]);
    paths.extend(env::split_paths(&inherited));
    env::join_paths(paths).map_err(|error| {
        VerificationError::new(
            ErrorCode::Io,
            format!("cannot construct controlled PATH for Quint: {error}"),
        )
    })
}

fn child_output(stdout: &[u8], stderr: &[u8]) -> String {
    let stdout = String::from_utf8_lossy(stdout).trim().to_owned();
    let stderr = String::from_utf8_lossy(stderr).trim().to_owned();
    match (stdout.is_empty(), stderr.is_empty()) {
        (true, true) => "child exited without output".to_owned(),
        (false, true) => stdout,
        (true, false) => stderr,
        (false, false) => format!("stdout: {stdout}; stderr: {stderr}"),
    }
}

#[derive(Default)]
struct CanaryDriver {
    value: i64,
    resets: i64,
    faulty: bool,
}

#[derive(Debug, Deserialize, PartialEq)]
struct CanaryState {
    value: i64,
    resets: i64,
}

impl State<CanaryDriver> for CanaryState {
    fn from_driver(driver: &CanaryDriver) -> quint_connect::Result<Self> {
        Ok(Self {
            value: driver.value,
            resets: driver.resets,
        })
    }
}

impl Driver for CanaryDriver {
    type State = CanaryState;

    fn config() -> DriverConfig {
        DriverConfig {
            state: &["state"],
            nondet: &["transition"],
        }
    }

    fn step(&mut self, step: &Step) -> quint_connect::Result {
        quint_connect::switch!(step {
            Init => {
                self.value = 0;
                self.resets = 0;
            },
            Increment(amount: i64) => {
                self.value += if self.faulty { amount + 1 } else { amount };
            },
            Reset => {
                self.value = 0;
                self.resets += 1;
            },
        })
    }
}

fn read_bytes(path: &Path) -> Result<Vec<u8>> {
    fs::read(path).map_err(|error| {
        VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
    })
}

fn read_text(path: &Path) -> Result<String> {
    fs::read_to_string(path).map_err(|error| {
        VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
    })
}

fn rooted_path(root: &Path, relative: &str, kind: &str) -> Result<PathBuf> {
    let path = Path::new(relative);
    if path.components().any(|component| {
        matches!(
            component,
            Component::ParentDir | Component::RootDir | Component::Prefix(_) | Component::CurDir
        )
    }) {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("{kind} path `{relative}` must be a clean relative path"),
        ));
    }
    Ok(root.join(path))
}

fn verify_sha256(path: &Path, expected: &str, bytes: &[u8]) -> Result<()> {
    if !lower_hex_sha256(expected) {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("{} has a noncanonical SHA-256 digest", path.display()),
        ));
    }
    let actual = format!("{:x}", Sha256::digest(bytes));
    if actual != expected {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "{} SHA-256 mismatch: expected {expected}, actual {actual}",
                path.display()
            ),
        ));
    }
    Ok(())
}

fn lower_hex_sha256(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn decimal_seed(value: &str) -> bool {
    !value.is_empty() && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn read_strict_json_file<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T> {
    let value = parse_strict_json_file(path)?;
    serde_json::from_value(value).map_err(|error| {
        VerificationError::new(ErrorCode::Schema, format!("{}: {error}", path.display()))
    })
}

fn parse_strict_json_file(path: &Path) -> Result<serde_json::Value> {
    let text = read_text(path)?;
    parse_strict_json_value(&text, path)
}

fn parse_strict_json_value(text: &str, path: &Path) -> Result<serde_json::Value> {
    let mut deserializer = serde_json::Deserializer::from_str(text);
    let value = StrictJson::deserialize(&mut deserializer).map_err(|error| {
        let code = if error.to_string().contains("duplicate JSON key") {
            ErrorCode::Duplicate
        } else {
            ErrorCode::Json
        };
        VerificationError::new(code, format!("{}: {error}", path.display()))
    })?;
    deserializer.end().map_err(|error| {
        VerificationError::new(ErrorCode::Json, format!("{}: {error}", path.display()))
    })?;
    Ok(value.0)
}

struct StrictJson(serde_json::Value);

impl<'de> Deserialize<'de> for StrictJson {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct StrictJsonVisitor;

        impl<'de> serde::de::Visitor<'de> for StrictJsonVisitor {
            type Value = StrictJson;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("a JSON value without duplicate object keys")
            }

            fn visit_bool<E>(self, value: bool) -> std::result::Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(StrictJson(serde_json::Value::Bool(value)))
            }

            fn visit_i64<E>(self, value: i64) -> std::result::Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(StrictJson(serde_json::Value::Number(value.into())))
            }

            fn visit_u64<E>(self, value: u64) -> std::result::Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(StrictJson(serde_json::Value::Number(value.into())))
            }

            fn visit_f64<E>(self, value: f64) -> std::result::Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                let number = serde_json::Number::from_f64(value)
                    .ok_or_else(|| E::custom("JSON number is not finite"))?;
                Ok(StrictJson(serde_json::Value::Number(number)))
            }

            fn visit_str<E>(self, value: &str) -> std::result::Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(StrictJson(serde_json::Value::String(value.to_owned())))
            }

            fn visit_string<E>(self, value: String) -> std::result::Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(StrictJson(serde_json::Value::String(value)))
            }

            fn visit_none<E>(self) -> std::result::Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(StrictJson(serde_json::Value::Null))
            }

            fn visit_unit<E>(self) -> std::result::Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(StrictJson(serde_json::Value::Null))
            }

            fn visit_seq<A>(self, mut sequence: A) -> std::result::Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let mut values = Vec::new();
                while let Some(value) = sequence.next_element::<StrictJson>()? {
                    values.push(value.0);
                }
                Ok(StrictJson(serde_json::Value::Array(values)))
            }

            fn visit_map<A>(self, mut map: A) -> std::result::Result<Self::Value, A::Error>
            where
                A: serde::de::MapAccess<'de>,
            {
                let mut values = serde_json::Map::new();
                while let Some(key) = map.next_key::<String>()? {
                    if values.contains_key(&key) {
                        return Err(serde::de::Error::custom(format!(
                            "duplicate JSON key `{key}`"
                        )));
                    }
                    let value = map.next_value::<StrictJson>()?;
                    values.insert(key, value.0);
                }
                Ok(StrictJson(serde_json::Value::Object(values)))
            }
        }

        deserializer.deserialize_any(StrictJsonVisitor)
    }
}

fn json_object<'a>(
    value: &'a serde_json::Value,
    path: &Path,
    context: &str,
) -> Result<&'a serde_json::Map<String, serde_json::Value>> {
    value.as_object().ok_or_else(|| {
        VerificationError::new(
            ErrorCode::Schema,
            format!("{} {context} must be an object", path.display()),
        )
    })
}

fn json_array<'a>(
    value: &'a serde_json::Value,
    path: &Path,
    context: &str,
) -> Result<&'a [serde_json::Value]> {
    value.as_array().map(Vec::as_slice).ok_or_else(|| {
        VerificationError::new(
            ErrorCode::Schema,
            format!("{} {context} must be an array", path.display()),
        )
    })
}

fn json_string(value: &serde_json::Value, path: &Path, context: &str) -> Result<String> {
    value.as_str().map(str::to_owned).ok_or_else(|| {
        VerificationError::new(
            ErrorCode::Schema,
            format!("{} {context} must be a string", path.display()),
        )
    })
}

fn json_u64(value: &serde_json::Value, path: &Path, context: &str) -> Result<u64> {
    value.as_u64().ok_or_else(|| {
        VerificationError::new(
            ErrorCode::Schema,
            format!("{} {context} must be an unsigned integer", path.display()),
        )
    })
}

fn required<'a>(
    object: &'a serde_json::Map<String, serde_json::Value>,
    key: &str,
    path: &Path,
) -> Result<&'a serde_json::Value> {
    object.get(key).ok_or_else(|| {
        VerificationError::new(
            ErrorCode::Schema,
            format!("{} is missing required key `{key}`", path.display()),
        )
    })
}

fn require_exact_keys(
    object: &serde_json::Map<String, serde_json::Value>,
    expected: &[&str],
    path: &Path,
    context: &str,
) -> Result<()> {
    let actual = object.keys().map(String::as_str).collect::<BTreeSet<_>>();
    let expected = expected.iter().copied().collect::<BTreeSet<_>>();
    if actual != expected {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "{} {context} keys do not match the canonical schema",
                path.display()
            ),
        ));
    }
    Ok(())
}

fn canonical_scalar(
    value: &serde_json::Value,
    path: &Path,
    context: &str,
) -> Result<CanonicalScalar> {
    match value {
        serde_json::Value::Bool(value) => Ok(CanonicalScalar::Boolean(*value)),
        serde_json::Value::Number(value) => {
            value.as_i64().map(CanonicalScalar::Integer).ok_or_else(|| {
                VerificationError::new(
                    ErrorCode::Schema,
                    format!("{} {context} integer is outside i64", path.display()),
                )
            })
        }
        serde_json::Value::Array(values) => values
            .iter()
            .enumerate()
            .map(|(index, value)| canonical_scalar(value, path, &format!("{context}[{index}]")))
            .collect::<Result<Vec<_>>>()
            .map(CanonicalScalar::Sequence),
        serde_json::Value::Object(object) if object.contains_key("#bigint") => {
            require_exact_keys(object, &["#bigint"], path, context)?;
            let bigint = json_string(required(object, "#bigint", path)?, path, context)?;
            bigint
                .parse::<i64>()
                .map(CanonicalScalar::Integer)
                .map_err(|error| {
                    VerificationError::new(
                        ErrorCode::Schema,
                        format!(
                            "{} {context} has invalid bigint `{bigint}`: {error}",
                            path.display()
                        ),
                    )
                })
        }
        serde_json::Value::Object(object) => object
            .iter()
            .map(|(name, value)| {
                canonical_scalar(value, path, &format!("{context}.{name}"))
                    .map(|value| (name.clone(), value))
            })
            .collect::<Result<BTreeMap<_, _>>>()
            .map(CanonicalScalar::Record),
        _ => Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "{} {context} is not a canonical Quint value",
                path.display()
            ),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SOURCE: &str = "fixture.jsonl";

    fn transition(id: &str, value: i64) -> CanonicalTransition {
        CanonicalTransition {
            action: CanonicalAction {
                name: "Increment".to_owned(),
                picks: CanonicalObject(BTreeMap::from([(
                    "amount".to_owned(),
                    CanonicalScalar::Integer(1),
                )])),
            },
            bounds: CanonicalBounds {
                max_samples: 200,
                max_steps: 12,
                seed: "101".to_owned(),
            },
            formal_model: "driver/DriverSystem.qnt".to_owned(),
            id: id.to_owned(),
            observable: CanonicalObject(BTreeMap::from([(
                "value".to_owned(),
                CanonicalScalar::Integer(value),
            )])),
            post: CanonicalObject(BTreeMap::from([(
                "value".to_owned(),
                CanonicalScalar::Integer(value),
            )])),
            pre: CanonicalObject(BTreeMap::from([(
                "value".to_owned(),
                CanonicalScalar::Integer(value - 1),
            )])),
            property: "bounded-transition".to_owned(),
        }
    }

    fn fixture_line(transition: &CanonicalTransition) -> String {
        format!("{}\n", serde_json::to_string(transition).unwrap())
    }

    #[test]
    fn fixture_parser_rejects_duplicate_keys() {
        let path = Path::new(SOURCE);
        let duplicate = concat!(
            "{\"action\":{\"name\":\"Increment\",\"name\":\"Reset\",\"picks\":{}},",
            "\"bounds\":{\"max_samples\":200,\"max_steps\":12,\"seed\":\"101\"},",
            "\"formal_model\":\"driver/DriverSystem.qnt\",\"id\":\"quint/DriverSystem/000\",",
            "\"observable\":{},\"post\":{\"value\":1},\"pre\":{\"value\":0},",
            "\"property\":\"bounded-transition\"}\n"
        );
        let error = parse_fixture_bytes(duplicate.as_bytes(), path).unwrap_err();
        assert_eq!(error.code(), ErrorCode::Duplicate);
    }

    #[test]
    fn fixture_parser_rejects_bad_action_and_bounds() {
        let path = Path::new(SOURCE);
        let mut invalid = transition("quint/DriverSystem/000", 1);
        invalid.action.name.clear();
        invalid.bounds.max_steps = 0;
        let error = parse_fixture_bytes(fixture_line(&invalid).as_bytes(), path).unwrap_err();
        assert_eq!(error.code(), ErrorCode::Schema);
    }

    #[test]
    fn fixture_parser_rejects_noncanonical_lines() {
        let path = Path::new(SOURCE);
        let line = concat!(
            "{\"id\":\"quint/DriverSystem/000\",\"action\":{\"name\":\"Increment\",\"picks\":{}},",
            "\"bounds\":{\"max_samples\":200,\"max_steps\":12,\"seed\":\"101\"},",
            "\"formal_model\":\"driver/DriverSystem.qnt\",\"observable\":{},",
            "\"post\":{\"value\":1},\"pre\":{\"value\":0},\"property\":\"bounded-transition\"}\n"
        );
        let error = parse_fixture_bytes(line.as_bytes(), path).unwrap_err();
        assert_eq!(error.code(), ErrorCode::Schema);
    }

    #[test]
    fn comparison_catches_missing_extra_and_reordered_transitions() {
        let first = transition("quint/DriverSystem/000", 1);
        let second = transition("quint/DriverSystem/001", 2);
        assert_eq!(
            compare_transitions(
                &[first.clone(), second.clone()],
                std::slice::from_ref(&first)
            )
            .unwrap_err()
            .code(),
            ErrorCode::SetMismatch
        );
        assert_eq!(
            compare_transitions(
                std::slice::from_ref(&first),
                &[first.clone(), second.clone()]
            )
            .unwrap_err()
            .code(),
            ErrorCode::SetMismatch
        );
        assert_eq!(
            compare_transitions(
                &[first, second],
                &[
                    transition("quint/DriverSystem/001", 2),
                    transition("quint/DriverSystem/000", 1)
                ]
            )
            .unwrap_err()
            .code(),
            ErrorCode::Transition
        );
    }

    #[test]
    fn digest_check_catches_itf_drift() {
        let error = verify_sha256(Path::new("trace.itf.json"), &"0".repeat(64), b"changed ITF")
            .unwrap_err();
        assert_eq!(error.code(), ErrorCode::Digest);
    }

    #[test]
    fn lane_registry_exposes_six_ready_lanes() {
        let lanes = ready_lane_records();
        assert_eq!(lanes.len(), 6);
        assert!(lanes.iter().all(|lane| lane.status == LaneStatus::Ready));
    }

    #[test]
    fn normalizer_preserves_named_action_and_picks() {
        let trace = concat!(
            "{\"#meta\":{\"description\":\"synthetic\",\"format\":\"ITF\",",
            "\"format-description\":\"https://apalache-mc.org/docs/adr/015adr-trace.html\",",
            "\"source\":\"driver/DriverSystem.qnt\",\"status\":\"ok\",\"timestamp\":1},",
            "\"states\":[",
            "{\"#meta\":{\"index\":0},\"mbt::actionTaken\":\"init\",\"mbt::nondetPicks\":{\"amount\":{\"tag\":\"None\",\"value\":{\"#tup\":[]}}},\"value\":{\"#bigint\":\"0\"}},",
            "{\"#meta\":{\"index\":1},\"mbt::actionTaken\":\"increment\",\"mbt::nondetPicks\":{\"amount\":{\"tag\":\"Some\",\"value\":{\"#bigint\":\"2\"}}},\"value\":{\"#bigint\":\"2\"}}],",
            "\"vars\":[\"mbt::actionTaken\",\"mbt::nondetPicks\",\"value\",\"mbt::actionTaken\",\"mbt::nondetPicks\"]}"
        );
        let run = RunRecord {
            init: "init".to_owned(),
            invariants: vec!["inv".to_owned()],
            liveness_witness: None,
            main_module: "DriverSystem".to_owned(),
            max_samples: 200,
            max_steps: 12,
            model: "driver/DriverSystem.qnt".to_owned(),
            seed: "101".to_owned(),
            step: "step".to_owned(),
            trace: "synthetic.itf.json".to_owned(),
            trace_sha256: "0".repeat(64),
        };
        let normalized =
            normalize_itf(Path::new("synthetic.itf.json"), trace.as_bytes(), &run).unwrap();
        assert_eq!(normalized.len(), 1);
        assert_eq!(normalized[0].action.name, "increment");
        assert_eq!(
            normalized[0].action.picks.0.get("amount"),
            Some(&CanonicalScalar::Integer(2))
        );
    }

    #[test]
    fn audit_g6_with_canonical_fixture() {
        let root = env::temp_dir().join(format!("bamts-formal-bridge-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();

        write_test_file(
            &root,
            "formal/toolchains.toml",
            &format!(
                "schema = \"bamti.formal-toolchains/v1\"\n\n[quint]\nversion = \"{QUINT_VERSION}\"\nnode_minimum = \"18\"\nurl = \"https://registry.npmjs.org/@informalsystems/quint/-/quint-0.32.0.tgz\"\ndigest_algorithm = \"sha512\"\ndigest = \"{QUINT_ARCHIVE_DIGEST}\"\ncommit = \"pinned\"\n"
            ),
        );
        let lock = b"{\"lockfileVersion\":3}\n";
        write_test_file(
            &root,
            "formal/quint/package-lock.json",
            std::str::from_utf8(lock).unwrap(),
        );

        let mut runs = Vec::new();
        for expected in expected_runs() {
            write_test_file(
                &root,
                &format!("formal/quint/{}", expected.model),
                "module synthetic {}\n",
            );
            let itf = synthetic_itf(expected.model);
            let hash = format!("{:x}", Sha256::digest(itf.as_bytes()));
            write_test_file(&root, expected.trace, &itf);
            runs.push(serde_json::json!({
                "invariants": ["inv"],
                "init": "init",
                "main_module": expected.main_module,
                "max_samples": 200,
                "max_steps": 12,
                "model": expected.model,
                "seed": expected.seed,
                "trace": expected.trace,
                "step": "step",
                "trace_sha256": hash,
            }));
        }
        let runs = serde_json::json!({
            "schema": "bamti.quint-runs/v1",
            "generator_backend": "quint",
            "node_version": "24.18.0",
            "package_lock_sha256": format!("{:x}", Sha256::digest(lock)),
            "runs": runs,
            "tool": {
                "archive_digest": QUINT_ARCHIVE_DIGEST,
                "archive_digest_algorithm": "sha512",
                "name": "@informalsystems/quint",
                "version": QUINT_VERSION,
            },
        });
        write_test_file(
            &root,
            "verification/formal/quint/runs.json",
            &serde_json::to_string(&runs).unwrap(),
        );
        write_test_file(
            &root,
            "verification/formal/trace-fixtures.jsonl",
            "stale fixture\n",
        );
        let fixture_path = root.join("verification/formal/trace-fixtures.jsonl");
        let (_, mut normalized) = load_normalized_transitions(&root).unwrap();
        normalized.sort_by(|left, right| left.id.cmp(&right.id));
        assert_eq!(normalized.len(), 6);
        let mut content = String::new();
        for transition in &normalized {
            validate_transition(transition, &fixture_path).unwrap();
            content.push_str(&serde_json::to_string(transition).unwrap());
            content.push('\n');
        }
        fs::write(&fixture_path, content.as_bytes()).unwrap();
        let regenerated = parse_canonical_fixture(&fixture_path).unwrap();
        assert_eq!(regenerated.len(), 6);
        assert!(regenerated.windows(2).all(|pair| pair[0].id < pair[1].id));

        let reports = audit_formal_artifacts(&root, &[Gate::G6]).unwrap();
        assert_eq!(reports.len(), 1);
        assert_eq!(reports[0].gate, Gate::G6);
        assert!(reports[0].checks > 0);
        fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn replay_canary_uses_real_quint_state_comparison() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .map(Path::to_path_buf)
            .unwrap();

        if env::var_os("BAMTS_FORMAL_CANARY_TEST_CHILD").is_some() {
            if env::var_os("BAMTS_FORMAL_CANARY_TEST_FAULTY").is_some() {
                let error = run_replay_canary_child(&root, true).unwrap_err();
                assert_eq!(error.code(), ErrorCode::Replay);
            } else {
                run_replay_canary_child(&root, false).unwrap();
            }
            return;
        }

        let executable = env::current_exe().unwrap();
        let path = prepend_path(&local_quint_bin_dir(&root).unwrap()).unwrap();
        for faulty in [false, true] {
            let mut command = Command::new(&executable);
            command
                .args([
                    "--exact",
                    "formal_bridge::tests::replay_canary_uses_real_quint_state_comparison",
                    "--nocapture",
                ])
                .current_dir(&root)
                .env("BAMTS_FORMAL_CANARY_TEST_CHILD", "1")
                .env("PATH", &path);
            if faulty {
                command.env("BAMTS_FORMAL_CANARY_TEST_FAULTY", "1");
            }
            let output = command.output().unwrap();
            assert!(
                output.status.success(),
                "canary child failed: {}",
                child_output(&output.stdout, &output.stderr)
            );
        }
    }

    fn write_test_file(root: &Path, relative: &str, contents: &str) {
        let path = root.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    fn synthetic_itf(model: &str) -> String {
        serde_json::to_string(&serde_json::json!({
            "#meta": {
                "description": "synthetic",
                "format": "ITF",
                "format-description": ITF_FORMAT_DESCRIPTION,
                "source": model,
                "status": "ok",
                "timestamp": 1,
            },
            "states": [
                {
                    "#meta": { "index": 0 },
                    "mbt::actionTaken": "init",
                    "mbt::nondetPicks": {
                        "amount": { "tag": "None", "value": { "#tup": [] } },
                    },
                    "value": { "#bigint": "0" },
                },
                {
                    "#meta": { "index": 1 },
                    "mbt::actionTaken": "increment",
                    "mbt::nondetPicks": {
                        "amount": { "tag": "Some", "value": { "#bigint": "2" } },
                    },
                    "value": { "#bigint": "2" },
                },
            ],
            "vars": [
                "mbt::actionTaken",
                "mbt::nondetPicks",
                "value",
                "mbt::actionTaken",
                "mbt::nondetPicks",
            ],
        }))
        .unwrap()
    }

    fn parse_fixture_bytes(bytes: &[u8], path: &Path) -> Result<Vec<CanonicalTransition>> {
        if bytes.is_empty() || !bytes.ends_with(b"\n") {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                "fixture must end with a newline",
            ));
        }
        let mut transitions = Vec::new();
        for raw_line in bytes.split_inclusive(|byte| *byte == b'\n') {
            let line = std::str::from_utf8(&raw_line[..raw_line.len() - 1])
                .map_err(|error| VerificationError::new(ErrorCode::Json, error.to_string()))?;
            let value = parse_strict_json_value(line, path)?;
            let transition: CanonicalTransition = serde_json::from_value(value)
                .map_err(|error| VerificationError::new(ErrorCode::Schema, error.to_string()))?;
            validate_transition(&transition, path)?;
            let canonical = serde_json::to_string(&transition)
                .map_err(|error| VerificationError::new(ErrorCode::Json, error.to_string()))?;
            if line != canonical {
                return Err(VerificationError::new(
                    ErrorCode::Schema,
                    "fixture line is not canonical JSON",
                ));
            }
            transitions.push(transition);
        }
        Ok(transitions)
    }
}
