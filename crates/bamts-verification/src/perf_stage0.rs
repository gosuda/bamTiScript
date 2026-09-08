//! Stage-0 predicate evidence harness (E5.3).
//!
//! The harness validates the registered host contract before executing the
//! five pre-registered Stage-0 predicates. A predicate is observed only after
//! its real compiler/runtime evidence provider succeeds.

use anyhow::{Context, Result};
use bamts_cli::args::{ExecutionTarget, Mode};
use bamts_cli::driver;
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::thread;
use std::time::Duration;

const EVIDENCE_SCHEMA: &str = "bamti.evidence/v1";
const LEAF: &str = "E5.3";
const RULE_NAMES: [&str; 5] = [
    "correctness",
    "integrity",
    "no-rwx",
    "event-completeness",
    "aot-no-jit-allocator",
];
const MANDATORY_EVENTS: [&str; 4] = ["sync", "micro", "timer", "timer-micro"];
const CHILD_MAP_TIMEOUT: Duration = Duration::from_secs(10);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HostConditions {
    pub governor: String,
    pub swap_total_kib: u64,
    pub cpu_affinity: String,
    pub mempolicy_mode: String,
    pub memory_nodes: Vec<u32>,
}

impl HostConditions {
    fn new() -> Result<Self> {
        Ok(Self {
            governor: capture_governor()?,
            swap_total_kib: capture_swap_total_kib()?,
            cpu_affinity: capture_cpu_affinity()?,
            mempolicy_mode: capture_mempolicy_mode(),
            memory_nodes: capture_memory_nodes()?,
        })
    }
}

#[derive(Debug, Clone, Serialize)]
struct RuleObservation {
    state: String,
    reason: String,
    observation: Option<Value>,
    decided_by: String,
    metric_key: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
struct RuleSpec {
    kind: String,
    decided_by: String,
    workload: String,
    argv: Vec<String>,
    #[serde(default)]
    baseline_argv: Vec<String>,
    #[serde(default)]
    metric_key: Option<String>,
    requires: String,
}

#[derive(Debug, Default, Clone)]
struct InputDigests {
    compiler_rules: Option<String>,
    catalog_inputs: Option<String>,
    baseline: Option<String>,
}

trait EvidenceProvider {
    fn observe(&mut self, name: &str, rule: &RuleSpec) -> Result<Value>;
}

struct RealEvidenceProvider<'a> {
    root: &'a Path,
}

impl EvidenceProvider for RealEvidenceProvider<'_> {
    fn observe(&mut self, name: &str, rule: &RuleSpec) -> Result<Value> {
        anyhow::ensure!(rule.kind == "predicate", "stage0.{name} is not a predicate");
        anyhow::ensure!(
            rule.workload == "corpus/cases/valita.ts"
                || rule.workload == "corpus/cases/event-loop.ts",
            "stage0.{name} names an unregistered workload"
        );
        match name {
            "correctness" => self.correctness(rule),
            "integrity" => self.integrity(rule),
            "no-rwx" => self.no_rwx(rule),
            "event-completeness" => self.event_completeness(rule),
            "aot-no-jit-allocator" => self.aot_no_jit_allocator(rule),
            _ => anyhow::bail!("unknown Stage-0 rule {name}"),
        }
    }
}

impl RealEvidenceProvider<'_> {
    fn workload(&self, rule: &RuleSpec) -> PathBuf {
        self.root.join(&rule.workload)
    }

    fn execute(&self, rule: &RuleSpec, mode: ExecutionTarget) -> Result<driver::CommandOutcome> {
        let args = crate::corpus::cli_args(Mode::Run, mode, self.workload(rule), None, false, &[])?;
        let outcome = driver::execute(&args).context("executing registered Stage-0 workload")?;
        anyhow::ensure!(
            outcome.exit_code == 0,
            "workload exited {}",
            outcome.exit_code
        );
        anyhow::ensure!(
            outcome.truncation.is_none(),
            "workload output was truncated"
        );
        Ok(outcome)
    }

    fn correctness(&self, rule: &RuleSpec) -> Result<Value> {
        anyhow::ensure!(
            rule.decided_by == "differential",
            "wrong correctness provider"
        );
        anyhow::ensure!(rule.argv == ["-r", "--jit"], "wrong JIT argv");
        anyhow::ensure!(rule.baseline_argv == ["-r", "--aot"], "wrong AOT argv");
        let jit = self.execute(rule, ExecutionTarget::Jit)?;
        let aot = self.execute(rule, ExecutionTarget::Aot)?;
        anyhow::ensure!(jit.stdout == aot.stdout, "JIT/AOT stdout mismatch");
        anyhow::ensure!(jit.exit_code == aot.exit_code, "JIT/AOT exit-code mismatch");
        Ok(json!({
            "jit_exit_code": jit.exit_code,
            "aot_exit_code": aot.exit_code,
            "stdout_sha256": sha256_bytes(&jit.stdout),
        }))
    }

    fn integrity(&self, rule: &RuleSpec) -> Result<Value> {
        anyhow::ensure!(
            rule.decided_by == "reproducible-artifact",
            "wrong integrity provider"
        );
        anyhow::ensure!(rule.argv == ["-c", "--aot"], "wrong integrity argv");
        let artifacts = crate::suite::TempDir::new("stage0-integrity")?;
        let first_path = artifacts.path().join("first.o");
        let second_path = artifacts.path().join("second.o");
        for destination in [&first_path, &second_path] {
            let args = crate::corpus::cli_args(
                Mode::Compile,
                ExecutionTarget::Aot,
                self.workload(rule),
                Some(destination),
                false,
                &[],
            )?;
            let outcome = driver::execute(&args).context("emitting registered AOT artifact")?;
            anyhow::ensure!(
                outcome.exit_code == 0,
                "AOT compilation exited {}",
                outcome.exit_code
            );
            anyhow::ensure!(
                outcome.truncation.is_none(),
                "AOT compilation output was truncated"
            );
        }
        let first = fs::read(&first_path)?;
        let second = fs::read(&second_path)?;
        anyhow::ensure!(
            !first.is_empty(),
            "AOT compilation emitted an empty artifact"
        );
        anyhow::ensure!(first == second, "independent AOT artifacts differ");
        Ok(json!({
            "artifact_sha256": sha256_bytes(&first),
            "artifact_bytes": first.len(),
        }))
    }

    fn no_rwx(&self, rule: &RuleSpec) -> Result<Value> {
        anyhow::ensure!(rule.decided_by == "process-maps", "wrong no-rwx provider");
        anyhow::ensure!(rule.argv == ["-r", "--jit"], "wrong no-rwx argv");
        let executable = bamts::compile_source_file(self.workload(rule))?;
        let (_program, telemetry) = bamts_codegen::compile_jit_with_telemetry(executable.wire())?;
        let maps = process_maps()?;
        anyhow::ensure!(!maps.is_empty(), "no address-space mappings sampled");
        anyhow::ensure!(
            maps.iter()
                .all(|mapping| !mapping.permissions.contains("rwx")),
            "an RWX address-space mapping was observed"
        );
        anyhow::ensure!(
            telemetry.code_bytes > 0,
            "JIT produced no executable code mapping"
        );
        Ok(json!({
            "sampled_mappings": maps.len(),
            "code_bytes": telemetry.code_bytes,
            "readonly_bytes": telemetry.readonly_bytes,
            "readwrite_bytes": telemetry.readwrite_bytes,
        }))
    }

    fn event_completeness(&self, rule: &RuleSpec) -> Result<Value> {
        anyhow::ensure!(rule.decided_by == "event-stream", "wrong event provider");
        anyhow::ensure!(rule.argv == ["-r", "--jit", "--json"], "wrong event argv");
        anyhow::ensure!(
            rule.metric_key.as_deref() == Some("events"),
            "wrong event metric key"
        );
        let jit = self.execute(rule, ExecutionTarget::Jit)?;
        let aot = self.execute(rule, ExecutionTarget::Aot)?;
        anyhow::ensure!(jit.stdout == aot.stdout, "JIT/AOT event-stream mismatch");
        let events = validate_event_stream(&jit.stdout)?;
        Ok(json!({"events": events, "event_count": events.len()}))
    }

    fn aot_no_jit_allocator(&self, rule: &RuleSpec) -> Result<Value> {
        anyhow::ensure!(
            rule.decided_by == "process-maps",
            "wrong AOT allocator provider"
        );
        anyhow::ensure!(rule.argv == ["-r", "--aot"], "wrong AOT argv");
        let outcome = self.execute(rule, ExecutionTarget::Aot)?;
        let sample = capture_aot_child_maps(self.root, &self.workload(rule))?;
        anyhow::ensure!(
            sample
                .mappings
                .iter()
                .all(|mapping| !mapping.permissions.contains("rwx")),
            "an RWX mapping was observed in the live AOT child"
        );
        let anonymous = anonymous_executable_mappings(&sample.mappings);
        anyhow::ensure!(
            anonymous.is_empty(),
            "live AOT child used anonymous executable mappings: {anonymous:?}"
        );
        Ok(json!({
            "exit_code": outcome.exit_code,
            "sampled_mappings": sample.mappings.len(),
            "process_map_samples": sample.samples,
            "aot_executable_mappings": sample.executable_mappings,
            "anonymous_executable_mappings": anonymous.len(),
        }))
    }
}

#[derive(Debug, Clone)]
struct ProcessMapping {
    identity: String,
    permissions: String,
    pathname: Option<String>,
}

pub fn run() -> Value {
    let root = match repo_root() {
        Ok(root) => root,
        Err(error) => {
            return error_receipt(
                "MEASUREMENT_UNAVAILABLE",
                &error.to_string(),
                &InputDigests::default(),
            );
        }
    };
    let mut provider = RealEvidenceProvider { root: &root };
    evaluate_with(&root, HostConditions::new, &mut provider)
}

fn evaluate_with(
    root: &Path,
    mut capture: impl FnMut() -> Result<HostConditions>,
    provider: &mut impl EvidenceProvider,
) -> Value {
    let rules_path = root.join("bench/compiler-rules.toml");
    let catalog_path = root.join("verification/catalog-inputs.json");
    let baseline_path = root.join("perf/baselines/s0.json");
    let mut digests = InputDigests::default();

    let rules_bytes = match read_and_digest(&rules_path, &mut digests.compiler_rules) {
        Ok(bytes) => bytes,
        Err(error) => {
            return error_receipt("MEASUREMENT_UNAVAILABLE", &error.to_string(), &digests);
        }
    };
    let catalog_bytes = match read_and_digest(&catalog_path, &mut digests.catalog_inputs) {
        Ok(bytes) => bytes,
        Err(error) => {
            return error_receipt("MEASUREMENT_UNAVAILABLE", &error.to_string(), &digests);
        }
    };
    let baseline_bytes = match read_and_digest(&baseline_path, &mut digests.baseline) {
        Ok(bytes) => bytes,
        Err(error) => {
            return error_receipt("MEASUREMENT_UNAVAILABLE", &error.to_string(), &digests);
        }
    };

    let rules = match parse_stage0_rules(&rules_bytes) {
        Ok(rules) => rules,
        Err(error) => {
            return error_receipt("MEASUREMENT_UNAVAILABLE", &error.to_string(), &digests);
        }
    };
    if let Err(error) = validate_catalog(&catalog_bytes) {
        return error_receipt("MEASUREMENT_UNAVAILABLE", &error.to_string(), &digests);
    }
    let baseline = match load_baseline_bytes(&baseline_path, &baseline_bytes) {
        Ok(baseline) => baseline,
        Err(error) => {
            return error_receipt("MEASUREMENT_UNAVAILABLE", &error.to_string(), &digests);
        }
    };
    let before = match capture() {
        Ok(before) => before,
        Err(error) => {
            return error_receipt(
                "MEASUREMENT_UNAVAILABLE",
                &format!("capturing initial host conditions: {error}"),
                &digests,
            );
        }
    };
    let mut condition_failures = validate_conditions(&baseline, &before);
    thread::sleep(Duration::from_millis(1));
    let after = capture();
    match &after {
        Ok(after) if condition_failures.is_empty() && before != *after => {
            condition_failures.push("host conditions drifted between before/after capture".into());
        }
        Err(error) if condition_failures.is_empty() => {
            return error_receipt(
                "MEASUREMENT_UNAVAILABLE",
                &format!("capturing final host conditions: {error}"),
                &digests,
            );
        }
        Err(error) => condition_failures.push(format!("final host capture failed: {error}")),
        _ => {}
    }

    let mut observations = Vec::with_capacity(RULE_NAMES.len());
    for name in RULE_NAMES {
        let spec = &rules[name];
        let observation = if condition_failures.is_empty() {
            match provider.observe(name, spec) {
                Ok(value) => RuleObservation {
                    state: "PASS".into(),
                    reason: spec.requires.clone(),
                    observation: Some(value),
                    decided_by: spec.decided_by.clone(),
                    metric_key: spec
                        .metric_key
                        .clone()
                        .or_else(|| Some(format!("stage0.{name}"))),
                },
                Err(error) => RuleObservation {
                    state: "MEASUREMENT_UNAVAILABLE".into(),
                    reason: error.to_string(),
                    observation: None,
                    decided_by: spec.decided_by.clone(),
                    metric_key: spec
                        .metric_key
                        .clone()
                        .or_else(|| Some(format!("stage0.{name}"))),
                },
            }
        } else {
            RuleObservation {
                state: "INVALID_CONDITIONS".into(),
                reason: condition_failures.join("; "),
                observation: None,
                decided_by: "host-condition contract".into(),
                metric_key: None,
            }
        };
        observations.push((name.to_owned(), observation));
    }

    let state = aggregate_state(&condition_failures, &observations);
    let reason = if condition_failures.is_empty() {
        observations
            .iter()
            .filter(|(_, observation)| observation.state != "PASS")
            .map(|(name, observation)| format!("stage0.{name}: {}", observation.reason))
            .collect::<Vec<_>>()
            .join("; ")
    } else {
        condition_failures.join("; ")
    };
    let rules = observations
        .into_iter()
        .map(|(name, observation)| {
            (
                name,
                serde_json::to_value(observation).expect("RuleObservation serializes"),
            )
        })
        .collect();
    receipt(
        state,
        &reason,
        &digests,
        Some(&before),
        after.as_ref().ok(),
        Some(&baseline),
        Some(rules),
    )
}

fn aggregate_state(
    condition_failures: &[String],
    rules: &[(String, RuleObservation)],
) -> &'static str {
    if !condition_failures.is_empty() {
        "INVALID_CONDITIONS"
    } else if rules.len() != RULE_NAMES.len()
        || rules
            .iter()
            .any(|(_, rule)| rule.state != "PASS" || rule.observation.is_none())
    {
        "MEASUREMENT_UNAVAILABLE"
    } else {
        "ACCEPTED"
    }
}

const CRATE_MANIFEST_DIR: &str = env!("CARGO_MANIFEST_DIR");

fn repo_root() -> Result<PathBuf> {
    let crate_dir = Path::new(CRATE_MANIFEST_DIR);
    let root = crate_dir
        .parent()
        .context("no package parent")?
        .parent()
        .context("no workspace parent")?;
    for required in [
        "bench/compiler-rules.toml",
        "verification/catalog-inputs.json",
        "perf/baselines/s0.json",
    ] {
        anyhow::ensure!(
            root.join(required).is_file(),
            "workspace root {} lacks {required}",
            root.display()
        );
    }
    Ok(root.to_path_buf())
}

fn read_and_digest(path: &Path, slot: &mut Option<String>) -> Result<Vec<u8>> {
    let bytes = fs::read(path).with_context(|| format!("reading {}", path.display()))?;
    *slot = Some(sha256_bytes(&bytes));
    Ok(bytes)
}

fn sha256_bytes(bytes: &[u8]) -> String {
    let hash = Sha256::digest(bytes);
    hash.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn parse_stage0_rules(bytes: &[u8]) -> Result<BTreeMap<String, RuleSpec>> {
    let document: toml::Value = toml::from_str(std::str::from_utf8(bytes)?)?;
    let table = document
        .get("rule")
        .and_then(toml::Value::as_table)
        .context("compiler rules lacks [rule] table")?;
    let mut rules = BTreeMap::new();
    for name in RULE_NAMES {
        let key = format!("stage0.{name}");
        let value = table
            .get(&key)
            .with_context(|| format!("compiler rules lacks {key}"))?;
        rules.insert(name.to_owned(), value.clone().try_into()?);
    }
    let actual = table
        .keys()
        .filter(|key| key.starts_with("stage0."))
        .cloned()
        .collect::<BTreeSet<_>>();
    let expected = RULE_NAMES
        .iter()
        .map(|name| format!("stage0.{name}"))
        .collect::<BTreeSet<_>>();
    anyhow::ensure!(
        actual == expected,
        "Stage-0 rule inventory differs from the closed five-rule contract"
    );
    Ok(rules)
}

fn validate_catalog(bytes: &[u8]) -> Result<()> {
    let value: Value = serde_json::from_slice(bytes)?;
    let identifiers = value
        .get("catalogs")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .find(|catalog| catalog.get("id").and_then(Value::as_str) == Some("benchmarks"))
        .and_then(|catalog| catalog.get("identifiers"))
        .and_then(Value::as_array)
        .context("catalog inputs lacks benchmarks identifiers")?;
    let mut stage0 = BTreeSet::new();
    for identifier in identifiers {
        let identifier = identifier
            .as_str()
            .context("benchmarks catalog identifier is not a string")?;
        if identifier.starts_with("stage0.") {
            anyhow::ensure!(
                stage0.insert(identifier.to_owned()),
                "duplicate Stage-0 catalog identifier {identifier}"
            );
        }
    }
    let expected = RULE_NAMES
        .iter()
        .map(|name| format!("stage0.{name}"))
        .collect::<BTreeSet<_>>();
    anyhow::ensure!(
        stage0 == expected,
        "benchmarks Stage-0 identifier set differs from the closed five-rule contract"
    );
    Ok(())
}

fn load_baseline_bytes(path: &Path, bytes: &[u8]) -> Result<HostConditions> {
    let value: Value = serde_json::from_slice(bytes)?;
    let cond = value
        .get("conditions_expected")
        .or_else(|| value.get("conditions"))
        .cloned()
        .unwrap_or_else(|| value.clone());
    let str_field = |name: &str| -> Result<String> {
        cond.get(name)
            .and_then(Value::as_str)
            .map(str::to_owned)
            .with_context(|| format!("baseline {} lacks string field {name}", path.display()))
    };
    let memory_nodes = match cond.get("memory_nodes") {
        Some(Value::Array(items)) => items
            .iter()
            .map(|value| {
                let node = value.as_u64().context("memory_nodes entry is not a u64")?;
                u32::try_from(node).context("memory_nodes entry exceeds u32::MAX")
            })
            .collect::<Result<Vec<_>>>()?,
        Some(Value::String(nodes)) => parse_range_list(nodes)?,
        _ => anyhow::bail!("baseline {} lacks memory_nodes", path.display()),
    };
    Ok(HostConditions {
        governor: str_field("governor")?,
        swap_total_kib: cond
            .get("swap_total_kib")
            .and_then(Value::as_u64)
            .with_context(|| format!("baseline {} lacks swap_total_kib", path.display()))?,
        cpu_affinity: str_field("cpu_affinity")?,
        mempolicy_mode: str_field("mempolicy_mode").or_else(|_| str_field("memory_policy"))?,
        memory_nodes,
    })
}

fn validate_conditions(expected: &HostConditions, actual: &HostConditions) -> Vec<String> {
    let mut failures = Vec::new();
    if expected.governor != actual.governor {
        failures.push(format!(
            "governor: expected {}, got {}",
            expected.governor, actual.governor
        ));
    }
    if expected.swap_total_kib != actual.swap_total_kib {
        failures.push(format!(
            "swap_total_kib: expected {}, got {}",
            expected.swap_total_kib, actual.swap_total_kib
        ));
    }
    if expected.cpu_affinity != actual.cpu_affinity {
        failures.push(format!(
            "cpu_affinity: expected {}, got {}",
            expected.cpu_affinity, actual.cpu_affinity
        ));
    }
    if expected.mempolicy_mode != actual.mempolicy_mode {
        failures.push(format!(
            "mempolicy_mode: expected {}, got {}",
            expected.mempolicy_mode, actual.mempolicy_mode
        ));
    }
    if expected.memory_nodes != actual.memory_nodes {
        failures.push(format!(
            "memory_nodes: expected {:?}, got {:?}",
            expected.memory_nodes, actual.memory_nodes
        ));
    }
    failures
}

fn receipt(
    state: &str,
    reason: &str,
    digests: &InputDigests,
    before: Option<&HostConditions>,
    after: Option<&HostConditions>,
    baseline: Option<&HostConditions>,
    rules: Option<Map<String, Value>>,
) -> Value {
    let mut receipt = Map::new();
    receipt.insert("schema".into(), EVIDENCE_SCHEMA.into());
    receipt.insert("leaf".into(), LEAF.into());
    receipt.insert("state".into(), state.into());
    receipt.insert("reason".into(), reason.into());
    if let Some(digest) = &digests.compiler_rules {
        receipt.insert("compiler_rules_digest".into(), digest.clone().into());
    }
    if let Some(digest) = &digests.catalog_inputs {
        receipt.insert("catalog_inputs_digest".into(), digest.clone().into());
    }
    if let Some(digest) = &digests.baseline {
        receipt.insert("baseline_digest".into(), digest.clone().into());
    }
    if let Some(value) = before {
        receipt.insert(
            "conditions_before".into(),
            serde_json::to_value(value).expect("conditions serialize"),
        );
    }
    if let Some(value) = after {
        receipt.insert(
            "conditions_after".into(),
            serde_json::to_value(value).expect("conditions serialize"),
        );
    }
    if let Some(value) = baseline {
        receipt.insert(
            "baseline".into(),
            serde_json::to_value(value).expect("conditions serialize"),
        );
    }
    if let Some(value) = rules {
        receipt.insert("rules".into(), Value::Object(value));
    }
    Value::Object(receipt)
}

fn error_receipt(state: &str, reason: &str, digests: &InputDigests) -> Value {
    receipt(state, reason, digests, None, None, None, None)
}

fn validate_event_stream(stdout: &[u8]) -> Result<Vec<String>> {
    let text = std::str::from_utf8(stdout).context("event stream is not UTF-8")?;
    let events = text.lines().map(str::to_owned).collect::<Vec<_>>();
    anyhow::ensure!(
        events.iter().map(String::as_str).eq(MANDATORY_EVENTS),
        "event stream must equal {:?}, got {:?}",
        MANDATORY_EVENTS,
        events
    );
    Ok(events)
}

#[derive(Debug)]
struct ChildMapSample {
    mappings: Vec<ProcessMapping>,
    executable_mappings: usize,
    samples: usize,
}

fn capture_aot_child_maps(root: &Path, workload: &Path) -> Result<ChildMapSample> {
    let artifacts = crate::suite::TempDir::new("stage0-aot-child")?;
    let executable = artifacts.path().join("stage0-aot-child");
    let args = crate::corpus::cli_args(
        Mode::Compile,
        ExecutionTarget::Aot,
        workload.to_owned(),
        Some(&executable),
        false,
        &[],
    )?;
    let compile = driver::execute(&args).context("building controlled AOT child")?;
    anyhow::ensure!(
        compile.exit_code == 0,
        "AOT child compilation exited {}",
        compile.exit_code
    );
    anyhow::ensure!(
        compile.truncation.is_none(),
        "AOT child compilation output was truncated"
    );
    let executable =
        fs::canonicalize(&executable).context("canonicalizing controlled AOT child")?;
    let launch_token = format!("stage0-{}", std::process::id());
    let child = Command::new(&executable)
        .current_dir(root)
        .env(bamts_node::AOT_ENTRYPOINT_ENV, workload)
        .env(bamts_node::AOT_LAUNCH_TOKEN_ENV, &launch_token)
        .arg(&launch_token)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .context("spawning controlled AOT child")?;
    sample_child_maps(child, &executable, CHILD_MAP_TIMEOUT)
}

fn sample_child_maps(child: Child, executable: &Path, timeout: Duration) -> Result<ChildMapSample> {
    sample_child_maps_with_observer(child, executable, timeout, |_, _| Ok(()))
}

fn sample_child_maps_with_observer(
    mut child: Child,
    executable: &Path,
    timeout: Duration,
    mut observed: impl FnMut(&mut Child, &[ProcessMapping]) -> Result<()>,
) -> Result<ChildMapSample> {
    let stdout = child
        .stdout
        .take()
        .context("controlled child stdout was not piped")?;
    let stderr = child
        .stderr
        .take()
        .context("controlled child stderr was not piped")?;
    let stdout_reader = spawn_pipe_reader(stdout);
    let stderr_reader = spawn_pipe_reader(stderr);
    let deadline = std::time::Instant::now() + timeout;
    let mut union = BTreeMap::new();
    let mut samples = 0;

    let outcome = loop {
        match child.try_wait().context("polling controlled child") {
            Ok(Some(status)) => break Ok(status),
            Ok(None) => {}
            Err(error) => break Err(error),
        }
        let mappings = match process_maps_for(child.id()) {
            Ok(mappings) => mappings,
            Err(error) => match child
                .try_wait()
                .context("checking child after map-read failure")
            {
                Ok(Some(status)) => break Ok(status),
                Ok(None) => break Err(error.context("live child process maps became unreadable")),
                Err(wait_error) => break Err(wait_error),
            },
        };
        samples += 1;
        let rwx = mappings
            .iter()
            .filter(|mapping| mapping.permissions.contains("rwx"))
            .map(|mapping| &mapping.identity)
            .collect::<Vec<_>>();
        if !rwx.is_empty() {
            break Err(anyhow::anyhow!(
                "RWX mappings were observed in the live child: {rwx:?}"
            ));
        }
        let anonymous = anonymous_executable_mappings(&mappings);
        if !anonymous.is_empty() {
            break Err(anyhow::anyhow!(
                "live child used anonymous executable mappings: {anonymous:?}"
            ));
        }
        // Coordinate fixtures only after this snapshot passes the real mapping checks.
        if let Err(error) = observed(&mut child, &mappings) {
            break Err(error);
        }
        for mapping in mappings {
            union.entry(mapping.identity.clone()).or_insert(mapping);
        }
        if std::time::Instant::now() >= deadline {
            break Err(anyhow::anyhow!(
                "controlled child did not exit before timeout"
            ));
        }
        thread::sleep(Duration::from_millis(1));
    };

    if outcome.is_err() {
        let _ = child.kill();
        let _ = child.wait();
    }
    let stdout = join_pipe_reader(stdout_reader).context("draining controlled child stdout")?;
    let stderr = join_pipe_reader(stderr_reader).context("draining controlled child stderr")?;
    let status = outcome?;
    anyhow::ensure!(
        status.success(),
        "controlled child exited {status}: {}",
        String::from_utf8_lossy(&stderr)
    );
    let mappings = union.into_values().collect::<Vec<_>>();
    let executable_mappings = mappings
        .iter()
        .filter(|mapping| {
            mapping
                .pathname
                .as_deref()
                .is_some_and(|path| Path::new(path) == executable)
        })
        .count();
    anyhow::ensure!(
        executable_mappings > 0,
        "emitted executable mapping was never observed in the live child"
    );
    let _ = stdout;
    Ok(ChildMapSample {
        mappings,
        executable_mappings,
        samples,
    })
}

fn spawn_pipe_reader(
    mut pipe: impl Read + Send + 'static,
) -> thread::JoinHandle<io::Result<Vec<u8>>> {
    thread::spawn(move || {
        let mut bytes = Vec::new();
        pipe.read_to_end(&mut bytes)?;
        Ok(bytes)
    })
}

fn join_pipe_reader(reader: thread::JoinHandle<io::Result<Vec<u8>>>) -> io::Result<Vec<u8>> {
    reader
        .join()
        .map_err(|_| io::Error::other("controlled child pipe reader panicked"))?
}

fn process_maps_for(pid: u32) -> Result<Vec<ProcessMapping>> {
    let text = fs::read_to_string(format!("/proc/{pid}/maps"))
        .with_context(|| format!("reading /proc/{pid}/maps"))?;
    parse_process_maps(&text)
}

fn process_maps() -> Result<Vec<ProcessMapping>> {
    process_maps_for(std::process::id())
}

fn parse_process_maps(text: &str) -> Result<Vec<ProcessMapping>> {
    text.lines()
        .map(|line| {
            let mut fields = line.split_whitespace();
            let range = fields.next().context("mapping lacks range")?;
            let permissions = fields
                .next()
                .context("mapping lacks permissions")?
                .to_owned();
            let offset = fields.next().context("mapping lacks offset")?;
            let device = fields.next().context("mapping lacks device")?;
            let inode = fields.next().context("mapping lacks inode")?;
            let pathname = fields.next().map(str::to_owned);
            Ok(ProcessMapping {
                identity: format!(
                    "{range} {offset} {device} {inode} {}",
                    pathname.as_deref().unwrap_or("")
                ),
                permissions,
                pathname,
            })
        })
        .collect()
}

fn anonymous_executable_mappings(maps: &[ProcessMapping]) -> BTreeSet<String> {
    maps.iter()
        .filter(|mapping| mapping.permissions.contains('x') && mapping.pathname.is_none())
        .map(|mapping| mapping.identity.clone())
        .collect()
}

fn capture_governor() -> Result<String> {
    Ok(
        fs::read_to_string("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor")?
            .trim()
            .to_owned(),
    )
}
fn capture_swap_total_kib() -> Result<u64> {
    let text = fs::read_to_string("/proc/meminfo")?;
    text.lines()
        .find_map(|line| line.strip_prefix("SwapTotal:"))
        .and_then(|rest| rest.split_whitespace().next())
        .context("SwapTotal not found")?
        .parse()
        .context("parsing SwapTotal")
}
fn capture_cpu_affinity() -> Result<String> {
    let text = fs::read_to_string("/proc/self/status")?;
    text.lines()
        .find_map(|line| line.strip_prefix("Cpus_allowed_list:"))
        .map(str::trim)
        .map(str::to_owned)
        .context("Cpus_allowed_list not found")
}
fn capture_mempolicy_mode() -> String {
    Command::new("numactl")
        .arg("--show")
        .output()
        .ok()
        .filter(|output| output.status.success())
        .and_then(|output| String::from_utf8(output.stdout).ok())
        .and_then(|text| {
            text.lines().find_map(|line| {
                line.strip_prefix("policy:")
                    .map(str::trim)
                    .map(str::to_owned)
            })
        })
        .unwrap_or_else(|| "unavailable".into())
}
fn capture_memory_nodes() -> Result<Vec<u32>> {
    if let Ok(output) = Command::new("numactl").arg("--show").output()
        && output.status.success()
        && let Ok(text) = String::from_utf8(output.stdout)
        && let Some(nodes) = text.lines().find_map(|line| line.strip_prefix("nodebind:"))
    {
        return parse_whitespace_list(nodes.trim());
    }
    let text = fs::read_to_string("/proc/self/status")?;
    text.lines()
        .find_map(|line| line.strip_prefix("Mems_allowed_list:"))
        .map(str::trim)
        .context("Mems_allowed_list not found")
        .and_then(parse_range_list)
}
fn parse_range_list(text: &str) -> Result<Vec<u32>> {
    anyhow::ensure!(!text.trim().is_empty(), "memory-node list is empty");
    let mut nodes = Vec::new();
    for token in text.split(',').map(str::trim) {
        anyhow::ensure!(
            !token.is_empty(),
            "memory-node list contains an empty token"
        );
        if let Some((start, end)) = token.split_once('-') {
            let start: u32 = start.parse()?;
            let end: u32 = end.parse()?;
            anyhow::ensure!(start <= end, "reversed memory-node range: {token}");
            nodes.extend(start..=end);
        } else {
            nodes.push(token.parse()?);
        }
    }
    Ok(nodes)
}
fn parse_whitespace_list(text: &str) -> Result<Vec<u32>> {
    text.split_whitespace()
        .map(|token| token.parse().map_err(Into::into))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::suite::TempDir;
    use std::io::Write;

    #[derive(Default)]
    struct CheckedProvider {
        fail: Option<&'static str>,
    }
    impl EvidenceProvider for CheckedProvider {
        fn observe(&mut self, name: &str, rule: &RuleSpec) -> Result<Value> {
            anyhow::ensure!(self.fail != Some(name), "mutated evidence rejected");
            Ok(json!({"provider": rule.decided_by, "checked": true}))
        }
    }

    fn conditions() -> HostConditions {
        HostConditions {
            governor: "powersave".into(),
            swap_total_kib: 0,
            cpu_affinity: "0".into(),
            mempolicy_mode: "bind".into(),
            memory_nodes: vec![0],
        }
    }

    fn fixture() -> TempDir {
        let temp = TempDir::new("stage0-evidence").unwrap();
        for directory in ["bench", "verification", "perf/baselines", "corpus/cases"] {
            fs::create_dir_all(temp.path().join(directory)).unwrap();
        }
        fs::write(temp.path().join("verification/catalog-inputs.json"), serde_json::to_vec(&json!({"catalogs":[{"id":"benchmarks","identifiers":RULE_NAMES.map(|name| format!("stage0.{name}"))}]})).unwrap()).unwrap();
        fs::write(
            temp.path().join("perf/baselines/s0.json"),
            serde_json::to_vec(&json!({"conditions_expected":conditions()})).unwrap(),
        )
        .unwrap();
        fs::write(
            temp.path().join("bench/compiler-rules.toml"),
            r#"
[rule."stage0.correctness"]
kind="predicate"
decided_by="differential"
workload="corpus/cases/valita.ts"
argv=["-r","--jit"]
baseline_argv=["-r","--aot"]
requires="both targets completed"
[rule."stage0.integrity"]
kind="predicate"
decided_by="reproducible-artifact"
workload="corpus/cases/valita.ts"
argv=["-c","--aot"]
requires="artifacts identical"
[rule."stage0.no-rwx"]
kind="predicate"
decided_by="process-maps"
workload="corpus/cases/valita.ts"
argv=["-r","--jit"]
requires="live map captured"
[rule."stage0.event-completeness"]
kind="predicate"
decided_by="event-stream"
workload="corpus/cases/event-loop.ts"
argv=["-r","--jit","--json"]
metric_key="events"
requires="ordered events emitted"
[rule."stage0.aot-no-jit-allocator"]
kind="predicate"
decided_by="process-maps"
workload="corpus/cases/valita.ts"
argv=["-r","--aot"]
requires="live map captured"
"#,
        )
        .unwrap();
        fs::write(
            temp.path().join("corpus/cases/valita.ts"),
            "setTimeout(() => process.stdout.write(\"ok\\n\"), 100);\n",
        )
        .unwrap();
        fs::write(
            temp.path().join("corpus/cases/event-loop.ts"),
            "process.stdout.write(\"sync\\nmicro\\ntimer\\ntimer-micro\\n\");\n",
        )
        .unwrap();
        temp
    }

    #[test]
    fn accepted_receipt_requires_checked_evidence_for_all_five_rules() {
        let temp = fixture();
        let current = conditions();
        let mut provider = CheckedProvider::default();
        let receipt = evaluate_with(temp.path(), || Ok(current.clone()), &mut provider);
        assert_eq!(receipt["state"], "ACCEPTED", "{}", receipt["reason"]);
        for name in RULE_NAMES {
            assert_eq!(receipt["rules"][name]["state"], "PASS");
            assert_eq!(receipt["rules"][name]["observation"]["checked"], true);
        }
    }

    #[test]
    fn initial_mismatch_precedes_failed_final_capture() {
        let temp = fixture();
        let mut mismatched = conditions();
        mismatched.governor = "performance".into();
        let mut captures =
            vec![Ok(mismatched), Err(anyhow::anyhow!("capture unavailable"))].into_iter();
        let mut provider = CheckedProvider::default();
        let receipt = evaluate_with(temp.path(), || captures.next().unwrap(), &mut provider);
        assert_eq!(receipt["state"], "INVALID_CONDITIONS");
        assert!(
            receipt["reason"]
                .as_str()
                .unwrap()
                .contains("capture unavailable")
        );
    }

    #[test]
    fn malformed_baseline_retains_every_computed_input_digest() {
        let temp = fixture();
        fs::write(temp.path().join("perf/baselines/s0.json"), b"{ malformed").unwrap();
        let mut provider = CheckedProvider::default();
        let receipt = evaluate_with(temp.path(), || Ok(conditions()), &mut provider);
        assert_eq!(receipt["state"], "MEASUREMENT_UNAVAILABLE");
        for key in [
            "compiler_rules_digest",
            "catalog_inputs_digest",
            "baseline_digest",
        ] {
            assert_eq!(receipt[key].as_str().unwrap().len(), 64);
        }
    }

    #[test]
    fn mutated_rule_evidence_cannot_accept() {
        let temp = fixture();
        let current = conditions();
        let mut provider = CheckedProvider {
            fail: Some("no-rwx"),
        };
        let receipt = evaluate_with(temp.path(), || Ok(current.clone()), &mut provider);
        assert_eq!(receipt["state"], "MEASUREMENT_UNAVAILABLE");
        assert_eq!(
            receipt["rules"]["no-rwx"]["state"],
            "MEASUREMENT_UNAVAILABLE"
        );
        assert!(receipt["rules"]["no-rwx"]["observation"].is_null());
    }

    #[test]
    fn event_stream_rejects_missing_reordered_duplicate_and_extra_events() {
        assert_eq!(
            validate_event_stream(b"sync\nmicro\ntimer\ntimer-micro\n").unwrap(),
            MANDATORY_EVENTS.map(str::to_owned)
        );
        for mutated in [
            b"sync\nmicro\ntimer\n".as_slice(),
            b"micro\nsync\ntimer\ntimer-micro\n".as_slice(),
            b"sync\nmicro\nmicro\ntimer\ntimer-micro\n".as_slice(),
            b"sync\nmicro\ntimer\ntimer-micro\nextra\n".as_slice(),
        ] {
            assert!(
                validate_event_stream(mutated).is_err(),
                "accepted {:?}",
                String::from_utf8_lossy(mutated)
            );
        }
    }

    #[test]
    fn catalog_requires_exact_typed_stage0_identifier_set() {
        let identifiers = RULE_NAMES.map(|name| json!(format!("stage0.{name}")));
        let catalog = |identifiers: Vec<Value>| {
            serde_json::to_vec(&json!({
                "catalogs": [{"id": "benchmarks", "identifiers": identifiers}]
            }))
            .unwrap()
        };
        assert!(validate_catalog(&catalog(identifiers.to_vec())).is_ok());

        let mut extra = identifiers.to_vec();
        extra.push(json!("stage0.unregistered"));
        assert!(validate_catalog(&catalog(extra)).is_err());

        let mut missing = identifiers.to_vec();
        missing.pop();
        assert!(validate_catalog(&catalog(missing)).is_err());

        let mut malformed = identifiers.to_vec();
        malformed.push(json!(42));
        assert!(validate_catalog(&catalog(malformed)).is_err());
        let mut duplicate = identifiers.to_vec();
        duplicate.push(identifiers[0].clone());
        assert!(validate_catalog(&catalog(duplicate)).is_err());
    }

    #[test]
    fn continuous_sampler_accepts_safe_child_through_exit() {
        let executable = fs::canonicalize("/bin/cat").unwrap();
        let child = Command::new(&executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let mut executable_samples = 0;
        let sample = sample_child_maps_with_observer(
            child,
            &executable,
            Duration::from_secs(2),
            |child, mappings| {
                if mappings.iter().any(|mapping| {
                    mapping.permissions.contains('x')
                        && mapping
                            .pathname
                            .as_deref()
                            .is_some_and(|path| Path::new(path) == executable)
                }) {
                    executable_samples += 1;
                    if executable_samples == 2 {
                        // EOF lets cat exit only after multiple executable observations.
                        drop(child.stdin.take());
                    }
                }
                Ok(())
            },
        )
        .unwrap();
        assert!(executable_samples >= 2);
        assert!(sample.samples > 1);
        assert!(sample.executable_mappings > 0);
        assert!(anonymous_executable_mappings(&sample.mappings).is_empty());
    }

    #[test]
    fn continuous_sampler_rejects_forbidden_mapping_added_after_executable_observation() {
        let temp = TempDir::new("stage0-late-executable-map").unwrap();
        let source = temp.path().join("late-map.c");
        let executable = temp.path().join("late-map");
        fs::write(
            &source,
            r#"
#include <sys/mman.h>
#include <unistd.h>
int main(void) {
    char observed;
    if (read(STDIN_FILENO, &observed, 1) != 1) return 3;
    void *page = mmap(0, 4096, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (page == MAP_FAILED || mprotect(page, 4096, PROT_READ | PROT_EXEC) != 0) return 2;
    /* Keep the forbidden mapping live until the sampler rejects and kills us. */
    if (read(STDIN_FILENO, &observed, 1) != 1) return 4;
    return 5;
}
"#,
        )
        .unwrap();
        let compiled = Command::new("cc")
            .arg("-O0")
            .arg(&source)
            .arg("-o")
            .arg(&executable)
            .status()
            .unwrap();
        assert!(compiled.success());
        let executable = fs::canonicalize(executable).unwrap();
        let child = Command::new(&executable)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let mut executable_observed = false;
        let error = sample_child_maps_with_observer(
            child,
            &executable,
            Duration::from_secs(2),
            |child, mappings| {
                if !executable_observed
                    && mappings.iter().any(|mapping| {
                        mapping.permissions.contains('x')
                            && mapping
                                .pathname
                                .as_deref()
                                .is_some_and(|path| Path::new(path) == executable)
                    })
                {
                    child
                        .stdin
                        .as_mut()
                        .context("late-map child stdin was not piped")?
                        .write_all(b"x")
                        .context("releasing late-map child after executable observation")?;
                    executable_observed = true;
                }
                Ok(())
            },
        )
        .unwrap_err();
        assert!(executable_observed);
        let message = error.to_string();
        assert!(
            message.contains("anonymous executable") || message.contains("RWX"),
            "{message}"
        );
    }

    #[test]
    fn live_process_map_provider_observes_no_rwx_mapping() {
        let maps = process_maps().unwrap();
        assert!(!maps.is_empty());
        assert!(
            maps.iter()
                .all(|mapping| !mapping.permissions.contains("rwx"))
        );
    }
}
