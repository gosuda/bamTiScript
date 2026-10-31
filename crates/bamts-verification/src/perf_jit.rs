//! E5.2 JIT compile-cost / payback / queue-tail-latency measurement.
//!
//! Reads the locked rule definitions in `bench/compiler-rules.toml` and the
//! closed catalog inventory in `verification/catalog-inputs.json`.  On a
//! conforming, pinned host it samples the `bamts` `--json` run output, reports
//! medians, and emits a content-addressed receipt.  When the runtime does not
//! emit the named counters the receipt records `MEASUREMENT_UNAVAILABLE`.

use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    fmt::Write as _,
    fs::read_to_string,
    io::{self, Read},
    path::{Path, PathBuf},
    process::{Command, ExitStatus, Stdio},
    thread,
    time::{Duration, Instant},
};

use anyhow::{Context, Result, anyhow};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};

const JIT_RULES: &[&str] = &["jit.compile-cost", "jit.payback", "jit.queue-tail-latency"];
const LEAF: &str = "E5.2";

fn root_dir() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("workspace")
        .parent()
        .expect("repo root")
}

fn compiler_rules_path() -> PathBuf {
    root_dir().join("bench/compiler-rules.toml")
}

fn catalog_inputs_path() -> PathBuf {
    root_dir().join("verification/catalog-inputs.json")
}

fn bamts_bin() -> PathBuf {
    env::var("BAMTS")
        .map(PathBuf::from)
        .unwrap_or_else(|_| root_dir().join("target/release/bamts"))
}

#[derive(Debug, Deserialize)]
pub struct CompilerRules {
    pub schema: String,
    pub conditions: ConditionRules,
    pub measurement: MeasurementRules,
    pub rule: BTreeMap<String, RuleConfig>,
}

#[derive(Debug, Deserialize)]
pub struct ConditionRules {
    pub required_governors: Vec<String>,
    pub require_swap_disabled: bool,
    pub require_pinned_affinity: bool,
    pub forbid_full_machine_affinity: bool,
    pub recapture_after_run: bool,
}

#[derive(Debug, Deserialize)]
pub struct MeasurementRules {
    pub statistic: String,
    pub samples: usize,
    pub warmup: usize,
}

#[derive(Debug, Deserialize)]
pub struct RuleConfig {
    pub kind: String,
    #[serde(default)]
    pub unit: String,
    pub workload: String,
    pub argv: Vec<String>,
    #[serde(default)]
    pub metric_key: String,
    pub requires: String,
}

#[derive(Debug, Clone)]
pub struct Conditions {
    pub governors: Vec<String>,
    pub swap_total_kb: u64,
    pub cpus_allowed_list: String,
    pub cpus_online: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct ConditionsRecord {
    pub governors: Vec<String>,
    pub swap_total_kb: u64,
    pub cpus_allowed_list: String,
    pub cpus_online: String,
}

impl Conditions {
    pub fn capture() -> Result<Self> {
        let facts = bamts_platform::machine_facts()?;
        let placement = bamts_platform::thread_placement()?;
        Ok(Self {
            governors: bamts_platform::cpu_governors()?,
            swap_total_kb: facts.swap_total_kib,
            cpus_allowed_list: placement.cpu_affinity,
            cpus_online: bamts_platform::online_cpu_list()?,
        })
    }

    pub fn validate(&self, rules: &ConditionRules) -> Vec<String> {
        let mut failures = Vec::new();

        if !self
            .governors
            .iter()
            .all(|g| rules.required_governors.contains(g))
        {
            failures.push(format!(
                "governors {:?} do not match required {:?}",
                self.governors, rules.required_governors
            ));
        }

        if rules.require_swap_disabled && self.swap_total_kb != 0 {
            failures.push(format!(
                "swap is not disabled: SwapTotal = {} kB",
                self.swap_total_kb
            ));
        }

        let allowed = parse_cpu_list(&self.cpus_allowed_list).unwrap_or_default();
        let online = parse_cpu_list(&self.cpus_online).unwrap_or_default();

        if allowed.is_empty() {
            failures.push("process has no CPU affinity".to_owned());
        } else if allowed == online {
            failures.push(format!(
                "process is not pinned: Cpus_allowed_list = {} covers all online CPUs",
                self.cpus_allowed_list
            ));
        }

        failures
    }

    pub fn to_record(&self) -> ConditionsRecord {
        ConditionsRecord {
            governors: self.governors.clone(),
            swap_total_kb: self.swap_total_kb,
            cpus_allowed_list: self.cpus_allowed_list.clone(),
            cpus_online: self.cpus_online.clone(),
        }
    }
}

fn parse_cpu_list(s: &str) -> Result<BTreeSet<u32>> {
    let mut set = BTreeSet::new();
    for part in s.split(',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        if let Some((a, b)) = part.split_once('-') {
            let start: u32 = a.trim().parse()?;
            let end: u32 = b.trim().parse()?;
            for c in start..=end {
                set.insert(c);
            }
        } else {
            set.insert(part.parse()?);
        }
    }
    Ok(set)
}

fn median(values: &mut [u64]) -> u64 {
    let mid = values.len() / 2;
    values.select_nth_unstable(mid);
    values[mid]
}

pub fn load_rules() -> Result<CompilerRules> {
    let text = read_to_string(compiler_rules_path())
        .with_context(|| compiler_rules_path().display().to_string())?;
    toml::from_str(&text).map_err(|e| anyhow!("compiler-rules.toml: {e}"))
}

pub fn verify_catalog() -> Result<()> {
    let catalog: Value = serde_json::from_str(&read_to_string(catalog_inputs_path())?)?;
    let benchmarks = catalog
        .get("catalogs")
        .and_then(|v| v.as_array())
        .ok_or_else(|| anyhow!("catalog-inputs.json missing catalogs"))?
        .iter()
        .find(|c| c.get("id").and_then(|i| i.as_str()) == Some("benchmarks"))
        .ok_or_else(|| anyhow!("catalog-inputs.json missing benchmarks catalog"))?;
    let identifiers = benchmarks
        .get("identifiers")
        .and_then(|v| v.as_array())
        .ok_or_else(|| anyhow!("benchmarks catalog missing identifiers"))?
        .iter()
        .filter_map(|v| v.as_str())
        .collect::<BTreeSet<_>>();
    for rule in JIT_RULES {
        if !identifiers.contains(rule) {
            return Err(anyhow!("rule {rule} not in benchmarks catalog"));
        }
    }
    Ok(())
}

fn extract_metric(text: &str, key: &str) -> Option<u64> {
    let key_pat = format!(r#""{}""#, key);
    let pos = text.find(&key_pat)? + key_pat.len();
    let after = &text[pos..];
    let num_start = after
        .find(|c: char| c.is_ascii_digit() || c == '-')
        .unwrap_or(0);
    let digits: String = after[num_start..]
        .chars()
        .take_while(|c| c.is_ascii_digit())
        .collect();
    if digits.is_empty() {
        return None;
    }
    digits.parse().ok()
}

#[derive(Debug)]
struct Captured {
    status: ExitStatus,
    stdout: String,
    stderr: String,
}

fn spawn_pipe_reader(
    mut pipe: impl Read + Send + 'static,
) -> thread::JoinHandle<io::Result<Vec<u8>>> {
    thread::spawn(move || {
        let mut bytes = Vec::new();
        pipe.read_to_end(&mut bytes).map(|_| bytes)
    })
}

fn join_pipe(reader: thread::JoinHandle<io::Result<Vec<u8>>>) -> Result<Vec<u8>> {
    reader
        .join()
        .map_err(|_| anyhow!("perf jit pipe reader panicked"))?
        .map_err(|e| anyhow!("perf jit pipe read: {e}"))
}

fn bound_stderr_snip(stderr: &str) -> String {
    const LIMIT: usize = 2048;
    if stderr.len() <= LIMIT {
        return stderr.to_owned();
    }
    let mut cut = LIMIT;
    while cut > 0 && !stderr.is_char_boundary(cut) {
        cut -= 1;
    }
    stderr[..cut].to_owned()
}

fn run_child(command: &mut Command, timeout: Duration) -> Result<Captured> {
    let mut child = command
        .spawn()
        .with_context(|| format!("failed to spawn {}", bamts_bin().display()))?;

    let stdout_pipe = child
        .stdout
        .take()
        .ok_or_else(|| io::Error::other("perf jit child stdout was not piped"))?;
    let stderr_pipe = child
        .stderr
        .take()
        .ok_or_else(|| io::Error::other("perf jit child stderr was not piped"))?;

    let stdout_reader = spawn_pipe_reader(stdout_pipe);
    let stderr_reader = spawn_pipe_reader(stderr_pipe);

    let deadline = Instant::now() + timeout;
    let status = loop {
        if let Some(s) = child.try_wait()? {
            break Some(s);
        }
        if Instant::now() >= deadline {
            break None;
        }
        thread::sleep(Duration::from_millis(50));
    };

    if let Some(status) = status {
        let stdout = join_pipe(stdout_reader);
        let stderr = join_pipe(stderr_reader);
        let stdout_bytes = stdout?;
        let stderr_bytes = stderr?;
        let captured = Captured {
            status,
            stdout: String::from_utf8_lossy(&stdout_bytes).into_owned(),
            stderr: String::from_utf8_lossy(&stderr_bytes).into_owned(),
        };
        if !captured.status.success() {
            let snip = bound_stderr_snip(&captured.stderr);
            if !snip.is_empty() {
                return Err(anyhow!("bamts exited with {}: {snip}", captured.status));
            }
            return Err(anyhow!("bamts exited with {}", captured.status));
        }
        if captured.stdout.is_empty() && !captured.stderr.is_empty() {
            let snip = bound_stderr_snip(&captured.stderr);
            return Err(anyhow!("bamts stderr: {snip}"));
        }
        Ok(captured)
    } else {
        let _ = child.kill();
        let _ = child.wait();
        let _ = join_pipe(stdout_reader);
        let _ = join_pipe(stderr_reader);
        Err(anyhow!("bamts run timed out after {timeout:?}"))
    }
}

fn run_once(config: &RuleConfig, timeout: Duration) -> Result<String> {
    let mut cmd = Command::new(bamts_bin());
    cmd.args(&config.argv)
        .arg(&config.workload)
        .current_dir(root_dir())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let captured = run_child(&mut cmd, timeout)?;
    Ok(captured.stdout)
}

#[derive(Debug, Clone, Serialize)]
pub struct RuleReceipt {
    pub metric_key: String,
    pub state: String,
    pub median: Option<u64>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Receipt {
    pub schema: String,
    pub leaf: String,
    pub state: String,
    pub conditions_before: ConditionsRecord,
    pub conditions_after: ConditionsRecord,
    pub reasons: Vec<String>,
    pub rules: BTreeMap<String, RuleReceipt>,
    pub sha256: String,
}

fn to_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(s, "{:02x}", b);
    }
    s
}

fn build_receipt(
    rules: &CompilerRules,
    before: &Conditions,
    after: &Conditions,
    state: &str,
    reasons: &[String],
    medians: Option<&BTreeMap<String, u64>>,
) -> Result<String> {
    let mut rule_receipts = BTreeMap::new();
    for rule in JIT_RULES {
        let cfg = rules
            .rule
            .get(*rule)
            .with_context(|| format!("missing rule config for {rule}"))?;
        let (median, rule_state) = match medians.and_then(|m| m.get(*rule)) {
            Some(v) => (Some(*v), "ACCEPTED"),
            None => (None, state),
        };
        rule_receipts.insert(
            rule.to_string(),
            RuleReceipt {
                metric_key: cfg.metric_key.clone(),
                state: rule_state.to_owned(),
                median,
            },
        );
    }

    let mut body = Receipt {
        schema: rules.schema.clone(),
        leaf: LEAF.to_owned(),
        state: state.to_owned(),
        conditions_before: before.to_record(),
        conditions_after: after.to_record(),
        reasons: reasons.to_vec(),
        rules: rule_receipts,
        sha256: String::new(),
    };

    let body_json = serde_json::to_string(&body)?;
    let digest = Sha256::digest(body_json.as_bytes());
    body.sha256 = to_hex(digest.as_ref());

    Ok(serde_json::to_string_pretty(&body)?)
}

/// Run the E5.2 measurement and return a JSON receipt.
pub fn run() -> Result<String> {
    let rules = load_rules()?;
    verify_catalog()?;

    let before = Conditions::capture()?;
    let before_failures = before.validate(&rules.conditions);
    if !before_failures.is_empty() {
        return build_receipt(
            &rules,
            &before,
            &before,
            "INVALID_CONDITIONS",
            &before_failures,
            None,
        );
    }

    let first_rule = rules
        .rule
        .get(JIT_RULES[0])
        .context("missing jit.compile-cost rule config")?;
    let total_runs = rules.measurement.warmup + rules.measurement.samples;
    let timeout = Duration::from_secs(120);
    let mut rows: BTreeMap<String, Vec<u64>> = BTreeMap::new();
    let mut failure: Option<String> = None;

    for i in 0..total_runs {
        match run_once(first_rule, timeout) {
            Ok(out) => {
                let mut got = BTreeMap::new();
                for &rule in JIT_RULES {
                    let key = &rules.rule[rule].metric_key;
                    if let Some(v) = extract_metric(&out, key) {
                        got.insert(rule.to_string(), v);
                    }
                }
                if got.len() == JIT_RULES.len() {
                    if i >= rules.measurement.warmup {
                        for (rule, v) in got {
                            rows.entry(rule).or_default().push(v);
                        }
                    }
                } else {
                    let missing = JIT_RULES
                        .iter()
                        .filter(|r| !got.contains_key(**r))
                        .copied()
                        .collect::<Vec<_>>()
                        .join(", ");
                    failure = Some(format!(
                        "missing counters [{missing}] in --json output on run {}",
                        i + 1
                    ));
                    break;
                }
            }
            Err(e) => {
                failure = Some(e.to_string());
                break;
            }
        }
    }

    let after = Conditions::capture()?;
    let after_failures = after.validate(&rules.conditions);
    if !after_failures.is_empty() {
        return build_receipt(
            &rules,
            &before,
            &after,
            "INVALID_CONDITIONS",
            &after_failures,
            None,
        );
    }

    if let Some(reason) = failure {
        return build_receipt(
            &rules,
            &before,
            &after,
            "MEASUREMENT_UNAVAILABLE",
            &[reason],
            None,
        );
    }

    let mut medians: BTreeMap<String, u64> = BTreeMap::new();
    for rule in JIT_RULES {
        let vals = rows
            .get(*rule)
            .with_context(|| format!("missing row for {rule}"))?;
        if vals.len() < rules.measurement.samples {
            return Err(anyhow!("insufficient samples for {rule}"));
        }
        let mut owned = vals.clone();
        medians.insert(rule.to_string(), median(&mut owned));
    }

    build_receipt(&rules, &before, &after, "ACCEPTED", &[], Some(&medians))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn median_selects_middle_observed_sample() {
        let mut v = vec![42, 1, 99, 7, 12];
        assert_eq!(median(&mut v), 12);
    }

    #[test]
    fn median_of_nine_is_fifth() {
        let mut v = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
        assert_eq!(median(&mut v), 5);
    }

    #[test]
    fn parse_cpu_list_handles_ranges_and_singletons() {
        assert_eq!(
            parse_cpu_list("0-3,5,7-9").unwrap(),
            [0, 1, 2, 3, 5, 7, 8, 9].iter().copied().collect()
        );
        assert_eq!(parse_cpu_list("0-79").unwrap().len(), 80);
    }

    #[test]
    fn compiler_rules_loads_and_matches_schema() {
        let rules = load_rules().unwrap();
        assert_eq!(rules.schema, "bamti.compiler-rules/v1");
        assert_eq!(rules.measurement.samples, 9);
        assert_eq!(rules.measurement.warmup, 2);
        assert_eq!(rules.conditions.required_governors, vec!["performance"]);
        assert!(rules.rule.contains_key("jit.compile-cost"));
    }

    #[test]
    fn catalog_contains_jit_rule_identifiers() {
        verify_catalog().unwrap();
    }

    /// The conditions come from the platform crate on every host, so macOS can
    /// read them too. The old readers opened `/sys` and `/proc` directly.
    #[test]
    fn conditions_come_from_the_platform_crate() {
        let conditions = Conditions::capture().unwrap();
        let facts = bamts_platform::machine_facts().unwrap();
        let placement = bamts_platform::thread_placement().unwrap();
        assert_eq!(
            conditions.governors,
            bamts_platform::cpu_governors().unwrap()
        );
        assert_eq!(conditions.swap_total_kb, facts.swap_total_kib);
        assert_eq!(conditions.cpus_allowed_list, placement.cpu_affinity);
        assert_eq!(
            conditions.cpus_online,
            bamts_platform::online_cpu_list().unwrap()
        );
    }

    #[test]
    fn conditions_detect_full_machine_affinity() {
        let c = Conditions {
            governors: vec!["performance".to_owned()],
            swap_total_kb: 0,
            cpus_allowed_list: "0-79".to_owned(),
            cpus_online: "0-79".to_owned(),
        };
        let rules = ConditionRules {
            required_governors: vec!["performance".to_owned()],
            require_swap_disabled: true,
            require_pinned_affinity: true,
            forbid_full_machine_affinity: true,
            recapture_after_run: true,
        };
        assert!(!c.validate(&rules).is_empty());
    }

    #[test]
    fn conditions_detect_swap_and_governor_mismatch() {
        let c = Conditions {
            governors: vec!["powersave".to_owned()],
            swap_total_kb: 1024,
            cpus_allowed_list: "0-19".to_owned(),
            cpus_online: "0-79".to_owned(),
        };
        let rules = ConditionRules {
            required_governors: vec!["performance".to_owned()],
            require_swap_disabled: true,
            require_pinned_affinity: true,
            forbid_full_machine_affinity: true,
            recapture_after_run: true,
        };
        let f = c.validate(&rules);
        assert_eq!(f.len(), 2);
    }

    #[test]
    fn extract_metric_parses_positive_numbers() {
        let text = r#"{"jit.compile_ns": 1234567, "ignored": "x"}"#;
        assert_eq!(extract_metric(text, "jit.compile_ns"), Some(1234567));
        assert_eq!(extract_metric(text, "jit.payback"), None);
    }

    #[test]
    fn receipt_hashes_can_be_verified() {
        let rules = load_rules().unwrap();
        let before = Conditions {
            governors: vec!["performance".to_owned()],
            swap_total_kb: 0,
            cpus_allowed_list: "0-19".to_owned(),
            cpus_online: "0-79".to_owned(),
        };
        let json = build_receipt(
            &rules,
            &before,
            &before,
            "ACCEPTED",
            &[],
            Some(&BTreeMap::from([("jit.compile-cost".to_owned(), 100)])),
        )
        .unwrap();
        let parsed: Value = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed["state"].as_str(), Some("ACCEPTED"));
        assert!(parsed["sha256"].as_str().unwrap().len() == 64);
    }

    #[cfg(unix)]
    #[test]
    fn run_child_drains_flooded_pipes_without_timeout() {
        let mut cmd = Command::new("sh");
        cmd.arg("-c")
            .arg("yes x | head -c 1048576 >&2; echo '{\"jit.compile_ns\": 42}'")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        let captured = run_child(&mut cmd, Duration::from_secs(5))
            .expect("flooded pipes must not false-timeout");
        assert!(
            captured.stdout.contains("jit.compile_ns"),
            "stdout missing metric: {captured:?}"
        );
        assert!(captured.status.success());
    }

    #[cfg(unix)]
    #[test]
    fn run_child_rejects_nonzero_exit_before_parsing() {
        let mut cmd = Command::new("sh");
        cmd.arg("-c")
            .arg("echo '{\"jit.compile_ns\": 99}'; echo 'boom' >&2; exit 3")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        let err =
            run_child(&mut cmd, Duration::from_secs(2)).expect_err("nonzero exit must be rejected");
        let msg = err.to_string();
        assert!(
            msg.contains("exited with"),
            "error must mention exit status: {msg}"
        );
        // stderr context is bounded, not unbounded raw dump.
        assert!(msg.contains("boom"), "stderr snip missing: {msg}");
    }

    #[cfg(unix)]
    #[test]
    fn run_child_timeout_still_bounded() {
        let mut cmd = Command::new("sh");
        cmd.arg("-c")
            .arg("exec sleep 10")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        let start = Instant::now();
        let err = run_child(&mut cmd, Duration::from_millis(200)).expect_err("sleep must timeout");
        let elapsed = start.elapsed();
        assert!(
            err.to_string().contains("timed out"),
            "timeout error missing: {err}"
        );
        assert!(
            elapsed < Duration::from_secs(2),
            "timeout not bounded, elapsed {elapsed:?}"
        );
    }

    #[test]
    fn bound_stderr_snip_limits_output() {
        let big = "x".repeat(5000);
        let snip = bound_stderr_snip(&big);
        assert_eq!(snip.len(), 2048);
        assert!(snip.chars().all(|c| c == 'x'));
        let small = "hello";
        assert_eq!(bound_stderr_snip(small), "hello");
    }
}
