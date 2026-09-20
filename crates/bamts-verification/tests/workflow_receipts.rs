use std::{collections::BTreeMap, fs, path::PathBuf};

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("verification crate is nested below the repository root")
        .to_path_buf()
}

fn workflow(name: &str) -> String {
    fs::read_to_string(repository_root().join(".github/workflows").join(name))
        .unwrap_or_else(|error| panic!("cannot read {name}: {error}"))
}

#[test]
fn compiler_receipt_jobs_use_pinned_authority_and_shared_tools() {
    const TOOLS_ARTIFACT: &str =
        "compiler-receipt-tools-${{ github.run_id }}-${{ github.run_attempt }}";
    #[derive(serde::Deserialize)]
    struct Workflow {
        jobs: BTreeMap<String, Job>,
    }

    #[derive(serde::Deserialize)]
    struct Job {
        #[serde(default)]
        steps: Vec<Step>,
    }

    #[derive(serde::Deserialize)]
    struct Step {
        #[serde(default)]
        run: String,
        #[serde(default)]
        uses: String,
        #[serde(default)]
        with: ArtifactInputs,
    }

    #[derive(Default, serde::Deserialize)]
    struct ArtifactInputs {
        #[serde(default)]
        name: String,
        #[serde(default)]
        path: String,
    }

    for name in ["ci.yml", "nightly.yml", "weekly-audit.yml"] {
        let parsed: Workflow = serde_saphyr::from_str(&workflow(name))
            .unwrap_or_else(|error| panic!("cannot parse {name}: {error}"));
        let producer = parsed.jobs.get("preflight").expect("preflight job");
        let upload = producer
            .steps
            .iter()
            .position(|step| {
                step.uses.starts_with("actions/upload-artifact@")
                    && step.with.name == TOOLS_ARTIFACT
                    && step.with.path == "target/receipt-tools"
            })
            .unwrap_or_else(|| panic!("{name} must publish one canonical receipt tool artifact"));
        assert!(producer.steps[..upload].iter().any(|step| {
            step.run.contains("cargo build --locked --release")
                && step
                    .run
                    .contains("--bin bamts-verification --bin ts_lane_worker")
        }));
        let mut checked_jobs = 0;
        for (job_name, job) in parsed.jobs {
            let Some(execution) = job.steps.iter().position(|step| {
                step.run.contains("--catalog typescript-7.0.2")
                    && (step.run.contains("suite run") || step.run.contains("suite merge"))
            }) else {
                continue;
            };
            checked_jobs += 1;
            let download = job.steps[..execution]
                .iter()
                .position(|step| {
                    step.uses.starts_with("actions/download-artifact@")
                        && step.with.name == TOOLS_ARTIFACT
                        && step.with.path == "target/receipt-tools"
                })
                .unwrap_or_else(|| panic!("{name}:{job_name} must download the canonical tools"));
            assert!(job.steps[download + 1..execution].iter().any(|step| {
                step.run.contains(
                    "chmod +x target/receipt-tools/bamts-verification target/receipt-tools/ts_lane_worker",
                )
            }));
            for step in &job.steps[execution..] {
                if step.run.contains("--catalog typescript-7.0.2") {
                    assert!(
                        step.run
                            .contains("target/receipt-tools/bamts-verification suite ")
                            && !step.run.contains("cargo run"),
                        "{name}:{job_name} must execute the downloaded harness, not rebuild it"
                    );
                }
            }
            for required in [
                "source fetch typescript-7-compiler --dest target/authority/typescript-7.0.2",
                "source fetch typescript-primary-tests --dest target/authority/typescript-7.0.2-tests",
            ] {
                assert!(
                    job.steps[..execution]
                        .iter()
                        .any(|step| step.run.contains(required)),
                    "{name}:{job_name} must provision `{required}` before receipt execution"
                );
            }
        }
        assert!(checked_jobs > 0, "{name} contains no compiler receipt jobs");
    }
}

#[test]
fn receipt_workflows_bind_attempt_and_merge_complete_matrices() {
    for (name, raw_root, merged_root, retention) in [
        (
            "ci.yml",
            "verification/evidence/pr/",
            "verification/evidence/pr-merged/",
            14,
        ),
        (
            "nightly.yml",
            "verification/evidence/nightly/",
            "verification/evidence/nightly-merged/",
            30,
        ),
        (
            "weekly-audit.yml",
            "verification/evidence/weekly/",
            "verification/evidence/weekly-merged/",
            30,
        ),
    ] {
        let text = workflow(name);
        let retention_line = format!("retention-days: {retention}");
        for required in [
            "--workflow .github/workflows/",
            "--run-id \"${{ github.run_id }}\"",
            "--run-attempt \"${{ github.run_attempt }}\"",
            "--source-sha",
            "--job ",
            "--host ",
            "--runtime ",
            "suite merge",
            "merge-multiple: true",
            retention_line.as_str(),
            raw_root,
            merged_root,
        ] {
            assert!(text.contains(required), "{name} omits `{required}`");
        }
        assert!(
            text.contains("${{ github.run_id }}-${{ github.run_attempt }}"),
            "{name} artifact identities do not distinguish rerun attempts"
        );
        assert!(
            text.contains("zero=$(( ${{ matrix.shard }} - 1 ))"),
            "{name} does not convert the one-based workflow coordinate once in the shell"
        );
    }
}

#[test]
fn workers_cannot_mint_pass_or_upload_logs_as_receipts() {
    for name in ["ci.yml", "nightly.yml", "weekly-audit.yml"] {
        let text = workflow(name);
        assert!(text.contains("target/receipt-tools/bamts-verification suite run"));
        assert!(
            !text.contains("--state PASS"),
            "{name} exposes worker PASS minting"
        );
        for line in text
            .lines()
            .filter(|line| line.trim_start().starts_with("path:"))
        {
            if line.contains("verification/evidence/") {
                assert!(
                    line.trim_end().ends_with(".jsonl") || line.trim_end().ends_with("*.jsonl")
                );
                assert!(!line.ends_with(".log"));
            }
        }
    }
}

#[test]
fn high_and_low_level_shard_coordinates_are_documented_at_the_boundary() {
    let weekly = workflow("weekly-audit.yml");
    assert!(weekly.contains("ts_conformance --shards is one-based"));
    assert!(weekly.contains("suite --shard is zero-based"));

    let gates = fs::read_to_string(repository_root().join(".outline/GATES.md")).expect("GATES.md");
    assert!(gates.contains("`ts_conformance --shards k/N` is deliberately one-based"));
    assert!(
        gates.contains("`bamts-verification suite run --shard i/N` is deliberately zero-based")
    );
}

#[test]
fn release_gate_is_one_ordered_fail_closed_root() {
    let justfile = fs::read_to_string(repository_root().join("Justfile")).expect("Justfile");
    let ordered = [
        "completion regenerate --check",
        "audit-ledger --require-complete",
        "ledger rebuild --check",
        "completion verify --root product",
        "RELEASE GATE PASS",
    ];
    let mut cursor = 0;
    for required in ordered {
        let relative = justfile[cursor..]
            .find(required)
            .unwrap_or_else(|| panic!("release-gate omits or misorders `{required}`"));
        cursor += relative + required.len();
    }
    assert_eq!(justfile.matches("release-gate:").count(), 1);
    assert_eq!(justfile.matches("RELEASE GATE PASS").count(), 1);
}
