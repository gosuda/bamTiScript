//! Deterministic materialization and offline verification of performance fixtures.

use std::{
    collections::BTreeMap,
    fs,
    path::{Component, Path, PathBuf},
};

use sha2::{Digest, Sha256};

use crate::{
    corpus,
    perf::{
        BenchmarkManifest, Fixture, FixtureGroup, FixtureOrigin, PerfError, PerfErrorCode, Result,
    },
    schema::{TYPESCRIPT_SUITE_SOURCE, load_sources, required_source, sha256_hex},
    suite::{SuiteIndex, extract_archive, fetch_archive, single_archive_root},
};

const JSX_FIXTURE_ID: &str = "bench-jsx-complexity";
const JSX_SOURCE_PATH: &str = "tests/cases/compiler/jsxComplexSignatureHasApplicabilityError.tsx";
const JSX_SNAPSHOT_SHA256: &str =
    "e2d2d8d47230600f5fb59d5417399b1fde427877e7ac3bddd963b2cfff25fba0";
const REQUIRED_FIXTURES: [(&str, &str); 37] = [
    (
        "bench-checker-ts",
        "781e627828fa7fe337d90815afa38f81a58620be7d141849d3c8efaf34893eaf",
    ),
    (
        "bench-dom-dts",
        "e05c7f2d7ca6295cbd672cedbd006bec4d65b99aec21b795740d0596e6936103",
    ),
    (
        "bench-empty-ts",
        "be0f24cbf28a8006de812b22ce161ea045cbfebb53e189fd400545a3da202063",
    ),
    (
        "bench-herebyfile",
        "c71f520073b1b1c4d870556b5eda487a70e605120b8b61a05515cb4b1215d862",
    ),
    (
        "bench-jsx-complexity",
        "5080818abe79bbd72a9f66021de7235cfd9f3303bbb18cf932184df36da5b0e0",
    ),
    (
        "boundary-json-depth-127",
        "9734a8b0e6643bc0646d1e64b9dec605e2380eebd108e7e18d2044781f4e6982",
    ),
    (
        "boundary-json-depth-128",
        "99b378ff2483455a064bea0fb0798022ac4a4b994947cc1305ba101098d545fb",
    ),
    (
        "boundary-json-depth-129",
        "997d3a2f9ab32ade8281d4dbbd88d50b90f95b2935f6a5f7ca13f332cecf0de0",
    ),
    (
        "boundary-parser-depth-255",
        "8e2e24d3780775f28dc5b35526003a1e65e7c8bb31587454fa64e0d3755aa341",
    ),
    (
        "boundary-parser-depth-256",
        "1385a88e20bde0877e157c5e5a1ceec295644057c1950bbe0e911974b06a0410",
    ),
    (
        "boundary-parser-depth-257",
        "000fc8154feaf51f010bc5a44a97bd9546db2c8f5be09b2c08d199ffecf5e8ca",
    ),
    (
        "boundary-source-bytes-16777215",
        "4745108f818591382b5c0a09ab228f5883e304ab161bf08321dd99af13a642e4",
    ),
    (
        "boundary-source-bytes-16777216",
        "2440034f5101492a434f35730116d0598bab18f7ba19360912503f82f543951f",
    ),
    (
        "boundary-source-bytes-16777217",
        "aa52ce4126e3af1a8f2400f27bb167d905a24ca2c51e406863da777f03e997a2",
    ),
    (
        "boundary-string-units-1048576",
        "cb517f637a55630e0df5ac920bdd5b51912e2cc3db1f22f829f96898aed3cd24",
    ),
    (
        "boundary-string-units-1048577",
        "955d6af996dade069841f82a5682a53736b1e444f900b497cf28ed88fbcc97fd",
    ),
    (
        "cli-startup-empty",
        "6adca747cc17166b870bdbbf5f36e3e596c6ed6695f04e4a2534eec0ced355f6",
    ),
    (
        "corpus-citty",
        "d4d8fe86618757c557339094395ab2e334cee7581e2243418ad9bd407fc89a68",
    ),
    (
        "corpus-defu",
        "4114ff22793337e83730269fae964e91c85edf79bda841fadd29493dbefa8096",
    ),
    (
        "corpus-destr",
        "38f3421fdecc25c7c06f71217e826f5a65b0bf17ca3a3580cf92307ca99a897d",
    ),
    (
        "corpus-dot-prop",
        "93daa66508bf3fb7ed451d925b6a3869fd5386032e601dd6a26a9aea93315c06",
    ),
    (
        "corpus-escape-string-regexp",
        "e48faa2c11dd53fb3b3ded3520c481b3741bc9d6093982ea176c2d3adfb8fb4c",
    ),
    (
        "corpus-hookable",
        "a4180e92356b5949f509e56c6b228e5cb501450e0dd35358be8e3d49d76a0f0d",
    ),
    (
        "corpus-is-plain-obj",
        "bc5922c5f71faecd1bfa36a5e50a2f1fc9dadd1463fe762c31a3d707d8854e00",
    ),
    (
        "corpus-mitt",
        "00fe102046d5b4b2e140ce4f8f9a9c446b398ae490b89f16c0fbb36c6e3d0596",
    ),
    (
        "corpus-ohash",
        "9dafd257a9527392533c394c462612a8819fd987cbccc9ab8eb271ed05ebcdca",
    ),
    (
        "corpus-p-defer",
        "7db58d81711c14b79e8c3c5f999d282401444fcd7ad3a3a173d0513df9b91569",
    ),
    (
        "corpus-p-map",
        "b71cd75c49ba0c6873f5e41352e40ef7d3b1f42dca51cc80b2eb7714ab12dde8",
    ),
    (
        "corpus-p-queue",
        "d048f49de52366273d01f5fb06218caa27720080196c4a2e28106282729d778e",
    ),
    (
        "corpus-pathe",
        "de21dc371c4893b8c1b09f774a481852da6e04645269153a6cfef83b9461942b",
    ),
    (
        "corpus-perfect-debounce",
        "408096139ed44b824edb7d50d708e1e1fe53e00b4e853b1a2e375f22d8414a75",
    ),
    (
        "corpus-rou3",
        "671119971f8dfdd7a8b3842909dbbf7c62452e0553dc51a14aaed4323ecb2d24",
    ),
    (
        "corpus-tiny-invariant",
        "92fa226f7c2e869af7608b96eec3e15908fd5f83926fc66ac90fbbbc7d69d603",
    ),
    (
        "corpus-tslib",
        "3f8d46da8739debe9df317f0bd5b31f1e8146bfa1594a1592d55905e2d076740",
    ),
    (
        "corpus-ufo",
        "62b3e30bd6019b5287572fe6ebe82c7f888e29ff0732bfc7fe15e71e201b21fe",
    ),
    (
        "corpus-valita",
        "3aeaeff7462dda2ea4035855b352c0e3788d243264bf935a19a3ab5d0a0a15fa",
    ),
    (
        "corpus-yocto-queue",
        "9aed574770e2aad03766b331d0d02d110b065539cbeaed5cacb05ce9e53e1994",
    ),
];

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaterializedFixture {
    pub id: String,
    pub sha256: String,
    pub bytes: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixtureVerification {
    pub fixtures: Vec<MaterializedFixture>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TreeHash {
    pub sha256: String,
    pub file_count: u64,
    pub bytes: u64,
}

pub fn hash_file(path: &Path) -> Result<String> {
    let bytes = fs::read(path)
        .map_err(|error| PerfError::harness(format!("{}: {error}", path.display())))?;
    Ok(sha256_hex(&bytes))
}

pub fn hash_tree(dir: &Path) -> Result<TreeHash> {
    let mut files = Vec::new();
    collect_tree_files(dir, dir, &mut files)?;
    files.sort_by(|left, right| left.0.as_slice().cmp(right.0.as_slice()));

    let mut hasher = Sha256::new();
    let mut bytes = 0_u64;
    for (relative, path) in &files {
        let content = fs::read(path)
            .map_err(|error| PerfError::harness(format!("{}: {error}", path.display())))?;
        let len = u64::try_from(content.len())
            .map_err(|_| PerfError::harness(format!("fixture too large: {}", path.display())))?;
        hasher.update(relative);
        hasher.update([0]);
        hasher.update(len.to_le_bytes());
        hasher.update(&content);
        bytes = bytes
            .checked_add(len)
            .ok_or_else(|| PerfError::harness("fixture tree byte count overflow"))?;
    }

    Ok(TreeHash {
        sha256: format!("{:x}", hasher.finalize()),
        file_count: files.len() as u64,
        bytes,
    })
}

#[cfg(unix)]
fn extend_path_component(output: &mut Vec<u8>, component: &std::ffi::OsStr) {
    use std::os::unix::ffi::OsStrExt;
    output.extend_from_slice(component.as_bytes());
}

#[cfg(not(unix))]
fn extend_path_component(output: &mut Vec<u8>, component: &std::ffi::OsStr) {
    output.extend_from_slice(component.to_string_lossy().as_bytes());
}

fn collect_tree_files(
    root: &Path,
    current: &Path,
    files: &mut Vec<(Vec<u8>, PathBuf)>,
) -> Result<()> {
    let entries = fs::read_dir(current)
        .map_err(|error| PerfError::harness(format!("{}: {error}", current.display())))?;
    for entry in entries {
        let entry =
            entry.map_err(|error| PerfError::harness(format!("{}: {error}", current.display())))?;
        let path = entry.path();
        let metadata = fs::symlink_metadata(&path)
            .map_err(|error| PerfError::harness(format!("{}: {error}", path.display())))?;
        if metadata.file_type().is_symlink() {
            return Err(PerfError::harness(format!(
                "fixture tree symlink rejected: {}",
                path.display()
            )));
        }
        if metadata.is_dir() {
            collect_tree_files(root, &path, files)?;
        } else if metadata.is_file() {
            let relative = path
                .strip_prefix(root)
                .map_err(|error| PerfError::harness(format!("{}: {error}", path.display())))?;
            let mut normalized = Vec::new();
            for (index, component) in relative.components().enumerate() {
                let Component::Normal(part) = component else {
                    return Err(PerfError::harness(format!(
                        "unclean fixture path: {}",
                        relative.display()
                    )));
                };
                if index != 0 {
                    normalized.push(b'/');
                }
                extend_path_component(&mut normalized, part);
            }
            files.push((normalized, path));
        } else {
            return Err(PerfError::harness(format!(
                "fixture tree non-regular entry rejected: {}",
                path.display()
            )));
        }
    }
    Ok(())
}

pub fn generate_boundary(generator: &str, params: &BTreeMap<String, u64>) -> Result<Vec<u8>> {
    let only = |name: &str| -> Result<u64> {
        if params.len() != 1 {
            return Err(PerfError::harness(format!(
                "generator `{generator}` requires only `{name}`"
            )));
        }
        params
            .get(name)
            .copied()
            .ok_or_else(|| PerfError::harness(format!("generator `{generator}` requires `{name}`")))
    };
    let count = |value: u64| {
        usize::try_from(value)
            .map_err(|_| PerfError::harness(format!("generator `{generator}` parameter overflow")))
    };

    match generator {
        "parser-depth" => {
            let depth = count(only("depth")?)?;
            let mut output = Vec::with_capacity(10 + depth * 2);
            output.extend_from_slice(b"let x =");
            output.extend(std::iter::repeat_n(b'(', depth));
            output.push(b'1');
            output.extend(std::iter::repeat_n(b')', depth));
            output.extend_from_slice(b";\n");
            Ok(output)
        }
        "json-depth" => {
            let depth = count(only("depth")?)?;
            let mut output = Vec::with_capacity(depth * 6 + 1);
            for _ in 0..depth {
                output.extend_from_slice(b"{\"a\":");
            }
            output.push(b'1');
            output.extend(std::iter::repeat_n(b'}', depth));
            Ok(output)
        }
        "source-bytes" => {
            let size = count(only("size")?)?;
            if size == 0 {
                return Ok(Vec::new());
            }
            let mut output = vec![b'a'; size];
            output[0] = b'/';
            if size > 1 {
                output[1] = b'/';
            }
            output[size - 1] = b'\n';
            Ok(output)
        }
        "string-units" => {
            let units = count(only("units")?)?;
            let mut output = Vec::with_capacity(units + 14);
            output.extend_from_slice(b"const s = \"");
            output.extend(std::iter::repeat_n(b'a', units));
            output.extend_from_slice(b"\";\n");
            Ok(output)
        }
        _ => Err(PerfError::harness(format!(
            "unknown boundary generator `{generator}`"
        ))),
    }
}

pub fn materialize_fixtures(
    root: &Path,
    manifest: &BenchmarkManifest,
) -> Result<Vec<MaterializedFixture>> {
    require_fixture_contract(manifest)?;
    let mut archive_root = None;
    let mut results = Vec::new();

    for fixture in &manifest.fixtures {
        let Some(path) = fixture.path.as_deref() else {
            continue;
        };
        let bytes = match fixture.origin {
            FixtureOrigin::TypescriptSuite => {
                if fixture.source_archive.as_deref() != Some(TYPESCRIPT_SUITE_SOURCE) {
                    return Err(PerfError::harness(format!(
                        "fixture `{}` has unknown source archive",
                        fixture.id
                    )));
                }
                if archive_root.is_none() {
                    let (sources, _) = load_sources(root)
                        .map_err(|error| PerfError::harness(error.to_string()))?;
                    let suite = required_source(&sources, TYPESCRIPT_SUITE_SOURCE)
                        .map_err(|error| PerfError::harness(error.to_string()))?;
                    if suite.digest_algorithm != "sha256" {
                        return Err(PerfError::harness(format!(
                            "source `{TYPESCRIPT_SUITE_SOURCE}` must use sha256"
                        )));
                    }
                    let cache = checked_root_path(root, "verification/ts-suite/.archives")?;
                    fs::create_dir_all(&cache).map_err(|error| {
                        PerfError::harness(format!("{}: {error}", cache.display()))
                    })?;
                    let archive = fetch_archive(&suite.url, &suite.digest, &cache)
                        .map_err(|error| PerfError::harness(error.to_string()))?;
                    let extracted = extract_archive(&archive)
                        .map_err(|error| PerfError::harness(error.to_string()))?;
                    let source_root = single_archive_root(extracted.path())
                        .map_err(|error| PerfError::harness(error.to_string()))?;
                    archive_root = Some((extracted, source_root));
                }
                let source_path = fixture.source_path.as_deref().ok_or_else(|| {
                    PerfError::harness(format!("fixture `{}` is missing source_path", fixture.id))
                })?;
                let source = checked_root_path(&archive_root.as_ref().unwrap().1, source_path)?;
                fs::read(&source)
                    .map_err(|error| PerfError::harness(format!("{}: {error}", source.display())))?
            }
            FixtureOrigin::Generated if fixture.generator.as_deref() == Some("empty-file") => {
                Vec::new()
            }
            FixtureOrigin::Generated if fixture.group == FixtureGroup::Boundary => {
                let generator = fixture.generator.as_deref().ok_or_else(|| {
                    PerfError::harness(format!("fixture `{}` is missing generator", fixture.id))
                })?;
                generate_boundary(generator, &fixture.params)?
            }
            FixtureOrigin::Corpus => continue,
            FixtureOrigin::Generated => continue,
        };

        let target = checked_root_path(root, path)?;
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| PerfError::harness(format!("{}: {error}", parent.display())))?;
        }
        fs::write(&target, &bytes)
            .map_err(|error| PerfError::harness(format!("{}: {error}", target.display())))?;
        let result = MaterializedFixture {
            id: fixture.id.clone(),
            sha256: sha256_hex(&bytes),
            bytes: bytes.len() as u64,
        };
        if fixture.id == JSX_FIXTURE_ID {
            verify_jsx_snapshot_anchor(root, &result.sha256)?;
        }
        results.push(result);
    }

    results.sort_by(|left, right| left.id.cmp(&right.id));
    Ok(results)
}

pub fn verify_fixtures(root: &Path, manifest: &BenchmarkManifest) -> Result<FixtureVerification> {
    require_fixture_contract(manifest)?;
    let mut mismatches = Vec::new();
    let mut verified = Vec::new();
    let corpus_loaded = manifest
        .fixtures
        .iter()
        .any(|fixture| fixture.origin == FixtureOrigin::Corpus);
    if corpus_loaded {
        corpus::load_corpus(root).map_err(|error| PerfError::harness(error.to_string()))?;
    }

    let fixture_ids: std::collections::BTreeSet<&str> = manifest
        .fixtures
        .iter()
        .map(|fixture| fixture.id.as_str())
        .collect();
    for fixture in &manifest.fixtures {
        if fixture.group == FixtureGroup::CliStartup
            && let Some(input) = fixture.input_fixture.as_deref()
            && !fixture_ids.contains(input)
        {
            mismatches.push(format!("{}: unknown input_fixture `{input}`", fixture.id));
            continue;
        }
        let outcome = verify_one(root, fixture);
        match outcome {
            Ok(Some(result)) => verified.push(result),
            Ok(None) => {}
            Err(detail) => mismatches.push(format!("{}: {detail}", fixture.id)),
        }
    }

    if !mismatches.is_empty() {
        return Err(PerfError::new(
            PerfErrorCode::FixtureMismatch,
            mismatches.join("; "),
        ));
    }
    verified.sort_by(|left, right| left.id.cmp(&right.id));
    Ok(FixtureVerification { fixtures: verified })
}

fn verify_one(
    root: &Path,
    fixture: &Fixture,
) -> std::result::Result<Option<MaterializedFixture>, String> {
    if fixture.group == FixtureGroup::CliStartup {
        let input = fixture
            .input_fixture
            .as_deref()
            .ok_or_else(|| "missing input_fixture".to_owned())?;
        return if fixture.argv.is_empty() {
            Err("missing argv".to_owned())
        } else if input == fixture.id {
            Err("input_fixture cannot reference itself".to_owned())
        } else {
            Ok(None)
        };
    }

    if fixture.origin == FixtureOrigin::Corpus {
        let path = fixture
            .path
            .as_deref()
            .ok_or_else(|| "missing path".to_owned())?;
        let tree = hash_tree(&checked_root_path(root, path).map_err(|e| e.to_string())?)
            .map_err(|error| error.to_string())?;
        compare_expected("tree_sha256", fixture.tree_sha256.as_deref(), &tree.sha256)?;
        compare_expected("file_count", fixture.file_count, tree.file_count)?;
        return Ok(Some(MaterializedFixture {
            id: fixture.id.clone(),
            sha256: tree.sha256,
            bytes: tree.bytes,
        }));
    }

    let bytes = if fixture.group == FixtureGroup::Boundary {
        generate_boundary(
            fixture
                .generator
                .as_deref()
                .ok_or_else(|| "missing generator".to_owned())?,
            &fixture.params,
        )
        .map_err(|error| error.to_string())?
    } else {
        let path = fixture
            .path
            .as_deref()
            .ok_or_else(|| "missing path".to_owned())?;
        fs::read(checked_root_path(root, path).map_err(|e| e.to_string())?)
            .map_err(|error| error.to_string())?
    };
    let sha256 = sha256_hex(&bytes);
    compare_expected("sha256", fixture.sha256.as_deref(), &sha256)?;
    compare_expected("bytes", fixture.bytes, bytes.len() as u64)?;
    Ok(Some(MaterializedFixture {
        id: fixture.id.clone(),
        sha256,
        bytes: bytes.len() as u64,
    }))
}

fn compare_expected<T>(
    name: &str,
    expected: Option<T>,
    actual: T,
) -> std::result::Result<(), String>
where
    T: PartialEq + std::fmt::Display,
{
    match expected {
        Some(expected) if expected == actual => Ok(()),
        Some(expected) => Err(format!("{name} expected `{expected}`, got `{actual}`")),
        None => Err(format!("missing {name}; observed `{actual}`")),
    }
}

fn require_fixture_inventory(manifest: &BenchmarkManifest) -> Result<()> {
    let mut actual: Vec<&str> = manifest
        .fixtures
        .iter()
        .map(|fixture| fixture.id.as_str())
        .collect();
    actual.sort_unstable();
    let required_ids: Vec<_> = REQUIRED_FIXTURES.iter().map(|(id, _)| *id).collect();
    if actual == required_ids {
        return Ok(());
    }
    let actual_set: std::collections::BTreeSet<&str> = actual.iter().copied().collect();
    let required: std::collections::BTreeSet<&str> = required_ids.iter().copied().collect();
    let missing: Vec<_> = required.difference(&actual_set).copied().collect();
    let unexpected: Vec<_> = actual_set.difference(&required).copied().collect();
    Err(PerfError::new(
        PerfErrorCode::FixtureMismatch,
        format!(
            "fixture inventory mismatch: expected {} rows, found {}; missing [{}]; unexpected [{}]",
            REQUIRED_FIXTURES.len(),
            actual.len(),
            missing.join(", "),
            unexpected.join(", ")
        ),
    ))
}

fn require_fixture_contract(manifest: &BenchmarkManifest) -> Result<()> {
    require_fixture_inventory(manifest)?;
    for fixture in &manifest.fixtures {
        if let Err(error) = validate_fixture_descriptor(fixture) {
            return Err(PerfError::new(
                PerfErrorCode::FixtureMismatch,
                format!("{}: {}", fixture.id, error.detail),
            ));
        }
        let expected = REQUIRED_FIXTURES
            .iter()
            .find_map(|(id, digest)| (*id == fixture.id).then_some(*digest))
            .expect("fixture inventory was validated");
        let encoded = serde_json::to_vec(fixture).map_err(|error| {
            PerfError::harness(format!("serialize fixture descriptor: {error}"))
        })?;
        let actual = sha256_hex(&encoded);
        if actual != expected {
            return Err(PerfError::new(
                PerfErrorCode::FixtureMismatch,
                format!(
                    "fixture `{}` descriptor mismatch: expected `{expected}`, got `{actual}`",
                    fixture.id
                ),
            ));
        }
    }
    Ok(())
}

fn validate_fixture_descriptor(fixture: &Fixture) -> Result<()> {
    for (name, value) in [
        ("path", fixture.path.as_deref()),
        ("source_path", fixture.source_path.as_deref()),
        ("spec", fixture.spec.as_deref()),
    ] {
        if let Some(value) = value {
            validate_relative_path(value).map_err(|_| {
                PerfError::harness(format!(
                    "fixture `{}` has invalid {name} `{value}`",
                    fixture.id
                ))
            })?;
        }
    }

    let valid = match (fixture.group, fixture.origin) {
        (FixtureGroup::Bench, FixtureOrigin::TypescriptSuite) => {
            fixture.path.is_some()
                && fixture.sha256.is_some()
                && fixture.bytes.is_some()
                && fixture.source_archive.as_deref() == Some(TYPESCRIPT_SUITE_SOURCE)
                && fixture.source_path.is_some()
                && fixture.spec.is_none()
                && fixture.tree_sha256.is_none()
                && fixture.file_count.is_none()
                && fixture.input_fixture.is_none()
                && fixture.argv.is_empty()
                && fixture.generator.is_none()
                && fixture.params.is_empty()
        }
        (FixtureGroup::Bench, FixtureOrigin::Generated) => {
            fixture.path.is_some()
                && fixture.sha256.is_some()
                && fixture.bytes.is_some()
                && fixture.source_archive.is_none()
                && fixture.source_path.is_none()
                && fixture.spec.is_none()
                && fixture.tree_sha256.is_none()
                && fixture.file_count.is_none()
                && fixture.input_fixture.is_none()
                && fixture.argv.is_empty()
                && fixture.generator.as_deref() == Some("empty-file")
                && fixture.params.is_empty()
        }
        (FixtureGroup::CliStartup, FixtureOrigin::Generated) => {
            fixture.path.is_none()
                && fixture.sha256.is_none()
                && fixture.bytes.is_none()
                && fixture.source_archive.is_none()
                && fixture.source_path.is_none()
                && fixture.spec.is_none()
                && fixture.tree_sha256.is_none()
                && fixture.file_count.is_none()
                && fixture.input_fixture.is_some()
                && !fixture.argv.is_empty()
                && fixture.generator.is_none()
                && fixture.params.is_empty()
        }
        (FixtureGroup::Corpus, FixtureOrigin::Corpus) => {
            fixture.path.is_some()
                && fixture.sha256.is_none()
                && fixture.bytes.is_none()
                && fixture.source_archive.is_none()
                && fixture.source_path.is_none()
                && fixture.spec.is_some()
                && fixture.tree_sha256.is_some()
                && fixture.file_count.is_some()
                && fixture.input_fixture.is_none()
                && fixture.argv.is_empty()
                && fixture.generator.is_none()
                && fixture.params.is_empty()
        }
        (FixtureGroup::Boundary, FixtureOrigin::Generated) => {
            fixture.path.is_some()
                && fixture.sha256.is_some()
                && fixture.bytes.is_some()
                && fixture.source_archive.is_none()
                && fixture.source_path.is_none()
                && fixture.spec.is_none()
                && fixture.tree_sha256.is_none()
                && fixture.file_count.is_none()
                && fixture.input_fixture.is_none()
                && fixture.argv.is_empty()
                && fixture.generator.is_some()
                && !fixture.params.is_empty()
        }
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err(PerfError::harness(format!(
            "fixture `{}` has fields incompatible with group `{:?}` and origin `{:?}`",
            fixture.id, fixture.group, fixture.origin
        )))
    }
}

fn validate_relative_path(relative: &str) -> Result<()> {
    let path = Path::new(relative);
    if relative.is_empty()
        || relative.contains('\\')
        || path.is_absolute()
        || path
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(PerfError::harness(format!(
            "fixture path must be clean and relative: `{relative}`"
        )));
    }
    Ok(())
}

pub(crate) fn checked_root_path(root: &Path, relative: &str) -> Result<PathBuf> {
    validate_relative_path(relative)?;
    let canonical_root = fs::canonicalize(root)
        .map_err(|error| PerfError::harness(format!("{}: {error}", root.display())))?;
    let components: Vec<_> = Path::new(relative).components().collect();
    let mut resolved = canonical_root.clone();
    for (index, component) in components.iter().enumerate() {
        let Component::Normal(part) = component else {
            unreachable!("relative fixture path was validated");
        };
        let candidate = resolved.join(part);
        match fs::symlink_metadata(&candidate) {
            Ok(metadata) => {
                if metadata.file_type().is_symlink() {
                    return Err(PerfError::harness(format!(
                        "fixture path symlink rejected: {}",
                        candidate.display()
                    )));
                }
                resolved = fs::canonicalize(&candidate).map_err(|error| {
                    PerfError::harness(format!("{}: {error}", candidate.display()))
                })?;
                if !resolved.starts_with(&canonical_root) {
                    return Err(PerfError::harness(format!(
                        "fixture path escapes workspace: {}",
                        resolved.display()
                    )));
                }
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                for remaining in &components[index..] {
                    let Component::Normal(part) = remaining else {
                        unreachable!("relative fixture path was validated");
                    };
                    resolved.push(part);
                }
                return Ok(resolved);
            }
            Err(error) => {
                return Err(PerfError::harness(format!(
                    "{}: {error}",
                    candidate.display()
                )));
            }
        }
    }
    Ok(resolved)
}

fn verify_jsx_snapshot_anchor(root: &Path, actual: &str) -> Result<()> {
    let index_path = checked_root_path(root, "verification/ts-suite/index.json")?;
    if !index_path.is_file() {
        return Ok(());
    }
    let text = fs::read_to_string(&index_path)
        .map_err(|error| PerfError::harness(format!("{}: {error}", index_path.display())))?;
    let index: SuiteIndex = serde_json::from_str(&text)
        .map_err(|error| PerfError::harness(format!("{}: {error}", index_path.display())))?;
    let entry = index.entries.get(JSX_SOURCE_PATH).ok_or_else(|| {
        PerfError::harness(format!(
            "suite index is missing JSX fixture anchor `{JSX_SOURCE_PATH}`"
        ))
    })?;
    if entry.sha256 != JSX_SNAPSHOT_SHA256 || actual != JSX_SNAPSHOT_SHA256 {
        return Err(PerfError::new(
            PerfErrorCode::FixtureMismatch,
            format!(
                "{JSX_FIXTURE_ID}: snapshot/archive digest mismatch (index `{}`, archive `{actual}`)",
                entry.sha256
            ),
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, fs};

    use super::*;
    use crate::{perf::Fixture, suite::TempDir};

    #[test]
    fn hash_file_pins_empty_sha256() {
        let temp = TempDir::new("fixture-empty").unwrap();
        let path = temp.path().join("empty.ts");
        fs::write(&path, []).unwrap();
        assert_eq!(
            hash_file(&path).unwrap(),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    #[test]
    fn hash_tree_is_independent_of_creation_order() {
        let left = TempDir::new("fixture-tree-left").unwrap();
        let right = TempDir::new("fixture-tree-right").unwrap();
        fs::create_dir(left.path().join("nested")).unwrap();
        fs::write(left.path().join("z.ts"), b"z").unwrap();
        fs::write(left.path().join("nested/a.ts"), b"a").unwrap();
        fs::create_dir(right.path().join("nested")).unwrap();
        fs::write(right.path().join("nested/a.ts"), b"a").unwrap();
        fs::write(right.path().join("z.ts"), b"z").unwrap();
        assert_eq!(
            hash_tree(left.path()).unwrap(),
            hash_tree(right.path()).unwrap()
        );
    }

    #[cfg(unix)]
    #[test]
    fn hash_tree_rejects_symlinks() {
        use std::os::unix::fs::symlink;
        let temp = TempDir::new("fixture-tree-link").unwrap();
        fs::write(temp.path().join("target"), b"x").unwrap();
        symlink("target", temp.path().join("link")).unwrap();
        assert!(
            hash_tree(temp.path())
                .unwrap_err()
                .detail
                .contains("symlink")
        );
    }

    #[test]
    fn boundary_generator_hashes_are_pinned() {
        let cases = [
            (
                "parser-depth",
                "depth",
                255,
                "164eb3b8c0e2c073235cc59a87f8e91cb6ca7f7430a6836723e352271c8750a9",
            ),
            (
                "parser-depth",
                "depth",
                256,
                "c241d0a70554242147060b7525ac61c570f93c76a056f09d7e331cb214020486",
            ),
            (
                "parser-depth",
                "depth",
                257,
                "e134674115f4a727409d062ae4cc4c62c59b580e36d621146a418bc1e5af7152",
            ),
            (
                "json-depth",
                "depth",
                127,
                "4b59109278cd44ed6ba5df90a136bfffaefa179d7fc0e90bcf85f9c4bfd4a667",
            ),
            (
                "json-depth",
                "depth",
                128,
                "a4908c65856c2fb1e94d6b2b55620177bd082f54d43252b9e0648f9ccd53e3fe",
            ),
            (
                "json-depth",
                "depth",
                129,
                "eeb23e8c9c090d0303063348ae7ca4a5914992972fc20e295e8e386802e2a95a",
            ),
            (
                "source-bytes",
                "size",
                16_777_215,
                "6e4c7fcabfc44a37a7878e6bfb23f450e6df98d77c8162337f5b7a2b8109dd69",
            ),
            (
                "source-bytes",
                "size",
                16_777_216,
                "e65ed8f3de864bcf15529e8f10bc44f75b0419942cc01f461ab183bc20ba325b",
            ),
            (
                "source-bytes",
                "size",
                16_777_217,
                "d8731bdeeb56258ee8eb5c8d46fd1aa2c28f9204590a9d42d8a892129355ddef",
            ),
            (
                "string-units",
                "units",
                1_048_576,
                "5981a8990bfdde21876089d60dcd1929bd691111c9a77ebe65d05bc1439ee18b",
            ),
            (
                "string-units",
                "units",
                1_048_577,
                "1c3f0318b5912f32a0072d1cda4a9318fbcf8dab93595dd567e43a30cf51148b",
            ),
        ];
        for (generator, parameter, value, expected) in cases {
            let params = BTreeMap::from([(parameter.to_owned(), value)]);
            assert_eq!(
                sha256_hex(&generate_boundary(generator, &params).unwrap()),
                expected
            );
        }
    }

    #[test]
    fn verify_fixtures_rejects_missing_required_id() {
        let manifest = BenchmarkManifest {
            schema: 1,
            benchmarks: Vec::new(),
            fixtures: Vec::new(),
        };
        let error = verify_fixtures(Path::new("."), &manifest).unwrap_err();
        assert_eq!(error.code, PerfErrorCode::FixtureMismatch);
        assert!(error.detail.contains("bench-checker-ts"));
    }

    #[test]
    fn verify_fixtures_names_mutated_fixture() {
        let temp = TempDir::new("fixture-mutation").unwrap();
        let path = temp.path().join("fixture.ts");
        fs::write(&path, b"original").unwrap();
        let manifest = BenchmarkManifest {
            schema: 1,
            benchmarks: Vec::new(),
            fixtures: vec![Fixture {
                id: "bench-test".to_owned(),
                group: FixtureGroup::Bench,
                path: Some("fixture.ts".to_owned()),
                sha256: Some(sha256_hex(b"original")),
                bytes: Some(8),
                origin: FixtureOrigin::TypescriptSuite,
                source_archive: Some(TYPESCRIPT_SUITE_SOURCE.to_owned()),
                source_path: Some("src/compiler/checker.ts".to_owned()),
                spec: None,
                tree_sha256: None,
                file_count: None,
                input_fixture: None,
                argv: Vec::new(),
                generator: None,
                params: BTreeMap::new(),
            }],
        };
        validate_fixture_descriptor(&manifest.fixtures[0]).unwrap();
        verify_one(temp.path(), &manifest.fixtures[0]).unwrap();
        fs::write(&path, b"Original").unwrap();
        let error = verify_one(temp.path(), &manifest.fixtures[0]).unwrap_err();
        assert!(error.contains("sha256"));
    }

    #[cfg(unix)]
    #[test]
    fn checked_root_path_rejects_existing_symlink_components() {
        use std::os::unix::fs::symlink;

        let workspace = TempDir::new("fixture-workspace-link").unwrap();
        let outside = TempDir::new("fixture-outside-link").unwrap();
        fs::write(outside.path().join("fixture.ts"), b"outside").unwrap();
        symlink(outside.path(), workspace.path().join("linked")).unwrap();

        let error = checked_root_path(workspace.path(), "linked/fixture.ts").unwrap_err();
        assert!(error.detail.contains("symlink rejected"));
    }

    #[cfg(unix)]
    #[test]
    fn checked_root_path_rejects_symlink_leaf_before_write() {
        use std::os::unix::fs::symlink;

        let workspace = TempDir::new("fixture-workspace-leaf-link").unwrap();
        let outside = TempDir::new("fixture-outside-leaf-link").unwrap();
        let outside_file = outside.path().join("fixture.ts");
        fs::write(&outside_file, b"outside").unwrap();
        symlink(&outside_file, workspace.path().join("fixture.ts")).unwrap();

        assert!(
            checked_root_path(workspace.path(), "fixture.ts")
                .unwrap_err()
                .detail
                .contains("symlink rejected")
        );
        assert_eq!(fs::read(outside_file).unwrap(), b"outside");
    }

    #[test]
    fn checked_root_path_preserves_missing_leaf_materialization() {
        let workspace = TempDir::new("fixture-missing-leaf").unwrap();
        fs::create_dir(workspace.path().join("fixtures")).unwrap();
        let path = checked_root_path(workspace.path(), "fixtures/new/input.ts").unwrap();
        assert!(path.starts_with(fs::canonicalize(workspace.path()).unwrap()));
        assert!(path.ends_with("fixtures/new/input.ts"));
    }

    #[test]
    fn descriptor_validation_accepts_every_pinned_shape() {
        let manifest: BenchmarkManifest =
            toml::from_str(include_str!("../../../perf/benchmarks.toml")).unwrap();
        assert_eq!(manifest.fixtures.len(), REQUIRED_FIXTURES.len());
        require_fixture_contract(&manifest).unwrap();
        for fixture in &manifest.fixtures {
            validate_fixture_descriptor(fixture)
                .unwrap_or_else(|error| panic!("{}: {error}", fixture.id));
        }
    }

    #[test]
    fn exact_descriptor_contract_rejects_destination_and_cli_drift_before_io() {
        let mut manifest: BenchmarkManifest =
            toml::from_str(include_str!("../../../perf/benchmarks.toml")).unwrap();
        manifest
            .fixtures
            .iter_mut()
            .find(|fixture| fixture.id == "bench-checker-ts")
            .unwrap()
            .path = Some("Cargo.toml".to_owned());
        assert!(require_fixture_contract(&manifest).is_err());

        let workspace = TempDir::new("fixture-descriptor-preflight").unwrap();
        assert!(materialize_fixtures(workspace.path(), &manifest).is_err());
        assert!(
            !workspace
                .path()
                .join("verification/ts-suite/.archives")
                .exists()
        );

        let mut manifest: BenchmarkManifest =
            toml::from_str(include_str!("../../../perf/benchmarks.toml")).unwrap();
        let cli = manifest
            .fixtures
            .iter_mut()
            .find(|fixture| fixture.id == "cli-startup-empty")
            .unwrap();
        cli.input_fixture = Some("bench-checker-ts".to_owned());
        assert!(require_fixture_contract(&manifest).is_err());

        let mut manifest: BenchmarkManifest =
            toml::from_str(include_str!("../../../perf/benchmarks.toml")).unwrap();
        manifest
            .fixtures
            .iter_mut()
            .find(|fixture| fixture.id == "cli-startup-empty")
            .unwrap()
            .argv = vec!["check".to_owned()];
        assert!(require_fixture_contract(&manifest).is_err());
    }

    #[test]
    fn descriptor_validation_rejects_missing_and_irrelevant_fields() {
        let mut fixture = Fixture {
            id: "bench-checker-ts".to_owned(),
            group: FixtureGroup::Bench,
            path: Some("perf/fixtures/upstream/checker.ts".to_owned()),
            sha256: Some("digest".to_owned()),
            bytes: Some(1),
            origin: FixtureOrigin::TypescriptSuite,
            source_archive: Some(TYPESCRIPT_SUITE_SOURCE.to_owned()),
            source_path: Some("src/compiler/checker.ts".to_owned()),
            spec: None,
            tree_sha256: None,
            file_count: None,
            input_fixture: None,
            argv: Vec::new(),
            generator: None,
            params: BTreeMap::new(),
        };
        validate_fixture_descriptor(&fixture).unwrap();
        fixture.source_path = None;
        assert!(validate_fixture_descriptor(&fixture).is_err());
        fixture.source_path = Some("../checker.ts".to_owned());
        assert!(validate_fixture_descriptor(&fixture).is_err());
        fixture.source_path = Some("src/compiler/checker.ts".to_owned());
        fixture.generator = Some("empty-file".to_owned());
        assert!(validate_fixture_descriptor(&fixture).is_err());
    }
}
