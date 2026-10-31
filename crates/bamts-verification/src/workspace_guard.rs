use crate::{ErrorCode, Gate, GateReport, Result, VerificationError};
use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io::ErrorKind;
use std::path::{Path, PathBuf};
use std::process::Command;
use toml::{Table, Value};

const MEMBERS: [(&str, &str); 12] = [
    ("bamts-compiler", "crates/bamts-compiler"),
    ("bamts-cancel", "crates/bamts-cancel"),
    ("bamts-platform", "crates/bamts-platform"),
    ("bamts-bytecode", "crates/bamts-bytecode"),
    ("bamts-runtime", "crates/bamts-runtime"),
    ("bamts-native", "crates/bamts-native"),
    ("bamts-node", "crates/bamts-node"),
    ("bamts-codegen", "crates/bamts-codegen"),
    ("bamts-cli", "crates/bamts-cli"),
    ("bamts-napi", "crates/bamts-napi"),
    ("bamts-verification", "crates/bamts-verification"),
    ("bamts", "crates/bamts"),
];

const DEPENDENCY_TABLES: [&str; 3] = ["dependencies", "dev-dependencies", "build-dependencies"];
const WORKSPACE_CHECKS: usize = 15;

#[derive(Debug)]
struct MemberManifest {
    directory: PathBuf,
    manifest_path: PathBuf,
    value: Value,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct InternalDependency {
    optional: bool,
    features: BTreeSet<String>,
}

type InternalGraph = BTreeMap<String, BTreeMap<String, InternalDependency>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VisitState {
    Visiting,
    Complete,
}

#[derive(Debug, Deserialize)]
struct CargoMetadata {
    packages: Vec<CargoPackage>,
    resolve: Option<CargoResolve>,
}

#[derive(Debug, Deserialize)]
struct CargoPackage {
    id: String,
    name: String,
}

#[derive(Debug, Deserialize)]
struct CargoResolve {
    nodes: Vec<CargoNode>,
}

#[derive(Debug, Deserialize)]
struct CargoNode {
    id: String,
    deps: Vec<CargoNodeDependency>,
    features: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct CargoNodeDependency {
    pkg: String,
    dep_kinds: Vec<CargoDependencyKind>,
}

#[derive(Debug, Deserialize)]
struct CargoDependencyKind {
    kind: Option<String>,
}

#[derive(Debug, Default)]
struct ResolvedClosure {
    package_names: BTreeSet<String>,
    package_features: BTreeMap<String, BTreeSet<String>>,
}

pub fn audit_workspace(root: &Path) -> Result<GateReport> {
    let root = fs::canonicalize(root).map_err(|error| {
        VerificationError::new(
            ErrorCode::Io,
            format!(
                "cannot resolve workspace root `{}`: {error}",
                root.display()
            ),
        )
    })?;
    let root_manifest = read_toml(&root.join("Cargo.toml"))?;

    validate_root_manifest(&root_manifest)?;
    validate_workspace_dependencies(&root_manifest)?;

    let members = load_members(&root)?;
    let graph = collect_internal_graph(&members)?;
    validate_internal_graph(&graph)?;
    validate_feature_closures(&root)?;

    Ok(GateReport {
        gate: Gate::G0,
        checks: WORKSPACE_CHECKS,
    })
}

fn read_toml(path: &Path) -> Result<Value> {
    let source = fs::read_to_string(path).map_err(|error| {
        VerificationError::new(
            ErrorCode::Io,
            format!(
                "cannot read workspace manifest `{}`: {error}",
                path.display()
            ),
        )
    })?;

    toml::from_str::<Value>(&source).map_err(|error| {
        VerificationError::new(
            ErrorCode::Toml,
            format!(
                "cannot parse workspace manifest `{}`: {error}",
                path.display()
            ),
        )
    })
}

fn validate_root_manifest(manifest: &Value) -> Result<()> {
    let root = root_table(manifest, "root Cargo.toml")?;
    let workspace = required_table(root, "workspace", "root Cargo.toml")?;

    validate_members(workspace)?;
    require_exact_string(workspace, "resolver", "3", "root [workspace]")?;

    let package = required_table(workspace, "package", "root [workspace]")?;
    require_exact_string(package, "edition", "2024", "root [workspace.package]")?;
    require_exact_string(
        package,
        "rust-version",
        "1.97.1",
        "root [workspace.package]",
    )?;

    let lints = required_table(workspace, "lints", "root [workspace]")?;
    let rust = required_table(lints, "rust", "root [workspace.lints]")?;
    require_exact_string(rust, "unsafe_code", "forbid", "root [workspace.lints.rust]")
}

fn validate_members(workspace: &Table) -> Result<()> {
    let values = match workspace.get("members") {
        Some(Value::Array(values)) => values,
        Some(_) => return Err(workspace_error("root [workspace].members must be an array")),
        None => return Err(workspace_error("root [workspace].members is missing")),
    };

    let mut members = BTreeSet::new();
    let mut duplicates = BTreeSet::new();
    for value in values {
        let member = match value.as_str() {
            Some(member) => member,
            None => {
                return Err(workspace_error(
                    "root [workspace].members must contain only strings",
                ));
            }
        };
        if !members.insert(member.to_owned()) {
            duplicates.insert(member.to_owned());
        }
    }

    if !duplicates.is_empty() {
        return Err(workspace_error(format!(
            "root [workspace].members contains duplicates [{}]",
            format_set(&duplicates)
        )));
    }

    let expected = expected_member_paths();
    if members != expected {
        return Err(workspace_error(format!(
            "root [workspace].members differ: {}",
            set_difference(&expected, &members)
        )));
    }

    Ok(())
}

fn expected_member_paths() -> BTreeSet<String> {
    MEMBERS.iter().map(|(_, path)| (*path).to_owned()).collect()
}

fn validate_workspace_dependencies(manifest: &Value) -> Result<()> {
    let root = root_table(manifest, "root Cargo.toml")?;
    let workspace = required_table(root, "workspace", "root Cargo.toml")?;
    let Some(value) = workspace.get("dependencies") else {
        return Ok(());
    };
    let dependencies = value.as_table().ok_or_else(|| {
        workspace_error("root [workspace.dependencies] must be a dependency table")
    })?;

    for (name, dependency) in sorted_table_entries(dependencies) {
        if is_member_name(name) {
            validate_workspace_internal_dependency(name, dependency)?;
        } else {
            validate_registry_dependency(name, dependency, "root [workspace.dependencies]")?;
        }
    }

    Ok(())
}

fn validate_workspace_internal_dependency(name: &str, dependency: &Value) -> Result<()> {
    let context = format!("root [workspace.dependencies].{name}");
    let attributes = dependency
        .as_table()
        .ok_or_else(|| workspace_error(format!("{context} must be a dependency table")))?;
    for key in attributes.keys() {
        if !matches!(key.as_str(), "path" | "version") {
            return Err(workspace_error(format!(
                "{context} may only declare `path` and `version`"
            )));
        }
    }
    let expected_path = MEMBERS
        .iter()
        .find_map(|(member, path)| (*member == name).then_some(*path))
        .expect("member name was checked");
    require_exact_string(attributes, "path", expected_path, &context)?;
    let version = required_string(attributes, "version", &context)?;
    if version.is_empty() || version.chars().any(char::is_whitespace) {
        return Err(workspace_error(format!(
            "{context}: `version` must be a non-empty version requirement"
        )));
    }
    Ok(())
}

fn load_members(root: &Path) -> Result<BTreeMap<String, MemberManifest>> {
    let mut members = BTreeMap::new();

    for (expected_name, member_path) in MEMBERS {
        let directory = fs::canonicalize(root.join(member_path)).map_err(|error| {
            VerificationError::new(
                ErrorCode::Io,
                format!(
                    "cannot resolve member directory `{}`: {error}",
                    root.join(member_path).display()
                ),
            )
        })?;
        let manifest_path = directory.join("Cargo.toml");
        let value = read_toml(&manifest_path)?;
        validate_member_manifest(expected_name, &value, &manifest_path)?;

        let member = MemberManifest {
            directory,
            manifest_path,
            value,
        };
        if members.insert(expected_name.to_owned(), member).is_some() {
            return Err(workspace_error(format!(
                "member `{expected_name}` was loaded more than once"
            )));
        }
    }

    Ok(members)
}

fn validate_member_manifest(expected_name: &str, manifest: &Value, path: &Path) -> Result<()> {
    let root = root_table(manifest, &path.display().to_string())?;
    let package = required_table(root, "package", &path.display().to_string())?;
    let name = required_string(package, "name", &format!("{} [package]", path.display()))?;
    if name != expected_name {
        return Err(workspace_error(format!(
            "{} declares package `{name}`, expected `{expected_name}`",
            path.display()
        )));
    }

    require_workspace_inheritance(package, "edition", path)?;
    require_workspace_inheritance(package, "rust-version", path)?;
    require_exact_bool(
        package,
        "publish",
        !matches!(expected_name, "bamts-verification" | "bamts-napi"),
        &format!("{} [package]", path.display()),
    )?;
    validate_member_lints(expected_name, manifest, &path.display().to_string())?;

    if expected_name == "bamts-native" {
        validate_native_features(manifest, &path.display().to_string())?;
    } else if expected_name == "bamts-codegen" {
        validate_codegen_features(manifest, &path.display().to_string())?;
    } else if expected_name == "bamts-cli" {
        validate_cli_features(manifest, &path.display().to_string())?;
    } else if expected_name == "bamts-node" {
        validate_node_features(manifest, &path.display().to_string())?;
    } else if expected_name == "bamts" {
        validate_facade_manifest_features(manifest, &path.display().to_string())?;
    }

    Ok(())
}

fn require_workspace_inheritance(package: &Table, key: &str, path: &Path) -> Result<()> {
    let context = format!("{} [package]", path.display());
    let setting = required_table(package, key, &context)?;
    if setting.len() != 1 || setting.get("workspace").and_then(Value::as_bool) != Some(true) {
        return Err(workspace_error(format!(
            "{context}.{key} must be inherited with `{key}.workspace = true`"
        )));
    }

    Ok(())
}

fn validate_member_lints(name: &str, manifest: &Value, context: &str) -> Result<()> {
    let root = root_table(manifest, context)?;
    let lints = required_table(root, "lints", context)?;

    // These crates own tightly-scoped unsafe boundaries, so they pin a local
    // `deny` policy instead of inheriting the workspace-wide `forbid`.
    if matches!(
        name,
        "bamts-native"
            | "bamts-node"
            | "bamts-codegen"
            | "bamts-napi"
            | "bamts-verification"
            | "bamts-platform"
    ) {
        if lints.contains_key("workspace") {
            return Err(workspace_error(format!(
                "{context}: {name} must not inherit workspace lints"
            )));
        }
        let rust = required_table(lints, "rust", context)?;
        if name == "bamts-native" {
            require_exact_string(
                rust,
                "unsafe_op_in_unsafe_fn",
                "deny",
                &format!("{context} [lints.rust]"),
            )?;
            if rust.contains_key("unsafe_code") {
                return Err(workspace_error(format!(
                    "{context}: bamts-native must not override `unsafe_code`"
                )));
            }
        } else {
            require_exact_string(
                rust,
                "unsafe_code",
                "deny",
                &format!("{context} [lints.rust]"),
            )?;
            if matches!(
                name,
                "bamts-codegen" | "bamts-napi" | "bamts-verification" | "bamts-platform"
            ) {
                require_exact_string(
                    rust,
                    "unsafe_op_in_unsafe_fn",
                    "deny",
                    &format!("{context} [lints.rust]"),
                )?;
            }
        }
        return Ok(());
    }

    if lints.get("workspace").and_then(Value::as_bool) != Some(true) {
        return Err(workspace_error(format!(
            "{context}: {name} must inherit workspace lints"
        )));
    }

    if let Some(rust) = lints.get("rust") {
        let rust = rust
            .as_table()
            .ok_or_else(|| workspace_error(format!("{context}: [lints.rust] must be a table")))?;
        if rust.contains_key("unsafe_code") {
            return Err(workspace_error(format!(
                "{context}: {name} must inherit the workspace `unsafe_code` policy"
            )));
        }
    }

    Ok(())
}

fn validate_native_features(manifest: &Value, context: &str) -> Result<()> {
    let root = root_table(manifest, context)?;
    let features = required_table(root, "features", context)?;
    let expected: BTreeSet<String> = [
        "default",
        "gc",
        "node-host",
        "jit-entry",
        "aot-image",
        "cache-guard",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    let actual: BTreeSet<String> = features.keys().cloned().collect();
    if actual != expected {
        return Err(workspace_error(format!(
            "{context}: bamts-native features differ: {}",
            set_difference(&expected, &actual)
        )));
    }

    for feature in ["default", "gc", "node-host", "aot-image"] {
        require_feature_set(features, feature, &[], context)?;
    }
    // `jit-entry` owns the JIT-only Cranelift dependencies so the AOT and
    // interpreter closures never pull an executable-memory provider.
    require_feature_set(
        features,
        "jit-entry",
        &["dep:cranelift-jit", "dep:cranelift-module"],
        context,
    )?;
    require_feature_set(features, "cache-guard", &["dep:windows"], context)?;

    Ok(())
}

fn validate_codegen_features(manifest: &Value, context: &str) -> Result<()> {
    let root = root_table(manifest, context)?;
    let features = required_table(root, "features", context)?;
    let expected_keys: BTreeSet<String> = ["default", "aot", "host-jit"]
        .into_iter()
        .map(str::to_owned)
        .collect();
    let actual_keys: BTreeSet<String> = features.keys().cloned().collect();
    if actual_keys != expected_keys {
        return Err(workspace_error(format!(
            "{context}: bamts-codegen features differ: {}",
            set_difference(&expected_keys, &actual_keys)
        )));
    }

    let default = parse_feature_set(features, "default", context)?;
    let aot = parse_feature_set(features, "aot", context)?;
    let host_jit = parse_feature_set(features, "host-jit", context)?;
    if !aot.is_disjoint(&host_jit) {
        let overlap: BTreeSet<String> = aot.intersection(&host_jit).cloned().collect();
        let allowed: BTreeSet<String> = ["dep:bamts-native"]
            .into_iter()
            .map(str::to_owned)
            .collect();
        if overlap != allowed {
            return Err(workspace_error(format!(
                "{context}: bamts-codegen `aot` and `host-jit` overlap [{}]",
                format_set(&overlap)
            )));
        }
    }

    require_exact_feature_set("default", &default, &[], context)?;
    require_exact_feature_set(
        "aot",
        &aot,
        &["dep:bamts-native", "dep:cranelift-object", "dep:sha2"],
        context,
    )?;
    require_exact_feature_set(
        "host-jit",
        &host_jit,
        &[
            "dep:bamts-native",
            "bamts-native/jit-entry",
            "dep:cranelift-jit",
            "dep:libc",
            "dep:region",
            "dep:wasmtime-internal-jit-icache-coherence",
        ],
        context,
    )
}

/// `bamts-node` keeps compiler and native capabilities behind explicit
/// features so its default host does not pull the frontend or AOT image reader.
fn validate_node_features(manifest: &Value, context: &str) -> Result<()> {
    let root = root_table(manifest, context)?;
    let features = required_table(root, "features", context)?;
    let expected_keys: BTreeSet<String> = ["default", "node-host", "script-compiler", "aot-main"]
        .into_iter()
        .map(str::to_owned)
        .collect();
    let actual_keys: BTreeSet<String> = features.keys().cloned().collect();
    if actual_keys != expected_keys {
        return Err(workspace_error(format!(
            "{context}: bamts-node features differ: {}",
            set_difference(&expected_keys, &actual_keys)
        )));
    }

    require_feature_set(features, "default", &["node-host"], context)?;
    require_feature_set(features, "node-host", &["bamts-native/node-host"], context)?;
    require_feature_set(
        features,
        "script-compiler",
        &["dep:bamts-compiler", "dep:bamts-bytecode"],
        context,
    )?;
    require_feature_set(
        features,
        "aot-main",
        &["node-host", "dep:bamts-bytecode", "bamts-native/aot-image"],
        context,
    )
}

fn validate_cli_features(manifest: &Value, context: &str) -> Result<()> {
    let root = root_table(manifest, context)?;
    if root.contains_key("features") {
        return Err(workspace_error(format!(
            "{context}: bamts-cli exposes no optional feature surface"
        )));
    }
    let bins = root
        .get("bin")
        .and_then(Value::as_array)
        .ok_or_else(|| workspace_error(format!("{context}: bamts-cli must declare [[bin]]")))?;
    if bins.len() != 1 {
        return Err(workspace_error(format!(
            "{context}: bamts-cli must declare exactly one binary"
        )));
    }
    let binary = bins[0]
        .as_table()
        .ok_or_else(|| workspace_error(format!("{context}: [[bin]] must be a table")))?;
    if required_string(binary, "name", context)? != "bamts"
        || required_string(binary, "path", context)? != "src/main.rs"
    {
        return Err(workspace_error(format!(
            "{context}: bamts-cli binary must be `bamts` at `src/main.rs`"
        )));
    }
    Ok(())
}

fn validate_facade_manifest_features(manifest: &Value, context: &str) -> Result<()> {
    let root = root_table(manifest, context)?;
    let features = required_table(root, "features", context)?;
    let expected_keys: BTreeSet<String> = ["default", "aot", "host-jit", "node-host"]
        .into_iter()
        .map(str::to_owned)
        .collect();
    let actual_keys: BTreeSet<String> = features.keys().cloned().collect();
    if actual_keys != expected_keys {
        return Err(workspace_error(format!(
            "{context}: bamts features differ: {}",
            set_difference(&expected_keys, &actual_keys)
        )));
    }

    require_feature_set(features, "default", &[], context)?;
    require_feature_set(
        features,
        "aot",
        &["dep:bamts-codegen", "bamts-codegen/aot"],
        context,
    )?;
    require_feature_set(
        features,
        "host-jit",
        &["dep:bamts-codegen", "bamts-codegen/host-jit"],
        context,
    )?;
    require_feature_set(
        features,
        "node-host",
        &[
            "dep:bamts-node",
            "bamts-node/node-host",
            "bamts-node/script-compiler",
        ],
        context,
    )
}

fn require_feature_set(
    features: &Table,
    feature: &str,
    expected: &[&str],
    context: &str,
) -> Result<()> {
    let actual = parse_feature_set(features, feature, context)?;
    require_exact_feature_set(feature, &actual, expected, context)
}

fn require_exact_feature_set(
    feature: &str,
    actual: &BTreeSet<String>,
    expected: &[&str],
    context: &str,
) -> Result<()> {
    let expected: BTreeSet<String> = expected.iter().map(|value| (*value).to_owned()).collect();
    if actual != &expected {
        return Err(workspace_error(format!(
            "{context}: feature `{feature}` differs: {}",
            set_difference(&expected, actual)
        )));
    }

    Ok(())
}

fn parse_feature_set(features: &Table, feature: &str, context: &str) -> Result<BTreeSet<String>> {
    let values = match features.get(feature) {
        Some(Value::Array(values)) => values,
        Some(_) => {
            return Err(workspace_error(format!(
                "{context}: feature `{feature}` must be an array"
            )));
        }
        None => {
            return Err(workspace_error(format!(
                "{context}: feature `{feature}` is missing"
            )));
        }
    };

    parse_string_set(values, &format!("{context}: feature `{feature}`"))
}

fn collect_internal_graph(members: &BTreeMap<String, MemberManifest>) -> Result<InternalGraph> {
    let mut member_directories = BTreeMap::new();
    for (name, member) in members {
        if member_directories
            .insert(member.directory.clone(), name.clone())
            .is_some()
        {
            return Err(workspace_error(format!(
                "members resolve to the same directory `{}`",
                member.directory.display()
            )));
        }
    }

    let mut graph = BTreeMap::new();
    for (name, member) in members {
        let mut dependencies = BTreeMap::new();
        inspect_member_dependencies(member, &member_directories, &mut dependencies)?;
        graph.insert(name.clone(), dependencies);
    }

    Ok(graph)
}

fn inspect_member_dependencies(
    member: &MemberManifest,
    member_directories: &BTreeMap<PathBuf, String>,
    edges: &mut BTreeMap<String, InternalDependency>,
) -> Result<()> {
    let root = root_table(&member.value, &member.manifest_path.display().to_string())?;

    for table_name in DEPENDENCY_TABLES {
        if let Some(value) = root.get(table_name) {
            let table = value.as_table().ok_or_else(|| {
                workspace_error(format!(
                    "{}: [{table_name}] must be a dependency table",
                    member.manifest_path.display()
                ))
            })?;
            inspect_dependency_table(member, table, member_directories, edges)?;
        }
    }

    let Some(targets) = root.get("target") else {
        return Ok(());
    };
    let targets = targets.as_table().ok_or_else(|| {
        workspace_error(format!(
            "{}: [target] must be a table",
            member.manifest_path.display()
        ))
    })?;

    for (target_name, target) in sorted_table_entries(targets) {
        let target = target.as_table().ok_or_else(|| {
            workspace_error(format!(
                "{}: [target.{target_name:?}] must be a table",
                member.manifest_path.display()
            ))
        })?;
        for table_name in DEPENDENCY_TABLES {
            if let Some(value) = target.get(table_name) {
                let table = value.as_table().ok_or_else(|| {
                    workspace_error(format!(
                        "{}: [target.{target_name:?}.{table_name}] must be a dependency table",
                        member.manifest_path.display()
                    ))
                })?;
                inspect_dependency_table(member, table, member_directories, edges)?;
            }
        }
    }

    Ok(())
}

fn inspect_dependency_table(
    member: &MemberManifest,
    dependencies: &Table,
    member_directories: &BTreeMap<PathBuf, String>,
    edges: &mut BTreeMap<String, InternalDependency>,
) -> Result<()> {
    for (name, dependency) in sorted_table_entries(dependencies) {
        let Some(table) = dependency.as_table() else {
            validate_registry_dependency(
                name,
                dependency,
                &member.manifest_path.display().to_string(),
            )?;
            continue;
        };

        if table.contains_key("path") {
            inspect_internal_dependency(member, name, table, member_directories, edges)?;
        } else if is_member_name(name) && table.contains_key("workspace") {
            inspect_workspace_internal_dependency(member, name, table, edges)?;
        } else {
            validate_registry_dependency(
                name,
                dependency,
                &member.manifest_path.display().to_string(),
            )?;
        }
    }

    Ok(())
}

fn inspect_internal_dependency(
    member: &MemberManifest,
    dependency_name: &str,
    attributes: &Table,
    member_directories: &BTreeMap<PathBuf, String>,
    edges: &mut BTreeMap<String, InternalDependency>,
) -> Result<()> {
    let context = format!(
        "{} dependency `{dependency_name}`",
        member.manifest_path.display()
    );
    for key in attributes.keys() {
        if !matches!(key.as_str(), "path" | "version" | "optional" | "features") {
            return Err(workspace_error(format!(
                "{context}: internal dependencies may only declare `path`, `version`, `optional`, and `features`"
            )));
        }
    }

    let path = required_string(attributes, "path", &context)?;
    let directory = fs::canonicalize(member.directory.join(path)).map_err(|error| {
        VerificationError::new(
            ErrorCode::Io,
            format!("{context}: cannot resolve path dependency `{path}`: {error}"),
        )
    })?;
    let target = member_directories.get(&directory).ok_or_else(|| {
        workspace_error(format!(
            "{context}: path dependency `{path}` does not resolve to an approved member"
        ))
    })?;
    if target.as_str() != dependency_name {
        return Err(workspace_error(format!(
            "{context}: dependency key must be `{target}`"
        )));
    }

    let dependency = InternalDependency {
        optional: optional_bool(attributes, "optional", &context)?,
        features: optional_feature_set(attributes, "features", &context)?,
    };
    if let Some(existing) = edges.get_mut(target) {
        existing.optional &= dependency.optional;
        existing.features.extend(dependency.features);
    } else {
        edges.insert(target.clone(), dependency);
    }

    Ok(())
}

fn inspect_workspace_internal_dependency(
    member: &MemberManifest,
    dependency_name: &str,
    attributes: &Table,
    edges: &mut BTreeMap<String, InternalDependency>,
) -> Result<()> {
    let context = format!(
        "{} dependency `{dependency_name}`",
        member.manifest_path.display()
    );
    for key in attributes.keys() {
        if !matches!(key.as_str(), "workspace" | "optional" | "features") {
            return Err(workspace_error(format!(
                "{context}: inherited internal dependencies may only declare `workspace`, `optional`, and `features`"
            )));
        }
    }
    require_exact_bool(attributes, "workspace", true, &context)?;
    let dependency = InternalDependency {
        optional: optional_bool(attributes, "optional", &context)?,
        features: optional_feature_set(attributes, "features", &context)?,
    };
    if let Some(existing) = edges.get_mut(dependency_name) {
        existing.optional &= dependency.optional;
        existing.features.extend(dependency.features);
    } else {
        edges.insert(dependency_name.to_owned(), dependency);
    }
    Ok(())
}

fn validate_registry_dependency(name: &str, dependency: &Value, context: &str) -> Result<()> {
    if is_member_name(name) {
        return Err(workspace_error(format!(
            "{context}: internal dependency `{name}` must use an approved path dependency"
        )));
    }

    match dependency {
        Value::String(version) => validate_registry_version(name, version, context),
        Value::Table(attributes) => {
            if attributes.contains_key("path") {
                return Err(workspace_error(format!(
                    "{context}: path dependency `{name}` does not resolve to an approved member"
                )));
            }
            if attributes.contains_key("workspace") {
                return Err(workspace_error(format!(
                    "{context}: dependency `{name}` must declare a registry version requirement directly"
                )));
            }
            if attributes.contains_key("git") {
                return Err(workspace_error(format!(
                    "{context}: dependency `{name}` must use a registry version requirement, not `git`"
                )));
            }

            let version = required_string(attributes, "version", context)?;
            validate_registry_version(name, version, context)?;
            optional_bool(attributes, "optional", context)?;
            optional_feature_set(attributes, "features", context)?;
            Ok(())
        }
        _ => Err(workspace_error(format!(
            "{context}: dependency `{name}` must be a version string or table"
        ))),
    }
}

fn validate_registry_version(name: &str, version: &str, context: &str) -> Result<()> {
    // Registry dependencies declare either a compatible caret requirement —
    // the Cargo default, a bare `X.Y[.Z]` that accepts compatible upgrades —
    // or an exact `=X.Y[.Z]` pin for private/tooling crates that must not
    // float. Wildcards (`*`, `1.*`), tilde (`~`), comparator ranges (`>`,
    // `<`, `>=`, `<=`), and multi-spec ranges (`,`) are unreviewed
    // constraints and remain rejected.
    let requirement = version.strip_prefix('=').unwrap_or(version);

    if requirement.is_empty() || requirement.chars().any(char::is_whitespace) {
        return Err(workspace_error(format!(
            "{context}: registry dependency `{name}` must use a non-empty version requirement, found `{version}`"
        )));
    }

    if requirement.contains('*') {
        return Err(workspace_error(format!(
            "{context}: registry dependency `{name}` must not use a wildcard version requirement, found `{version}`"
        )));
    }

    let component_count = requirement.bytes().filter(|byte| *byte == b'.').count() + 1;
    let plain_semver = (2..=3).contains(&component_count)
        && requirement.split('.').all(|component| {
            !component.is_empty()
                && (component == "0" || !component.starts_with('0'))
                && component.parse::<u64>().is_ok()
        });
    if !plain_semver {
        return Err(workspace_error(format!(
            "{context}: registry dependency `{name}` must use a compatible caret requirement (`X.Y[.Z]`) or exact `=` pin, found `{version}`"
        )));
    }

    Ok(())
}

fn is_member_name(name: &str) -> bool {
    MEMBERS.iter().any(|(member, _)| *member == name)
}

fn optional_bool(table: &Table, key: &str, context: &str) -> Result<bool> {
    match table.get(key) {
        None => Ok(false),
        Some(Value::Boolean(value)) => Ok(*value),
        Some(_) => Err(workspace_error(format!(
            "{context}: `{key}` must be a boolean"
        ))),
    }
}

fn optional_feature_set(table: &Table, key: &str, context: &str) -> Result<BTreeSet<String>> {
    match table.get(key) {
        None => Ok(BTreeSet::new()),
        Some(Value::Array(values)) => parse_string_set(values, &format!("{context}: `{key}`")),
        Some(_) => Err(workspace_error(format!(
            "{context}: `{key}` must be an array"
        ))),
    }
}

fn parse_string_set(values: &[Value], context: &str) -> Result<BTreeSet<String>> {
    let mut parsed = BTreeSet::new();
    for value in values {
        let value = value
            .as_str()
            .ok_or_else(|| workspace_error(format!("{context} must contain only strings")))?;
        if value.is_empty() {
            return Err(workspace_error(format!(
                "{context} must not contain empty strings"
            )));
        }
        if !parsed.insert(value.to_owned()) {
            return Err(workspace_error(format!(
                "{context} contains duplicate `{value}`"
            )));
        }
    }

    Ok(parsed)
}

fn validate_internal_graph(graph: &InternalGraph) -> Result<()> {
    ensure_acyclic(graph)?;

    let expected = expected_internal_graph();
    let actual_members: BTreeSet<String> = graph.keys().cloned().collect();
    let expected_members: BTreeSet<String> = expected.keys().cloned().collect();
    if actual_members != expected_members {
        return Err(workspace_error(format!(
            "internal dependency graph members differ: {}",
            set_difference(&expected_members, &actual_members)
        )));
    }

    for (owner, expected_dependencies) in &expected {
        let actual_dependencies = graph
            .get(owner)
            .ok_or_else(|| workspace_error(format!("internal dependency graph lacks `{owner}`")))?;
        let actual_targets: BTreeSet<String> = actual_dependencies.keys().cloned().collect();
        let expected_targets: BTreeSet<String> = expected_dependencies.keys().cloned().collect();
        if actual_targets != expected_targets {
            return Err(workspace_error(format!(
                "internal dependencies of `{owner}` differ: {}",
                set_difference(&expected_targets, &actual_targets)
            )));
        }

        for (target, expected_attributes) in expected_dependencies {
            let actual_attributes = actual_dependencies.get(target).ok_or_else(|| {
                workspace_error(format!(
                    "internal dependency `{owner}` -> `{target}` is missing"
                ))
            })?;
            if actual_attributes != expected_attributes {
                return Err(workspace_error(format!(
                    "internal dependency `{owner}` -> `{target}` has {}, expected {}",
                    format_internal_dependency(actual_attributes),
                    format_internal_dependency(expected_attributes)
                )));
            }
        }
    }

    Ok(())
}

fn expected_internal_graph() -> InternalGraph {
    let mut graph = BTreeMap::new();
    graph.insert("bamts-bytecode".to_owned(), BTreeMap::new());
    graph.insert("bamts-cancel".to_owned(), BTreeMap::new());
    graph.insert("bamts-platform".to_owned(), BTreeMap::new());
    graph.insert(
        "bamts-native".to_owned(),
        BTreeMap::from([("bamts-bytecode".to_owned(), internal_dependency(false, &[]))]),
    );
    graph.insert(
        "bamts-compiler".to_owned(),
        BTreeMap::from([
            ("bamts-bytecode".to_owned(), internal_dependency(false, &[])),
            ("bamts-cancel".to_owned(), internal_dependency(false, &[])),
        ]),
    );
    graph.insert(
        "bamts-runtime".to_owned(),
        BTreeMap::from([
            ("bamts-bytecode".to_owned(), internal_dependency(false, &[])),
            ("bamts-cancel".to_owned(), internal_dependency(false, &[])),
            (
                "bamts-native".to_owned(),
                internal_dependency(false, &["gc"]),
            ),
            ("bamts-platform".to_owned(), internal_dependency(false, &[])),
        ]),
    );
    graph.insert(
        "bamts-node".to_owned(),
        BTreeMap::from([
            ("bamts-runtime".to_owned(), internal_dependency(false, &[])),
            ("bamts-compiler".to_owned(), internal_dependency(true, &[])),
            ("bamts-native".to_owned(), internal_dependency(false, &[])),
            // Enabled only by `aot-main`, which decodes the canonical bytecode
            // embedded in a linked AOT image before handing it to the engine.
            ("bamts-bytecode".to_owned(), internal_dependency(true, &[])),
        ]),
    );
    graph.insert(
        "bamts-codegen".to_owned(),
        BTreeMap::from([
            ("bamts-bytecode".to_owned(), internal_dependency(false, &[])),
            ("bamts-cancel".to_owned(), internal_dependency(false, &[])),
            ("bamts-platform".to_owned(), internal_dependency(false, &[])),
            ("bamts-runtime".to_owned(), internal_dependency(false, &[])),
            ("bamts-native".to_owned(), internal_dependency(true, &[])),
        ]),
    );
    graph.insert(
        "bamts".to_owned(),
        BTreeMap::from([
            ("bamts-bytecode".to_owned(), internal_dependency(false, &[])),
            ("bamts-cancel".to_owned(), internal_dependency(false, &[])),
            ("bamts-codegen".to_owned(), internal_dependency(true, &[])),
            ("bamts-compiler".to_owned(), internal_dependency(false, &[])),
            ("bamts-node".to_owned(), internal_dependency(true, &[])),
            ("bamts-runtime".to_owned(), internal_dependency(false, &[])),
        ]),
    );
    graph.insert(
        "bamts-cli".to_owned(),
        BTreeMap::from([
            (
                "bamts".to_owned(),
                internal_dependency(false, &["node-host"]),
            ),
            ("bamts-compiler".to_owned(), internal_dependency(false, &[])),
            ("bamts-runtime".to_owned(), internal_dependency(false, &[])),
            (
                "bamts-codegen".to_owned(),
                internal_dependency(false, &["aot", "host-jit"]),
            ),
            (
                "bamts-node".to_owned(),
                internal_dependency(false, &["aot-main", "script-compiler"]),
            ),
        ]),
    );
    graph.insert(
        "bamts-napi".to_owned(),
        BTreeMap::from([
            ("bamts-cancel".to_owned(), internal_dependency(false, &[])),
            ("bamts-cli".to_owned(), internal_dependency(false, &[])),
        ]),
    );
    graph.insert(
        "bamts-verification".to_owned(),
        BTreeMap::from([
            (
                "bamts".to_owned(),
                internal_dependency(false, &["aot", "host-jit"]),
            ),
            ("bamts-bytecode".to_owned(), internal_dependency(false, &[])),
            ("bamts-cli".to_owned(), internal_dependency(false, &[])),
            ("bamts-codegen".to_owned(), internal_dependency(false, &[])),
            ("bamts-compiler".to_owned(), internal_dependency(false, &[])),
            ("bamts-native".to_owned(), internal_dependency(false, &[])),
            (
                "bamts-node".to_owned(),
                internal_dependency(false, &["script-compiler"]),
            ),
            ("bamts-platform".to_owned(), internal_dependency(false, &[])),
            ("bamts-runtime".to_owned(), internal_dependency(false, &[])),
        ]),
    );
    graph
}

fn internal_dependency(optional: bool, features: &[&str]) -> InternalDependency {
    InternalDependency {
        optional,
        features: features
            .iter()
            .map(|feature| (*feature).to_owned())
            .collect(),
    }
}

fn ensure_acyclic(graph: &InternalGraph) -> Result<()> {
    let mut states = BTreeMap::new();
    let mut stack = Vec::new();

    for node in graph.keys() {
        if states.get(node).copied() == Some(VisitState::Complete) {
            continue;
        }
        visit_graph(node, graph, &mut states, &mut stack)?;
    }

    Ok(())
}

fn visit_graph(
    node: &str,
    graph: &InternalGraph,
    states: &mut BTreeMap<String, VisitState>,
    stack: &mut Vec<String>,
) -> Result<()> {
    states.insert(node.to_owned(), VisitState::Visiting);
    stack.push(node.to_owned());

    let dependencies = graph
        .get(node)
        .ok_or_else(|| workspace_error(format!("internal dependency graph lacks node `{node}`")))?;
    for dependency in dependencies.keys() {
        match states.get(dependency).copied() {
            Some(VisitState::Complete) => {}
            Some(VisitState::Visiting) => {
                let position = stack
                    .iter()
                    .position(|entry| entry == dependency)
                    .ok_or_else(|| {
                        workspace_error(format!(
                            "internal dependency graph lost cycle origin `{dependency}`"
                        ))
                    })?;
                let mut cycle = stack[position..].to_vec();
                cycle.push(dependency.clone());
                return Err(workspace_error(format!(
                    "internal dependency graph contains cycle {}",
                    cycle.join(" -> ")
                )));
            }
            None => visit_graph(dependency, graph, states, stack)?,
        }
    }

    let _ = stack.pop();
    states.insert(node.to_owned(), VisitState::Complete);
    Ok(())
}

fn validate_feature_closures(root: &Path) -> Result<()> {
    // Positive check: unified workspace metadata closure.
    let metadata = cargo_metadata(root, None)?;
    let closure = codegen_closure(&metadata)?;
    require_enabled_feature(&closure, "bamts-cli", "aot")?;
    require_enabled_feature(&closure, "bamts-cli", "host-jit")?;
    require_present_package(&closure, "bamts-cli", "cranelift-object")?;
    require_present_package(&closure, "bamts-cli", "cranelift-jit")?;
    require_present_package(&closure, "bamts-cli", "bamts-native")?;

    // Package-selected closure checks via `cargo tree`.
    //
    // Executable-memory packages that must only appear behind `host-jit` or
    // `jit-entry` features:
    let exec_memory: &[&str] = &[
        "cranelift-jit",
        "region",
        "wasmtime-internal-jit-icache-coherence",
    ];

    // ── bamts-codegen default ────────────────────────────────────────────
    let names = cargo_tree_package_names(root, "bamts-codegen", &[])?;
    assert_forbidden_packages("bamts-codegen default", &names, exec_memory)?;

    // ── bamts-codegen/aot ───────────────────────────────────────────────
    let names = cargo_tree_package_names(root, "bamts-codegen", &["aot"])?;
    assert_present_packages("bamts-codegen/aot", &names, &["cranelift-object"])?;
    assert_forbidden_packages("bamts-codegen/aot", &names, exec_memory)?;

    // ── bamts-codegen/host-jit ───────────────────────────────────────────
    let names = cargo_tree_package_names(root, "bamts-codegen", &["host-jit"])?;
    assert_present_packages(
        "bamts-codegen/host-jit",
        &names,
        &[
            "bamts-native",
            "cranelift-jit",
            "region",
            "wasmtime-internal-jit-icache-coherence",
        ],
    )?;
    assert_forbidden_packages("bamts-codegen/host-jit", &names, &["cranelift-object"])?;

    // ── bamts-native non-JIT closures ────────────────────────────────────
    for (label, features) in [
        ("bamts-native default", &[][..]),
        ("bamts-native/gc", &["gc"][..]),
        ("bamts-native/node-host", &["node-host"][..]),
        ("bamts-native/aot-image", &["aot-image"][..]),
    ] {
        let names = cargo_tree_package_names(root, "bamts-native", features)?;
        assert_forbidden_packages(label, &names, exec_memory)?;
    }

    // ── bamts-native/jit-entry ───────────────────────────────────────────
    let names = cargo_tree_package_names(root, "bamts-native", &["jit-entry"])?;
    assert_present_packages(
        "bamts-native/jit-entry",
        &names,
        &["cranelift-jit", "cranelift-module"],
    )?;

    // ── bamts non-JIT closures ───────────────────────────────────────────
    let names = cargo_tree_package_names(root, "bamts", &[])?;
    assert_forbidden_packages("bamts default", &names, exec_memory)?;
    assert_forbidden_packages("bamts default", &names, &["bamts-codegen"])?;

    let names = cargo_tree_package_names(root, "bamts", &["aot"])?;
    assert_present_packages("bamts/aot", &names, &["bamts-codegen", "cranelift-object"])?;
    assert_forbidden_packages("bamts/aot", &names, exec_memory)?;

    let names = cargo_tree_package_names(root, "bamts", &["node-host"])?;
    assert_present_packages("bamts/node-host", &names, &["bamts-node"])?;
    assert_forbidden_packages("bamts/node-host", &names, exec_memory)?;
    assert_forbidden_packages(
        "bamts/node-host",
        &names,
        &["bamts-codegen", "cranelift-object"],
    )?;

    // ── bamts/host-jit ──────────────────────────────────────────────────
    let names = cargo_tree_package_names(root, "bamts", &["host-jit"])?;
    assert_present_packages(
        "bamts/host-jit",
        &names,
        &[
            "bamts-codegen",
            "bamts-native",
            "cranelift-jit",
            "region",
            "wasmtime-internal-jit-icache-coherence",
        ],
    )?;

    assert_forbidden_packages("bamts/host-jit", &names, &["cranelift-object"])?;
    // Feature activation: resolve closures through the correct root
    // package so that feature flags on dependencies are captured accurately.
    //
    // `bamts-codegen/host-jit`: host-jit is a feature of bamts-codegen, so
    // cargo_metadata + codegen_closure resolves correctly from bamts-codegen.
    let meta = cargo_metadata(root, Some("bamts-codegen/host-jit"))?;
    let closure = codegen_closure(&meta)?;
    require_enabled_feature(&closure, "bamts-codegen/host-jit", "host-jit")?;
    // `bamts-native/jit-entry` is activated transitively by
    // `bamts-codegen/host-jit`; verify it on bamts-native's features.
    let native_features = closure
        .package_features
        .get("bamts-native")
        .ok_or_else(|| {
            workspace_error("bamts-codegen/host-jit closure does not contain bamts-native features")
        })?;
    if !native_features.contains("jit-entry") {
        return Err(workspace_error(
            "bamts-codegen/host-jit closure does not enable bamts-native/jit-entry",
        ));
    }

    // `bamts/host-jit`: host-jit is a feature of bamts (the facade), so we
    // must resolve from `bamts`, not `bamts-codegen`.
    let meta = cargo_metadata(root, Some("bamts/host-jit"))?;
    let closure = resolve_closure_from(&meta, "bamts")?;
    // Verify host-jit reaches bamts-codegen with host-jit enabled.
    let codegen_features = closure
        .package_features
        .get("bamts-codegen")
        .ok_or_else(|| {
            workspace_error("bamts/host-jit closure does not contain bamts-codegen features")
        })?;
    if !codegen_features.contains("host-jit") {
        return Err(workspace_error(
            "bamts/host-jit closure does not enable bamts-codegen/host-jit",
        ));
    }

    Ok(())
}

fn cargo_metadata(root: &Path, feature: Option<&str>) -> Result<CargoMetadata> {
    let cargo = match env::var_os("CARGO") {
        Some(path) => path,
        None => "cargo".into(),
    };
    let mut command = Command::new(cargo);
    command
        .current_dir(root)
        .arg("metadata")
        .arg("--format-version")
        .arg("1")
        .arg("--locked")
        .arg("--offline")
        .arg("--no-default-features");
    if let Some(feature) = feature {
        command.arg("--features").arg(feature);
    }

    let output = command.output().map_err(|error| {
        let code = if error.kind() == ErrorKind::NotFound {
            ErrorCode::ToolMissing
        } else {
            ErrorCode::ToolFailed
        };
        VerificationError::new(code, format!("cargo metadata could not start: {error}"))
    })?;
    if !output.status.success() {
        let status = match output.status.code() {
            Some(code) => format!("exit status {code}"),
            None => "terminated by signal".to_owned(),
        };
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stderr = stderr.trim();
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!("cargo metadata {status}: {stderr}"),
        ));
    }

    serde_json::from_slice(&output.stdout).map_err(|error| {
        VerificationError::new(
            ErrorCode::Json,
            format!("cargo metadata emitted invalid JSON: {error}"),
        )
    })
}

fn codegen_closure(metadata: &CargoMetadata) -> Result<ResolvedClosure> {
    resolve_closure_from(metadata, "bamts-codegen")
}

fn require_enabled_feature(closure: &ResolvedClosure, mode: &str, feature: &str) -> Result<()> {
    let active = closure
        .package_features
        .get("bamts-codegen")
        .ok_or_else(|| workspace_error("codegen closure lacks bamts-codegen features"))?;
    if !active.contains(feature) {
        return Err(workspace_error(format!(
            "{mode} metadata closure does not enable bamts-codegen feature `{feature}`"
        )));
    }

    Ok(())
}

fn require_present_package(closure: &ResolvedClosure, mode: &str, package: &str) -> Result<()> {
    if !closure.package_names.contains(package) {
        return Err(workspace_error(format!(
            "{mode} metadata closure does not reach `{package}`"
        )));
    }

    Ok(())
}

/// Resolve the package-closure from the given root, returning package names
/// and their enabled features.
fn resolve_closure_from(metadata: &CargoMetadata, root_name: &str) -> Result<ResolvedClosure> {
    let resolve = metadata
        .resolve
        .as_ref()
        .ok_or_else(|| workspace_error("cargo metadata did not include a resolve graph"))?;
    let mut packages = BTreeMap::new();
    let mut root = None;
    for package in &metadata.packages {
        if packages
            .insert(package.id.as_str(), package.name.as_str())
            .is_some()
        {
            return Err(workspace_error(format!(
                "cargo metadata contains duplicate package id `{}`",
                package.id
            )));
        }
        if package.name == root_name && root.replace(package.id.as_str()).is_some() {
            return Err(workspace_error(format!(
                "cargo metadata contains multiple {root_name} packages",
            )));
        }
    }
    let root = root
        .ok_or_else(|| workspace_error(format!("cargo metadata does not contain {root_name}")))?;

    let mut nodes = BTreeMap::new();
    for node in &resolve.nodes {
        if nodes.insert(node.id.as_str(), node).is_some() {
            return Err(workspace_error(format!(
                "cargo metadata contains duplicate resolve node `{}`",
                node.id
            )));
        }
    }

    let mut closure = ResolvedClosure::default();
    let mut pending = vec![root];
    let mut visited = BTreeSet::new();
    while let Some(package_id) = pending.pop() {
        if !visited.insert(package_id) {
            continue;
        }
        let node = nodes.get(package_id).ok_or_else(|| {
            workspace_error(format!(
                "cargo metadata resolve graph lacks package `{package_id}`"
            ))
        })?;
        let name = packages.get(package_id).ok_or_else(|| {
            workspace_error(format!("cargo metadata package table lacks `{package_id}`"))
        })?;
        closure.package_names.insert((*name).to_owned());
        let features = closure
            .package_features
            .entry((*name).to_owned())
            .or_default();
        features.extend(node.features.iter().cloned());
        for dependency in &node.deps {
            let contributes_to_artifact = dependency
                .dep_kinds
                .iter()
                .any(|kind| kind.kind.as_deref() != Some("dev"));
            if contributes_to_artifact {
                pending.push(dependency.pkg.as_str());
            }
        }
    }

    Ok(closure)
}

/// Run `cargo tree` for the given package and feature set, returning the
/// deduplicated set of resolved package names.
///
/// Uses the exact command contract:
/// ```text
/// cargo tree --locked --offline -p PACKAGE --no-default-features \
///   [--features FEATURES] -e normal,build --target all --prefix none \
///   --format '{p}|{f}'
/// ```
///
/// Duplicate markers `(*)` are handled deterministically. Fails closed on
/// malformed nonempty lines or tool errors.
fn cargo_tree_package_names(
    root: &Path,
    package: &str,
    features: &[&str],
) -> Result<BTreeSet<String>> {
    let cargo = match env::var_os("CARGO") {
        Some(path) => path,
        None => "cargo".into(),
    };
    let mut command = Command::new(cargo);
    command
        .current_dir(root)
        .arg("tree")
        .arg("--locked")
        .arg("--offline")
        .arg("-p")
        .arg(package)
        .arg("--no-default-features")
        .arg("-e")
        .arg("normal,build")
        .arg("--target")
        .arg("all")
        .arg("--prefix")
        .arg("none")
        .arg("--format")
        .arg("{p}|{f}");
    for feature in features {
        command.arg("--features").arg(feature);
    }

    let output = command.output().map_err(|error| {
        let code = if error.kind() == ErrorKind::NotFound {
            ErrorCode::ToolMissing
        } else {
            ErrorCode::ToolFailed
        };
        VerificationError::new(
            code,
            format!("cargo tree -p {package} could not start: {error}"),
        )
    })?;
    if !output.status.success() {
        let status = match output.status.code() {
            Some(code) => format!("exit status {code}"),
            None => "terminated by signal".to_owned(),
        };
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stderr = stderr.trim();
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!("cargo tree -p {package} {status}: {stderr}"),
        ));
    }

    parse_cargo_tree_package_names(&output.stdout, package)
}

/// Parse `cargo tree --format '{p}|{f}'` output into a set of unique
/// package names.
///
/// Each nonempty line is expected to match one of:
/// - `NAME SEMVER FEAT1,FEAT2,…`   (first occurrence)
/// - `NAME SEMVER (*)`              (duplicate marker)
///
/// Fails closed on any line that does not match.
fn parse_cargo_tree_package_names(stdout: &[u8], package: &str) -> Result<BTreeSet<String>> {
    let text = std::str::from_utf8(stdout).map_err(|error| {
        workspace_error(format!(
            "cargo tree -p {package} output is not valid UTF-8: {error}"
        ))
    })?;

    let mut names = BTreeSet::new();
    for line in text.lines() {
        if line.is_empty() {
            continue;
        }

        // The format `{p}|{f}` produces lines like:
        //   bamts-codegen 0.1.0|
        //   region 1.0.0 (*)|
        // After the `|` separator the rest is features (possibly empty).
        // Split on `|` to separate the package identifier from features.
        let Some(pipe) = line.find('|') else {
            return Err(workspace_error(format!(
                "cargo tree -p {package}: malformed line (no pipe separator): `{line}`"
            )));
        };

        let ident = &line[..pipe];

        // Ident portion: `NAME SEMVER` or `NAME SEMVER (*)`.
        let trimmed = ident.trim();
        if trimmed.is_empty() {
            return Err(workspace_error(format!(
                "cargo tree -p {package}: empty package identifier in `{line}`"
            )));
        }

        let name_part = trimmed.strip_suffix("(*)").map_or(trimmed, str::trim);
        let mut fields = name_part.split_whitespace();
        let pkg_name = fields.next().ok_or_else(|| {
            workspace_error(format!(
                "cargo tree -p {package}: cannot extract package name from `{line}`"
            ))
        })?;
        let version = fields.next().ok_or_else(|| {
            workspace_error(format!(
                "cargo tree -p {package}: missing package version in `{line}`"
            ))
        })?;
        let version = version.strip_prefix('v').unwrap_or(version);
        if !version
            .as_bytes()
            .first()
            .is_some_and(|byte| byte.is_ascii_digit())
        {
            return Err(workspace_error(format!(
                "cargo tree -p {package}: malformed package version in `{line}`"
            )));
        }
        names.insert(pkg_name.to_owned());
    }

    // Anti-vacuity: the closure must contain at least the queried package.
    if !names.contains(package) {
        return Err(workspace_error(format!(
            "cargo tree -p {package}: output does not contain the queried package"
        )));
    }

    Ok(names)
}

/// Assert that `names` contains every `required` package. Fails with a
/// descriptive message when any expected package is absent.
fn assert_present_packages(label: &str, names: &BTreeSet<String>, required: &[&str]) -> Result<()> {
    let expected: BTreeSet<String> = required.iter().map(|s| (*s).to_owned()).collect();
    let missing: BTreeSet<String> = expected.difference(names).cloned().collect();
    if !missing.is_empty() {
        return Err(workspace_error(format!(
            "{label}: missing required packages [{}]",
            format_set(&missing)
        )));
    }
    Ok(())
}

/// Assert that `names` contains none of the `forbidden` packages. Fails with
/// a descriptive message when any forbidden package is present.
fn assert_forbidden_packages(
    label: &str,
    names: &BTreeSet<String>,
    forbidden: &[&str],
) -> Result<()> {
    let banned: BTreeSet<String> = forbidden.iter().map(|s| (*s).to_owned()).collect();
    let found: BTreeSet<String> = banned.intersection(names).cloned().collect();
    if !found.is_empty() {
        return Err(workspace_error(format!(
            "{label}: contains forbidden packages [{}]",
            format_set(&found)
        )));
    }
    Ok(())
}

fn root_table<'a>(value: &'a Value, context: &str) -> Result<&'a Table> {
    value
        .as_table()
        .ok_or_else(|| workspace_error(format!("{context} must be a TOML table")))
}

fn required_table<'a>(table: &'a Table, key: &str, context: &str) -> Result<&'a Table> {
    match table.get(key) {
        Some(Value::Table(value)) => Ok(value),
        Some(_) => Err(workspace_error(format!(
            "{context}: `{key}` must be a TOML table"
        ))),
        None => Err(workspace_error(format!("{context}: `{key}` is missing"))),
    }
}

fn required_string<'a>(table: &'a Table, key: &str, context: &str) -> Result<&'a str> {
    match table.get(key) {
        Some(Value::String(value)) => Ok(value),
        Some(_) => Err(workspace_error(format!(
            "{context}: `{key}` must be a string"
        ))),
        None => Err(workspace_error(format!("{context}: `{key}` is missing"))),
    }
}

fn require_exact_string(table: &Table, key: &str, expected: &str, context: &str) -> Result<()> {
    let actual = required_string(table, key, context)?;
    if actual != expected {
        return Err(workspace_error(format!(
            "{context}: `{key}` must be `{expected}`, found `{actual}`"
        )));
    }

    Ok(())
}

fn require_exact_bool(table: &Table, key: &str, expected: bool, context: &str) -> Result<()> {
    let actual = match table.get(key) {
        Some(Value::Boolean(value)) => *value,
        Some(_) => {
            return Err(workspace_error(format!(
                "{context}: `{key}` must be a boolean"
            )));
        }
        None => return Err(workspace_error(format!("{context}: `{key}` is missing"))),
    };
    if actual != expected {
        return Err(workspace_error(format!(
            "{context}: `{key}` must be `{expected}`, found `{actual}`"
        )));
    }

    Ok(())
}

fn sorted_table_entries(table: &Table) -> BTreeMap<&str, &Value> {
    table
        .iter()
        .map(|(key, value)| (key.as_str(), value))
        .collect()
}

fn format_internal_dependency(dependency: &InternalDependency) -> String {
    format!(
        "optional={}; features=[{}]",
        dependency.optional,
        dependency
            .features
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn set_difference(expected: &BTreeSet<String>, actual: &BTreeSet<String>) -> String {
    let missing: BTreeSet<String> = expected.difference(actual).cloned().collect();
    let extra: BTreeSet<String> = actual.difference(expected).cloned().collect();
    format!(
        "missing [{}]; extra [{}]",
        format_set(&missing),
        format_set(&extra)
    )
}

fn format_set(values: &BTreeSet<String>) -> String {
    values
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .join(", ")
}

fn workspace_error(detail: impl Into<String>) -> VerificationError {
    VerificationError::new(ErrorCode::Workspace, detail)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_manifest(source: &str) -> Value {
        toml::from_str(source).expect("valid TOML fixture")
    }

    fn root_manifest(omit: Option<&str>, extra: Option<&str>) -> Value {
        let mut members: Vec<String> = MEMBERS
            .iter()
            .filter(|(_, path)| Some(*path) != omit)
            .map(|(_, path)| format!("{path:?}"))
            .collect();
        if let Some(extra) = extra {
            members.push(format!("{extra:?}"));
        }
        parse_manifest(&format!(
            r#"
[workspace]
members = [{}]
resolver = "3"

[workspace.package]
edition = "2024"
rust-version = "1.97.1"

[workspace.lints.rust]
unsafe_code = "forbid"
"#,
            members.join(", ")
        ))
    }

    fn assert_workspace_error<T: std::fmt::Debug>(result: Result<T>) {
        let error = result.expect_err("fixture must fail");
        assert_eq!(error.code(), ErrorCode::Workspace);
    }

    #[test]
    fn rejects_missing_and_extra_members() {
        assert_workspace_error(validate_root_manifest(&root_manifest(
            Some("crates/bamts-cli"),
            None,
        )));
        assert_workspace_error(validate_root_manifest(&root_manifest(
            None,
            Some("crates/not-approved"),
        )));
    }

    #[test]
    fn rejects_forbidden_internal_edge() {
        let mut graph = expected_internal_graph();
        graph
            .get_mut("bamts-compiler")
            .expect("approved graph includes compiler")
            .insert("bamts-native".to_owned(), internal_dependency(false, &[]));

        assert_workspace_error(validate_internal_graph(&graph));
    }

    #[test]
    fn accepts_compatible_registry_requirement() {
        // The Cargo default caret requirement `X.Y[.Z]` is the standard
        // compatible minimum advertised by published registry dependencies.
        validate_registry_version("tokio", "1.53", "fixture").expect("bare minor caret");
        validate_registry_version("tokio-util", "0.7", "fixture").expect("minor-only caret");
        validate_registry_version("serde", "1.0.0", "fixture").expect("full semver caret");
    }

    #[test]
    fn accepts_exact_registry_pin() {
        // Exact `=` pins remain allowed for private/tooling dependencies.
        validate_registry_version("tokio", "=1.53.1", "fixture").expect("exact patch pin");
        validate_registry_version("anyhow", "=1.0.104", "fixture").expect("exact pin");
    }

    #[test]
    fn rejects_wildcard_registry_requirement() {
        assert_workspace_error(validate_registry_version("serde", "*", "fixture"));
        assert_workspace_error(validate_registry_version("serde", "1.*", "fixture"));
    }

    #[test]
    fn rejects_malformed_registry_requirements() {
        for requirement in [
            "1..0",
            "1.2.3.4",
            "=.",
            "1",
            "=1.",
            "01.2",
            "=1.02.3",
            "18446744073709551616.0",
        ] {
            assert_workspace_error(validate_registry_version("serde", requirement, "fixture"));
        }
    }

    #[test]
    fn rejects_overlapping_codegen_features() {
        let manifest = parse_manifest(
            r#"
[features]
default = []
aot = ["dep:bamts-native", "dep:cranelift-object", "dep:sha2", "dep:cranelift-jit"]
host-jit = ["dep:cranelift-jit", "dep:bamts-native"]
"#,
        );

        assert_workspace_error(validate_codegen_features(&manifest, "fixture"));
    }

    #[test]
    fn rejects_unsafe_exception_drift() {
        let manifest = parse_manifest(
            r#"
[lints]
workspace = false
"#,
        );

        assert_workspace_error(validate_member_lints("bamts-runtime", &manifest, "fixture"));
    }

    #[test]
    fn rejects_internal_cycles() {
        let mut graph = expected_internal_graph();
        graph
            .get_mut("bamts-bytecode")
            .expect("approved graph includes bytecode")
            .insert("bamts-compiler".to_owned(), internal_dependency(false, &[]));

        assert_workspace_error(validate_internal_graph(&graph));
    }

    // ── cargo tree parser tests ──────────────────────────────────────────

    #[test]
    fn cargo_tree_parser_extracts_unique_packages() {
        let output = b"bamts-codegen v0.1.0|host-jit\nbamts-runtime 0.1.0|\ncranelift-jit 0.1.0|\nregion 1.0.0 (*)|\ncranelift-jit 0.1.0 (*)|\n";
        let names = parse_cargo_tree_package_names(output, "bamts-codegen").expect("parse");
        assert!(names.contains("bamts-codegen"));
        assert!(names.contains("bamts-runtime"));
        assert!(names.contains("cranelift-jit"));
        assert!(names.contains("region"));
        assert_eq!(names.len(), 4);
    }

    #[test]
    fn cargo_tree_parser_rejects_malformed_line() {
        for output in [
            &b"bamts-codegen 0.1.0|\nno-pipe-here\n"[..],
            &b"bamts-codegen|\n"[..],
            &b"bamts-codegen nope|\n"[..],
        ] {
            assert_workspace_error(parse_cargo_tree_package_names(output, "bamts-codegen"));
        }
    }

    #[test]
    fn cargo_tree_parser_fails_when_queried_package_missing() {
        // Output does not contain the queried package at all.
        let output = b"some-other 1.0.0|\n";
        let result = parse_cargo_tree_package_names(output, "bamts-codegen");
        assert_workspace_error(result);
    }

    #[test]
    fn assert_present_packages_detects_missing() {
        let mut names = BTreeSet::new();
        names.insert("bamts-codegen".to_owned());
        names.insert("region".to_owned());
        // `cranelift-jit` is required but missing.
        let result = assert_present_packages("test", &names, &["cranelift-jit", "region"]);
        assert_workspace_error(result);
    }

    #[test]
    fn assert_forbidden_packages_detects_violation() {
        let mut names = BTreeSet::new();
        names.insert("bamts-runtime".to_owned());
        names.insert("region".to_owned());
        // `region` is in the forbidden set.
        let result = assert_forbidden_packages("test", &names, &["region", "cranelift-jit"]);
        assert_workspace_error(result);
    }

    #[test]
    fn host_jit_feature_set_includes_provider_deps() {
        // Verify that the host-jit feature set contains every
        // executable-memory direct dependency. This is a pure structural
        // assertion; it does not run cargo.
        let manifest = parse_manifest(
            r#"
[features]
default = []
aot = ["dep:bamts-native", "dep:cranelift-object", "dep:sha2"]
host-jit = [
    "dep:bamts-native",
    "bamts-native/jit-entry",
    "dep:cranelift-jit",
    "dep:libc",
    "dep:region",
    "dep:wasmtime-internal-jit-icache-coherence",
]
"#,
        );

        // Must not error — the exact set matches.
        validate_codegen_features(&manifest, "fixture").expect("host-jit feature set");
    }
}
