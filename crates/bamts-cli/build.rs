use std::env;
use std::ffi::{OsStr, OsString};
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    let out_dir = required_path("OUT_DIR");
    let cargo = cargo_build_context(
        &env::current_exe().expect("could not locate the running Cargo build script"),
    )
    .unwrap_or_else(|error| panic!("could not locate Cargo build metadata: {error}"));
    let dependencies = cargo.dependencies;
    let target = required("TARGET");
    let host = required("HOST");
    let archive = out_dir.join(staticlib_archive_name(&target));

    let mut native_libraries = String::new();
    match node_staticlib_action(&target, &host) {
        NodeStaticlibAction::Assemble => {
            let wrapper = out_dir.join("embedded_node.rs");
            fs::write(&wrapper, wrapper_source())
                .expect("could not write bamts-node staticlib wrapper");
            let rustc = env::var_os("RUSTC").unwrap_or_else(|| OsString::from("rustc"));
            let node_rlib_metadata = env::var_os("DEP_BAMTS_NODE_RLIB").map(PathBuf::from);
            match select_node_rlib(
                &rustc,
                &target,
                &dependencies,
                &wrapper,
                &out_dir,
                node_rlib_metadata.as_deref(),
                &cargo.fingerprint,
            ) {
                Some(node_rlib) => {
                    native_libraries = assemble_staticlib(
                        &rustc,
                        &target,
                        &dependencies,
                        &node_rlib,
                        &archive,
                        &wrapper,
                    );
                }
                None => write_check_placeholder(&dependencies, &archive),
            }
        }
        NodeStaticlibAction::WriteEmptyArchive => write_empty_archive(&archive),
    }

    cargo_line("rerun-if-changed=../bamts-node/src");
    cargo_line("rerun-if-changed=../bamts-node/Cargo.toml");
    cargo_line("rerun-if-env-changed=DEP_BAMTS_NODE_RLIB");
    cargo_line(&format!(
        "rustc-env=BAMTS_NODE_STATICLIB={}",
        archive.display()
    ));
    cargo_line(&format!(
        "rustc-env=BAMTS_NODE_NATIVE_LIBS={native_libraries}"
    ));
    cargo_line(&format!("rustc-env=BAMTS_HOST_TARGET={host}"));
    cargo_line(&format!("rustc-env=BAMTS_BUILD_TARGET={target}"));
    // The compiler recurses on the main thread. Linux and macOS give that thread
    // 8 MiB and link.exe gives it 1 MiB, on which a nesting depth that the parser
    // accepts overflows the stack.
    if env::var_os("CARGO_CFG_TARGET_ENV").is_some_and(|environment| environment == "msvc") {
        cargo_line("rustc-link-arg-bin=bamts=/STACK:8388608");
    }
}

fn wrapper_source() -> &'static str {
    "extern crate bamts_node;\n#[used]\nstatic KEEP_NODE: fn() -> bamts_node::NodeHost = bamts_node::NodeHost::new;\n#[used]\nstatic KEEP_AOT_MAIN: extern \"C\" fn() -> i32 = bamts_node::main;\n"
}

struct CargoBuildContext {
    dependencies: PathBuf,
    fingerprint: PathBuf,
}

fn cargo_build_context(current_exe: &Path) -> Result<CargoBuildContext, String> {
    let build_script_dir = current_exe
        .parent()
        .ok_or_else(|| format!("`{}` has no parent directory", current_exe.display()))?;
    let build_dir = build_script_dir.parent().ok_or_else(|| {
        format!(
            "`{}` is not in Cargo's build directory",
            current_exe.display()
        )
    })?;
    let profile_dir = build_dir.parent().ok_or_else(|| {
        format!(
            "`{}` is not in Cargo's profile directory",
            current_exe.display()
        )
    })?;
    let build_name = build_script_dir
        .file_name()
        .and_then(OsStr::to_str)
        .ok_or_else(|| {
            format!(
                "`{}` has a non-UTF-8 build directory name",
                build_script_dir.display()
            )
        })?;

    Ok(CargoBuildContext {
        dependencies: profile_dir.join("deps"),
        fingerprint: profile_dir
            .join(".fingerprint")
            .join(build_name)
            .join("build-script-build-script-build.json"),
    })
}

fn select_node_rlib(
    rustc: &OsStr,
    target: &str,
    dependencies: &Path,
    wrapper: &Path,
    out_dir: &Path,
    metadata_candidate: Option<&Path>,
    build_fingerprint: &Path,
) -> Option<PathBuf> {
    if let Some(candidate) = metadata_candidate {
        if candidate.extension() != Some(OsStr::new("rlib")) || !candidate.is_file() {
            panic!(
                "Cargo provided invalid bamts-node rlib metadata `{}`",
                candidate.display()
            );
        }
        if !metadata_supports_aot_main(rustc, target, dependencies, candidate, wrapper, out_dir) {
            panic!(
                "Cargo-selected bamts-node rlib `{}` lacks the metadata required for the aot-main entrypoint",
                candidate.display()
            );
        }
        return Some(candidate.to_path_buf());
    }

    match node_rlib_from_fingerprint(build_fingerprint, dependencies) {
        Ok(Some(candidate)) => return Some(candidate),
        Ok(None) => {}
        Err(error) => {
            panic!("could not resolve bamts-node from Cargo fingerprint metadata: {error}")
        }
    }

    let candidates = artifacts(dependencies, "libbamts_node-", "rlib");
    if candidates.is_empty() {
        return None;
    }
    let compatible = candidates
        .iter()
        .filter(|candidate| {
            metadata_supports_aot_main(rustc, target, dependencies, candidate, wrapper, out_dir)
        })
        .cloned()
        .collect::<Vec<_>>();
    choose_compatible_node_rlib(&compatible).or_else(|| {
        panic!(
            "no bamts-node rlib in `{}` has the metadata required for the aot-main entrypoint; candidates: {}",
            dependencies.display(),
            display_paths(&candidates)
        )
    })
}

fn node_rlib_from_fingerprint(
    build_fingerprint: &Path,
    dependencies: &Path,
) -> Result<Option<PathBuf>, String> {
    if !build_fingerprint.exists() {
        return Ok(None);
    }

    // Cargo's `.fingerprint` JSON is an undocumented, version-dependent
    // implementation detail. When the file is absent or does not match the
    // expected shape, treat the metadata as unavailable and fall back to
    // the compatible-candidate scan in `select_node_rlib`. Only errors from
    // `exact_node_rlib` — which indicate valid metadata pointing at a
    // missing or ambiguous artifact — propagate as hard errors.
    let dependency_hash = try_parse_fingerprint_hash(build_fingerprint);
    let Some(dependency_hash) = dependency_hash else {
        return Ok(None);
    };

    let fingerprint_root = build_fingerprint
        .parent()
        .and_then(Path::parent)
        .ok_or_else(|| {
            format!(
                "`{}` is not below Cargo's .fingerprint directory",
                build_fingerprint.display()
            )
        })?;

    exact_node_rlib(fingerprint_root, dependencies, dependency_hash)
}

/// Best-effort extraction of the `bamts_node` fingerprint hash from Cargo's
/// build-script fingerprint JSON. Returns `None` when the file is absent or
/// the shape does not match, so callers can fall back to a candidate scan.
fn try_parse_fingerprint_hash(build_fingerprint: &Path) -> Option<u64> {
    let contents = fs::read_to_string(build_fingerprint).ok()?;
    let fingerprint = parse_cargo_build_fingerprint(&contents).ok()?;
    fingerprint.bamts_node_hash().ok()
}

struct CargoBuildFingerprint {
    dependencies: Vec<CargoDependency>,
}

impl CargoBuildFingerprint {
    fn bamts_node_hash(&self) -> Result<u64, String> {
        let mut dependencies = self
            .dependencies
            .iter()
            .filter(|dependency| dependency.name == "bamts_node");
        let Some(dependency) = dependencies.next() else {
            return Err("has no `bamts_node` build dependency".to_owned());
        };
        if dependencies.next().is_some() {
            return Err("has multiple `bamts_node` build dependencies".to_owned());
        }
        Ok(dependency.fingerprint)
    }
}

struct CargoDependency {
    _package_id_hash: u64,
    name: String,
    _is_public: bool,
    fingerprint: u64,
}

fn parse_cargo_build_fingerprint(contents: &str) -> Result<CargoBuildFingerprint, String> {
    let document: serde_json::Value =
        serde_json::from_str(contents).map_err(|error| format!("invalid JSON: {error}"))?;
    let dependencies = document
        .as_object()
        .ok_or_else(|| "top level is not an object".to_owned())?
        .get("deps")
        .ok_or_else(|| "missing `deps`".to_owned())?
        .as_array()
        .ok_or_else(|| "`deps` is not an array".to_owned())?
        .iter()
        .enumerate()
        .map(|(index, dependency)| parse_cargo_dependency(index, dependency))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(CargoBuildFingerprint { dependencies })
}

fn parse_cargo_dependency(
    index: usize,
    dependency: &serde_json::Value,
) -> Result<CargoDependency, String> {
    let fields = dependency
        .as_array()
        .ok_or_else(|| format!("`deps[{index}]` is not a four-element array"))?;
    if fields.len() != 4 {
        return Err(format!("`deps[{index}]` is not a four-element array"));
    }

    let package_id_hash = fields[0]
        .as_u64()
        .ok_or_else(|| format!("`deps[{index}][0]` is not a u64"))?;
    let name = fields[1]
        .as_str()
        .ok_or_else(|| format!("`deps[{index}][1]` is not a string"))?
        .to_owned();
    let is_public = fields[2]
        .as_bool()
        .ok_or_else(|| format!("`deps[{index}][2]` is not a bool"))?;
    let fingerprint = fields[3]
        .as_u64()
        .ok_or_else(|| format!("`deps[{index}][3]` is not a u64"))?;

    Ok(CargoDependency {
        _package_id_hash: package_id_hash,
        name,
        _is_public: is_public,
        fingerprint,
    })
}

fn fingerprint_stamp(dependency_hash: u64) -> String {
    format!("{:016x}", dependency_hash.swap_bytes())
}

fn exact_node_rlib(
    fingerprint_root: &Path,
    dependencies: &Path,
    dependency_hash: u64,
) -> Result<Option<PathBuf>, String> {
    let wanted_stamp = fingerprint_stamp(dependency_hash);
    let mut matches = Vec::new();
    let entries = fs::read_dir(fingerprint_root).map_err(|error| {
        format!(
            "could not inspect `{}`: {error}",
            fingerprint_root.display()
        )
    })?;

    for entry in entries {
        let entry = entry.map_err(|error| {
            format!(
                "could not inspect `{}`: {error}",
                fingerprint_root.display()
            )
        })?;
        let file_type = entry
            .file_type()
            .map_err(|error| format!("could not inspect `{}`: {error}", entry.path().display()))?;
        if !file_type.is_dir() {
            continue;
        }
        let name = entry.file_name();
        let name = name.to_str().ok_or_else(|| {
            format!(
                "Cargo fingerprint directory `{}` has a non-UTF-8 name",
                entry.path().display()
            )
        })?;
        let Some(suffix) = name.strip_prefix("bamts-node-") else {
            continue;
        };
        if suffix.is_empty() {
            return Err(format!(
                "Cargo fingerprint directory `{}` has no artifact suffix",
                entry.path().display()
            ));
        }

        let stamp_path = entry.path().join("lib-bamts_node");
        let stamp = match fs::read_to_string(&stamp_path) {
            Ok(stamp) => stamp,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => {
                return Err(format!(
                    "could not read Cargo fingerprint stamp `{}`: {error}",
                    stamp_path.display()
                ));
            }
        };
        if stamp.len() != 16
            || !stamp.bytes().all(|byte| {
                byte.is_ascii_digit() || (byte.is_ascii_lowercase() && byte.is_ascii_hexdigit())
            })
        {
            // Cargo may leave a partial sibling fingerprint while jobs run in parallel.
            continue;
        }
        if stamp == wanted_stamp {
            let rlib = dependencies.join(format!("libbamts_node-{suffix}.rlib"));
            if !rlib.is_file() {
                return Err(format!(
                    "Cargo fingerprint stamp `{}` selected missing rlib `{}`",
                    stamp_path.display(),
                    rlib.display()
                ));
            }
            matches.push(rlib);
        }
    }

    match matches.as_slice() {
        [candidate] => Ok(Some(candidate.clone())),
        // No matching stamp: the fingerprint may be stale or a parallel
        // build has not finished writing yet. Fall back to the candidate scan.
        [] => Ok(None),
        candidates => Err(format!(
            "multiple `bamts-node-*` fingerprint stamps in `{}` match `{wanted_stamp}`: {}",
            fingerprint_root.display(),
            display_paths(candidates)
        )),
    }
}

fn choose_compatible_node_rlib(compatible: &[PathBuf]) -> Option<PathBuf> {
    match compatible {
        [] => None,
        [candidate] => Some(candidate.clone()),
        candidates => panic!(
            "ambiguous compatible bamts-node rlibs; Cargo fingerprint metadata is unavailable: {}",
            display_paths(candidates)
        ),
    }
}

fn metadata_supports_aot_main(
    rustc: &OsStr,
    target: &str,
    dependencies: &Path,
    candidate: &Path,
    wrapper: &Path,
    out_dir: &Path,
) -> bool {
    let probe = out_dir.join(format!(
        "bamts-node-probe-{}.rmeta",
        candidate
            .file_stem()
            .and_then(OsStr::to_str)
            .unwrap_or("unknown")
    ));
    let output = Command::new(rustc)
        .arg("--crate-name")
        .arg("bamts_node_probe")
        .arg("--crate-type")
        .arg("lib")
        .arg("--emit=metadata")
        .arg("--edition=2024")
        .arg("--target")
        .arg(target)
        .arg("--extern")
        .arg(format!("bamts_node={}", candidate.display()))
        .arg("-L")
        .arg(format!("dependency={}", dependencies.display()))
        .arg("-o")
        .arg(&probe)
        .arg(wrapper)
        .output()
        .unwrap_or_else(|error| {
            panic!("could not start `{}`: {error}", Path::new(rustc).display())
        });
    let _ = fs::remove_file(probe);
    output.status.success()
}

fn assemble_staticlib(
    rustc: &OsStr,
    target: &str,
    dependencies: &Path,
    node_rlib: &Path,
    archive: &Path,
    wrapper: &Path,
) -> String {
    let mut command = Command::new(rustc);
    command
        .arg("--crate-name")
        .arg("bamts_node_embedded")
        .arg("--crate-type")
        .arg("staticlib")
        .arg("--edition=2024")
        .arg("--target")
        .arg(target)
        .arg("--extern")
        .arg(format!("bamts_node={}", node_rlib.display()))
        .arg("-L")
        .arg(format!("dependency={}", dependencies.display()))
        .arg("-C")
        .arg(if required("PROFILE") == "release" {
            "opt-level=3"
        } else {
            "opt-level=0"
        })
        .arg("-o")
        .arg(archive)
        .arg(wrapper);
    // The MSVC linker takes no libraries from the archive, so the link step has to
    // name the system libraries that the archive needs. Only rustc knows them.
    let needs_libraries = targets_msvc(target);
    if needs_libraries {
        command.arg("--print=native-static-libs");
    }
    let output = command.output().unwrap_or_else(|error| {
        panic!("could not start `{}`: {error}", Path::new(rustc).display())
    });
    if !output.status.success() {
        panic!(
            "bamts-node staticlib assembly failed with {}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    if !needs_libraries {
        return String::new();
    }
    native_static_libraries(&String::from_utf8_lossy(&output.stderr)).unwrap_or_else(|| {
        panic!(
            "rustc did not report the native libraries of the bamts-node staticlib\nstderr:\n{}",
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

/// The libraries rustc says to link with a staticlib, from its
/// `note: native-static-libs: kernel32.lib ntdll.lib /defaultlib:msvcrt` line.
fn native_static_libraries(stderr: &str) -> Option<String> {
    const MARKER: &str = "native-static-libs:";
    stderr.lines().find_map(|line| {
        let libraries = line.split_once(MARKER)?.1;
        let libraries = libraries.split_whitespace().collect::<Vec<_>>().join(" ");
        (!libraries.is_empty()).then_some(libraries)
    })
}

fn write_check_placeholder(dependencies: &Path, archive: &Path) {
    if artifacts(dependencies, "libbamts_node-", "rmeta").len() != 1 {
        panic!(
            "bamts-node build dependency did not produce exactly one metadata artifact in `{}`",
            dependencies.display()
        );
    }
    write_empty_archive(archive);
}

fn write_empty_archive(archive: &Path) {
    fs::write(archive, b"!<arch>\n").unwrap_or_else(|error| {
        panic!(
            "could not create runtime archive `{}`: {error}",
            archive.display()
        )
    });
}

fn artifacts(directory: &Path, prefix: &str, extension: &str) -> Vec<PathBuf> {
    let suffix = format!(".{extension}");
    let mut artifacts = fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("could not inspect `{}`: {error}", directory.display()))
        .filter_map(Result::ok)
        .filter_map(|entry| {
            let name = entry.file_name();
            let name = name.to_string_lossy();
            (name.starts_with(prefix) && name.ends_with(&suffix)).then(|| entry.path())
        })
        .collect::<Vec<_>>();
    artifacts.sort();
    artifacts
}

fn display_paths(paths: &[PathBuf]) -> String {
    paths
        .iter()
        .map(|path| path.display().to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

fn required(name: &str) -> String {
    env::var(name).unwrap_or_else(|_| panic!("Cargo did not provide required {name}"))
}

fn required_path(name: &str) -> PathBuf {
    PathBuf::from(required(name))
}

fn cargo_line(directive: &str) {
    writeln!(io::stdout().lock(), "cargo:{directive}").expect("could not emit Cargo directive");
}

#[derive(Debug, Eq, PartialEq)]
enum NodeStaticlibAction {
    Assemble,
    WriteEmptyArchive,
}

fn node_staticlib_action(target: &str, host: &str) -> NodeStaticlibAction {
    if target == host {
        NodeStaticlibAction::Assemble
    } else {
        NodeStaticlibAction::WriteEmptyArchive
    }
}

fn targets_msvc(target: &str) -> bool {
    target.contains("windows-msvc")
}

fn staticlib_archive_name(target: &str) -> &'static str {
    if targets_msvc(target) {
        "bamts_node.lib"
    } else {
        "libbamts_node.a"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    static NEXT_TEST_DIRECTORY: AtomicUsize = AtomicUsize::new(0);

    fn test_directory() -> PathBuf {
        let directory = env::temp_dir().join(format!(
            "bamts-cli-build-rs-{}-{}",
            std::process::id(),
            NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&directory).expect("could not create test directory");
        directory
    }

    #[test]
    fn native_libraries_come_from_the_rustc_note() {
        let stderr = "warning: something\nnote: link against the following native artifacts when linking against this static library\nnote: native-static-libs: kernel32.lib  ntdll.lib userenv.lib /defaultlib:msvcrt\n\nwarning: 1 warning emitted\n";
        assert_eq!(
            native_static_libraries(stderr).as_deref(),
            Some("kernel32.lib ntdll.lib userenv.lib /defaultlib:msvcrt")
        );
    }

    #[test]
    fn a_missing_or_empty_native_libraries_note_gives_nothing() {
        assert_eq!(native_static_libraries(""), None);
        assert_eq!(
            native_static_libraries("note: native-static-libs:   \n"),
            None
        );
        assert_eq!(
            native_static_libraries("note: link against the following native artifacts\n"),
            None
        );
    }

    fn fingerprint_json(dependency_hash: u64) -> String {
        format!(r#"{{"deps":[[8623995201299226029,"bamts_node",false,{dependency_hash}]]}}"#)
    }

    #[test]
    fn host_build_assembles_node_staticlib() {
        assert_eq!(
            node_staticlib_action("x86_64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"),
            NodeStaticlibAction::Assemble
        );
    }

    #[test]
    fn cross_target_build_writes_empty_node_staticlib() {
        assert_eq!(
            node_staticlib_action("aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"),
            NodeStaticlibAction::WriteEmptyArchive
        );
    }

    #[test]
    fn cross_target_windows_placeholder_is_a_valid_unused_archive() {
        let directory = test_directory();
        let archive = directory.join(staticlib_archive_name("x86_64-pc-windows-msvc"));

        write_empty_archive(&archive);

        assert_eq!(archive.file_name(), Some(OsStr::new("bamts_node.lib")));
        assert!(archive.is_file());
        assert_eq!(
            fs::read(&archive).expect("could not read archive"),
            b"!<arch>\n"
        );
        fs::remove_dir_all(directory).expect("could not remove test directory");
    }

    #[test]
    fn fingerprint_stamp_uses_little_endian_bytes() {
        assert_eq!(fingerprint_stamp(0x6c72_5109_f3a6_1984), "8419a6f30951726c");
    }

    #[test]
    fn fingerprint_selects_exact_rlib_among_compatible_candidates() {
        let directory = test_directory();
        let fingerprint_root = directory.join(".fingerprint");
        let dependencies = directory.join("deps");
        fs::create_dir_all(&dependencies).expect("could not create deps directory");
        let dependency_hash = 0x6c72_5109_f3a6_1984;
        let exact_suffix = "f0a5527c30509477";
        for (suffix, stamp) in [
            ("normal-workspace", "409792dc5b64bb07"),
            ("partial-parallel-build", "f046"),
            (exact_suffix, "8419a6f30951726c"),
        ] {
            let artifact = fingerprint_root.join(format!("bamts-node-{suffix}"));
            fs::create_dir_all(&artifact).expect("could not create fingerprint directory");
            fs::write(artifact.join("lib-bamts_node"), stamp)
                .expect("could not write fingerprint stamp");
            fs::write(
                dependencies.join(format!("libbamts_node-{suffix}.rlib")),
                b"",
            )
            .expect("could not write rlib");
        }
        let build_fingerprint = fingerprint_root
            .join("bamts-cli-current")
            .join("build-script-build-script-build.json");
        fs::create_dir_all(build_fingerprint.parent().expect("fingerprint parent"))
            .expect("could not create build fingerprint directory");
        fs::write(&build_fingerprint, fingerprint_json(dependency_hash))
            .expect("could not write build fingerprint");

        assert_eq!(
            node_rlib_from_fingerprint(&build_fingerprint, &dependencies)
                .expect("could not select exact fingerprint"),
            Some(dependencies.join(format!("libbamts_node-{exact_suffix}.rlib")))
        );
        fs::remove_dir_all(directory).expect("could not remove test directory");
    }

    #[test]
    fn malformed_fingerprint_metadata_is_rejected() {
        let error = match parse_cargo_build_fingerprint("{\"deps\":[[1,\"bamts_node\",false]]}") {
            Ok(_) => panic!("malformed metadata should fail"),
            Err(error) => error,
        };

        assert!(error.contains("four-element array"));
    }

    #[test]
    fn missing_metadata_allows_one_compatible_fallback() {
        let directory = test_directory();
        let missing = directory.join("missing.json");
        assert_eq!(
            node_rlib_from_fingerprint(&missing, Path::new("/unused"))
                .expect("missing metadata should not be malformed"),
            None
        );
        let candidate = PathBuf::from("/cache/libbamts_node-current.rlib");
        assert_eq!(
            choose_compatible_node_rlib(std::slice::from_ref(&candidate)),
            Some(candidate)
        );
        fs::remove_dir_all(directory).expect("could not remove test directory");
    }

    #[test]
    #[should_panic(expected = "ambiguous compatible bamts-node rlibs")]
    fn multiple_compatible_artifacts_are_rejected_without_metadata() {
        let compatible = [
            PathBuf::from("/cache/libbamts_node-first.rlib"),
            PathBuf::from("/cache/libbamts_node-second.rlib"),
        ];

        let _ = choose_compatible_node_rlib(&compatible);
    }

    #[test]
    fn parser_preserves_large_dependency_hashes() {
        let fingerprint =
            parse_cargo_build_fingerprint(&fingerprint_json(7_814_397_406_625_536_388))
                .expect("valid metadata should parse");

        assert_eq!(
            fingerprint
                .bamts_node_hash()
                .expect("bamts_node dependency should exist"),
            7_814_397_406_625_536_388
        );
    }
}
