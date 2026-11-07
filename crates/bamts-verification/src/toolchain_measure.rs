//! Measures one target cell with real tools and real runs.
//!
//! Every value in a cell comes from something that happened here: the probe is
//! emitted twice through production codegen, linked twice with the committed
//! freestanding support, run natively or under the cell's emulator, and read back
//! from its own headers. What cannot be observed stays a gap for [`generate_cell`]
//! to classify. A measurement never fills one in.

use std::{
    env, fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

use crate::{
    ErrorCode, Result, VerificationError,
    schema::sha256_hex,
    toolchain_image::{ImageFacts, inspect_image},
    toolchain_schema::{
        CellClass, HostObservation, RustcPin, TargetCellRecord, cell_class_for, emit_probe_object,
        generate_cell,
    },
};

/// The Rust source of the image's runtime, with its value still to fill in.
const SUPPORT_SOURCE: &str = include_str!("../probe/support.rs");

/// Where Rosetta's runtime lives once it is installed.
const ROSETTA_RUNTIME: &str = "/Library/Apple/usr/libexec/oah/libRosettaRuntime";

/// One cell, and what stopped any obligation from being observed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CellMeasurement {
    pub record: TargetCellRecord,
    pub notes: Vec<String>,
}

/// Measures `target` from this host, using `work` for its files.
///
/// # Errors
///
/// Returns an error when `target` cannot be measured from this host at all, when
/// `rustc` cannot be read, or when `work` cannot be written. A step that fails
/// after that leaves a gap in the record and a line in the notes.
pub fn measure_cell(target: &str, work: &Path) -> Result<CellMeasurement> {
    fs::create_dir_all(work).map_err(|error| io_path(work, &error))?;
    let (rustc, manifest) = read_rustc()?;
    let class = cell_class_for(target, rustc.host())?;
    let mut observation = HostObservation::new(rustc).with_toolchain_manifest(manifest);
    let notes = match observe(target, class, work, &mut observation) {
        Ok(()) => Vec::new(),
        Err(error) => vec![error.to_string()],
    };
    Ok(CellMeasurement {
        record: generate_cell(target, &observation)?,
        notes,
    })
}

/// Records each obligation as it is observed, so a later step that fails leaves
/// what came before it in place.
fn observe(
    target: &str,
    class: CellClass,
    work: &Path,
    observed: &mut HostObservation,
) -> Result<()> {
    let first = work.join("first");
    let second = work.join("second");
    for build in [&first, &second] {
        fs::create_dir_all(build).map_err(|error| io_path(build, &error))?;
    }
    let probe = emit_probe_object(target, &first.join("probe.o"))?;
    let repeat = emit_probe_object(target, &second.join("probe.o"))?;
    let object_facts = inspect_image(&read_file(&first.join("probe.o"))?)?;
    *observed = observed.clone().with_target_object(
        target,
        format!(
            "command=bamts-verification toolchain object --target {target} --out probe.o; object_sha256={}; {}; bytes={}; entry={}; helpers={}",
            probe.sha256,
            identity_fields(&object_facts),
            probe.byte_len,
            probe.entry_symbol,
            probe.required_helpers.join(","),
        ),
    );

    let linker = find_linker(target).ok_or_else(|| {
        VerificationError::new(
            ErrorCode::ToolMissing,
            format!("no linker for `{target}` was found on PATH"),
        )
    })?;
    *observed = observed.clone().with_linker(target, linker.identity()?);
    compile_support(target, work)?;
    let command = linker.link(&first)?;
    linker.link(&second)?;
    let image = read_file(&first.join("probe"))?;
    let executable_sha256 = sha256_hex(&image);
    let second_image = sha256_hex(&read_file(&second.join("probe"))?);
    let mut facts = inspect_image(&image)?;
    if let Some(signature) = linker.signature(&first)? {
        facts.format_evidence.push(("signature", signature));
    }
    *observed = observed.clone().with_hardened_link(
        target,
        format!(
            "command={command}; executable_sha256={executable_sha256}; {}; {}; {}",
            identity_fields(&facts),
            format_fields(&facts),
            linker.provenance()?,
        ),
    );

    let inspector = env::current_exe().map_err(|error| {
        VerificationError::new(ErrorCode::Io, format!("cannot name this program: {error}"))
    })?;
    *observed = observed.clone().with_execmem_guard(
        target,
        format!(
            "command=bamts-verification toolchain measure --target {target}; executable_sha256={executable_sha256}; inspector_sha256={}; writable_executable_regions={}; {}",
            sha256_hex(&read_file(&inspector)?),
            facts.writable_executable_regions,
            format_fields(&facts),
        ),
    );

    if probe.sha256 == repeat.sha256 && executable_sha256 == second_image {
        *observed = observed.clone().with_reproducible_build(
            target,
            format!(
                "command=bamts-verification toolchain measure --target {target}; first_object_sha256={}; second_object_sha256={}; first_executable_sha256={executable_sha256}; second_executable_sha256={second_image}; byte_identical=true",
                probe.sha256, repeat.sha256
            ),
        );
    }

    let runner = Runner::for_class(class, target)?;
    run_probe(&runner, &first)?;
    let evidence = format!(
        "command={}; executable_sha256={executable_sha256}; execution={}; exit=0; result=int32:42; fuel=positive{}",
        runner.display("./probe"),
        runner.execution(target),
        runner.identity_fields()?,
    );
    *observed = match class {
        CellClass::NativeHost => observed.clone().with_native_execution(target, evidence),
        CellClass::CrossQemu | CellClass::CrossRosetta => {
            observed.clone().with_emulator(target, evidence)
        }
    };
    Ok(())
}

/// Runs the image. A clean exit is how it reports that it returned `int32:42` and
/// charged fuel, so anything else leaves the run unobserved.
fn run_probe(runner: &Runner, directory: &Path) -> Result<()> {
    let output = run(runner.command("./probe").current_dir(directory))?;
    if output.status.code() == Some(0) {
        Ok(())
    } else {
        Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!("the probe did not finish cleanly: {:?}", output.status),
        ))
    }
}

fn identity_fields(facts: &ImageFacts) -> String {
    format!(
        "object_format={}; object_type={}; machine={}",
        facts.object_format, facts.object_type, facts.machine
    )
}

fn format_fields(facts: &ImageFacts) -> String {
    facts
        .format_evidence
        .iter()
        .map(|(key, value)| format!("{key}={value}"))
        .collect::<Vec<_>>()
        .join("; ")
}

/// The image's runtime, with the value it must see filled in.
fn support_source() -> String {
    let int32_42 = bamts_native::Value::int32(42).to_bits();
    SUPPORT_SOURCE.replace("@INT32_42@", &format!("{int32_42:#x}"))
}

/// Compiles the image's runtime for `target` into `work/support.o`.
fn compile_support(target: &str, work: &Path) -> Result<()> {
    let source = work.join("support.rs");
    fs::write(&source, support_source()).map_err(|error| io_path(&source, &error))?;
    require_success(
        "rustc",
        &run(Command::new("rustc")
            .args(["--edition=2024", "--crate-type=lib", "--crate-name=support"])
            .args(["--emit=obj", "-Cpanic=abort", "-Copt-level=2"])
            .args(["-Ccodegen-units=1", "--target", target])
            .arg("-o")
            .arg(work.join("support.o"))
            .arg(&source))?,
    )
}

/// The linker a target's image is built with.
enum Linker {
    Lld {
        path: PathBuf,
        emulation: &'static str,
    },
    Cc {
        path: PathBuf,
        arch: &'static str,
    },
}

fn find_linker(target: &str) -> Option<Linker> {
    let elf = |emulation| find_program("ld.lld").map(|path| Linker::Lld { path, emulation });
    let macho = |arch| find_program("cc").map(|path| Linker::Cc { path, arch });
    match target {
        "x86_64-unknown-linux-gnu" => elf("elf_x86_64"),
        "aarch64-unknown-linux-gnu" => elf("aarch64linux"),
        "s390x-unknown-linux-gnu" => elf("elf64_s390"),
        "riscv64gc-unknown-linux-gnu" => elf("elf64lriscv"),
        "aarch64-apple-darwin" => macho("arm64"),
        "x86_64-apple-darwin" => macho("x86_64"),
        _ => None,
    }
}

impl Linker {
    const fn path(&self) -> &PathBuf {
        match self {
            Self::Lld { path, .. } | Self::Cc { path, .. } => path,
        }
    }

    fn version(&self) -> Result<String> {
        let output = run(Command::new(self.path()).arg("--version"))?;
        require_success("linker", &output)?;
        Ok(first_line(&output.stdout))
    }

    fn identity(&self) -> Result<String> {
        Ok(format!("linker={}", self.version()?))
    }

    fn provenance(&self) -> Result<String> {
        Ok(format!(
            "linker_version={}; linker_sha256={}",
            self.version()?,
            sha256_hex(&read_file(self.path())?)
        ))
    }

    /// Links `directory/probe`, and returns the command as it should be replayed.
    fn link(&self, directory: &Path) -> Result<String> {
        let mut command = Command::new(self.path());
        let replay = match self {
            Self::Lld { emulation, .. } => {
                let args = [
                    "-m",
                    emulation,
                    "-static",
                    "-e",
                    "_start",
                    "-z",
                    "relro",
                    "-z",
                    "now",
                    "-z",
                    "noexecstack",
                    "-z",
                    "defs",
                    "--build-id=none",
                    "-o",
                    "probe",
                    "../support.o",
                    "probe.o",
                ];
                command.args(args);
                format!("ld.lld {}", args.join(" "))
            }
            Self::Cc { arch, .. } => {
                let args = ["-arch", arch, "-o", "probe", "../support.o", "probe.o"];
                command.args(args);
                format!("cc {}", args.join(" "))
            }
        };
        require_success("linker", &run(command.current_dir(directory))?)?;
        if matches!(self, Self::Cc { .. }) {
            require_success(
                "codesign",
                &run(Command::new("codesign")
                    .args([
                        "--force",
                        "--sign",
                        "-",
                        "--identifier",
                        "bamts-probe",
                        "probe",
                    ])
                    .current_dir(directory))?,
            )?;
        }
        Ok(replay)
    }

    /// The kind of signature `directory/probe` carries, on formats that sign.
    fn signature(&self, directory: &Path) -> Result<Option<String>> {
        if matches!(self, Self::Lld { .. }) {
            return Ok(None);
        }
        require_success(
            "codesign",
            &run(Command::new("codesign")
                .args(["--verify", "probe"])
                .current_dir(directory))?,
        )?;
        let output = run(Command::new("codesign")
            .args(["--display", "--verbose=2", "probe"])
            .current_dir(directory))?;
        let details = String::from_utf8_lossy(&output.stderr);
        Ok(Some(
            details
                .lines()
                .find_map(|line| line.strip_prefix("Signature="))
                .unwrap_or("none")
                .to_owned(),
        ))
    }
}

/// How a cell's image is started.
enum Runner {
    Native,
    Emulated {
        program: PathBuf,
        prefix: Vec<String>,
        version: String,
        identity: PathBuf,
    },
}

impl Runner {
    fn for_class(class: CellClass, target: &str) -> Result<Self> {
        match class {
            CellClass::NativeHost => Ok(Self::Native),
            CellClass::CrossRosetta => {
                let identity = PathBuf::from(ROSETTA_RUNTIME);
                let build = run(Command::new("sw_vers").arg("-buildVersion"))?;
                require_success("sw_vers", &build)?;
                read_file(&identity)?;
                Ok(Self::Emulated {
                    program: PathBuf::from("/usr/bin/arch"),
                    prefix: vec!["-x86_64".to_owned()],
                    version: format!("rosetta on macOS {}", first_line(&build.stdout)),
                    identity,
                })
            }
            CellClass::CrossQemu => {
                let name = format!("qemu-{}", qemu_arch(target));
                let program = find_program(&format!("{name}-static"))
                    .or_else(|| find_program(&name))
                    .ok_or_else(|| {
                        VerificationError::new(
                            ErrorCode::ToolMissing,
                            format!("`{name}` was not found on PATH"),
                        )
                    })?;
                let output = run(Command::new(&program).arg("--version"))?;
                require_success(&name, &output)?;
                Ok(Self::Emulated {
                    identity: program.clone(),
                    program,
                    prefix: Vec::new(),
                    version: first_line(&output.stdout),
                })
            }
        }
    }

    fn command(&self, image: &str) -> Command {
        match self {
            Self::Native => Command::new(image),
            Self::Emulated {
                program, prefix, ..
            } => {
                let mut command = Command::new(program);
                command.args(prefix).arg(image);
                command
            }
        }
    }

    fn display(&self, image: &str) -> String {
        match self {
            Self::Native => image.to_owned(),
            Self::Emulated {
                program, prefix, ..
            } => {
                let mut words = vec![program.display().to_string()];
                words.extend(prefix.iter().cloned());
                words.push(image.to_owned());
                words.join(" ")
            }
        }
    }

    fn execution(&self, target: &str) -> String {
        match self {
            Self::Native => "native".to_owned(),
            Self::Emulated { identity, .. } if identity.ends_with("libRosettaRuntime") => {
                "rosetta".to_owned()
            }
            Self::Emulated { .. } => format!("qemu-{}", qemu_arch(target)),
        }
    }

    fn identity_fields(&self) -> Result<String> {
        match self {
            Self::Native => Ok(String::new()),
            Self::Emulated {
                version, identity, ..
            } => Ok(format!(
                "; emulator_version={version}; emulator_sha256={}",
                sha256_hex(&read_file(identity)?)
            )),
        }
    }
}

fn qemu_arch(target: &str) -> &str {
    let arch = target.split('-').next().unwrap_or(target);
    arch.strip_suffix("gc").unwrap_or(arch)
}

/// Reads `rustc -vV` and the identity of the binary behind it.
fn read_rustc() -> Result<(RustcPin, String)> {
    let output = run(Command::new("rustc").arg("-vV"))?;
    require_success("rustc", &output)?;
    let pin = parse_rustc(&String::from_utf8_lossy(&output.stdout))?;
    let sysroot = run(Command::new("rustc").args(["--print", "sysroot"]))?;
    require_success("rustc", &sysroot)?;
    let binary = PathBuf::from(first_line(&sysroot.stdout)).join("bin/rustc");
    let manifest = format!(
        "command=rustc -vV; rustc_version={}; rustc_host={}; rustc_sha256={}",
        pin.version(),
        pin.host(),
        sha256_hex(&read_file(&binary)?)
    );
    Ok((pin, manifest))
}

fn parse_rustc(text: &str) -> Result<RustcPin> {
    let field = |name: &str| {
        text.lines()
            .find_map(|line| line.strip_prefix(name)?.strip_prefix(": "))
            .ok_or_else(|| {
                VerificationError::new(ErrorCode::Schema, format!("`rustc -vV` has no `{name}`"))
            })
    };
    RustcPin::new(
        field("commit-hash")?,
        field("commit-date")?,
        field("host")?,
        field("LLVM version")?,
        field("release")?,
    )
}

fn find_program(name: &str) -> Option<PathBuf> {
    env::split_paths(&env::var_os("PATH")?)
        .map(|directory| directory.join(name))
        .find(|path| path.is_file())
}

fn first_line(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes)
        .lines()
        .next()
        .unwrap_or_default()
        .replace("; ", ", ")
}

fn run(command: &mut Command) -> Result<Output> {
    command.output().map_err(|error| {
        VerificationError::new(
            ErrorCode::ToolMissing,
            format!("cannot run `{}`: {error}", command.get_program().display()),
        )
    })
}

fn require_success(tool: &str, output: &Output) -> Result<()> {
    if output.status.success() {
        Ok(())
    } else {
        Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!(
                "`{tool}` failed: {}",
                String::from_utf8_lossy(&output.stderr)
                    .chars()
                    .take(500)
                    .collect::<String>()
            ),
        ))
    }
}

fn read_file(path: &Path) -> Result<Vec<u8>> {
    fs::read(path).map_err(|error| io_path(path, &error))
}

fn io_path(path: &Path, error: &std::io::Error) -> VerificationError {
    VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::evidence::TerminalState;

    #[test]
    fn rustc_version_output_becomes_a_pin() {
        let pin = parse_rustc(
            "rustc 1.97.1 (8bab26f4f 2026-07-14)\nbinary: rustc\ncommit-hash: 8bab26f4f68e0e26f0bb7960be334d5b520ea452\ncommit-date: 2026-07-14\nhost: aarch64-apple-darwin\nrelease: 1.97.1\nLLVM version: 22.1.6\n",
        )
        .expect("pin");
        assert_eq!(pin.host(), "aarch64-apple-darwin");
        assert_eq!(pin.version(), "1.97.1");
        parse_rustc("rustc 1.97.1\n").expect_err("a field is missing");
    }

    #[test]
    fn emulators_are_named_for_the_architecture_they_run() {
        assert_eq!(qemu_arch("riscv64gc-unknown-linux-gnu"), "riscv64");
        assert_eq!(qemu_arch("s390x-unknown-linux-gnu"), "s390x");
        assert_eq!(qemu_arch("aarch64-unknown-linux-gnu"), "aarch64");
    }

    #[test]
    fn the_support_source_expects_the_boxed_value_of_int32_42() {
        let expected = bamts_native::Value::int32(42);
        assert_eq!(expected.as_int32(), Some(42));
        let declaration = format!("const INT32_42: u64 = {:#x};", expected.to_bits());
        assert!(support_source().contains(&declaration));
    }

    #[test]
    fn an_emulated_run_names_its_emulator_and_hashes_it() {
        let identity =
            std::env::temp_dir().join(format!("bamts-measure-{}-emulator", std::process::id()));
        fs::write(&identity, "emulator").expect("write");
        let digest = sha256_hex(b"emulator");
        let runner = Runner::Emulated {
            program: PathBuf::from("/usr/bin/qemu-s390x-static"),
            prefix: Vec::new(),
            version: "qemu-s390x 8.2".to_owned(),
            identity: identity.clone(),
        };
        assert_eq!(
            runner.identity_fields().expect("identity"),
            format!("; emulator_version=qemu-s390x 8.2; emulator_sha256={digest}")
        );
        assert_eq!(runner.execution("s390x-unknown-linux-gnu"), "qemu-s390x");
        assert_eq!(
            runner.display("./probe"),
            "/usr/bin/qemu-s390x-static ./probe"
        );
        fs::remove_file(identity).expect("remove");

        let rosetta = Runner::Emulated {
            program: PathBuf::from("/usr/bin/arch"),
            prefix: vec!["-x86_64".to_owned()],
            version: "rosetta".to_owned(),
            identity: PathBuf::from(ROSETTA_RUNTIME),
        };
        assert_eq!(rosetta.execution("x86_64-apple-darwin"), "rosetta");
        assert_eq!(rosetta.display("./probe"), "/usr/bin/arch -x86_64 ./probe");
    }

    #[test]
    fn a_target_with_no_route_from_this_host_is_refused_not_guessed() {
        let work = std::env::temp_dir().join(format!("bamts-measure-{}-norun", std::process::id()));
        let foreign = if bamts_platform::host_triple().contains("windows") {
            "aarch64-apple-darwin"
        } else {
            "x86_64-pc-windows-msvc"
        };
        measure_cell(foreign, &work).expect_err("no route");
        let _ = fs::remove_dir_all(work);
    }

    #[cfg(unix)]
    #[test]
    fn a_probe_that_exits_nonzero_is_not_an_observed_run() {
        use std::os::unix::fs::PermissionsExt;
        let directory =
            std::env::temp_dir().join(format!("bamts-measure-{}-exit", std::process::id()));
        fs::create_dir_all(&directory).expect("scratch");
        let probe = directory.join("probe");
        fs::write(&probe, "#!/bin/sh\nexit 11\n").expect("script");
        fs::set_permissions(&probe, fs::Permissions::from_mode(0o755)).expect("mode");
        let error = run_probe(&Runner::Native, &directory).expect_err("exit 11 is a failure");
        assert_eq!(error.code(), ErrorCode::ToolFailed);
        fs::write(&probe, "#!/bin/sh\nexit 0\n").expect("script");
        run_probe(&Runner::Native, &directory).expect("exit 0 is the probe's success");
        fs::remove_dir_all(directory).expect("remove scratch");
    }

    #[test]
    fn a_mac_cell_without_rosetta_stops_at_the_emulator() {
        if bamts_platform::host_triple() != "aarch64-apple-darwin"
            || Path::new(ROSETTA_RUNTIME).exists()
        {
            return;
        }
        let work = std::env::temp_dir().join(format!("bamts-measure-{}-mac", std::process::id()));
        let measured = measure_cell("x86_64-apple-darwin", &work).expect("measure");
        let _ = fs::remove_dir_all(work);
        assert_eq!(measured.notes.len(), 1, "{:?}", measured.notes);
        let obligations = measured.record.obligations();
        assert_eq!(
            obligations["target-functional"].status(),
            TerminalState::ExternalBlocked
        );
        assert_eq!(
            obligations["target-functional"].missing_artifact(),
            "rosetta"
        );
        assert_eq!(obligations["hardened-link"].status(), TerminalState::Pass);
    }

    #[test]
    fn the_host_cell_measures_end_to_end_on_a_host_with_a_linker() {
        let host = bamts_platform::host_triple();
        if find_linker(&host).is_none() {
            return;
        }
        let work = std::env::temp_dir().join(format!("bamts-measure-{}-host", std::process::id()));
        let measured = measure_cell(&host, &work).expect("measure");
        let _ = fs::remove_dir_all(work);
        assert_eq!(measured.notes, Vec::<String>::new());
        assert_eq!(measured.record.triple(), host);
        assert_eq!(
            measured.record.obligations()["target-functional"].status(),
            TerminalState::Pass
        );
        assert!(measured.record.is_closed(), "{:?}", measured.record);
        measured
            .record
            .check_committable(Path::new("cell.json"))
            .expect("a measured cell passes the committed rules");
    }
}
