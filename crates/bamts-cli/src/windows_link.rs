//! Linking a native executable with the Microsoft linker.
//!
//! The Unix path hands the object and the runtime archive to `cc`. On MSVC the
//! linker is `link.exe`, which is not a compiler driver. It needs the object, the
//! archive, the system libraries that the Rust runtime depends on, and a `LIB`
//! search path that only a Visual Studio command prompt sets. This module finds the
//! linker, builds that search path and builds the command line.
//!
//! The linker is found in this order, and the first answer wins:
//!
//! 1. `BAMTS_LINKER`, which names the linker. A wrong value is an error; the
//!    search does not go on, so a typo cannot pick another linker silently.
//! 2. A `link.exe` on `PATH` that prints the Microsoft banner. Git for Windows puts
//!    a GNU `link.exe` on `PATH`, and it is skipped.
//! 3. The newest Visual Studio with the C++ tools, found with `vswhere.exe` at its
//!    fixed place in the Visual Studio Installer directory.
//!
//! The pure parts build on every host, so their tests run on Linux and macOS too.

use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

#[cfg(target_env = "msvc")]
use std::{
    fs, io,
    path::{Component, Prefix},
    process::Command,
};

#[cfg(target_env = "msvc")]
use bamts_compiler::CancellationToken;

#[cfg(target_env = "msvc")]
use crate::context::ExecutionContext;
#[cfg(target_env = "msvc")]
use crate::driver::{DriverError, capture_process_with_cancel};

/// The text the Microsoft linker prints first, whatever it is asked.
const BANNER: &str = "Microsoft (R) Incremental Linker";

/// The component that a Visual Studio installation needs for `link.exe`.
#[cfg(target_env = "msvc")]
const CPP_TOOLS_COMPONENT: &str = "Microsoft.VisualStudio.Component.VC.Tools.x86.x64";

/// Whether what a program printed is the banner of the Microsoft linker.
fn is_microsoft_linker(stdout: &str, stderr: &str) -> bool {
    stdout.contains(BANNER) || stderr.contains(BANNER)
}

/// The numeric parts of a version-like directory name, such as `14.44.35207` or
/// `10.0.26100.0`. A name with any other part is not a version.
fn version_key(name: &str) -> Option<Vec<u64>> {
    name.split('.').map(|part| part.parse().ok()).collect()
}

/// The newest of the names that are versions, compared part by part, so `14.9` is
/// older than `14.44`.
fn newest_version<'a>(names: impl IntoIterator<Item = &'a str>) -> Option<&'a str> {
    names
        .into_iter()
        .filter_map(|name| version_key(name).map(|key| (key, name)))
        .max_by(|left, right| left.0.cmp(&right.0))
        .map(|(_, name)| name)
}

/// The install path in what `vswhere -property installationPath` printed: its
/// first non-empty line.
fn installation_path(vswhere_output: &str) -> Option<PathBuf> {
    vswhere_output
        .lines()
        .map(str::trim)
        .find(|line| !line.is_empty())
        .map(PathBuf::from)
}

/// The toolset directory of a `link.exe` that sits where Visual Studio puts it,
/// `...\VC\Tools\MSVC\<version>\bin\Host<arch>\<arch>\link.exe`.
fn toolset_of(linker: &Path) -> Option<PathBuf> {
    let host = linker.parent()?.parent()?;
    let binaries = host.parent()?;
    let is_host = host
        .file_name()?
        .to_str()
        .is_some_and(|name| name.len() > 4 && name[..4].eq_ignore_ascii_case("host"));
    (is_host && binaries.file_name()?.eq_ignore_ascii_case("bin"))
        .then(|| binaries.parent().map(Path::to_path_buf))?
}

/// The library directories of a toolset and a Windows SDK, in the order that the
/// Visual Studio command prompt puts them in `LIB`.
fn library_directories(toolset: &Path, sdk_lib: &Path, sdk_version: &str) -> Vec<PathBuf> {
    let versioned = sdk_lib.join(sdk_version);
    vec![
        toolset.join("lib").join("x64"),
        versioned.join("ucrt").join("x64"),
        versioned.join("um").join("x64"),
    ]
}

/// The arguments that link the object and the runtime archive into `output`.
///
/// `/BREPRO` leaves the build time out of the file, so the same inputs give the
/// same bytes. `native_libraries` is what rustc reported for the archive, such as
/// `kernel32.lib ntdll.lib /defaultlib:msvcrt`; the archive carries none of them.
fn link_arguments(
    object: &Path,
    archive: &Path,
    output: &Path,
    native_libraries: &str,
) -> Vec<OsString> {
    let mut arguments: Vec<OsString> = ["/NOLOGO", "/MACHINE:X64", "/SUBSYSTEM:CONSOLE", "/BREPRO"]
        .map(OsString::from)
        .to_vec();
    let mut output_option = OsString::from("/OUT:");
    output_option.push(output);
    arguments.push(output_option);
    arguments.push(object.as_os_str().to_owned());
    arguments.push(archive.as_os_str().to_owned());
    arguments.extend(native_libraries.split_whitespace().map(OsString::from));
    arguments
}

/// What a failed link says. `link.exe` prints its errors on standard output and
/// leaves standard error empty, so both streams are kept, output first.
fn link_diagnostics(stdout: &str, stderr: &str) -> String {
    [stdout, stderr]
        .map(str::trim)
        .into_iter()
        .filter(|text| !text.is_empty())
        .collect::<Vec<_>>()
        .join("\n")
}

/// A variable of the context, found without regard to case: Windows spells the
/// search path `Path`, and the environment of the context is a case-sensitive map.
fn variable(context: &crate::context::ExecutionContext, name: &str) -> Option<OsString> {
    crate::context::env_ignoring_case(context.envs(), name).map(OsStr::to_os_string)
}

/// The linker and everything it needs to run.
#[cfg(target_env = "msvc")]
pub(crate) struct Linker {
    program: PathBuf,
    /// The `LIB` value to give the linker, or `None` when the context has its own.
    library_path: Option<OsString>,
    native_libraries: &'static str,
}

#[cfg(target_env = "msvc")]
impl Linker {
    /// The text to show when the link failed.
    pub(crate) fn diagnostics(&self, output: &std::process::Output) -> String {
        link_diagnostics(
            &String::from_utf8_lossy(&output.stdout),
            &String::from_utf8_lossy(&output.stderr),
        )
    }

    /// The command that links `object` and `archive` into `executable`.
    ///
    /// The linker gets the environment of the context. The two variables that
    /// `link.exe` reads as extra options, `LINK` and `_LINK_`, are dropped, so an
    /// option set in a shell cannot change what is built.
    pub(crate) fn command(
        &self,
        context: &ExecutionContext,
        object: &Path,
        archive: &Path,
        executable: &Path,
    ) -> Command {
        let mut command = context_command(&self.program, context);
        command.env_remove("LINK").env_remove("_LINK_");
        if let Some(library_path) = &self.library_path {
            command.env("LIB", library_path);
        }
        command.args(link_arguments(
            object,
            archive,
            executable,
            self.native_libraries,
        ));
        command
    }
}

/// The system libraries that rustc says the embedded runtime archive needs, which
/// the MSVC linker does not take from the archive.
#[cfg(target_env = "msvc")]
const NODE_NATIVE_LIBRARIES: &str = env!("BAMTS_NODE_NATIVE_LIBS");

/// Finds the linker and the library path to give it.
///
/// # Errors
/// [`DriverError::ToolchainMissing`] when no linker is found, and the probe errors
/// when a program cannot be run.
#[cfg(target_env = "msvc")]
pub(crate) fn discover(
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<Linker, DriverError> {
    discover_with(context, cancel, NODE_NATIVE_LIBRARIES)
}

/// [`discover`] for a given list of the libraries that rustc reported for the
/// runtime archive.
#[cfg(target_env = "msvc")]
fn discover_with(
    context: &ExecutionContext,
    cancel: &CancellationToken,
    native_libraries: &'static str,
) -> Result<Linker, DriverError> {
    let program = if let Some(program) = explicit_linker(context, cancel)? {
        program
    } else if let Some(program) = linker_on_path(context, cancel)? {
        program
    } else if let Some(program) = linker_from_visual_studio(context, cancel)? {
        program
    } else {
        return Err(DriverError::ToolchainMissing {
            program: OsString::from("link.exe"),
        });
    };
    let library_path = library_path(context, &program);
    Ok(Linker {
        program,
        library_path,
        native_libraries,
    })
}

/// The root of the drive in `path`, such as `C:\` for `C:\Windows`.
#[cfg(target_env = "msvc")]
fn drive_root(path: &Path) -> Option<PathBuf> {
    let mut components = path.components();
    match (components.next()?, components.next()?) {
        (Component::Prefix(prefix), Component::RootDir)
            if matches!(prefix.kind(), Prefix::Disk(_) | Prefix::VerbatimDisk(_)) =>
        {
            let mut root = PathBuf::from(prefix.as_os_str());
            root.push(Component::RootDir);
            Some(root)
        }
        _ => None,
    }
}

/// The root of the drive that holds Windows. The system folders that the context
/// does not name are looked for there, so a process with a cleared environment
/// finds them without asking the host process, which keeps the answer the same.
#[cfg(target_env = "msvc")]
fn system_drive(context: &ExecutionContext) -> PathBuf {
    variable(context, "SystemRoot")
        .and_then(|root| drive_root(Path::new(&root)))
        .unwrap_or_else(|| PathBuf::from(r"C:\"))
}

#[cfg(target_env = "msvc")]
fn program_files_x86(context: &ExecutionContext) -> PathBuf {
    variable(context, "ProgramFiles(x86)").map_or_else(
        || system_drive(context).join("Program Files (x86)"),
        PathBuf::from,
    )
}

/// `vswhere` reads the Visual Studio setup store under `ProgramData`. Without it
/// `vswhere` finds no installation and still exits with success.
#[cfg(target_env = "msvc")]
fn program_data(context: &ExecutionContext) -> PathBuf {
    variable(context, "ProgramData")
        .map_or_else(|| system_drive(context).join("ProgramData"), PathBuf::from)
}

/// A command that runs in the working directory of the context with exactly the
/// environment of the context.
#[cfg(target_env = "msvc")]
fn context_command(program: impl AsRef<OsStr>, context: &ExecutionContext) -> Command {
    let mut command = Command::new(program);
    command
        .current_dir(context.cwd())
        .env_clear()
        .envs(context.envs());
    command
}

/// Runs `program /?` and returns what it printed, or `None` when there is no such
/// program.
#[cfg(target_env = "msvc")]
fn ask_for_help(
    program: &Path,
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<Option<std::process::Output>, DriverError> {
    let mut command = context_command(program, context);
    command.arg("/?");
    match capture_process_with_cancel(&mut command, cancel) {
        Ok(Some(output)) => Ok(Some(output)),
        Ok(None) => Err(DriverError::Cancelled),
        Err(source) if source.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(source) => Err(DriverError::ToolchainProbe {
            program: program.as_os_str().to_owned(),
            source,
        }),
    }
}

/// The linker that `BAMTS_LINKER` names. It is taken as it is: any program that
/// starts is accepted, so a compatible linker such as `lld-link.exe` can be named.
#[cfg(target_env = "msvc")]
fn explicit_linker(
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<Option<PathBuf>, DriverError> {
    let Some(value) = variable(context, "BAMTS_LINKER") else {
        return Ok(None);
    };
    let named = Path::new(&value);
    let program = if named.components().count() > 1 {
        context.resolve_path(named)
    } else {
        path_candidates(context, named)
            .next()
            .unwrap_or_else(|| named.to_path_buf())
    };
    match ask_for_help(&program, context, cancel)? {
        Some(_) => Ok(Some(program)),
        None => Err(DriverError::ToolchainMissing { program: value }),
    }
}

/// The files called `name` in the directories of `PATH`, in search order.
#[cfg(target_env = "msvc")]
fn path_candidates(context: &ExecutionContext, name: &Path) -> impl Iterator<Item = PathBuf> {
    let directories: Vec<PathBuf> = variable(context, "PATH")
        .map(|search| std::env::split_paths(&search).collect())
        .unwrap_or_default();
    directories
        .into_iter()
        .map(move |directory| directory.join(name))
        .filter(|candidate| candidate.is_file())
}

/// The first `link.exe` on `PATH` that is the Microsoft linker.
#[cfg(target_env = "msvc")]
fn linker_on_path(
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<Option<PathBuf>, DriverError> {
    for candidate in path_candidates(context, Path::new("link.exe")) {
        match ask_for_help(&candidate, context, cancel) {
            Ok(Some(output))
                if is_microsoft_linker(
                    &String::from_utf8_lossy(&output.stdout),
                    &String::from_utf8_lossy(&output.stderr),
                ) =>
            {
                return Ok(Some(candidate));
            }
            Err(DriverError::Cancelled) => return Err(DriverError::Cancelled),
            // Another program called link.exe, or one that does not start: not ours.
            _ => {}
        }
    }
    Ok(None)
}

/// The `link.exe` of the newest Visual Studio that has the C++ tools.
#[cfg(target_env = "msvc")]
fn linker_from_visual_studio(
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<Option<PathBuf>, DriverError> {
    let vswhere = program_files_x86(context)
        .join("Microsoft Visual Studio")
        .join("Installer")
        .join("vswhere.exe");
    if !vswhere.is_file() {
        return Ok(None);
    }
    let mut command = context_command(&vswhere, context);
    command
        .env("ProgramData", program_data(context))
        .args([
            "-latest",
            "-products",
            "*",
            "-requires",
            CPP_TOOLS_COMPONENT,
        ])
        .args(["-property", "installationPath", "-utf8"]);
    let output = match capture_process_with_cancel(&mut command, cancel) {
        Ok(Some(output)) => output,
        Ok(None) => return Err(DriverError::Cancelled),
        Err(source) => {
            return Err(DriverError::ToolchainProbe {
                program: vswhere.into_os_string(),
                source,
            });
        }
    };
    if !output.status.success() {
        return Ok(None);
    }
    let Some(installation) = installation_path(&String::from_utf8_lossy(&output.stdout)) else {
        return Ok(None);
    };
    let Some(toolset) = toolset_directory(&installation) else {
        return Ok(None);
    };
    let linker = toolset
        .join("bin")
        .join("Hostx64")
        .join("x64")
        .join("link.exe");
    Ok(linker.is_file().then_some(linker))
}

/// The toolset that Visual Studio's own command prompt uses: the one named in
/// `Microsoft.VCToolsVersion.default.txt`, or the newest one when that file does
/// not name an installed one.
#[cfg(target_env = "msvc")]
fn toolset_directory(installation: &Path) -> Option<PathBuf> {
    let tools = installation.join("VC").join("Tools").join("MSVC");
    let default = fs::read_to_string(
        installation
            .join("VC")
            .join("Auxiliary")
            .join("Build")
            .join("Microsoft.VCToolsVersion.default.txt"),
    )
    .ok()
    .map(|text| text.trim().to_owned())
    .filter(|version| !version.is_empty() && tools.join(version).is_dir());
    if let Some(version) = default {
        return Some(tools.join(version));
    }
    let names = entry_names(&tools)?;
    newest_version(names.iter().map(String::as_str)).map(|version| tools.join(version))
}

/// The names of the entries of `directory`, leaving out any that is not text.
#[cfg(target_env = "msvc")]
fn entry_names(directory: &Path) -> Option<Vec<String>> {
    Some(
        fs::read_dir(directory)
            .ok()?
            .filter_map(Result::ok)
            .filter_map(|entry| entry.file_name().into_string().ok())
            .collect(),
    )
}

/// The `LIB` value to give the linker, or `None` when the context sets its own, as
/// a Visual Studio command prompt does, or when the directories cannot be worked
/// out. In that case the linker reports the first library it cannot open.
#[cfg(target_env = "msvc")]
fn library_path(context: &ExecutionContext, linker: &Path) -> Option<OsString> {
    if variable(context, "LIB").is_some() {
        return None;
    }
    let toolset = toolset_of(linker)?;
    let kits = variable(context, "WindowsSdkDir").map_or_else(
        || program_files_x86(context).join("Windows Kits").join("10"),
        PathBuf::from,
    );
    let sdk_lib = kits.join("Lib");
    // An SDK counts when it has both the import libraries and the C runtime ones.
    let complete = |version: &Path| {
        version
            .join("um")
            .join("x64")
            .join("kernel32.lib")
            .is_file()
            && version.join("ucrt").join("x64").join("ucrt.lib").is_file()
    };
    let versions: Vec<String> = entry_names(&sdk_lib)?
        .into_iter()
        .filter(|name| complete(&sdk_lib.join(name)))
        .collect();
    let version = newest_version(versions.iter().map(String::as_str))?;
    std::env::join_paths(library_directories(&toolset, &sdk_lib, version)).ok()
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::context::ExecutionContext;

    fn context_with(variables: &[(&str, &str)]) -> ExecutionContext {
        let env = variables
            .iter()
            .map(|(key, value)| (OsString::from(key), OsString::from(value)))
            .collect::<BTreeMap<_, _>>();
        ExecutionContext::new(std::env::temp_dir(), env).expect("execution context")
    }

    #[test]
    fn only_the_microsoft_banner_marks_the_microsoft_linker() {
        let banner = "Microsoft (R) Incremental Linker Version 14.44.35228.0\nCopyright (C) Microsoft Corporation.  All rights reserved.\n";
        assert!(is_microsoft_linker(banner, ""));
        assert!(is_microsoft_linker("", banner));
        // GNU `link` and the Windows command processor are not the linker.
        assert!(!is_microsoft_linker(
            "",
            "/usr/bin/link: missing operand after '/?'\n"
        ));
        assert!(!is_microsoft_linker(
            "Starts a new instance of the Windows command interpreter\n",
            ""
        ));
        assert!(!is_microsoft_linker("", ""));
    }

    #[test]
    fn versions_are_compared_part_by_part() {
        assert_eq!(version_key("14.44.35207"), Some(vec![14, 44, 35207]));
        assert_eq!(version_key("10.0.26100.0"), Some(vec![10, 0, 26100, 0]));
        assert_eq!(version_key("latest"), None);
        assert_eq!(version_key("14.x"), None);
        assert_eq!(version_key(""), None);

        // A text comparison would put 14.9 after 14.44, and 10.0.9 after 10.0.26100.
        assert_eq!(
            newest_version(["14.9.1", "14.44.35207", "14.43.34808"]),
            Some("14.44.35207")
        );
        assert_eq!(
            newest_version(["10.0.9600.0", "10.0.26100.0", "wdf", "10.0.22621.0"]),
            Some("10.0.26100.0")
        );
        assert_eq!(newest_version(["wdf", "um"]), None);
        assert_eq!(newest_version([]), None);
    }

    #[test]
    fn the_install_path_is_the_first_line_vswhere_prints() {
        assert_eq!(
            installation_path("C:\\Program Files\\Microsoft Visual Studio\\2022\\Community\r\n"),
            Some(PathBuf::from(
                "C:\\Program Files\\Microsoft Visual Studio\\2022\\Community"
            ))
        );
        assert_eq!(
            installation_path("\n  C:\\VS  \nC:\\Older\n"),
            Some(PathBuf::from("C:\\VS"))
        );
        assert_eq!(installation_path(""), None);
        assert_eq!(installation_path("\r\n  \r\n"), None);
    }

    #[test]
    fn the_toolset_is_found_from_the_place_of_link_exe() {
        let linker = Path::new("root/VC/Tools/MSVC/14.44.35207/bin/Hostx64/x64/link.exe");
        assert_eq!(
            toolset_of(linker),
            Some(PathBuf::from("root/VC/Tools/MSVC/14.44.35207"))
        );
        let upper = Path::new("root/MSVC/14.1/BIN/Hostx86/x64/link.exe");
        assert_eq!(toolset_of(upper), Some(PathBuf::from("root/MSVC/14.1")));
        // A linker that is not inside a toolset has none.
        assert_eq!(toolset_of(Path::new("tools/link.exe")), None);
        assert_eq!(toolset_of(Path::new("llvm/bin/x64/lld/link.exe")), None);
        assert_eq!(toolset_of(Path::new("link.exe")), None);
    }

    #[test]
    fn library_directories_follow_the_visual_studio_prompt_order() {
        let directories = library_directories(
            Path::new("tools/14.44"),
            Path::new("kits/Lib"),
            "10.0.26100.0",
        );
        let expected: Vec<PathBuf> = [
            "tools/14.44/lib/x64",
            "kits/Lib/10.0.26100.0/ucrt/x64",
            "kits/Lib/10.0.26100.0/um/x64",
        ]
        .iter()
        .map(PathBuf::from)
        .collect();
        assert_eq!(directories, expected);
    }

    #[test]
    fn the_link_command_line_names_the_inputs_and_the_system_libraries() {
        let arguments = link_arguments(
            Path::new("out/.app.o"),
            Path::new("cache/bamts-node.lib"),
            Path::new("out/app with space.exe"),
            "kernel32.lib  ntdll.lib\t/defaultlib:msvcrt",
        );
        let text: Vec<String> = arguments
            .iter()
            .map(|argument| argument.to_string_lossy().into_owned())
            .collect();
        assert_eq!(
            text,
            [
                "/NOLOGO",
                "/MACHINE:X64",
                "/SUBSYSTEM:CONSOLE",
                "/BREPRO",
                "/OUT:out/app with space.exe",
                "out/.app.o",
                "cache/bamts-node.lib",
                "kernel32.lib",
                "ntdll.lib",
                "/defaultlib:msvcrt",
            ]
        );
        // No system libraries gives no extra arguments, not an empty one.
        let bare = link_arguments(Path::new("a.o"), Path::new("b.lib"), Path::new("c.exe"), "");
        assert_eq!(bare.len(), 7);
    }

    #[test]
    fn a_failed_link_keeps_the_output_and_the_error_stream() {
        let error = "LINK : fatal error LNK1561: entry point must be defined\r\n";
        assert_eq!(link_diagnostics(error, ""), error.trim());
        assert_eq!(link_diagnostics("", " cannot start \n"), "cannot start");
        assert_eq!(link_diagnostics("first\n", "second\n"), "first\nsecond");
        assert_eq!(link_diagnostics("", ""), "");
    }

    #[test]
    fn variables_are_found_without_regard_to_case() {
        let context = context_with(&[("Path", "C:\\a;C:\\b"), ("ProgramFiles(x86)", "D:\\PF")]);
        assert_eq!(
            variable(&context, "PATH"),
            Some(OsString::from("C:\\a;C:\\b"))
        );
        assert_eq!(
            variable(&context, "path"),
            Some(OsString::from("C:\\a;C:\\b"))
        );
        assert_eq!(
            variable(&context, "programfiles(x86)"),
            Some(OsString::from("D:\\PF"))
        );
        assert_eq!(variable(&context, "LIB"), None);
    }

    #[cfg(target_env = "msvc")]
    mod live {
        use std::ffi::OsString;
        use std::path::{Path, PathBuf};

        use bamts_compiler::CancellationToken;

        use super::*;
        use crate::driver::DriverError;

        /// What a hermetic process still has: no `PATH`, no `LIB`, no Visual Studio
        /// command prompt. `extra` replaces or adds variables.
        fn context(extra: &[(&str, &str)]) -> ExecutionContext {
            let mut variables: Vec<(String, String)> =
                ["SystemRoot", "windir", "TEMP", "TMP", "ProgramFiles(x86)"]
                    .into_iter()
                    .filter_map(|name| Some((name.to_owned(), std::env::var(name).ok()?)))
                    .collect();
            for (name, value) in extra {
                variables.retain(|(existing, _)| !existing.eq_ignore_ascii_case(name));
                variables.push(((*name).to_owned(), (*value).to_owned()));
            }
            let pairs: Vec<(&str, &str)> = variables
                .iter()
                .map(|(name, value)| (name.as_str(), value.as_str()))
                .collect();
            context_with(&pairs)
        }

        fn discover_in(context: &ExecutionContext) -> Result<Linker, DriverError> {
            discover_with(context, &CancellationToken::new(), "kernel32.lib ntdll.lib")
        }

        fn visual_studio_linker() -> Linker {
            discover_in(&context(&[])).expect("this host has the Visual Studio C++ tools")
        }

        #[test]
        fn system_folders_are_looked_for_on_the_drive_of_windows() {
            assert_eq!(
                drive_root(Path::new(r"D:\Windows")),
                Some(PathBuf::from(r"D:\"))
            );
            assert_eq!(drive_root(Path::new(r"\\server\share\Windows")), None);
            assert_eq!(drive_root(Path::new("relative")), None);

            let on_d = context_with(&[("SystemRoot", r"D:\Windows")]);
            assert_eq!(system_drive(&on_d), PathBuf::from(r"D:\"));
            assert_eq!(program_data(&on_d), PathBuf::from(r"D:\ProgramData"));
            assert_eq!(
                program_files_x86(&on_d),
                PathBuf::from(r"D:\Program Files (x86)")
            );
            // What the context names is used as it is.
            let named = context_with(&[
                ("SystemRoot", r"D:\Windows"),
                ("ProgramData", r"E:\Data"),
                ("ProgramFiles(x86)", r"E:\PF86"),
            ]);
            assert_eq!(program_data(&named), PathBuf::from(r"E:\Data"));
            assert_eq!(program_files_x86(&named), PathBuf::from(r"E:\PF86"));
            // With nothing to go by, the default drive.
            let bare = context_with(&[]);
            assert_eq!(program_data(&bare), PathBuf::from(r"C:\ProgramData"));
        }

        #[test]
        fn a_hermetic_environment_finds_the_linker_through_vswhere() {
            let linker = visual_studio_linker();

            assert_eq!(
                linker.program.file_name().and_then(|n| n.to_str()),
                Some("link.exe")
            );
            assert!(linker.program.is_file(), "{}", linker.program.display());
            assert!(
                toolset_of(&linker.program).is_some(),
                "{}",
                linker.program.display()
            );
            let library_path = linker.library_path.expect("a hermetic process has no LIB");
            let directories: Vec<PathBuf> = std::env::split_paths(&library_path).collect();
            assert_eq!(directories.len(), 3, "{directories:?}");
            assert!(
                directories.iter().all(|directory| directory.is_dir()),
                "{directories:?}"
            );
            assert!(directories[0].join("msvcrt.lib").is_file());
            assert!(directories[1].join("ucrt.lib").is_file());
            assert!(directories[2].join("kernel32.lib").is_file());
        }

        #[test]
        fn the_microsoft_linker_on_path_is_used_as_found() {
            let found = visual_studio_linker().program;
            let directory = found.parent().expect("link.exe has a directory");
            // No Visual Studio Installer here, so only PATH can give the linker.
            let context = context(&[
                ("Path", &directory.to_string_lossy()),
                ("ProgramFiles(x86)", r"C:\no-such-program-files"),
                (
                    "WindowsSdkDir",
                    &PathBuf::from(std::env::var("ProgramFiles(x86)").expect("ProgramFiles(x86)"))
                        .join("Windows Kits")
                        .join("10")
                        .to_string_lossy(),
                ),
            ]);

            let linker = discover_in(&context).expect("the linker on PATH");

            assert_eq!(linker.program, found.parent().unwrap().join("link.exe"));
            assert!(
                linker.library_path.is_some(),
                "the toolset gives the library path"
            );
        }

        #[test]
        fn a_link_exe_that_is_not_the_microsoft_linker_is_skipped() {
            let scratch = tempfile::tempdir().expect("temporary directory");
            let directory = scratch.path();
            let imposter = directory.join("link.exe");
            let system = std::env::var_os("SystemRoot").expect("SystemRoot");
            std::fs::copy(
                Path::new(&system).join("System32").join("cmd.exe"),
                &imposter,
            )
            .expect("a program that is not a linker");

            let linker = discover_in(&context(&[("Path", &directory.to_string_lossy())]))
                .expect("Visual Studio still gives the linker");
            assert_ne!(linker.program, imposter);
            assert!(
                toolset_of(&linker.program).is_some(),
                "{}",
                linker.program.display()
            );
        }

        #[test]
        fn an_explicit_linker_wins_and_a_wrong_one_is_an_error() {
            let real = visual_studio_linker().program;

            let chosen = discover_in(&context(&[("BAMTS_LINKER", &real.to_string_lossy())]))
                .expect("the named linker");
            assert_eq!(chosen.program, real);

            let wrong = discover_in(&context(&[("BAMTS_LINKER", r"C:\no\such\link.exe")]));
            // The search does not go on to Visual Studio, which is installed here.
            assert!(
                matches!(
                    &wrong,
                    Err(DriverError::ToolchainMissing { program })
                        if program == &OsString::from(r"C:\no\such\link.exe")
                ),
                "{:?}",
                wrong.err()
            );
        }

        #[test]
        fn no_linker_anywhere_is_reported_as_missing() {
            let context = context(&[("ProgramFiles(x86)", r"C:\no-such-program-files")]);

            let error = discover_in(&context).err().expect("there is no linker");

            assert!(
                matches!(&error, DriverError::ToolchainMissing { program }
                    if program == &OsString::from("link.exe")),
                "{error}"
            );
        }

        #[test]
        fn the_library_path_of_the_context_is_kept_and_link_options_are_dropped() {
            let context = context(&[
                ("LIB", r"C:\my\libs"),
                ("LINK", "/DEBUG"),
                ("_LINK_", "/OPT:NOREF"),
            ]);
            let linker = discover_in(&context).expect("the linker");
            assert!(linker.library_path.is_none(), "the context has its own LIB");

            let command = linker.command(
                &context,
                Path::new("a.o"),
                Path::new("b.lib"),
                Path::new("c.out"),
            );
            let set = |name: &str| {
                command
                    .get_envs()
                    .find(|(key, _)| {
                        key.to_str()
                            .is_some_and(|key| key.eq_ignore_ascii_case(name))
                    })
                    .map(|(_, value)| value.map(OsString::from))
            };
            assert_eq!(set("LIB"), Some(Some(OsString::from(r"C:\my\libs"))));
            // The environment was cleared first, so a removed variable is absent.
            assert_eq!(set("LINK"), None);
            assert_eq!(set("_LINK_"), None);
        }

        #[test]
        fn the_command_runs_the_linker_with_the_link_arguments() {
            let context = context(&[]);
            let linker = discover_in(&context).expect("the linker");

            let command = linker.command(
                &context,
                Path::new("a.o"),
                Path::new("b.lib"),
                Path::new("c.out"),
            );

            assert_eq!(command.get_program(), linker.program.as_os_str());
            let arguments: Vec<OsString> = command.get_args().map(OsString::from).collect();
            assert_eq!(
                arguments,
                link_arguments(
                    Path::new("a.o"),
                    Path::new("b.lib"),
                    Path::new("c.out"),
                    "kernel32.lib ntdll.lib"
                )
            );
            assert_eq!(command.get_current_dir(), Some(context.cwd()));
            let library_path = command
                .get_envs()
                .find(|(key, _)| key.eq_ignore_ascii_case("LIB"))
                .and_then(|(_, value)| value);
            assert_eq!(library_path, linker.library_path.as_deref());
        }
    }
}
