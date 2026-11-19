use super::*;
use super::process::*;
use bamts_compiler::program::lower_program;
use bamts_compiler::program::lower_program_with_cancel;
use bamts_runtime::run_linked_program_tiered;
use bamts_runtime::WarmupPolicy;
use std::ffi::OsStr;
use std::fs::File;
use std::fs::OpenOptions;
use std::io::Write;
use std::process::Command;
use std::process::Output;
use std::sync::atomic::Ordering;

pub(super) fn check(args: &CliArgs, frontend: &LoadedProgramFrontend) -> Result<CommandOutcome, DriverError> {
    let diagnostics = render_program_diagnostics(args, frontend);
    if frontend
        .output
        .modules()
        .iter()
        .any(|module| module.has_errors())
    {
        return Err(DriverError::Diagnostics {
            rendered: diagnostics.text,
            truncation: diagnostics.truncation,
        });
    }
    Ok(CommandOutcome {
        stderr: diagnostics.text.into_bytes(),
        truncation: diagnostics.truncation,
        ..CommandOutcome::default()
    })
}

pub(super) fn compile_in_context_with_cancel(
    args: &CliArgs,
    frontend: &LoadedProgramFrontend,
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<CommandOutcome, DriverError> {
    if !args.extra_inputs.is_empty() {
        return Err(DriverError::MultipleCompileInputs);
    }
    if args.target != ExecutionTarget::Aot {
        return Err(DriverError::UnsupportedCompileTarget(args.target));
    }
    if args.output.emit_declarations {
        return Err(DriverError::UnsupportedOutputOption("--emit-declarations"));
    }
    if args.output.source_maps {
        return Err(DriverError::UnsupportedOutputOption("--source-maps"));
    }

    let entrypoint = required_entrypoint(args)?;
    let warnings = require_clean_frontend(args, frontend)?;
    let executable = lower_program_with_cancel(
        &frontend.program,
        &frontend.output,
        lower_options(args),
        cancel,
    )
    .map_err(DriverError::Lower)?;
    if BUILD_TARGET != HOST_TARGET {
        return Err(DriverError::CrossTargetLink {
            host: HOST_TARGET,
            target: BUILD_TARGET,
        });
    }
    let object = bamts_codegen::compile_aot_with_cancel(executable.wire(), HOST_TARGET, cancel)
        .map_err(|error| match error {
            bamts_codegen::AotError::Cancelled => DriverError::Cancelled,
            error => DriverError::Aot(error),
        })?;
    let destination = output_path(args, entrypoint, context)?;
    link_executable(&object.bytes, &destination, context, cancel)?;
    Ok(CommandOutcome {
        stderr: warnings.text.into_bytes(),
        truncation: warnings.truncation,
        ..CommandOutcome::default()
    })
}

pub(super) fn run_in_context_with_cancel(
    args: &CliArgs,
    frontend: &LoadedProgramFrontend,
    context: &ExecutionContext,
    cancel: &CancellationToken,
    limits: &Limits,
) -> Result<CommandOutcome, DriverError> {
    let entrypoint = required_entrypoint(args)?;
    let warnings = require_runnable_frontend(args, frontend)?;
    let executable = lower_program_with_cancel(
        &frontend.program,
        &frontend.output,
        lower_options(args),
        cancel,
    )
    .map_err(DriverError::Lower)?;
    let inputs = RunInputs {
        args,
        entrypoint,
        warnings,
        executable: &executable,
        context,
    };
    match args.target {
        ExecutionTarget::Jit => run_jit(inputs, cancel, limits),
        ExecutionTarget::Aot => run_aot(inputs, cancel),
    }
}

/// The inputs that travel together through one run: what the caller asked
/// for, the lowered program, and where the process stands.
pub(super) struct RunInputs<'a> {
    pub(super) args: &'a CliArgs,
    pub(super) entrypoint: &'a Path,
    pub(super) warnings: RenderedDiagnostics,
    pub(super) executable: &'a bamts_compiler::program::ExecutableProgram,
    pub(super) context: &'a ExecutionContext,
}

impl RunInputs<'_> {
    /// Builds the host with the environment, argv, and script compiler that a
    /// program run observes.
    pub(super) fn host(&self) -> Result<bamts_node::NodeHost, DriverError> {
        let mut host = bamts_node::NodeHost::new();
        populate_node_environment(&mut host, self.context)?;
        host.set_script_compiler(Box::new(bamts::ScriptCompiler));
        host.set_argv(
            ["bamts".to_owned(), self.entrypoint.display().to_string()]
                .into_iter()
                .chain(self.args.program_args.iter().cloned()),
        );
        Ok(host)
    }

    /// Assembles the outcome from the host's captured streams and the engine's
    /// completion.
    pub(super) fn outcome(
        self,
        host: &bamts_node::NodeHost,
        outcome: bamts_runtime::ExecutionOutcome,
    ) -> CommandOutcome {
        let mut stdout = host.stdout().to_vec();
        stdout.extend_from_slice(&outcome.stdout);
        let exit_code = host.completion_exit_code(outcome.exit_code);
        let mut stderr = self.warnings.text.into_bytes();
        stderr.extend_from_slice(host.stderr());
        CommandOutcome {
            stdout,
            stderr,
            exit_code,
            truncation: self.warnings.truncation,
        }
    }
}

/// Runs a program in the JIT on a thread of its own, with the stack that the AOT tier
/// gives a program. The thread that calls the driver can have much less, as the
/// worker of the npm package does. A builtin that calls builtins adds no guest
/// frame, so only the native stack bound stops it, and both tiers stop it at the
/// same depth.
pub(super) fn run_jit(
    inputs: RunInputs<'_>,
    cancel: &CancellationToken,
    limits: &Limits,
) -> Result<CommandOutcome, DriverError> {
    std::thread::scope(|scope| {
        let program = std::thread::Builder::new()
            .name("bamts-jit".to_owned())
            .stack_size(Limits::PROGRAM_STACK)
            .spawn_scoped(scope, || run_jit_program(inputs, cancel, limits))
            .map_err(DriverError::ProgramThread)?;
        program
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

pub(super) fn run_jit_program(
    inputs: RunInputs<'_>,
    cancel: &CancellationToken,
    limits: &Limits,
) -> Result<CommandOutcome, DriverError> {
    let program = bamts_codegen::compile_jit_with_cancel(inputs.executable.wire(), cancel)
        .map_err(|error| match error {
            bamts_codegen::JitError::Cancelled => DriverError::Cancelled,
            error => DriverError::Jit(error),
        })?;
    let mut host = inputs.host()?;
    let (tiered, _) = run_linked_program_tiered(
        inputs.executable.wire(),
        &program,
        &mut host,
        limits,
        WarmupPolicy::DEFAULT,
        cancel.clone(),
    )
    .map_err(DriverError::Native)?;
    let outcome = tiered.map_err(DriverError::Native)?;
    Ok(inputs.outcome(&host, outcome))
}

/// Runs a program in the AOT tier. Its image is a linked executable in its own
/// process with the program limits and the CLI argv, so the caller's budget does
/// not reach it; cancellation terminates the child.
pub(super) fn run_aot(
    inputs: RunInputs<'_>,
    cancel: &CancellationToken,
) -> Result<CommandOutcome, DriverError> {
    let args = inputs.args;
    let entrypoint = inputs.entrypoint;
    let context = inputs.context;
    let warnings = inputs.warnings;
    if BUILD_TARGET != HOST_TARGET {
        return Err(DriverError::CrossTargetLink {
            host: HOST_TARGET,
            target: BUILD_TARGET,
        });
    }
    let object =
        bamts_codegen::compile_aot_with_cancel(inputs.executable.wire(), HOST_TARGET, cancel)
            .map_err(|error| match error {
                bamts_codegen::AotError::Cancelled => DriverError::Cancelled,
                error => DriverError::Aot(error),
            })?;
    let id = NEXT_CACHE_TEMP_ID.fetch_add(1, Ordering::Relaxed);
    let root = cache_root(context)?;
    let destination = root.join("run").join(format!(
        "bamts-run-{}-{id}{}",
        std::process::id(),
        std::env::consts::EXE_SUFFIX
    ));
    require_within_cache_root(&destination, &root)?;
    link_executable(&object.bytes, &destination, context, cancel)?;
    let _published = claim_published_executable(&destination, cancel)?;
    require_within_cache_root(&destination, &root)?;
    let launch_token = format!("{}-{id}", std::process::id());
    let mut command = Command::new(&destination);
    command
        .current_dir(context.cwd())
        .env_clear()
        .envs(context.envs())
        .env(bamts_node::AOT_ENTRYPOINT_ENV, entrypoint.as_os_str())
        .env(bamts_node::AOT_LAUNCH_TOKEN_ENV, &launch_token)
        .arg(launch_token)
        .args(&args.program_args);
    let output = capture_process_with_cancel(&mut command, cancel);
    let output = output
        .map_err(|source| DriverError::LinkStart {
            program: destination.into_os_string(),
            source,
        })?
        .ok_or(DriverError::Cancelled)?;
    let mut stderr = warnings.text.into_bytes();
    stderr.extend_from_slice(&output.stderr);
    Ok(CommandOutcome {
        stdout: output.stdout,
        stderr,
        exit_code: output.status.code().unwrap_or(1),
        truncation: warnings.truncation,
    })
}
#[derive(Debug)]
pub(super) struct PublishedExecutable {
    path: PathBuf,
}

impl Drop for PublishedExecutable {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

pub(super) fn claim_published_executable(
    destination: &Path,
    cancel: &CancellationToken,
) -> Result<PublishedExecutable, DriverError> {
    let published = PublishedExecutable {
        path: destination.to_owned(),
    };
    cancel.check().map_err(|_| DriverError::Cancelled)?;
    Ok(published)
}

pub(super) fn populate_node_environment(
    host: &mut bamts_node::NodeHost,
    context: &ExecutionContext,
) -> Result<(), DriverError> {
    for (name, value) in context.envs() {
        let name = name
            .to_str()
            .ok_or(DriverError::NonUnicodeEnvironmentName)?;
        let value = value
            .to_str()
            .ok_or_else(|| DriverError::NonUnicodeEnvironmentValue {
                name: name.to_owned(),
            })?;
        host.set_env(name, value);
    }
    Ok(())
}

pub(super) fn output_path(
    args: &CliArgs,
    entrypoint: &Path,
    context: &ExecutionContext,
) -> Result<PathBuf, DriverError> {
    if let Some(file) = &args.output.file {
        return Ok(context.resolve_path(file));
    }
    let file_name = entrypoint
        .file_stem()
        .filter(|name| !name.is_empty())
        .unwrap_or_else(|| OsStr::new("a"));
    let mut file_name = file_name.to_os_string();
    file_name.push(std::env::consts::EXE_SUFFIX);
    if let Some(directory) = &args.output.dir {
        let directory = context.resolve_path(directory);
        fs::create_dir_all(&directory).map_err(|source| DriverError::CreateDirectory {
            path: directory.clone(),
            source,
        })?;
        return Ok(directory.join(file_name));
    }
    Ok(entrypoint.with_file_name(file_name))
}

pub(super) fn link_executable(
    object: &[u8],
    destination: &Path,
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<(), DriverError> {
    let destination = context.resolve_path(destination);
    let parent = destination.parent().unwrap_or_else(|| Path::new("."));
    fs::create_dir_all(parent).map_err(|source| DriverError::CreateDirectory {
        path: parent.to_owned(),
        source,
    })?;
    let archive = cached_node_archive(context)?;
    let linker = discover_linker(context, cancel)?;
    let temporary = TemporaryLinkFiles::create(parent, &destination)?;
    fs::write(&temporary.object, object).map_err(|source| DriverError::WriteObject {
        path: temporary.object.clone(),
        source,
    })?;

    let mut command = linker.command(context, &temporary.object, &archive, &temporary.executable);
    let output = capture_process_with_cancel(&mut command, cancel)
        .map_err(|source| DriverError::LinkStart {
            program: command.get_program().to_owned(),
            source,
        })?
        .ok_or(DriverError::Cancelled)?;
    if !output.status.success() {
        return Err(DriverError::LinkFailed {
            program: command.get_program().to_owned(),
            status: output.status,
            stderr: linker.diagnostics(&output),
        });
    }
    publish_linked_executable(&temporary.executable, &destination)
}

/// The system C compiler that links on every host except Windows MSVC.
#[cfg(not(target_env = "msvc"))]
pub(super) struct Linker {
    compiler: OsString,
}

#[cfg(not(target_env = "msvc"))]
impl Linker {
    pub(super) fn command(
        &self,
        context: &ExecutionContext,
        object: &Path,
        archive: &Path,
        executable: &Path,
    ) -> Command {
        let mut command = Command::new(&self.compiler);
        command
            .current_dir(context.cwd())
            .env_clear()
            .envs(context.envs())
            .arg(object)
            .arg(archive)
            .arg("-o")
            .arg(executable);
        if cfg!(target_os = "linux") {
            command.args(["-ldl", "-lpthread", "-lm"]);
        }
        command
    }

    pub(super) fn diagnostics(&self, output: &Output) -> String {
        String::from_utf8_lossy(&output.stderr).into_owned()
    }
}

#[cfg(not(target_env = "msvc"))]
pub(super) fn discover_linker(
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<Linker, DriverError> {
    discover_toolchain(context, cancel).map(|compiler| Linker { compiler })
}

#[cfg(target_env = "msvc")]
use crate::windows_link::discover as discover_linker;

#[cfg(not(target_env = "msvc"))]
pub(super) fn discover_toolchain(
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<OsString, DriverError> {
    let program = context
        .env("CC")
        .map_or_else(|| OsString::from("cc"), OsStr::to_os_string);
    probe_toolchain_in_context(program, context, cancel)
}

#[cfg(any(test, not(target_env = "msvc")))]
pub(super) fn probe_toolchain_in_context(
    program: OsString,
    context: &ExecutionContext,
    cancel: &CancellationToken,
) -> Result<OsString, DriverError> {
    let mut command = Command::new(&program);
    command
        .current_dir(context.cwd())
        .env_clear()
        .envs(context.envs())
        .arg("--version");
    match capture_process_with_cancel(&mut command, cancel) {
        Ok(Some(output)) if output.status.success() => Ok(program),
        Ok(Some(output)) => Err(DriverError::ToolchainRejected {
            program,
            status: output.status,
        }),
        Ok(None) => Err(DriverError::Cancelled),
        Err(source) if source.kind() == io::ErrorKind::NotFound => {
            Err(DriverError::ToolchainMissing { program })
        }
        Err(source) => Err(DriverError::ToolchainProbe { program, source }),
    }
}

#[cfg(test)]
pub(super) fn probe_toolchain(program: OsString) -> Result<OsString, DriverError> {
    let context = ExecutionContext::ambient()?;
    probe_toolchain_in_context(program, &context, &CancellationToken::new())
}
pub(super) fn cached_node_archive(context: &ExecutionContext) -> Result<PathBuf, DriverError> {
    let cache_dir = cache_root(context)?.join("runtime");
    fs::create_dir_all(&cache_dir).map_err(|source| DriverError::CacheArchive {
        path: cache_dir.clone(),
        source,
    })?;
    let extension = if cfg!(target_env = "msvc") {
        "lib"
    } else {
        "a"
    };
    let path = cache_dir.join(format!(
        "bamts-node-{:016x}.{extension}",
        content_hash(NODE_STATICLIB)
    ));
    if path.is_file() {
        return Ok(path);
    }
    let (temporary, mut file) = loop {
        let id = NEXT_CACHE_TEMP_ID.fetch_add(1, Ordering::Relaxed);
        let temporary =
            path.with_extension(format!("{extension}.{}.{}.tmp", std::process::id(), id));
        match OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)
        {
            Ok(file) => break (temporary, file),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(source) => {
                return Err(DriverError::CacheArchive {
                    path: temporary,
                    source,
                });
            }
        }
    };
    if let Err(error) = write_cached_archive(&mut file, &temporary) {
        drop(file);
        let _ = fs::remove_file(&temporary);
        return Err(error);
    }
    drop(file);
    match fs::rename(&temporary, &path) {
        Ok(()) => Ok(path),
        Err(_error) if path.is_file() => {
            let _ = fs::remove_file(&temporary);
            Ok(path)
        }
        Err(source) => {
            let _ = fs::remove_file(&temporary);
            Err(DriverError::CacheArchive { path, source })
        }
    }
}

pub(super) fn write_cached_archive(file: &mut File, path: &Path) -> Result<(), DriverError> {
    file.write_all(NODE_STATICLIB)
        .and_then(|()| file.sync_all())
        .map_err(|source| DriverError::CacheArchive {
            path: path.to_owned(),
            source,
        })
}

pub(super) fn cache_root(context: &ExecutionContext) -> Result<PathBuf, DriverError> {
    if let Some(path) = context.env("BAMTS_CACHE_DIR") {
        return Ok(context.resolve_path(path));
    }
    if let Some(path) = context.env("XDG_CACHE_HOME") {
        return Ok(context.resolve_path(path).join("bamts"));
    }
    if let Some(path) = context.env("HOME") {
        return Ok(context.resolve_path(path).join(".cache/bamts"));
    }
    ensure_private_fallback_cache_root_in_context(
        fallback_cache_root_path_in_context(context)?,
        context,
    )
}

#[cfg(unix)]
pub(super) fn fallback_cache_root_path_in_context(context: &ExecutionContext) -> Result<PathBuf, DriverError> {
    let parent = validate_fallback_parent_chain_in_context(context.temp_dir(), context)?;
    Ok(parent.join(format!(
        "bamts-cache-{}",
        fallback_cache_user_key_in_context(context)?
    )))
}

#[cfg(not(unix))]
pub(super) fn fallback_cache_root_path_in_context(context: &ExecutionContext) -> Result<PathBuf, DriverError> {
    #[cfg(windows)]
    if is_windows_temp_directory(context.temp_dir(), context) {
        return Err(DriverError::UnsafeFallbackCacheRoot {
            path: context.temp_dir().to_owned(),
        });
    }
    Ok(context.temp_dir().join(format!(
        "bamts-cache-{}",
        fallback_cache_user_key_in_context(context)?
    )))
}

/// Whether `directory` is in the temporary directory of Windows itself. A process with
/// no `TMP`, `TEMP` or `USERPROFILE` falls back to it, and so does the SYSTEM account.
/// Every user can create a directory there, so another user could make the cache
/// first, and a link trusts the archive and the libraries that it finds in the cache.
/// Windows has no check here like the owner and mode check of a Unix fallback.
#[cfg(windows)]
pub(super) fn is_windows_temp_directory(directory: &Path, context: &ExecutionContext) -> bool {
    // One directory has many spellings: slashes, `\\?\`, a short name, a junction.
    // Only a directory that exists has a canonical path, so a new one resolves through
    // its nearest parent that exists, and a path on no drive compares by components.
    let identity = |path: &Path| -> PathBuf {
        path.ancestors()
            .find_map(|ancestor| {
                let parent = std::fs::canonicalize(ancestor).ok()?;
                Some(parent.join(path.strip_prefix(ancestor).ok()?))
            })
            .unwrap_or_else(|| path.components().collect())
            .to_string_lossy()
            .to_ascii_lowercase()
            .into()
    };
    let directory = identity(directory);
    ["SystemRoot", "WINDIR"]
        .into_iter()
        .filter_map(|name| crate::context::env_ignoring_case(context.envs(), name))
        .map(|root| Path::new(root).join("Temp"))
        .chain([PathBuf::from(r"C:\Windows\Temp")])
        .any(|shared| directory.starts_with(identity(&shared)))
}

#[cfg(unix)]
pub(super) fn fallback_cache_user_key_in_context(context: &ExecutionContext) -> Result<String, DriverError> {
    Ok(effective_uid_in_context(context)?.to_string())
}

#[cfg(not(unix))]
pub(super) fn fallback_cache_user_key_in_context(context: &ExecutionContext) -> Result<String, DriverError> {
    Ok(context
        .env("USERNAME")
        .or_else(|| context.env("USER"))
        .map(|value| value.to_string_lossy().into_owned())
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| "default".to_owned()))
}

#[cfg(all(test, unix))]
pub(super) fn fallback_cache_root_path() -> Result<PathBuf, DriverError> {
    let context = ExecutionContext::ambient()?;
    fallback_cache_root_path_in_context(&context)
}

pub(super) fn ensure_private_fallback_cache_root_in_context(
    path: PathBuf,
    context: &ExecutionContext,
) -> Result<PathBuf, DriverError> {
    #[cfg(unix)]
    let path = {
        let parent = path
            .parent()
            .ok_or_else(|| DriverError::UnsafeFallbackCacheRoot { path: path.clone() })?;
        let name = path
            .file_name()
            .ok_or_else(|| DriverError::UnsafeFallbackCacheRoot { path: path.clone() })?;
        validate_fallback_parent_chain_in_context(parent, context)?.join(name)
    };
    match create_private_fallback_dir(&path) {
        Ok(()) => {}
        Err(source) if source.kind() == io::ErrorKind::AlreadyExists => {}
        Err(source) => {
            return Err(DriverError::CreateDirectory { path, source });
        }
    }
    validate_private_fallback_dir_in_context(&path, context)?;
    Ok(path)
}

#[cfg(unix)]
pub(super) fn create_private_fallback_dir(path: &Path) -> io::Result<()> {
    use std::os::unix::fs::DirBuilderExt;
    fs::DirBuilder::new().mode(0o700).create(path)
}

#[cfg(not(unix))]
pub(super) fn create_private_fallback_dir(path: &Path) -> io::Result<()> {
    fs::create_dir(path)
}

#[cfg(unix)]
pub(super) fn validate_fallback_parent_chain_in_context(
    path: &Path,
    context: &ExecutionContext,
) -> Result<PathBuf, DriverError> {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    let canonical = fs::canonicalize(path).map_err(|source| DriverError::CreateDirectory {
        path: path.to_owned(),
        source,
    })?;
    let euid = effective_uid_in_context(context)?;
    for ancestor in canonical.ancestors() {
        let metadata =
            fs::symlink_metadata(ancestor).map_err(|source| DriverError::CreateDirectory {
                path: ancestor.to_owned(),
                source,
            })?;
        let mode = metadata.permissions().mode();
        let writable = mode & 0o022 != 0;
        let owner = metadata.uid();
        let protected_by_sticky_owner = mode & 0o1000 != 0 && (owner == 0 || owner == euid);
        if !metadata.is_dir() || (writable && !protected_by_sticky_owner) {
            return Err(DriverError::UnsafeFallbackCacheRoot {
                path: ancestor.to_owned(),
            });
        }
    }
    Ok(canonical)
}

#[cfg(unix)]
pub(super) fn validate_private_fallback_dir_in_context(
    path: &Path,
    context: &ExecutionContext,
) -> Result<(), DriverError> {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    let metadata = fs::symlink_metadata(path).map_err(|source| DriverError::CreateDirectory {
        path: path.to_owned(),
        source,
    })?;
    let euid = effective_uid_in_context(context)?;
    let permissions = metadata.permissions().mode() & 0o777;
    if metadata.file_type().is_symlink()
        || !metadata.is_dir()
        || metadata.uid() != euid
        || permissions & 0o077 != 0
    {
        return Err(DriverError::UnsafeFallbackCacheRoot {
            path: path.to_owned(),
        });
    }
    Ok(())
}

#[cfg(not(unix))]
pub(super) fn validate_private_fallback_dir_in_context(
    path: &Path,
    _context: &ExecutionContext,
) -> Result<(), DriverError> {
    let metadata = fs::metadata(path).map_err(|source| DriverError::CreateDirectory {
        path: path.to_owned(),
        source,
    })?;
    if !metadata.is_dir() {
        return Err(DriverError::UnsafeFallbackCacheRoot {
            path: path.to_owned(),
        });
    }
    Ok(())
}

#[cfg(all(test, unix))]
pub(super) fn ensure_private_fallback_cache_root(path: PathBuf) -> Result<PathBuf, DriverError> {
    let context = ExecutionContext::ambient()?;
    ensure_private_fallback_cache_root_in_context(path, &context)
}

#[cfg(all(test, unix))]
pub(super) fn validate_fallback_parent_chain(path: &Path) -> Result<PathBuf, DriverError> {
    let context = ExecutionContext::ambient()?;
    validate_fallback_parent_chain_in_context(path, &context)
}
/// Probe the effective user id without `unsafe` through an atomic random file.
#[cfg(unix)]
pub(super) fn effective_uid_in_context(context: &ExecutionContext) -> Result<u32, DriverError> {
    use std::os::unix::fs::MetadataExt;

    let parent = context.temp_dir().to_owned();
    let probe = tempfile::Builder::new()
        .prefix(".bamts-euid-")
        .tempfile_in(&parent)
        .map_err(|source| DriverError::CreateDirectory {
            path: parent,
            source,
        })?;
    probe
        .as_file()
        .metadata()
        .map(|metadata| metadata.uid())
        .map_err(|source| DriverError::CreateDirectory {
            path: probe.path().to_owned(),
            source,
        })
}

#[cfg(all(test, unix))]
pub(super) fn effective_uid() -> Result<u32, DriverError> {
    let context = ExecutionContext::ambient()?;
    effective_uid_in_context(&context)
}

pub(super) fn require_within_cache_root(path: &Path, root: &Path) -> Result<(), DriverError> {
    if path.starts_with(root) {
        Ok(())
    } else {
        Err(DriverError::UnsafeFallbackCacheRoot {
            path: path.to_owned(),
        })
    }
}

pub(super) const fn content_hash(bytes: &[u8]) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64;
    let mut index = 0;
    while index < bytes.len() {
        hash ^= bytes[index] as u64;
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        index += 1;
    }
    hash
}

pub(super) struct TemporaryLinkFiles {
    object: PathBuf,
    executable: PathBuf,
}

impl TemporaryLinkFiles {
    pub(super) fn create(parent: &Path, destination: &Path) -> Result<Self, DriverError> {
        let stem = destination
            .file_name()
            .unwrap_or_else(|| OsStr::new("bamts-output"))
            .to_string_lossy();
        for attempt in 0_u32..128 {
            let prefix = format!(".{stem}.bamts-{}-{attempt}", std::process::id());
            let object = parent.join(format!("{prefix}.o"));
            match OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&object)
            {
                Ok(_) => {
                    return Ok(Self {
                        object,
                        executable: parent.join(format!("{prefix}.out")),
                    });
                }
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(source) => {
                    return Err(DriverError::WriteObject {
                        path: object,
                        source,
                    });
                }
            }
        }
        Err(DriverError::WriteObject {
            path: parent.to_owned(),
            source: io::Error::new(
                io::ErrorKind::AlreadyExists,
                "temporary-name attempts exhausted",
            ),
        })
    }
}

impl Drop for TemporaryLinkFiles {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.object);
        let _ = fs::remove_file(&self.executable);
    }
}

pub(super) fn publish_linked_executable(temporary: &Path, destination: &Path) -> Result<(), DriverError> {
    match fs::rename(temporary, destination) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            fs::remove_file(destination).map_err(|source| DriverError::PublishExecutable {
                path: destination.to_owned(),
                source,
            })?;
            fs::rename(temporary, destination).map_err(|source| DriverError::PublishExecutable {
                path: destination.to_owned(),
                source,
            })
        }
        Err(source) => Err(DriverError::PublishExecutable {
            path: destination.to_owned(),
            source,
        }),
    }
}

/// Compiles a source entrypoint through the same frontend, lint, and lowering
/// pipeline as [`execute`], returning the lowered executable program without
/// running or linking it.  This is the in-process interpreter seam used by the
/// corpus differential harness so that CLI-supplied lint overrides and
/// JavaScript-compatibility flags reach the lowering stage.
///
/// Type diagnostics do not block lowering. That matches TypeScript's default
/// emit-on-error policy; `check` still fail-closes on error diagnostics.
pub fn compile_program(
    args: &CliArgs,
) -> Result<bamts_compiler::program::ExecutableProgram, DriverError> {
    let frontend = load_program_frontend(args)?;
    let _diagnostics = require_clean_frontend(args, &frontend)?;
    lower_program(&frontend.program, &frontend.output, lower_options(args))
        .map_err(DriverError::Lower)
}
