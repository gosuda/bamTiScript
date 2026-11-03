//! Pure output-path planning and durable atomic artifact publication.
//!
//! Planning is deliberately lexical: callers provide an absolute output root, and no
//! filesystem lookup (including symlink resolution) occurs. Publication is isolated
//! behind [`AtomicFs`] so the write protocol can be tested without touching a real
//! filesystem.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fs::{File, OpenOptions};
use std::io::{self, Write};
use std::path::{Component, Path, PathBuf};

/// The kind of compiler artifact assigned to an output path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArtifactKind {
    /// Executable JavaScript (`.js`, `.mjs`, or `.cjs`).
    JavaScript,
    /// A TypeScript declaration (`.d.ts`).
    Declaration,
    /// A source map for the JavaScript artifact (`.map`).
    SourceMap,
}

/// One normalized source-to-output assignment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlannedArtifact {
    /// The normalized absolute entrypoint that produces this artifact.
    pub source: PathBuf,
    /// The normalized absolute destination path.
    pub path: PathBuf,
    /// The artifact written at `path`.
    pub kind: ArtifactKind,
}

/// A complete, collision-free output plan.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutputPlan {
    /// The normalized absolute confinement root.
    pub root: PathBuf,
    /// Artifacts in entrypoint order, then JavaScript/declaration/source-map order.
    pub artifacts: Vec<PlannedArtifact>,
}

/// Inputs to pure output planning.
///
/// Relative entrypoints and output options are interpreted beneath `root`. An absolute
/// path is accepted only when its lexical normalization remains beneath `root`.
#[derive(Debug, Clone, Copy)]
pub struct PlanRequest<'a> {
    /// Absolute lexical confinement root.
    pub root: &'a Path,
    /// Source entrypoints to compile.
    pub entrypoints: &'a [PathBuf],
    /// Exact JavaScript output path, valid for one entrypoint only.
    pub output_file: Option<&'a Path>,
    /// Output directory. Source-relative subdirectories are preserved beneath it.
    pub output_dir: Option<&'a Path>,
    /// Whether to plan `.d.ts` companions.
    pub emit_declarations: bool,
    /// Whether to plan JavaScript source-map companions.
    pub source_maps: bool,
}

/// A rejected output plan.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlanError {
    /// A pure planner cannot resolve a relative confinement root without consulting the
    /// process environment.
    RootNotAbsolute { root: PathBuf },
    /// At least one entrypoint is required.
    NoEntrypoints,
    /// `--output` and `--out-dir` select incompatible layouts.
    ConflictingOutputOptions,
    /// An exact output file is ambiguous for multiple entrypoints.
    OutputFileRequiresSingleEntrypoint { count: usize },
    /// A path lexically escapes the output root.
    OutsideRoot { path: PathBuf, root: PathBuf },
    /// A source or destination does not name a file.
    MissingFileName { path: PathBuf },
    /// An entrypoint normalizes to the confinement root itself rather than a file
    /// beneath it.
    EntrypointIsRoot { path: PathBuf },
    /// The same normalized entrypoint was supplied more than once.
    DuplicateEntrypoint { path: PathBuf },
    /// An artifact would overwrite one of the input files.
    ClobbersInput { path: PathBuf, source: PathBuf },
    /// Two artifacts normalize to the same destination.
    Collision {
        path: PathBuf,
        first_source: PathBuf,
        first_kind: ArtifactKind,
        second_source: PathBuf,
        second_kind: ArtifactKind,
    },
}

impl fmt::Display for PlanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RootNotAbsolute { root } => {
                write!(f, "output root must be absolute: {}", root.display())
            }
            Self::NoEntrypoints => f.write_str("at least one entrypoint is required"),
            Self::ConflictingOutputOptions => {
                f.write_str("cannot use an output file and output directory together")
            }
            Self::OutputFileRequiresSingleEntrypoint { count } => write!(
                f,
                "an explicit output file requires exactly one entrypoint, got {count}"
            ),
            Self::OutsideRoot { path, root } => write!(
                f,
                "path {} escapes output root {}",
                path.display(),
                root.display()
            ),
            Self::MissingFileName { path } => {
                write!(f, "path does not name a file: {}", path.display())
            }
            Self::EntrypointIsRoot { path } => {
                write!(
                    f,
                    "entrypoint is the output root, not a file: {}",
                    path.display()
                )
            }
            Self::DuplicateEntrypoint { path } => {
                write!(f, "duplicate entrypoint: {}", path.display())
            }
            Self::ClobbersInput { path, source } => write!(
                f,
                "output {} would overwrite input {}",
                path.display(),
                source.display()
            ),
            Self::Collision {
                path,
                first_source,
                first_kind,
                second_source,
                second_kind,
            } => write!(
                f,
                "output collision at {} between {:?} from {} and {:?} from {}",
                path.display(),
                first_kind,
                first_source.display(),
                second_kind,
                second_source.display()
            ),
        }
    }
}

impl std::error::Error for PlanError {}

/// Produces a normalized, confined, collision-free output plan without filesystem I/O.
pub fn plan_outputs(request: PlanRequest<'_>) -> Result<OutputPlan, PlanError> {
    let root = normalize_lexically(request.root).ok_or_else(|| PlanError::OutsideRoot {
        path: request.root.to_path_buf(),
        root: request.root.to_path_buf(),
    })?;
    if !root.is_absolute() {
        return Err(PlanError::RootNotAbsolute {
            root: request.root.to_path_buf(),
        });
    }
    if request.entrypoints.is_empty() {
        return Err(PlanError::NoEntrypoints);
    }
    if request.output_file.is_some() && request.output_dir.is_some() {
        return Err(PlanError::ConflictingOutputOptions);
    }
    if request.output_file.is_some() && request.entrypoints.len() != 1 {
        return Err(PlanError::OutputFileRequiresSingleEntrypoint {
            count: request.entrypoints.len(),
        });
    }

    let mut sources = Vec::with_capacity(request.entrypoints.len());
    let mut source_set = BTreeSet::new();
    for entrypoint in request.entrypoints {
        let source = confined_path(&root, entrypoint)?;
        if source == root {
            return Err(PlanError::EntrypointIsRoot { path: source });
        }
        require_file_name(&source)?;
        if !source_set.insert(source.clone()) {
            return Err(PlanError::DuplicateEntrypoint { path: source });
        }
        sources.push(source);
    }

    let output_dir = request
        .output_dir
        .map(|path| confined_path(&root, path))
        .transpose()?;
    let output_file = request
        .output_file
        .map(|path| confined_path(&root, path))
        .transpose()?;
    if let Some(path) = &output_file {
        require_file_name(path)?;
    }

    let mut artifacts = Vec::new();
    let mut destinations: BTreeMap<PathBuf, (PathBuf, ArtifactKind)> = BTreeMap::new();

    for source in sources {
        let javascript = match &output_file {
            Some(path) => path.clone(),
            None => {
                let relative = source
                    .strip_prefix(&root)
                    .expect("confined source must be beneath normalized root");
                let parent = match &output_dir {
                    Some(dir) => dir.join(relative.parent().unwrap_or_else(|| Path::new(""))),
                    None => source
                        .parent()
                        .expect("absolute source with a file name must have a parent")
                        .to_path_buf(),
                };
                parent.join(javascript_file_name(&source)?)
            }
        };

        push_artifact(
            &mut artifacts,
            &mut destinations,
            &source_set,
            source.clone(),
            javascript.clone(),
            ArtifactKind::JavaScript,
        )?;

        if request.emit_declarations {
            let declaration = declaration_path(&javascript);
            push_artifact(
                &mut artifacts,
                &mut destinations,
                &source_set,
                source.clone(),
                declaration,
                ArtifactKind::Declaration,
            )?;
        }
        if request.source_maps {
            let source_map = append_suffix(&javascript, ".map")?;
            push_artifact(
                &mut artifacts,
                &mut destinations,
                &source_set,
                source.clone(),
                source_map,
                ArtifactKind::SourceMap,
            )?;
        }
    }

    Ok(OutputPlan { root, artifacts })
}

fn push_artifact(
    artifacts: &mut Vec<PlannedArtifact>,
    destinations: &mut BTreeMap<PathBuf, (PathBuf, ArtifactKind)>,
    sources: &BTreeSet<PathBuf>,
    source: PathBuf,
    path: PathBuf,
    kind: ArtifactKind,
) -> Result<(), PlanError> {
    if let Some(input) = sources.get(&path) {
        return Err(PlanError::ClobbersInput {
            path,
            source: input.clone(),
        });
    }
    if let Some((first_source, first_kind)) = destinations.get(&path) {
        return Err(PlanError::Collision {
            path,
            first_source: first_source.clone(),
            first_kind: *first_kind,
            second_source: source,
            second_kind: kind,
        });
    }
    destinations.insert(path.clone(), (source.clone(), kind));
    artifacts.push(PlannedArtifact { source, path, kind });
    Ok(())
}

fn confined_path(root: &Path, path: &Path) -> Result<PathBuf, PlanError> {
    let candidate = if path.is_absolute() {
        path.to_path_buf()
    } else {
        root.join(path)
    };
    let normalized = normalize_lexically(&candidate).ok_or_else(|| PlanError::OutsideRoot {
        path: path.to_path_buf(),
        root: root.to_path_buf(),
    })?;
    if normalized.starts_with(root) {
        Ok(normalized)
    } else {
        Err(PlanError::OutsideRoot {
            path: path.to_path_buf(),
            root: root.to_path_buf(),
        })
    }
}

fn normalize_lexically(path: &Path) -> Option<PathBuf> {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::Prefix(prefix) => normalized.push(prefix.as_os_str()),
            Component::RootDir => normalized.push(component.as_os_str()),
            Component::CurDir => {}
            Component::ParentDir => {
                if !normalized.pop() {
                    return None;
                }
            }
            Component::Normal(part) => normalized.push(part),
        }
    }
    Some(normalized)
}

fn require_file_name(path: &Path) -> Result<&OsStr, PlanError> {
    path.file_name().ok_or_else(|| PlanError::MissingFileName {
        path: path.to_path_buf(),
    })
}

fn javascript_file_name(source: &Path) -> Result<OsString, PlanError> {
    let mut path = PathBuf::from(require_file_name(source)?);
    let extension = source
        .extension()
        .and_then(OsStr::to_str)
        .map(str::to_ascii_lowercase);
    let output_extension = match extension.as_deref() {
        Some("mts" | "mjs") => "mjs",
        Some("cts" | "cjs") => "cjs",
        _ => "js",
    };
    path.set_extension(output_extension);
    Ok(path.into_os_string())
}

// The declaration extension is derived from the emitted JavaScript module kind
// (`.mjs` -> `.d.mts`, `.cjs` -> `.d.cts`, otherwise `.d.ts`), matching tsc. This is
// intentionally coupled to `javascript_file_name`'s source-to-output extension table:
// both describe the same emitted module, so its kind is read once from the planned
// JavaScript path rather than re-derived from the source.
fn declaration_path(javascript: &Path) -> PathBuf {
    let extension = javascript
        .extension()
        .and_then(OsStr::to_str)
        .map(str::to_ascii_lowercase);
    match extension.as_deref() {
        Some("mjs") => javascript.with_extension("d.mts"),
        Some("cjs") => javascript.with_extension("d.cts"),
        Some("js" | "jsx") => javascript.with_extension("d.ts"),
        _ => append_suffix(javascript, ".d.ts")
            .expect("a planned JavaScript path was already required to have a file name"),
    }
}

fn append_suffix(path: &Path, suffix: &str) -> Result<PathBuf, PlanError> {
    let name = require_file_name(path)?;
    let mut suffixed = name.to_os_string();
    suffixed.push(suffix);
    Ok(path.with_file_name(suffixed))
}

/// Result of exclusive temporary-file creation.
pub enum CreateTemp<F> {
    /// The path was unused and the returned file is open for writing.
    Created(F),
    /// The candidate path already exists and must not be modified.
    AlreadyExists,
}

/// Filesystem operations required by [`publish_atomic`].
///
/// `create_new` must be exclusive. `rename` must perform an atomic same-directory
/// replacement. Implementations must not buffer `write` calls beyond `sync_file`.
pub trait AtomicFs {
    /// Open temporary-file handle.
    type File;
    /// Filesystem-specific error.
    type Error;

    /// Exclusively creates `path`, or reports that the candidate already exists.
    fn create_new(&mut self, path: &Path) -> Result<CreateTemp<Self::File>, Self::Error>;
    /// Writes some bytes and returns the number consumed.
    fn write(&mut self, file: &mut Self::File, bytes: &[u8]) -> Result<usize, Self::Error>;
    /// Flushes file contents and metadata to durable storage.
    fn sync_file(&mut self, file: &mut Self::File) -> Result<(), Self::Error>;
    /// Atomically renames `from` over `to` within one directory.
    fn rename(&mut self, from: &Path, to: &Path) -> Result<(), Self::Error>;
    /// Flushes directory metadata after the rename.
    fn sync_dir(&mut self, dir: &Path) -> Result<(), Self::Error>;
    /// Removes an unpublished temporary file during rollback.
    fn remove_file(&mut self, path: &Path) -> Result<(), Self::Error>;
}

/// Standard-library implementation of [`AtomicFs`].
#[derive(Debug, Default, Clone, Copy)]
pub struct StdAtomicFs;

impl AtomicFs for StdAtomicFs {
    type File = File;
    type Error = io::Error;

    fn create_new(&mut self, path: &Path) -> Result<CreateTemp<Self::File>, Self::Error> {
        match OpenOptions::new().write(true).create_new(true).open(path) {
            Ok(file) => Ok(CreateTemp::Created(file)),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                Ok(CreateTemp::AlreadyExists)
            }
            Err(error) => Err(error),
        }
    }

    fn write(&mut self, file: &mut Self::File, bytes: &[u8]) -> Result<usize, Self::Error> {
        file.write(bytes)
    }

    fn sync_file(&mut self, file: &mut Self::File) -> Result<(), Self::Error> {
        file.sync_all()
    }

    fn rename(&mut self, from: &Path, to: &Path) -> Result<(), Self::Error> {
        std::fs::rename(from, to)
    }

    fn sync_dir(&mut self, dir: &Path) -> Result<(), Self::Error> {
        // Windows is skipped: `File::open` cannot open a directory there. A handle
        // opened with `FILE_FLAG_BACKUP_SEMANTICS` for writing can be flushed on
        // NTFS, but this code does not do that. NTFS journals the rename, which is
        // not a promise that it is on disk after a power loss.
        if cfg!(windows) {
            return Ok(());
        }
        File::open(dir)?.sync_all()
    }

    fn remove_file(&mut self, path: &Path) -> Result<(), Self::Error> {
        std::fs::remove_file(path)
    }
}

/// Publication protocol stage that failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PublishStage {
    /// Exclusive temporary-file creation.
    CreateTemp,
    /// Temporary-file content write.
    Write,
    /// Temporary-file durability sync.
    SyncFile,
    /// Atomic destination replacement.
    Rename,
    /// Destination-directory durability sync.
    SyncDirectory,
}

/// Failure from atomic publication.
#[derive(Debug)]
pub enum PublishError<E> {
    /// The destination has no usable file name.
    InvalidDestination { path: PathBuf },
    /// Every bounded temporary-file candidate already existed.
    TempNamesExhausted { destination: PathBuf },
    /// A filesystem operation failed. `cleanup` records a rollback failure without
    /// hiding the primary failure.
    Operation {
        stage: PublishStage,
        source: E,
        cleanup: Option<E>,
    },
    /// A write made no progress before all bytes were consumed.
    WriteZero { cleanup: Option<E> },
    /// A filesystem implementation reported consuming more bytes than it received.
    InvalidWriteCount {
        reported: usize,
        remaining: usize,
        cleanup: Option<E>,
    },
}

impl<E: fmt::Display> fmt::Display for PublishError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidDestination { path } => {
                write!(f, "invalid output destination: {}", path.display())
            }
            Self::TempNamesExhausted { destination } => write!(
                f,
                "could not reserve a temporary file beside {}",
                destination.display()
            ),
            Self::Operation {
                stage,
                source,
                cleanup,
            } => {
                write!(f, "atomic publication failed during {stage:?}: {source}")?;
                if let Some(cleanup) = cleanup {
                    write!(f, "; temporary-file cleanup also failed: {cleanup}")?;
                }
                Ok(())
            }
            Self::WriteZero { cleanup } => {
                f.write_str("atomic publication write made no progress")?;
                if let Some(cleanup) = cleanup {
                    write!(f, "; temporary-file cleanup also failed: {cleanup}")?;
                }
                Ok(())
            }
            Self::InvalidWriteCount {
                reported,
                remaining,
                cleanup,
            } => {
                write!(
                    f,
                    "filesystem reported writing {reported} bytes from a {remaining}-byte buffer"
                )?;
                if let Some(cleanup) = cleanup {
                    write!(f, "; temporary-file cleanup also failed: {cleanup}")?;
                }
                Ok(())
            }
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for PublishError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Operation { source, .. } => Some(source),
            _ => None,
        }
    }
}

const TEMP_ATTEMPTS: u32 = 128;

/// Deterministic 64-bit seed for temporary-file names, derived from the destination
/// path via FNV-1a. Distinct destinations in one directory get distinct temp names,
/// avoiding spurious collisions, while the emitted basename length stays constant and
/// independent of the destination basename length.
fn temp_name_seed(destination: &Path) -> u64 {
    const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;
    let mut hash = FNV_OFFSET;
    for byte in destination.as_os_str().to_string_lossy().as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

/// Bounded temporary-file basename. Its length is fixed at 31 bytes (`.bamts-tmp-` +
/// 16 hex digits + `-` + up to 3 attempt digits), so it never exceeds the portable
/// 255-byte `NAME_MAX` regardless of how long the destination basename is.
fn temp_file_name(seed: u64, attempt: u32) -> String {
    format!(".bamts-tmp-{seed:016x}-{attempt}")
}

/// Publishes `contents` with the protocol:
///
/// `create temp in destination directory -> write all -> fsync file -> rename -> fsync dir`.
///
/// Any failure before a successful rename attempts to remove the temporary file. A
/// directory-sync failure is returned after publication because the rename cannot be
/// safely rolled back. The destination directory must already exist.
pub fn publish_atomic<F: AtomicFs>(
    fs: &mut F,
    destination: &Path,
    contents: &[u8],
) -> Result<(), PublishError<F::Error>> {
    if destination
        .file_name()
        .filter(|name| !name.is_empty())
        .is_none()
    {
        return Err(PublishError::InvalidDestination {
            path: destination.to_path_buf(),
        });
    }
    let dir = destination
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));

    let name_seed = temp_name_seed(destination);
    let mut reserved = None;
    for attempt in 0..TEMP_ATTEMPTS {
        let path = dir.join(temp_file_name(name_seed, attempt));
        match fs.create_new(&path) {
            Ok(CreateTemp::Created(file)) => {
                reserved = Some((path, file));
                break;
            }
            Ok(CreateTemp::AlreadyExists) => {}
            Err(source) => {
                return Err(PublishError::Operation {
                    stage: PublishStage::CreateTemp,
                    source,
                    cleanup: None,
                });
            }
        }
    }

    let Some((temporary, mut file)) = reserved else {
        return Err(PublishError::TempNamesExhausted {
            destination: destination.to_path_buf(),
        });
    };

    let mut written = 0;
    while written < contents.len() {
        let remaining = contents.len() - written;
        match fs.write(&mut file, &contents[written..]) {
            Ok(0) => {
                drop(file);
                let cleanup = fs.remove_file(&temporary).err();
                return Err(PublishError::WriteZero { cleanup });
            }
            Ok(count) if count > remaining => {
                drop(file);
                let cleanup = fs.remove_file(&temporary).err();
                return Err(PublishError::InvalidWriteCount {
                    reported: count,
                    remaining,
                    cleanup,
                });
            }
            Ok(count) => written += count,
            Err(source) => {
                drop(file);
                let cleanup = fs.remove_file(&temporary).err();
                return Err(PublishError::Operation {
                    stage: PublishStage::Write,
                    source,
                    cleanup,
                });
            }
        }
    }

    if let Err(source) = fs.sync_file(&mut file) {
        drop(file);
        let cleanup = fs.remove_file(&temporary).err();
        return Err(PublishError::Operation {
            stage: PublishStage::SyncFile,
            source,
            cleanup,
        });
    }
    drop(file);

    if let Err(source) = fs.rename(&temporary, destination) {
        let cleanup = fs.remove_file(&temporary).err();
        return Err(PublishError::Operation {
            stage: PublishStage::Rename,
            source,
            cleanup,
        });
    }

    fs.sync_dir(dir).map_err(|source| PublishError::Operation {
        stage: PublishStage::SyncDirectory,
        source,
        cleanup: None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    /// A fixture path written the Unix way, on the drive Windows needs to call it absolute.
    fn abs(unix: &str) -> PathBuf {
        if cfg!(windows) {
            PathBuf::from(format!("C:{}", unix.replace('/', "\\")))
        } else {
            PathBuf::from(unix)
        }
    }

    fn request<'a>(root: &'a Path, entrypoints: &'a [PathBuf]) -> PlanRequest<'a> {
        PlanRequest {
            root,
            entrypoints,
            output_file: None,
            output_dir: None,
            emit_declarations: false,
            source_maps: false,
        }
    }

    #[test]
    fn plans_confined_source_relative_outputs_in_stable_order() {
        let root = abs("/workspace");
        let entries = vec![PathBuf::from("src/main.mts"), PathBuf::from("lib/util.cts")];
        let mut input = request(&root, &entries);
        input.output_dir = Some(Path::new("dist/./generated"));
        input.emit_declarations = true;
        input.source_maps = true;

        let plan = plan_outputs(input).unwrap();
        let actual: Vec<_> = plan
            .artifacts
            .iter()
            .map(|artifact| (artifact.kind, artifact.path.as_path()))
            .collect();
        assert_eq!(
            actual,
            vec![
                (
                    ArtifactKind::JavaScript,
                    abs("/workspace/dist/generated/src/main.mjs").as_path()
                ),
                (
                    ArtifactKind::Declaration,
                    abs("/workspace/dist/generated/src/main.d.mts").as_path()
                ),
                (
                    ArtifactKind::SourceMap,
                    abs("/workspace/dist/generated/src/main.mjs.map").as_path()
                ),
                (
                    ArtifactKind::JavaScript,
                    abs("/workspace/dist/generated/lib/util.cjs").as_path()
                ),
                (
                    ArtifactKind::Declaration,
                    abs("/workspace/dist/generated/lib/util.d.cts").as_path()
                ),
                (
                    ArtifactKind::SourceMap,
                    abs("/workspace/dist/generated/lib/util.cjs.map").as_path()
                ),
            ]
        );
    }

    #[test]
    fn exact_output_derives_declaration_and_map_companions() {
        let entries = vec![PathBuf::from("src/main.ts")];
        let root = abs("/workspace");
        let mut input = request(&root, &entries);
        input.output_file = Some(Path::new("build/bundle.js"));
        input.emit_declarations = true;
        input.source_maps = true;

        let plan = plan_outputs(input).unwrap();
        let paths: Vec<_> = plan
            .artifacts
            .iter()
            .map(|artifact| artifact.path.as_path())
            .collect();
        assert_eq!(
            paths,
            vec![
                abs("/workspace/build/bundle.js").as_path(),
                abs("/workspace/build/bundle.d.ts").as_path(),
                abs("/workspace/build/bundle.js.map").as_path(),
            ]
        );
    }

    #[cfg(unix)]
    #[test]
    fn preserves_non_utf8_file_names_during_planning() {
        use std::os::unix::ffi::OsStrExt;

        let entries = vec![
            PathBuf::from(OsStr::from_bytes(b"src/\xff.ts")),
            PathBuf::from(OsStr::from_bytes(b"src/\xfe.mts")),
        ];
        let root = abs("/workspace");
        let mut input = request(&root, &entries);
        input.output_dir = Some(Path::new("dist"));

        let plan = plan_outputs(input).unwrap();

        assert_eq!(plan.artifacts.len(), 2);
        assert_eq!(
            plan.artifacts[0].path.as_os_str().as_bytes(),
            b"/workspace/dist/src/\xff.js"
        );
        assert_eq!(
            plan.artifacts[1].path.as_os_str().as_bytes(),
            b"/workspace/dist/src/\xfe.mjs"
        );
    }

    #[test]
    fn rejects_lexical_path_traversal() {
        let entries = vec![PathBuf::from("src/main.ts")];
        let root = abs("/workspace/project");
        let mut input = request(&root, &entries);
        input.output_dir = Some(Path::new("../../escape"));

        assert!(matches!(
            plan_outputs(input),
            Err(PlanError::OutsideRoot { .. })
        ));
    }

    #[test]
    fn rejects_absolute_paths_outside_root() {
        let entries = vec![abs("/other/main.ts")];
        let root = abs("/workspace");
        let input = request(&root, &entries);

        assert!(matches!(
            plan_outputs(input),
            Err(PlanError::OutsideRoot { .. })
        ));
    }

    #[test]
    fn rejects_normalized_output_collisions() {
        let entries = vec![
            PathBuf::from("src/value.ts"),
            PathBuf::from("src/value.tsx"),
        ];
        let root = abs("/workspace");
        let mut input = request(&root, &entries);
        input.output_dir = Some(Path::new("dist/a/../"));

        assert!(matches!(
            plan_outputs(input),
            Err(PlanError::Collision {
                path,
                second_kind: ArtifactKind::JavaScript,
                ..
            }) if path == abs("/workspace/dist/src/value.js").as_path()
        ));
    }

    #[test]
    fn rejects_outputs_that_clobber_javascript_inputs() {
        let entries = vec![PathBuf::from("src/value.js")];
        let root = abs("/workspace");
        let input = request(&root, &entries);

        assert!(matches!(
            plan_outputs(input),
            Err(PlanError::ClobbersInput { path, .. })
                if path == abs("/workspace/src/value.js").as_path()
        ));
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum FakeError {
        Injected(PublishStage),
        Cleanup,
        Missing,
    }

    impl fmt::Display for FakeError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{self:?}")
        }
    }

    impl std::error::Error for FakeError {}

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum Call {
        Create(PathBuf),
        Write(PathBuf, usize),
        SyncFile(PathBuf),
        Rename(PathBuf, PathBuf),
        SyncDir(PathBuf),
        Remove(PathBuf),
    }

    #[derive(Default)]
    struct MemoryFs {
        files: BTreeMap<PathBuf, Vec<u8>>,
        calls: Vec<Call>,
        fail: Option<PublishStage>,
        fail_write_after: Option<usize>,
        fail_cleanup: bool,
        max_write: usize,
        writes: usize,
    }

    impl MemoryFs {
        fn new() -> Self {
            Self {
                max_write: usize::MAX,
                ..Self::default()
            }
        }

        fn temporary_files(&self) -> Vec<&Path> {
            self.files
                .keys()
                .filter(|path| path.to_string_lossy().contains(".bamts-tmp-"))
                .map(PathBuf::as_path)
                .collect()
        }
    }

    impl AtomicFs for MemoryFs {
        type File = PathBuf;
        type Error = FakeError;

        fn create_new(&mut self, path: &Path) -> Result<CreateTemp<Self::File>, Self::Error> {
            self.calls.push(Call::Create(path.to_path_buf()));
            if self.fail == Some(PublishStage::CreateTemp) {
                return Err(FakeError::Injected(PublishStage::CreateTemp));
            }
            if self.files.contains_key(path) {
                return Ok(CreateTemp::AlreadyExists);
            }
            self.files.insert(path.to_path_buf(), Vec::new());
            Ok(CreateTemp::Created(path.to_path_buf()))
        }

        fn write(&mut self, file: &mut Self::File, bytes: &[u8]) -> Result<usize, Self::Error> {
            self.calls.push(Call::Write(file.clone(), bytes.len()));
            if self.fail == Some(PublishStage::Write)
                && self
                    .fail_write_after
                    .is_none_or(|limit| self.writes >= limit)
            {
                return Err(FakeError::Injected(PublishStage::Write));
            }
            self.writes += 1;
            let count = bytes.len().min(self.max_write);
            self.files
                .get_mut(file)
                .ok_or(FakeError::Missing)?
                .extend_from_slice(&bytes[..count]);
            Ok(count)
        }

        fn sync_file(&mut self, file: &mut Self::File) -> Result<(), Self::Error> {
            self.calls.push(Call::SyncFile(file.clone()));
            if self.fail == Some(PublishStage::SyncFile) {
                Err(FakeError::Injected(PublishStage::SyncFile))
            } else {
                Ok(())
            }
        }

        fn rename(&mut self, from: &Path, to: &Path) -> Result<(), Self::Error> {
            self.calls
                .push(Call::Rename(from.to_path_buf(), to.to_path_buf()));
            if self.fail == Some(PublishStage::Rename) {
                return Err(FakeError::Injected(PublishStage::Rename));
            }
            let contents = self.files.remove(from).ok_or(FakeError::Missing)?;
            self.files.insert(to.to_path_buf(), contents);
            Ok(())
        }

        fn sync_dir(&mut self, dir: &Path) -> Result<(), Self::Error> {
            self.calls.push(Call::SyncDir(dir.to_path_buf()));
            if self.fail == Some(PublishStage::SyncDirectory) {
                Err(FakeError::Injected(PublishStage::SyncDirectory))
            } else {
                Ok(())
            }
        }

        fn remove_file(&mut self, path: &Path) -> Result<(), Self::Error> {
            self.calls.push(Call::Remove(path.to_path_buf()));
            if self.fail_cleanup {
                return Err(FakeError::Cleanup);
            }
            self.files.remove(path).ok_or(FakeError::Missing)?;
            Ok(())
        }
    }

    #[test]
    fn atomic_publication_retries_partial_writes_then_syncs_in_order() {
        let mut fs = MemoryFs::new();
        fs.max_write = 2;
        let destination = Path::new("/out/program.js");

        publish_atomic(&mut fs, destination, b"abcdef").unwrap();

        assert_eq!(fs.files.get(destination).unwrap(), b"abcdef");
        assert!(fs.temporary_files().is_empty());
        assert!(matches!(fs.calls[0], Call::Create(_)));
        assert!(matches!(fs.calls[1], Call::Write(_, 6)));
        assert!(matches!(fs.calls[2], Call::Write(_, 4)));
        assert!(matches!(fs.calls[3], Call::Write(_, 2)));
        assert!(matches!(fs.calls[4], Call::SyncFile(_)));
        assert!(matches!(fs.calls[5], Call::Rename(_, ref to) if to == destination));
        assert_eq!(fs.calls[6], Call::SyncDir(PathBuf::from("/out")));
    }

    #[test]
    fn partial_write_failure_rolls_back_temp_and_preserves_destination() {
        let mut fs = MemoryFs::new();
        let destination = PathBuf::from("/out/program.js");
        fs.files.insert(destination.clone(), b"old".to_vec());
        fs.max_write = 2;
        fs.fail = Some(PublishStage::Write);
        fs.fail_write_after = Some(1);

        let error = publish_atomic(&mut fs, &destination, b"abcdef").unwrap_err();

        assert!(matches!(
            error,
            PublishError::Operation {
                stage: PublishStage::Write,
                cleanup: None,
                ..
            }
        ));
        assert_eq!(fs.files.get(&destination).unwrap(), b"old");
        assert!(fs.temporary_files().is_empty());
        assert!(matches!(fs.calls.last(), Some(Call::Remove(_))));
    }

    #[test]
    fn sync_and_rename_failures_remove_unpublished_temp() {
        for stage in [PublishStage::SyncFile, PublishStage::Rename] {
            let mut fs = MemoryFs::new();
            fs.fail = Some(stage);
            let destination = Path::new("/out/program.js");

            let error = publish_atomic(&mut fs, destination, b"new").unwrap_err();

            assert!(matches!(
                error,
                PublishError::Operation {
                    stage: actual,
                    cleanup: None,
                    ..
                } if actual == stage
            ));
            assert!(!fs.files.contains_key(destination));
            assert!(fs.temporary_files().is_empty());
            assert!(matches!(fs.calls.last(), Some(Call::Remove(_))));
        }
    }

    #[test]
    fn cleanup_failure_is_reported_without_hiding_primary_failure() {
        let mut fs = MemoryFs::new();
        fs.fail = Some(PublishStage::Write);
        fs.fail_cleanup = true;

        let error = publish_atomic(&mut fs, Path::new("/out/program.js"), b"new").unwrap_err();

        assert!(matches!(
            error,
            PublishError::Operation {
                stage: PublishStage::Write,
                source: FakeError::Injected(PublishStage::Write),
                cleanup: Some(FakeError::Cleanup),
            }
        ));
    }

    #[test]
    fn directory_sync_failure_reports_uncertain_durability_without_rollback() {
        let mut fs = MemoryFs::new();
        fs.fail = Some(PublishStage::SyncDirectory);
        let destination = Path::new("/out/program.js");

        let error = publish_atomic(&mut fs, destination, b"new").unwrap_err();

        assert!(matches!(
            error,
            PublishError::Operation {
                stage: PublishStage::SyncDirectory,
                cleanup: None,
                ..
            }
        ));
        assert_eq!(fs.files.get(destination).unwrap(), b"new");
        assert!(!fs.calls.iter().any(|call| matches!(call, Call::Remove(_))));
    }

    #[test]
    fn existing_temp_candidate_is_never_overwritten() {
        let mut fs = MemoryFs::new();
        let destination = Path::new("/out/program.js");
        let seed = temp_name_seed(destination);
        let occupied = PathBuf::from("/out").join(temp_file_name(seed, 0));
        fs.files.insert(occupied.clone(), b"occupied".to_vec());

        publish_atomic(&mut fs, destination, b"new").unwrap();

        assert_eq!(fs.files.get(&occupied).unwrap(), b"occupied");
        let expected_second = PathBuf::from("/out").join(temp_file_name(seed, 1));
        assert!(matches!(
            fs.calls.as_slice(),
            [Call::Create(first), Call::Create(second), ..]
                if first == &occupied && second == &expected_second
        ));
    }

    #[test]
    fn rejects_entrypoint_normalizing_to_root() {
        let root = abs("/workspace");
        for entrypoint in [
            PathBuf::from("."),
            abs("/workspace"),
            PathBuf::from("src/.."),
        ] {
            let entrypoints = [entrypoint.clone()];
            let input = request(&root, &entrypoints);
            assert!(
                matches!(plan_outputs(input), Err(PlanError::EntrypointIsRoot { .. })),
                "entrypoint {entrypoint:?} must be rejected as the confinement root"
            );
        }
    }

    #[test]
    fn temp_name_stays_within_name_max_for_max_length_multibyte_destination() {
        let mut fs = MemoryFs::new();
        // 84 three-byte chars + ".js" == exactly 255 UTF-8 bytes: the portable NAME_MAX.
        let basename = format!("{}.js", "好".repeat(84));
        assert_eq!(basename.len(), 255);
        let destination = PathBuf::from("/out").join(&basename);

        publish_atomic(&mut fs, &destination, b"payload").unwrap();

        assert_eq!(fs.files.get(&destination).unwrap(), b"payload");
        assert!(fs.temporary_files().is_empty());
        let Call::Create(first) = &fs.calls[0] else {
            panic!("first publication call must reserve a temporary file");
        };
        let temp_name = first.file_name().unwrap().to_string_lossy();
        assert!(
            temp_name.len() <= 255,
            "temp basename {temp_name:?} ({} bytes) exceeds NAME_MAX",
            temp_name.len()
        );
        assert!(temp_name.starts_with(".bamts-tmp-"));
        // Deterministic bounded scheme: constant basename, independent of the 255-byte
        // destination basename.
        assert_eq!(temp_name, temp_file_name(temp_name_seed(&destination), 0));
        // Same-directory atomic rename: the temporary lives beside the destination.
        assert_eq!(first.parent(), destination.parent());
    }
}
