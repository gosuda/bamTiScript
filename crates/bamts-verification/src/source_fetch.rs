//! Digest-first, atomic materialization of pinned source archives.
//!
//! The archive bytes are verified before extraction. Publication uses a
//! sibling staging directory and a source identity record inside the published
//! tree. Existing verified trees are idempotent; changed trees fail closed.

use std::{
    ffi::{OsStr, OsString},
    fs::{self, File, OpenOptions},
    io::{Read, Write},
    path::{Component, Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
    time::Duration,
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256, Sha512};

use crate::{
    ErrorCode, Result, VerificationError,
    corpus::{OracleLimits, normalized_env, run_process},
    fsync,
    schema::{SourcePin, base64_value, load_sources, required_source},
};

const IDENTITY_FILE: &str = ".bamti-source.json";
const MAX_ARCHIVE_BYTES: &str = "2147483648";
const OUTPUT_LIMIT: usize = 1 << 20;
const FETCH_TIMEOUT: Duration = Duration::from_secs(15 * 60);
const EXTRACT_TIMEOUT: Duration = Duration::from_secs(5 * 60);
static NEXT_STAGING: AtomicU64 = AtomicU64::new(0);

/// Pinned archive identity accepted by the source materializer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceArchive {
    pub name: String,
    pub pin: String,
    pub url: String,
    pub digest_algorithm: String,
    pub digest: String,
}

impl SourceArchive {
    pub fn new(
        name: impl Into<String>,
        pin: impl Into<String>,
        url: impl Into<String>,
        digest_algorithm: impl Into<String>,
        digest: impl Into<String>,
    ) -> Result<Self> {
        let source = Self {
            name: name.into(),
            pin: pin.into(),
            url: url.into(),
            digest_algorithm: digest_algorithm.into(),
            digest: digest.into(),
        };
        source.validate()?;
        Ok(source)
    }

    pub(crate) fn from_pin(source: &SourcePin) -> Result<Self> {
        Self::new(
            source.name.clone(),
            source.pin.clone(),
            source.url.clone(),
            source.digest_algorithm.clone(),
            source.digest.clone(),
        )
    }

    fn validate(&self) -> Result<()> {
        for (field, value) in [
            ("name", self.name.as_str()),
            ("pin", self.pin.as_str()),
            ("url", self.url.as_str()),
            ("digest", self.digest.as_str()),
        ] {
            if value.trim().is_empty() || value.as_bytes().contains(&0) {
                return Err(VerificationError::new(
                    ErrorCode::Schema,
                    format!("source {field} must be nonempty and NUL-free"),
                ));
            }
        }
        match self.digest_algorithm.as_str() {
            "sha256" if is_lower_hex(&self.digest, 64) => Ok(()),
            "sha512" if decode_base64(&self.digest).is_some_and(|bytes| bytes.len() == 64) => {
                Ok(())
            }
            "sha256" | "sha512" => Err(VerificationError::new(
                ErrorCode::Digest,
                format!(
                    "source `{}` has a malformed {} digest",
                    self.name, self.digest_algorithm
                ),
            )),
            other => Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "source `{}` uses unsupported digest algorithm `{other}`",
                    self.name
                ),
            )),
        }
    }
}

/// Archive formats supported by the pinned source ledger.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArchiveFormat {
    GzipTar,
    XzTar,
}

impl ArchiveFormat {
    fn from_url(url: &str) -> Result<Self> {
        let path = url.split_once('?').map_or(url, |(path, _)| path);
        if path.ends_with(".tar.gz") || path.ends_with(".tgz") || path.ends_with(".crate") {
            return Ok(Self::GzipTar);
        }
        if path.ends_with(".tar.xz") {
            return Ok(Self::XzTar);
        }
        Err(VerificationError::new(
            ErrorCode::Schema,
            format!("unsupported source archive URL `{url}`"),
        ))
    }

    fn tar_flag(self) -> &'static str {
        match self {
            Self::GzipTar => "--gzip",
            Self::XzTar => "--xz",
        }
    }
}

/// I/O boundary for download and extraction.
pub trait ArchiveBackend {
    fn fetch(&self, url: &str, destination: &Path) -> Result<()>;
    fn extract(&self, archive: &Path, format: ArchiveFormat, destination: &Path) -> Result<()>;
}

/// Production backend using bounded `curl` and `tar` subprocesses.
#[derive(Debug, Clone)]
pub struct CommandBackend {
    curl: PathBuf,
    tar: PathBuf,
}

impl Default for CommandBackend {
    fn default() -> Self {
        Self {
            curl: PathBuf::from("curl"),
            tar: PathBuf::from("tar"),
        }
    }
}

impl CommandBackend {
    #[must_use]
    pub fn new(curl: impl Into<PathBuf>, tar: impl Into<PathBuf>) -> Self {
        Self {
            curl: curl.into(),
            tar: tar.into(),
        }
    }

    fn invoke(
        &self,
        label: &str,
        program: &Path,
        cwd: &Path,
        args: &[OsString],
        timeout: Duration,
    ) -> Result<()> {
        let mut environment = normalized_env();
        if let Some(path) = std::env::var_os("PATH") {
            environment.push(("PATH".to_owned(), path.to_string_lossy().into_owned()));
        }
        let outcome = run_process(
            label,
            program,
            cwd,
            &environment,
            args,
            &OracleLimits {
                timeout,
                max_output_bytes: OUTPUT_LIMIT,
            },
        )?;
        if outcome.timed_out {
            return Err(VerificationError::new(
                ErrorCode::ToolFailed,
                format!("{label} timed out"),
            ));
        }
        if outcome.stdout_truncated || outcome.stderr_truncated {
            return Err(VerificationError::new(
                ErrorCode::ToolFailed,
                format!("{label} output exceeded {OUTPUT_LIMIT} bytes"),
            ));
        }
        if outcome.exit_code != Some(0) {
            let stderr = String::from_utf8_lossy(&outcome.stderr);
            return Err(VerificationError::new(
                ErrorCode::ToolFailed,
                format!(
                    "{label} failed with {:?}: {}",
                    outcome.exit_code,
                    stderr.trim()
                ),
            ));
        }
        Ok(())
    }
}

impl ArchiveBackend for CommandBackend {
    fn fetch(&self, url: &str, destination: &Path) -> Result<()> {
        let cwd = destination.parent().ok_or_else(|| {
            VerificationError::new(ErrorCode::Io, "download destination has no parent")
        })?;
        let args = [
            OsString::from("--fail"),
            OsString::from("--location"),
            OsString::from("--silent"),
            OsString::from("--show-error"),
            OsString::from("--max-filesize"),
            OsString::from(MAX_ARCHIVE_BYTES),
            OsString::from("--output"),
            destination.as_os_str().to_owned(),
            OsString::from(url),
        ];
        self.invoke("source download", &self.curl, cwd, &args, FETCH_TIMEOUT)
    }

    fn extract(&self, archive: &Path, format: ArchiveFormat, destination: &Path) -> Result<()> {
        let cwd = destination.parent().ok_or_else(|| {
            VerificationError::new(ErrorCode::Io, "extraction destination has no parent")
        })?;
        let args = [
            OsString::from("--extract"),
            OsString::from(format.tar_flag()),
            OsString::from("--file"),
            archive.as_os_str().to_owned(),
            OsString::from("--directory"),
            destination.as_os_str().to_owned(),
            OsString::from("--no-same-owner"),
            OsString::from("--no-same-permissions"),
        ];
        self.invoke("source extraction", &self.tar, cwd, &args, EXTRACT_TIMEOUT)
    }
}

/// Successful materialization report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaterializedSource {
    pub name: String,
    pub pin: String,
    pub destination: PathBuf,
    pub tree_digest: String,
}
/// Resolves a named source from `vendor/sources.toml` and materializes it.
pub fn materialize_named<B: ArchiveBackend>(
    root: &Path,
    name: &str,
    destination: &Path,
    backend: &B,
) -> Result<MaterializedSource> {
    let (sources, _) = load_sources(root)?;
    let source = SourceArchive::from_pin(required_source(&sources, name)?)?;
    let absolute = if destination.is_absolute() {
        destination.to_owned()
    } else {
        root.join(destination)
    };
    let parent = absolute.parent().ok_or_else(|| {
        VerificationError::new(ErrorCode::Usage, "source destination has no parent")
    })?;
    let name = absolute.file_name().ok_or_else(|| {
        VerificationError::new(ErrorCode::Usage, "source destination has no file name")
    })?;
    materialize(&source, parent, Path::new(name), backend)
}

/// Materializes a pinned source archive without overwriting any existing tree.
pub fn materialize<B: ArchiveBackend>(
    source: &SourceArchive,
    parent: &Path,
    destination: &Path,
    backend: &B,
) -> Result<MaterializedSource> {
    source.validate()?;
    let parent = ensure_parent(parent)?;
    let destination_name = validate_destination(destination)?;
    let destination = parent.join(destination_name);

    if destination.exists() {
        return verify_existing(source, destination);
    }

    let staging = Staging::new(&parent, &source.name)?;
    let archive = staging.root.join("archive");
    let extracted = staging.root.join("tree");
    fs::create_dir(&extracted).map_err(|error| io_error(&extracted, error))?;

    backend.fetch(&source.url, &archive)?;
    verify_archive(source, &archive)?;
    backend.extract(&archive, ArchiveFormat::from_url(&source.url)?, &extracted)?;

    let payload = select_payload(&extracted)?;
    let tree_digest = compute_tree_digest(&payload)?;
    let identity = IdentityRecord::from_source(source, tree_digest.clone());
    write_identity(&payload.join(IDENTITY_FILE), &identity)?;
    sync_tree(&payload)?;

    let lock = PublishLock::acquire(
        &parent,
        destination.file_name().unwrap_or(OsStr::new("source")),
    )?;
    if destination.exists() {
        return Err(VerificationError::new(
            ErrorCode::Duplicate,
            format!(
                "{} appeared during source materialization",
                destination.display()
            ),
        ));
    }
    fs::rename(&payload, &destination).map_err(|error| io_error(&destination, error))?;
    sync_directory(&parent)?;
    drop(lock);

    Ok(MaterializedSource {
        name: source.name.clone(),
        pin: source.pin.clone(),
        destination,
        tree_digest,
    })
}

fn verify_existing(source: &SourceArchive, destination: PathBuf) -> Result<MaterializedSource> {
    let metadata =
        fs::symlink_metadata(&destination).map_err(|error| io_error(&destination, error))?;
    if !metadata.is_dir() || metadata.file_type().is_symlink() {
        return Err(VerificationError::new(
            ErrorCode::Duplicate,
            format!(
                "{} is not a materialized source directory",
                destination.display()
            ),
        ));
    }
    let identity_path = destination.join(IDENTITY_FILE);
    let identity = read_identity(&identity_path)?;
    if !identity.matches(source) {
        return Err(VerificationError::new(
            ErrorCode::Duplicate,
            format!(
                "{} belongs to a different source identity",
                destination.display()
            ),
        ));
    }
    let tree_digest = compute_tree_digest(&destination)?;
    if tree_digest != identity.tree_digest {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "{} tree digest does not match its identity",
                destination.display()
            ),
        ));
    }
    Ok(MaterializedSource {
        name: source.name.clone(),
        pin: source.pin.clone(),
        destination,
        tree_digest,
    })
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct IdentityRecord {
    schema: String,
    name: String,
    pin: String,
    url: String,
    digest_algorithm: String,
    digest: String,
    tree_digest: String,
}

impl IdentityRecord {
    fn from_source(source: &SourceArchive, tree_digest: String) -> Self {
        Self {
            schema: "bamti.source/v1".to_owned(),
            name: source.name.clone(),
            pin: source.pin.clone(),
            url: source.url.clone(),
            digest_algorithm: source.digest_algorithm.clone(),
            digest: source.digest.clone(),
            tree_digest,
        }
    }

    fn matches(&self, source: &SourceArchive) -> bool {
        self.schema == "bamti.source/v1"
            && self.name == source.name
            && self.pin == source.pin
            && self.url == source.url
            && self.digest_algorithm == source.digest_algorithm
            && self.digest == source.digest
    }
}

fn write_identity(path: &Path, identity: &IdentityRecord) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(identity).map_err(|error| {
        VerificationError::new(ErrorCode::Json, format!("encode source identity: {error}"))
    })?;
    bytes.push(b'\n');
    let mut file = File::create(path).map_err(|error| io_error(path, error))?;
    file.write_all(&bytes)
        .map_err(|error| io_error(path, error))?;
    file.sync_all().map_err(|error| io_error(path, error))
}

fn read_identity(path: &Path) -> Result<IdentityRecord> {
    let metadata = fs::symlink_metadata(path).map_err(|error| io_error(path, error))?;
    if !metadata.is_file() || metadata.file_type().is_symlink() {
        return Err(VerificationError::new(
            ErrorCode::Duplicate,
            format!("{} is not a valid source identity file", path.display()),
        ));
    }
    let bytes = fs::read(path).map_err(|error| io_error(path, error))?;
    serde_json::from_slice(&bytes).map_err(|error| {
        VerificationError::new(ErrorCode::Json, format!("{}: {error}", path.display()))
    })
}

fn verify_archive(source: &SourceArchive, archive: &Path) -> Result<()> {
    let mut file = File::open(archive).map_err(|error| io_error(archive, error))?;
    match source.digest_algorithm.as_str() {
        "sha256" => {
            let actual = hash_reader::<Sha256>(&mut file)?;
            if to_hex(&actual) != source.digest {
                return Err(digest_mismatch(source));
            }
        }
        "sha512" => {
            let actual = hash_reader::<Sha512>(&mut file)?;
            let expected = decode_base64(&source.digest).ok_or_else(|| digest_mismatch(source))?;
            if actual != expected {
                return Err(digest_mismatch(source));
            }
        }
        _ => unreachable!("validated source digest algorithm"),
    }
    Ok(())
}

fn hash_reader<D: Digest + Default>(reader: &mut File) -> Result<Vec<u8>> {
    let mut hasher = D::default();
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let read = reader.read(&mut buffer).map_err(|error| {
            VerificationError::new(ErrorCode::Io, format!("read source archive: {error}"))
        })?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(hasher.finalize().to_vec())
}

fn digest_mismatch(source: &SourceArchive) -> VerificationError {
    VerificationError::new(
        ErrorCode::Digest,
        format!(
            "source `{}` archive digest does not match its pin",
            source.name
        ),
    )
}

fn decode_base64(value: &str) -> Option<Vec<u8>> {
    if !value.len().is_multiple_of(4) {
        return None;
    }
    let mut output = Vec::with_capacity(value.len() / 4 * 3);
    for chunk in value.as_bytes().chunks_exact(4) {
        let padding = usize::from(chunk[3] == b'=') + usize::from(chunk[2] == b'=');
        if padding > 2 || (padding == 1 && chunk[2] == b'=') {
            return None;
        }
        let a = base64_value(chunk[0])? as u32;
        let b = base64_value(chunk[1])? as u32;
        let c = if chunk[2] == b'=' {
            0
        } else {
            base64_value(chunk[2])? as u32
        };
        let d = if chunk[3] == b'=' {
            0
        } else {
            base64_value(chunk[3])? as u32
        };
        let bits = (a << 18) | (b << 12) | (c << 6) | d;
        output.push((bits >> 16) as u8);
        if padding < 2 {
            output.push((bits >> 8) as u8);
        }
        if padding == 0 {
            output.push(bits as u8);
        }
    }
    Some(output)
}

fn compute_tree_digest(root: &Path) -> Result<String> {
    let mut records = Vec::new();
    collect_tree_records(root, Path::new(""), &mut records)?;
    records.sort_by(|left, right| left.0.cmp(&right.0));
    let mut hasher = Sha256::new();
    for (path, kind) in records {
        let encoded = path.to_str().ok_or_else(|| {
            VerificationError::new(ErrorCode::Schema, "source tree path is not UTF-8")
        })?;
        hasher.update([kind]);
        hasher.update((encoded.len() as u64).to_be_bytes());
        hasher.update(encoded.as_bytes());
        let absolute = root.join(&path);
        match kind {
            b'F' => {
                let bytes = fs::read(&absolute).map_err(|error| io_error(&absolute, error))?;
                hasher.update((bytes.len() as u64).to_be_bytes());
                hasher.update(bytes);
            }
            b'L' => {
                let target =
                    fs::read_link(&absolute).map_err(|error| io_error(&absolute, error))?;
                let target = target.to_str().ok_or_else(|| {
                    VerificationError::new(ErrorCode::Schema, "source symlink target is not UTF-8")
                })?;
                hasher.update((target.len() as u64).to_be_bytes());
                hasher.update(target.as_bytes());
            }
            b'D' => {}
            _ => unreachable!("tree record kind"),
        }
    }
    Ok(to_hex(&hasher.finalize()))
}

fn collect_tree_records(
    root: &Path,
    relative: &Path,
    records: &mut Vec<(PathBuf, u8)>,
) -> Result<()> {
    let directory = root.join(relative);
    let entries = fs::read_dir(&directory).map_err(|error| io_error(&directory, error))?;
    for entry in entries {
        let entry = entry.map_err(|error| io_error(&directory, error))?;
        let name = entry.file_name();
        if relative.as_os_str().is_empty() && name == OsStr::new(IDENTITY_FILE) {
            continue;
        }
        let child = relative.join(name);
        let metadata =
            fs::symlink_metadata(entry.path()).map_err(|error| io_error(&entry.path(), error))?;
        if metadata.file_type().is_symlink() {
            records.push((child, b'L'));
        } else if metadata.is_dir() {
            records.push((child.clone(), b'D'));
            collect_tree_records(root, &child, records)?;
        } else if metadata.is_file() {
            records.push((child, b'F'));
        } else {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!("{} has unsupported file type", entry.path().display()),
            ));
        }
    }
    Ok(())
}

fn select_payload(extracted: &Path) -> Result<PathBuf> {
    let mut entries = fs::read_dir(extracted)
        .map_err(|error| io_error(extracted, error))?
        .collect::<std::result::Result<Vec<_>, _>>()
        .map_err(|error| io_error(extracted, error))?;
    // macOS can write this into any new directory, which must not hide the
    // archive's single root and change the layout of the whole tree.
    entries.retain(|entry| entry.file_name() != ".DS_Store");
    if entries.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            "source archive extracted no files",
        ));
    }
    if entries.len() == 1 {
        let entry = entries.pop().expect("one entry");
        let metadata =
            fs::symlink_metadata(entry.path()).map_err(|error| io_error(&entry.path(), error))?;
        if metadata.is_dir() && !metadata.file_type().is_symlink() {
            return Ok(entry.path());
        }
    }
    Ok(extracted.to_owned())
}

fn sync_tree(root: &Path) -> Result<()> {
    for entry in fs::read_dir(root).map_err(|error| io_error(root, error))? {
        let entry = entry.map_err(|error| io_error(root, error))?;
        let metadata =
            fs::symlink_metadata(entry.path()).map_err(|error| io_error(&entry.path(), error))?;
        if metadata.is_dir() && !metadata.file_type().is_symlink() {
            sync_tree(&entry.path())?;
        } else if metadata.is_file() {
            fsync::sync_file(&entry.path()).map_err(|error| io_error(&entry.path(), error))?;
        }
    }
    sync_directory(root)
}

fn sync_directory(path: &Path) -> Result<()> {
    fsync::sync_directory(path).map_err(|error| io_error(path, error))
}

fn ensure_parent(parent: &Path) -> Result<PathBuf> {
    fs::create_dir_all(parent).map_err(|error| io_error(parent, error))?;
    fs::canonicalize(parent).map_err(|error| io_error(parent, error))
}

fn validate_destination(destination: &Path) -> Result<&OsStr> {
    let mut components = destination.components();
    match (components.next(), components.next()) {
        (Some(Component::Normal(name)), None) => Ok(name),
        _ => Err(VerificationError::new(
            ErrorCode::Usage,
            "source destination must be one relative path component",
        )),
    }
}

struct Staging {
    root: PathBuf,
}

impl Staging {
    fn new(parent: &Path, source_name: &str) -> Result<Self> {
        let serial = NEXT_STAGING.fetch_add(1, Ordering::Relaxed);
        let root = parent.join(format!(
            ".source-{}-{serial}-{source_name}",
            std::process::id()
        ));
        fs::create_dir(&root).map_err(|error| io_error(&root, error))?;
        Ok(Self { root })
    }
}

impl Drop for Staging {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

struct PublishLock {
    path: PathBuf,
    _file: File,
}

impl PublishLock {
    fn acquire(parent: &Path, destination: &OsStr) -> Result<Self> {
        let path = parent.join(format!(".{}.publish.lock", destination.to_string_lossy()));
        let file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .map_err(|error| io_error(&path, error))?;
        Ok(Self { path, _file: file })
    }
}

impl Drop for PublishLock {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn io_error(path: &Path, error: std::io::Error) -> VerificationError {
    VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
}

fn is_lower_hex(value: &str, length: usize) -> bool {
    value.len() == length
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn to_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(HEX[(byte >> 4) as usize] as char);
        output.push(HEX[(byte & 0x0f) as usize] as char);
    }
    output
}

#[cfg(test)]
mod tests {
    use std::{cell::Cell, process::Command};

    use super::*;

    struct Scratch(PathBuf);

    impl Scratch {
        fn new(label: &str) -> Self {
            let serial = NEXT_STAGING.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "bamts-source-test-{}-{serial}-{label}",
                std::process::id()
            ));
            fs::create_dir(&path).expect("scratch");
            Self(path)
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    struct FakeBackend {
        archive: Vec<u8>,
        fetches: Cell<usize>,
        extracts: Cell<usize>,
    }

    impl FakeBackend {
        fn new(archive: &[u8]) -> Self {
            Self {
                archive: archive.to_vec(),
                fetches: Cell::new(0),
                extracts: Cell::new(0),
            }
        }
    }

    impl ArchiveBackend for FakeBackend {
        fn fetch(&self, _url: &str, destination: &Path) -> Result<()> {
            self.fetches.set(self.fetches.get() + 1);
            fs::write(destination, &self.archive).map_err(|error| io_error(destination, error))
        }

        fn extract(
            &self,
            _archive: &Path,
            _format: ArchiveFormat,
            destination: &Path,
        ) -> Result<()> {
            self.extracts.set(self.extracts.get() + 1);
            let package = destination.join("package");
            fs::create_dir(&package).map_err(|error| io_error(&package, error))?;
            fs::write(package.join("index.ts"), b"export const answer = 42;\n")
                .map_err(|error| io_error(&package, error))
        }
    }

    fn source(bytes: &[u8]) -> SourceArchive {
        SourceArchive::new(
            "typescript-primary",
            "7.0.2",
            "https://example.invalid/typescript.tgz",
            "sha256",
            to_hex(&Sha256::digest(bytes)),
        )
        .expect("source")
    }

    #[test]
    fn materializes_verified_archive() {
        let scratch = Scratch::new("materialize");
        let backend = FakeBackend::new(b"verified archive");
        let report = materialize(
            &source(b"verified archive"),
            &scratch.0,
            Path::new("typescript"),
            &backend,
        )
        .expect("materialize");
        assert_eq!(report.name, "typescript-primary");
        assert_eq!(report.pin, "7.0.2");
        assert_eq!(
            fs::read(report.destination.join("index.ts")).unwrap(),
            b"export const answer = 42;\n"
        );
        assert_eq!(backend.fetches.get(), 1);
        assert_eq!(backend.extracts.get(), 1);
    }

    #[test]
    fn digest_failure_is_atomic() {
        let scratch = Scratch::new("digest");
        let backend = FakeBackend::new(b"mutated archive");
        let error = materialize(
            &source(b"expected archive"),
            &scratch.0,
            Path::new("typescript"),
            &backend,
        )
        .expect_err("digest mismatch");
        assert_eq!(error.code(), ErrorCode::Digest);
        assert!(!scratch.0.join("typescript").exists());
        assert_eq!(backend.extracts.get(), 0);
    }

    #[test]
    fn verified_destination_is_idempotent() {
        let scratch = Scratch::new("idempotent");
        let backend = FakeBackend::new(b"verified archive");
        let pinned = source(b"verified archive");
        let first = materialize(&pinned, &scratch.0, Path::new("typescript"), &backend).unwrap();
        let second = materialize(&pinned, &scratch.0, Path::new("typescript"), &backend).unwrap();
        assert_eq!(first, second);
        assert_eq!(backend.fetches.get(), 1);
        assert_eq!(backend.extracts.get(), 1);
    }

    #[test]
    fn rejects_conflicting_destination() {
        let scratch = Scratch::new("conflict");
        let backend = FakeBackend::new(b"verified archive");
        let pinned = source(b"verified archive");
        let report = materialize(&pinned, &scratch.0, Path::new("typescript"), &backend).unwrap();
        fs::write(report.destination.join("index.ts"), b"changed\n").unwrap();
        let error = materialize(&pinned, &scratch.0, Path::new("typescript"), &backend)
            .expect_err("changed tree");
        assert_eq!(error.code(), ErrorCode::Digest);
        assert_eq!(backend.fetches.get(), 1);
    }

    #[test]
    fn a_finder_file_does_not_hide_the_archive_root() {
        let root = std::env::temp_dir().join(format!("select-payload-{}", std::process::id()));
        let payload = root.join("source-1234");
        fs::create_dir_all(&payload).expect("payload");
        fs::write(root.join(".DS_Store"), b"finder").expect("finder file");
        assert_eq!(select_payload(&root).expect("payload"), payload);
        fs::remove_dir_all(&root).expect("remove root");
    }

    #[test]
    fn command_backend_argv_is_accepted_by_tools() {
        let scratch = Scratch::new("commands");
        let payload = scratch.0.join("payload.txt");
        fs::write(&payload, b"payload\n").unwrap();
        let archive = scratch.0.join("fixture.tar.gz");
        let status = Command::new("tar")
            .args(["--create", "--gzip", "--file"])
            .arg(&archive)
            .args(["--directory"])
            .arg(&scratch.0)
            .arg("payload.txt")
            .status()
            .expect("tar create");
        assert!(status.success());

        let backend = CommandBackend::default();
        let fetched = scratch.0.join("fetched.tar.gz");
        backend
            .fetch(&format!("file://{}", archive.display()), &fetched)
            .expect("curl exact argv");
        let extracted = scratch.0.join("extracted");
        fs::create_dir(&extracted).unwrap();
        backend
            .extract(&fetched, ArchiveFormat::GzipTar, &extracted)
            .expect("tar exact argv");
        assert_eq!(
            fs::read(extracted.join("payload.txt")).unwrap(),
            b"payload\n"
        );
    }
}
