use std::{
    fmt, fs, io,
    path::{Component, Path, PathBuf},
    time::SystemTime,
};

/// Metadata used to decide whether a closed file needs a fresh compiler snapshot.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FileMetadata {
    pub len: u64,
    pub modified: Option<SystemTime>,
}

/// A filesystem failure with a stable kind suitable for protocol conversion.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FileSystemError {
    kind: io::ErrorKind,
    message: String,
}

impl FileSystemError {
    #[must_use]
    pub fn new(kind: io::ErrorKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
        }
    }

    #[must_use]
    pub const fn kind(&self) -> io::ErrorKind {
        self.kind
    }
}

impl fmt::Display for FileSystemError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for FileSystemError {}

impl From<io::Error> for FileSystemError {
    fn from(error: io::Error) -> Self {
        Self::new(error.kind(), error.to_string())
    }
}

/// The service's only filesystem seam. Implementations must return one canonical
/// identity for every accepted path.
pub trait FileSystem: Send + Sync + 'static {
    fn normalize(&self, path: &Path) -> Result<PathBuf, FileSystemError>;
    fn read(&self, path: &Path) -> Result<String, FileSystemError>;
    fn metadata(&self, path: &Path) -> Result<FileMetadata, FileSystemError>;
    fn read_dir(&self, path: &Path) -> Result<Vec<PathBuf>, FileSystemError>;
}

/// A project-root-confined operating-system filesystem.
#[derive(Clone, Debug)]
pub struct OsFileSystem {
    root: PathBuf,
}

impl OsFileSystem {
    pub fn new(root: impl AsRef<Path>) -> Result<Self, FileSystemError> {
        let root = fs::canonicalize(root).map_err(FileSystemError::from)?;
        if !root.is_dir() {
            return Err(FileSystemError::new(
                io::ErrorKind::NotADirectory,
                format!("service root is not a directory: {}", root.display()),
            ));
        }
        Ok(Self { root })
    }

    #[must_use]
    pub fn root(&self) -> &Path {
        &self.root
    }

    fn confined(&self, path: PathBuf) -> Result<PathBuf, FileSystemError> {
        if path.starts_with(&self.root) {
            Ok(path)
        } else {
            Err(FileSystemError::new(
                io::ErrorKind::PermissionDenied,
                format!("path escapes service root: {}", path.display()),
            ))
        }
    }
}

impl FileSystem for OsFileSystem {
    fn normalize(&self, path: &Path) -> Result<PathBuf, FileSystemError> {
        let joined = if path.is_absolute() {
            path.to_path_buf()
        } else {
            self.root.join(path)
        };
        let lexical = normalize_lexically(&joined)?;
        let mut ancestor = lexical.as_path();
        loop {
            match fs::symlink_metadata(ancestor) {
                Ok(_) => break,
                Err(error) if error.kind() == io::ErrorKind::NotFound => {
                    ancestor = ancestor.parent().ok_or_else(|| {
                        FileSystemError::new(
                            io::ErrorKind::NotFound,
                            format!("path has no existing ancestor: {}", lexical.display()),
                        )
                    })?;
                }
                Err(error) => return Err(FileSystemError::from(error)),
            }
        }
        let mut canonical = fs::canonicalize(ancestor).map_err(FileSystemError::from)?;
        let suffix = lexical
            .strip_prefix(ancestor)
            .expect("selected ancestor is a lexical path prefix");
        for component in suffix.components() {
            canonical.push(component);
        }
        self.confined(canonical)
    }

    fn read(&self, path: &Path) -> Result<String, FileSystemError> {
        let path = self.normalize(path)?;
        fs::read_to_string(path).map_err(FileSystemError::from)
    }

    fn metadata(&self, path: &Path) -> Result<FileMetadata, FileSystemError> {
        let path = self.normalize(path)?;
        let metadata = fs::metadata(path).map_err(FileSystemError::from)?;
        if !metadata.is_file() {
            return Err(FileSystemError::new(
                io::ErrorKind::InvalidInput,
                "service source is not a regular file",
            ));
        }
        Ok(FileMetadata {
            len: metadata.len(),
            modified: metadata.modified().ok(),
        })
    }

    fn read_dir(&self, path: &Path) -> Result<Vec<PathBuf>, FileSystemError> {
        let path = self.normalize(path)?;
        let mut entries = Vec::new();
        for entry in fs::read_dir(&path).map_err(FileSystemError::from)? {
            let entry = entry.map_err(FileSystemError::from)?;
            let child = path.join(entry.file_name());
            let canonical = fs::canonicalize(&child).map_err(FileSystemError::from)?;
            entries.push(self.confined(canonical)?);
        }
        entries.sort();
        entries.dedup();
        Ok(entries)
    }
}

fn normalize_lexically(path: &Path) -> Result<PathBuf, FileSystemError> {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::Prefix(_) => {
                return Err(FileSystemError::new(
                    io::ErrorKind::InvalidInput,
                    "platform path prefix is unsupported",
                ));
            }
            Component::RootDir => normalized.push(component.as_os_str()),
            Component::CurDir => {}
            Component::ParentDir => {
                if !normalized.pop() {
                    return Err(FileSystemError::new(
                        io::ErrorKind::PermissionDenied,
                        "path escapes filesystem root",
                    ));
                }
            }
            Component::Normal(segment) => normalized.push(segment),
        }
    }
    Ok(normalized)
}

#[cfg(test)]
mod tests {
    use std::{
        fs, io,
        path::Path,
        time::{SystemTime, UNIX_EPOCH},
    };

    use super::{FileSystem, OsFileSystem};

    fn temporary_root() -> std::path::PathBuf {
        crate::service::test_support::fresh_dir("bamts-service-fs")
    }

    fn collect_names(entries: Vec<std::path::PathBuf>) -> Vec<String> {
        entries
            .into_iter()
            .map(|p| p.file_name().unwrap().to_str().unwrap().to_string())
            .collect()
    }

    #[test]
    fn filesystem_confines_paths_and_reports_missing_files() {
        let root = temporary_root();
        fs::write(root.join("a.ts"), "const a = 1;").expect("write source");
        let filesystem = OsFileSystem::new(&root).expect("filesystem");

        assert_eq!(
            filesystem.read(Path::new("a.ts")).expect("read"),
            "const a = 1;"
        );
        assert_eq!(
            filesystem
                .read(Path::new("missing.ts"))
                .expect_err("missing")
                .kind(),
            io::ErrorKind::NotFound
        );
        assert_eq!(
            filesystem
                .normalize(Path::new("../escape.ts"))
                .expect_err("escape")
                .kind(),
            io::ErrorKind::PermissionDenied
        );

        fs::remove_dir_all(root).expect("remove temporary root");
    }

    #[test]
    fn read_dir_sorts_entries_and_includes_directories() {
        let root = temporary_root();
        fs::write(root.join("b.ts"), "b").expect("write b");
        fs::write(root.join("a.ts"), "a").expect("write a");
        fs::create_dir(root.join("c")).expect("create c");

        let filesystem = OsFileSystem::new(&root).expect("filesystem");
        let names = collect_names(filesystem.read_dir(Path::new(".")).expect("read_dir"));
        assert_eq!(names, vec!["a.ts", "b.ts", "c"]);

        fs::remove_dir_all(root).expect("remove temporary root");
    }

    #[test]
    fn read_dir_is_direct_not_recursive() {
        let root = temporary_root();
        fs::create_dir(root.join("sub")).expect("create sub");
        fs::write(root.join("sub/x.ts"), "x").expect("write x");
        fs::write(root.join("y.ts"), "y").expect("write y");

        let filesystem = OsFileSystem::new(&root).expect("filesystem");
        let root_names = collect_names(filesystem.read_dir(Path::new(".")).expect("read_dir root"));
        assert_eq!(root_names, vec!["sub", "y.ts"]);

        let sub_names = collect_names(filesystem.read_dir(Path::new("sub")).expect("read_dir sub"));
        assert_eq!(sub_names, vec!["x.ts"]);

        fs::remove_dir_all(root).expect("remove temporary root");
    }

    #[test]
    fn read_dir_empty_directory() {
        let root = temporary_root();
        fs::create_dir(root.join("empty")).expect("create empty");

        let filesystem = OsFileSystem::new(&root).expect("filesystem");
        assert!(
            filesystem
                .read_dir(Path::new("empty"))
                .expect("read_dir")
                .is_empty()
        );

        fs::remove_dir_all(root).expect("remove temporary root");
    }

    #[test]
    fn read_dir_missing_returns_not_found() {
        let root = temporary_root();
        let filesystem = OsFileSystem::new(&root).expect("filesystem");

        assert_eq!(
            filesystem
                .read_dir(Path::new("missing"))
                .expect_err("missing")
                .kind(),
            io::ErrorKind::NotFound
        );

        fs::remove_dir_all(root).expect("remove temporary root");
    }

    #[test]
    fn read_dir_non_directory_returns_not_a_directory() {
        let root = temporary_root();
        fs::write(root.join("file.ts"), "x").expect("write file");
        let filesystem = OsFileSystem::new(&root).expect("filesystem");

        assert_eq!(
            filesystem
                .read_dir(Path::new("file.ts"))
                .expect_err("not a directory")
                .kind(),
            io::ErrorKind::NotADirectory
        );

        fs::remove_dir_all(root).expect("remove temporary root");
    }

    #[test]
    #[cfg(unix)]
    fn read_dir_rejects_escaping_symlink() {
        use std::os::unix::fs::symlink;

        let root = temporary_root();
        let outside = root.parent().unwrap().join(format!("bamts-outside-{}", {
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        }));
        fs::create_dir(&outside).expect("create outside");

        fs::create_dir(root.join("bad")).expect("create bad");
        let link_target = Path::new("../..").join(outside.file_name().unwrap());
        symlink(&link_target, root.join("bad/link")).expect("create escape symlink");

        let filesystem = OsFileSystem::new(&root).expect("filesystem");
        assert_eq!(
            filesystem
                .read_dir(Path::new("bad"))
                .expect_err("escape")
                .kind(),
            io::ErrorKind::PermissionDenied
        );

        fs::remove_dir_all(root).expect("remove temporary root");
        fs::remove_dir_all(outside).expect("remove outside");
    }
}
