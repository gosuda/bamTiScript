//! Flushes that mean the same thing on every host.
//!
//! Windows flushes a file only through a handle with write access, and refuses
//! to open a directory as a plain file, so `File::open(..).sync_all()` fails
//! there with "access denied".

use std::{fs::File, io, path::Path};

/// Flushes the file at `path` to storage. Other hosts flush through a read-only
/// handle, which also covers files whose mode forbids writing.
#[cfg(not(windows))]
pub(crate) fn sync_file(path: &Path) -> io::Result<()> {
    File::open(path)?.sync_all()
}

/// Flushes the file at `path` to storage through a handle with write access.
///
/// A file with the read-only attribute refuses such a handle. The attribute is
/// lifted for the flush and put back afterwards, whether or not the flush worked.
#[cfg(windows)]
pub(crate) fn sync_file(path: &Path) -> io::Result<()> {
    let flush = || {
        std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(path)?
            .sync_all()
    };
    match flush() {
        Err(denied) if denied.kind() == io::ErrorKind::PermissionDenied && is_read_only(path) => {
            set_read_only(path, false)?;
            let flushed = flush();
            let restored = set_read_only(path, true);
            flushed.and(restored)
        }
        flushed => flushed,
    }
}

#[cfg(windows)]
fn is_read_only(path: &Path) -> bool {
    std::fs::metadata(path).is_ok_and(|metadata| metadata.permissions().readonly())
}

/// Sets or clears the read-only attribute. Only Windows reaches this code: on
/// Unix, clearing the flag would make the file writable for everyone.
#[cfg(windows)]
fn set_read_only(path: &Path, read_only: bool) -> io::Result<()> {
    let mut permissions = std::fs::metadata(path)?.permissions();
    permissions.set_readonly(read_only);
    std::fs::set_permissions(path, permissions)
}

/// Flushes the directory entry list at `path`.
///
/// Windows is skipped. `std` cannot open a directory there; a handle opened with
/// `FILE_FLAG_BACKUP_SEMANTICS` for writing can be flushed on NTFS, but this code
/// does not do that. NTFS journals the rename, which is not a promise that the
/// rename is on disk after a power loss, so a rename that has returned is
/// slightly less durable on Windows than on other hosts.
pub(crate) fn sync_directory(path: &Path) -> io::Result<()> {
    if cfg!(windows) {
        return Ok(());
    }
    File::open(path)?.sync_all()
}

#[cfg(test)]
mod tests {
    use std::{env, fs};

    use super::{sync_directory, sync_file};

    fn scratch(tag: &str) -> std::path::PathBuf {
        let dir = env::temp_dir().join(format!("bamts-fsync-{tag}-{}", std::process::id()));
        fs::create_dir_all(&dir).expect("create scratch dir");
        dir
    }

    #[test]
    fn a_written_file_and_its_directory_flush() {
        let dir = scratch("written");
        let file = dir.join("data");
        fs::write(&file, b"payload").expect("write file");

        sync_file(&file).expect("flush file");
        sync_directory(&dir).expect("flush directory");

        fs::remove_dir_all(dir).expect("remove scratch dir");
    }

    #[test]
    fn a_missing_file_is_an_error_not_a_silent_success() {
        let dir = scratch("missing");

        assert_eq!(
            sync_file(&dir.join("absent"))
                .expect_err("missing file")
                .kind(),
            std::io::ErrorKind::NotFound
        );

        fs::remove_dir_all(dir).expect("remove scratch dir");
    }

    #[test]
    #[cfg(windows)]
    fn a_file_with_the_read_only_attribute_flushes_and_stays_read_only() {
        let dir = scratch("attribute");
        let file = dir.join("data");
        fs::write(&file, b"payload").expect("write file");
        super::set_read_only(&file, true).expect("set the read-only attribute");

        sync_file(&file).expect("flush read-only file");

        let read_only = fs::metadata(&file)
            .expect("metadata")
            .permissions()
            .readonly();
        super::set_read_only(&file, false).expect("clear the attribute for cleanup");
        assert!(read_only, "the attribute is restored after the flush");

        fs::remove_dir_all(dir).expect("remove scratch dir");
    }

    #[test]
    #[cfg(unix)]
    fn a_file_whose_mode_forbids_writing_still_flushes() {
        use std::os::unix::fs::PermissionsExt;

        let dir = scratch("readonly");
        let file = dir.join("data");
        fs::write(&file, b"payload").expect("write file");
        fs::set_permissions(&file, fs::Permissions::from_mode(0o444)).expect("drop write bit");

        sync_file(&file).expect("flush read-only file");

        fs::remove_dir_all(dir).expect("remove scratch dir");
    }
}
