//! Flushes that mean the same thing on every host.
//!
//! Windows flushes a file only through a handle with write access, and refuses
//! to open a directory as a plain file, so `File::open(..).sync_all()` fails
//! there with "access denied".

use std::{
    fs::{File, OpenOptions},
    io,
    path::Path,
};

/// Flushes the file at `path` to storage. Other hosts flush through a read-only
/// handle, which also covers files whose mode forbids writing.
pub(crate) fn sync_file(path: &Path) -> io::Result<()> {
    OpenOptions::new()
        .read(true)
        .write(cfg!(windows))
        .open(path)?
        .sync_all()
}

/// Flushes the directory entry list at `path`. Windows has no directory flush:
/// a directory cannot be opened for writing, and NTFS journals the rename itself.
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
