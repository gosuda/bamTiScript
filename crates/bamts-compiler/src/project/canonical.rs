//! One spelling for every canonical path.
//!
//! On Windows, `fs::canonicalize` returns the verbatim spelling (`\\?\C:\dir`),
//! while the working directory, the temp directory and user input use the plain
//! spelling (`C:\dir`). `Path::starts_with` treats the two spellings as different
//! roots, so a file that lies inside a project looks like an escape. Every canonical
//! path in the product goes through [`canonicalize`], which returns the plain
//! spelling whenever the plain spelling names the same file.

use std::{
    ffi::{OsStr, OsString},
    fs, io,
    path::{Component, MAIN_SEPARATOR, Path, PathBuf, Prefix},
};

/// `fs::canonicalize` with the verbatim prefix removed when that is safe.
///
/// On platforms without path prefixes this is exactly `fs::canonicalize`.
pub fn canonicalize(path: impl AsRef<Path>) -> io::Result<PathBuf> {
    fs::canonicalize(path).map(|canonical| simplify(&canonical))
}

/// Rewrites a verbatim disk path (`\\?\C:\a`) or verbatim UNC path
/// (`\\?\UNC\server\share\a`) to its plain spelling (`C:\a`, `\\server\share\a`).
///
/// A verbatim path stays as it is when the plain spelling could name a different
/// file: when it has a relative `.` or `..` segment, when a segment is a reserved
/// device name, ends in a dot or a space, contains a character that Win32 does not
/// accept, or is not valid Unicode, and when it has no root directory.
#[must_use]
pub fn simplify(path: &Path) -> PathBuf {
    let mut components = path.components();
    let Some(Component::Prefix(prefix)) = components.next() else {
        return path.to_path_buf();
    };
    let mut plain = match prefix.kind() {
        Prefix::VerbatimDisk(drive) => PathBuf::from(format!("{}:", char::from(drive))),
        Prefix::VerbatimUNC(server, share) => {
            if !(is_plain_name(server) && is_plain_name(share)) {
                return path.to_path_buf();
            }
            let mut unc = OsString::from(r"\\");
            unc.push(server);
            unc.push(r"\");
            unc.push(share);
            PathBuf::from(unc)
        }
        _ => return path.to_path_buf(),
    };
    if components.next() != Some(Component::RootDir) {
        return path.to_path_buf();
    }
    plain.push(Component::RootDir.as_os_str());
    for component in components {
        match component {
            Component::Normal(name) if is_plain_name(name) => plain.push(name),
            _ => return path.to_path_buf(),
        }
    }
    plain
}

/// The path as TypeScript prints it: `/` separates segments on every platform.
///
/// Source-map URLs, `sources` entries and tsc messages use this text. Where the
/// platform separator is already `/`, the text is the path unchanged.
#[must_use]
pub fn slash_text(path: &Path) -> String {
    path.to_string_lossy().replace(MAIN_SEPARATOR, "/")
}

fn is_plain_name(name: &OsStr) -> bool {
    let Some(name) = name.to_str() else {
        return false;
    };
    let invalid = |character: char| {
        character.is_control()
            || matches!(
                character,
                '<' | '>' | ':' | '"' | '/' | '\\' | '|' | '?' | '*'
            )
    };
    !name.is_empty()
        && !name.ends_with(['.', ' '])
        && !name.contains(invalid)
        && !is_reserved_device_name(name)
}

/// Win32 reads `NUL`, `nul.txt` and `NUL .txt` as the device, not as a file.
fn is_reserved_device_name(name: &str) -> bool {
    let stem = name
        .split('.')
        .next()
        .unwrap_or_default()
        .trim_end_matches(' ');
    const DEVICES: [&str; 6] = ["CON", "PRN", "AUX", "NUL", "CONIN$", "CONOUT$"];
    if DEVICES
        .iter()
        .any(|device| stem.eq_ignore_ascii_case(device))
    {
        return true;
    }
    let mut characters = stem.chars();
    let family: String = characters.by_ref().take(3).collect();
    let numbered = matches!(
        (characters.next(), characters.next()),
        (Some('1'..='9' | '¹' | '²' | '³'), None)
    );
    numbered && (family.eq_ignore_ascii_case("COM") || family.eq_ignore_ascii_case("LPT"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fresh_dir(label: &str) -> PathBuf {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock after epoch")
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "bamts-canonical-{label}-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&directory).expect("create test directory");
        directory
    }

    #[test]
    fn canonicalize_of_a_missing_path_is_the_platform_error() {
        let missing = std::env::temp_dir().join("bamts-canonical-path-that-does-not-exist");
        assert_eq!(
            canonicalize(&missing).expect_err("missing").kind(),
            io::ErrorKind::NotFound
        );
    }

    #[test]
    fn canonicalize_names_the_same_directory_as_the_platform() {
        let directory = fresh_dir("path");
        let platform = fs::canonicalize(&directory).expect("platform canonical path");
        let canonical = canonicalize(&directory).expect("canonical path");

        assert_eq!(simplify(&platform), canonical);
        assert!(canonical.is_absolute());

        fs::remove_dir_all(directory).expect("remove temporary directory");
    }

    #[test]
    fn slash_text_uses_forward_slashes_and_keeps_relative_segments() {
        let mut path = PathBuf::from("..");
        path.push("sub");
        path.push("name.part.js.map");

        assert_eq!(slash_text(&path), "../sub/name.part.js.map");
        assert_eq!(slash_text(Path::new("a/b")), "a/b");
        assert_eq!(slash_text(Path::new("")), "");
    }

    #[test]
    #[cfg(windows)]
    fn slash_text_rewrites_windows_separators() {
        assert_eq!(slash_text(Path::new(r"C:\a\b.ts")), "C:/a/b.ts");
        assert_eq!(slash_text(Path::new(r"..\a\*\*.ts")), "../a/*/*.ts");
    }

    #[test]
    fn paths_without_a_verbatim_prefix_are_returned_unchanged() {
        for input in ["", "a/b", "/", "/a/b/../c"] {
            assert_eq!(simplify(Path::new(input)), Path::new(input), "{input}");
        }
    }

    #[test]
    #[cfg(windows)]
    fn verbatim_disk_and_unc_paths_become_plain_paths() {
        for (input, expected) in [
            (r"\\?\C:\", r"C:\"),
            (r"\\?\C:\Users\me\project", r"C:\Users\me\project"),
            (r"\\?\d:\a b\c.d", r"d:\a b\c.d"),
            (r"\\?\UNC\server\share\dir", r"\\server\share\dir"),
            (r"\\?\UNC\server\share\", r"\\server\share\"),
            (r"C:\already\plain", r"C:\already\plain"),
            (r"\\server\share\plain", r"\\server\share\plain"),
        ] {
            assert_eq!(simplify(Path::new(input)), Path::new(expected), "{input}");
        }
    }

    #[test]
    #[cfg(windows)]
    fn verbatim_paths_stay_verbatim_when_the_plain_spelling_is_not_equivalent() {
        for input in [
            r"\\?\C:",
            r"\\?\C:\a\.\b",
            r"\\?\C:\a\..\b",
            r"\\?\C:\a.\b",
            r"\\?\C:\a \b",
            r"\\?\C:\dir\nul",
            r"\\?\C:\dir\NUL.txt",
            r"\\?\C:\dir\com1",
            r"\\?\C:\dir\COM².txt",
            r"\\?\C:\dir\LPT9.log",
            r"\\?\C:\dir\CONOUT$",
            r"\\?\C:\dir\file:stream",
            r"\\?\C:\dir\what?",
            r"\\?\UNC\server\sh*re\dir",
            r"\\?\pipe\name",
            r"\\?\Volume{01234567-89ab-cdef-0123-456789abcdef}\dir",
            r"\\.\C:\dir",
        ] {
            assert_eq!(simplify(Path::new(input)), Path::new(input), "{input}");
        }
        for input in [
            r"\\?\C:\dir\comma",
            r"\\?\C:\dir\com10",
            r"\\?\C:\dir\nullable",
            r"\\?\C:\dir\console",
        ] {
            assert_ne!(simplify(Path::new(input)), Path::new(input), "{input}");
        }
    }

    #[test]
    #[cfg(windows)]
    fn canonicalize_returns_the_plain_spelling_of_a_real_directory() {
        let directory = fresh_dir("plain");
        let canonical = canonicalize(&directory).expect("canonical path");

        assert!(
            matches!(
                canonical.components().next(),
                Some(Component::Prefix(prefix)) if matches!(prefix.kind(), Prefix::Disk(_))
            ),
            "{} is not a plain drive path",
            canonical.display()
        );
        assert!(canonical.starts_with(simplify(&directory)));

        fs::remove_dir_all(directory).expect("remove temporary directory");
    }
}
