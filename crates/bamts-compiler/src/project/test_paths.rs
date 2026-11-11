//! Absolute paths for tests.
//!
//! Fixtures name absolute paths the Unix way (`/workspace/a.ts`). A path without
//! a drive is not absolute on Windows, so [`abs`] puts such a path on the `C:`
//! drive there. Expected values are built with the same helpers, never written
//! out, so a test says the same thing on every platform.

use std::path::PathBuf;

/// The platform's absolute spelling of a fixture path written with `/` separators.
#[cfg(not(windows))]
pub(crate) fn abs(unix: &str) -> PathBuf {
    PathBuf::from(unix)
}

/// The platform's absolute spelling of a fixture path written with `/` separators.
#[cfg(windows)]
pub(crate) fn abs(unix: &str) -> PathBuf {
    assert!(unix.starts_with('/'), "fixture path {unix} is not rooted");
    PathBuf::from(format!("C:{}", unix.replace('/', "\\")))
}

/// [`abs`] as text, for expected messages.
pub(crate) fn abs_text(unix: &str) -> String {
    abs(unix).to_string_lossy().into_owned()
}

/// [`abs`] as the content of a JSON string literal: backslashes are escaped.
pub(crate) fn abs_json(unix: &str) -> String {
    abs_text(unix).replace('\\', "\\\\")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(not(windows))]
    fn fixture_paths_are_unchanged_where_they_are_already_absolute() {
        assert_eq!(abs("/workspace/a.ts"), PathBuf::from("/workspace/a.ts"));
        assert_eq!(abs_json("/workspace/a.ts"), "/workspace/a.ts");
    }

    #[test]
    #[cfg(windows)]
    fn fixture_paths_move_onto_the_system_drive() {
        assert_eq!(abs("/"), PathBuf::from(r"C:\"));
        assert_eq!(abs("/workspace/a.ts"), PathBuf::from(r"C:\workspace\a.ts"));
        assert!(abs("/workspace").is_absolute());
        assert_eq!(abs_text("/workspace/a.ts"), r"C:\workspace\a.ts");
        assert_eq!(abs_json("/workspace/a.ts"), r"C:\\workspace\\a.ts");
    }
}
