//! Programs that every host has, for the tests that need a child process.

use std::path::PathBuf;

/// A program of the Windows system directory, such as `PING.EXE`.
pub(crate) fn windows_system_program(name: &str) -> PathBuf {
    let root = std::env::var_os("SystemRoot").expect("SystemRoot is set on Windows");
    PathBuf::from(root).join("System32").join(name)
}
