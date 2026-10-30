//! Host facts and process observation.
//!
//! OS-specific reads live here so callers stay portable. A fact the host
//! cannot provide is [`UNAVAILABLE`] or a typed error, never a fabricated value.

use std::fmt;

/// Recorded for a fact this host does not have, such as a CPU governor on macOS.
pub const UNAVAILABLE: &str = "unavailable";

/// Why a host fact could not be read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlatformError {
    /// This host has no implementation of the named capability.
    Unsupported(&'static str),
    /// The process no longer exists.
    ProcessGone(u32),
    /// The host failed the read.
    Read { source: String, detail: String },
    /// The host answered in a shape the parser does not accept.
    Malformed { source: String, detail: String },
}

impl fmt::Display for PlatformError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsupported(what) => write!(formatter, "{what} is not available on this host"),
            Self::ProcessGone(pid) => write!(formatter, "process {pid} no longer exists"),
            Self::Read { source, detail } | Self::Malformed { source, detail } => {
                write!(formatter, "{source}: {detail}")
            }
        }
    }
}

impl std::error::Error for PlatformError {}

/// The Rust target triple of this host, in the form receipts record.
#[must_use]
pub fn host_triple() -> String {
    let environment = if cfg!(target_env = "musl") {
        "musl"
    } else if cfg!(target_env = "msvc") {
        "msvc"
    } else {
        "gnu"
    };
    match std::env::consts::OS {
        "linux" => format!("{}-unknown-linux-{environment}", std::env::consts::ARCH),
        "macos" => format!("{}-apple-darwin", std::env::consts::ARCH),
        "windows" => format!("{}-pc-windows-{environment}", std::env::consts::ARCH),
        os => format!("{}-unknown-{os}", std::env::consts::ARCH),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn host_triple_matches_the_running_host() {
        let triple = host_triple();
        assert!(triple.starts_with(std::env::consts::ARCH), "{triple}");
        if cfg!(target_os = "macos") {
            assert_eq!(triple, format!("{}-apple-darwin", std::env::consts::ARCH));
        }
        if cfg!(target_os = "linux") {
            assert!(triple.contains("-unknown-linux-"), "{triple}");
        }
    }
}
