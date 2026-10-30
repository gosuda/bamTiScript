//! Host facts and process observation.
//!
//! OS-specific reads live here so callers stay portable. A fact the host
//! cannot provide is [`UNAVAILABLE`] or a typed error, never a fabricated value.

use std::fmt;

#[cfg(any(target_os = "linux", test))]
mod linux;
#[cfg(any(target_os = "macos", test))]
mod macos;

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

/// Facts that identify the machine, for matching a measurement host.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MachineFacts {
    /// Kernel release, such as `7.0.0-30-generic`.
    pub kernel_release: String,
    /// Kernel build version tail.
    pub kernel_version: String,
    /// CPU model name.
    pub cpu_model: String,
    /// Distinct physical sockets.
    pub sockets: u32,
    /// Physical cores per socket.
    pub cores_per_socket: u32,
    /// CPU microcode revision, or [`UNAVAILABLE`].
    pub microcode: String,
    /// CPU frequency governor, or the host's marker for none.
    pub governor: String,
    /// Total swap in KiB.
    pub swap_total_kib: u64,
}

/// How the calling thread is placed on the machine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ThreadPlacement {
    /// CPUs the thread may run on, such as `0-19`, or [`UNAVAILABLE`].
    pub cpu_affinity: String,
    /// NUMA memory policy, or [`UNAVAILABLE`].
    pub memory_policy: String,
    /// NUMA memory nodes, or [`UNAVAILABLE`].
    pub memory_nodes: String,
}

/// Reads the facts that identify this machine.
///
/// # Errors
/// Returns [`PlatformError`] when this host has no implementation or the host
/// answers in a shape the reader does not accept.
pub fn machine_facts() -> Result<MachineFacts, PlatformError> {
    #[cfg(target_os = "linux")]
    {
        linux::machine_facts()
    }
    #[cfg(target_os = "macos")]
    {
        macos::machine_facts()
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        Err(PlatformError::Unsupported("machine facts"))
    }
}

/// Reads how the calling thread is placed on this machine.
///
/// # Errors
/// Returns [`PlatformError`] when this host has no implementation or the host
/// answers in a shape the reader does not accept.
pub fn thread_placement() -> Result<ThreadPlacement, PlatformError> {
    #[cfg(target_os = "linux")]
    {
        linux::thread_placement()
    }
    #[cfg(target_os = "macos")]
    {
        macos::thread_placement()
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        Err(PlatformError::Unsupported("thread placement"))
    }
}

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
