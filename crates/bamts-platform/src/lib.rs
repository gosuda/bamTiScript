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

/// The file the Linux backend reads for the CPU governor. A host manifest
/// records it as the evidence source of its `governor` condition, so a test can
/// hold the manifest to the code that does the reading.
pub const LINUX_GOVERNOR_SOURCE: &str = "/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor";

/// Why a host fact could not be read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlatformError {
    /// This host has no implementation of the named capability.
    Unsupported(&'static str),
    /// The host cannot find the process, which has exited or is exiting.
    ProcessGone(u32),
    /// The process shows no address space at this moment. It may be exiting,
    /// replacing its image with `exec` on macOS, or running on after its main
    /// thread exited on Linux. Only a later read can tell which.
    NoAddressSpace(u32),
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
            Self::NoAddressSpace(pid) => {
                write!(formatter, "process {pid} has no address space right now")
            }
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

/// The CPUs that are online, as a kernel CPU list such as `0-19`.
///
/// # Errors
/// Returns [`PlatformError`] when this host has no implementation or the host
/// fails the read.
pub fn online_cpu_list() -> Result<String, PlatformError> {
    #[cfg(target_os = "linux")]
    {
        linux::online_cpu_list()
    }
    #[cfg(target_os = "macos")]
    {
        macos::online_cpu_list()
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        Err(PlatformError::Unsupported("online CPU list"))
    }
}

/// The frequency governor of each online CPU, sorted. A host that has none,
/// such as macOS, reports a single [`UNAVAILABLE`].
///
/// # Errors
/// Returns [`PlatformError`] when this host has no implementation or the host
/// fails the read.
pub fn cpu_governors() -> Result<Vec<String>, PlatformError> {
    #[cfg(target_os = "linux")]
    {
        linux::cpu_governors()
    }
    #[cfg(target_os = "macos")]
    {
        Ok(vec![UNAVAILABLE.to_owned()])
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        Err(PlatformError::Unsupported("CPU governors"))
    }
}

/// The memory policy of this process as `numactl --show` reports it, or
/// [`UNAVAILABLE`] when the host or the tool does not say.
#[must_use]
pub fn numa_policy_mode() -> String {
    #[cfg(target_os = "linux")]
    {
        linux::numa_policy_mode()
    }
    #[cfg(not(target_os = "linux"))]
    {
        UNAVAILABLE.to_owned()
    }
}

/// The memory nodes this process is bound to. A host without NUMA nodes, such as
/// macOS, has none and returns an empty list.
///
/// # Errors
/// Returns [`PlatformError`] when this host has no implementation or the host
/// fails the read.
pub fn numa_memory_nodes() -> Result<Vec<u32>, PlatformError> {
    #[cfg(target_os = "linux")]
    {
        linux::numa_memory_nodes()
    }
    #[cfg(target_os = "macos")]
    {
        Ok(Vec::new())
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        Err(PlatformError::Unsupported("memory nodes"))
    }
}

/// One contiguous memory region of a process.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryRegion {
    /// Names this region. Stable across samples of one address space.
    pub identity: String,
    /// Four characters: `r`, `w`, and `x`, each `-` when absent, then `p`.
    /// For example `r-xp`.
    pub permissions: String,
    /// The backing file, or `None` for anonymous memory.
    pub pathname: Option<String>,
}

/// Lists the memory regions of a process.
///
/// The read is not atomic. While a process execs or exits, a list can be partial
/// or mix its old and new images, so sample a changing process repeatedly. A
/// mapping that comes and goes between samples is not seen at all.
///
/// # Errors
/// Returns [`PlatformError::ProcessGone`] when the host cannot find the process
/// and [`PlatformError::NoAddressSpace`] when it has no regions at this moment.
/// Neither means a child can be reaped yet, so poll it rather than concluding
/// from one read, and do not block on it: after `NoAddressSpace` it may still be
/// running. Returns another [`PlatformError`] when this host has no
/// implementation or the host fails the read.
pub fn process_regions(pid: u32) -> Result<Vec<MemoryRegion>, PlatformError> {
    #[cfg(target_os = "linux")]
    {
        linux::process_regions(pid)
    }
    #[cfg(target_os = "macos")]
    {
        macos::process_regions(pid)
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        let _ = pid;
        Err(PlatformError::Unsupported("process regions"))
    }
}

#[cfg(target_os = "linux")]
use linux::Window as WindowImpl;
#[cfg(target_os = "macos")]
use macos::Window as WindowImpl;

/// A host with no peak-memory window cannot construct one.
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
enum WindowImpl {}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
impl WindowImpl {
    fn start() -> Result<Self, PlatformError> {
        Err(PlatformError::Unsupported("peak memory window"))
    }

    fn finish(self) -> Result<u64, PlatformError> {
        match self {}
    }
}

/// Peak memory of a process since it started or last execed, in bytes.
///
/// This is the resident-set peak on Linux and the physical-footprint peak on
/// macOS.
///
/// # Errors
/// Returns [`PlatformError::ProcessGone`] when the host cannot find the process
/// and [`PlatformError::NoAddressSpace`] when it has no address space at this
/// moment. Returns another [`PlatformError`] when this host has no
/// implementation or the host fails the read.
///
/// To follow a child to its end, poll beside a `wait` until `ProcessGone`, which
/// comes only after the reap, and keep polling through `NoAddressSpace`. Linux
/// reads the main thread, so it reports that during an exit and for a process
/// running on after its main thread exited. macOS keeps answering with the
/// final peak until the reap.
pub fn peak_memory_bytes(pid: u32) -> Result<u64, PlatformError> {
    #[cfg(target_os = "linux")]
    {
        linux::peak_memory_bytes(pid)
    }
    #[cfg(target_os = "macos")]
    {
        macos::peak_memory_bytes(pid)
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        let _ = pid;
        Err(PlatformError::Unsupported("peak memory"))
    }
}

/// Measures the peak memory of the current process across a span of work.
///
/// On Linux the host resets its high-water mark when the window starts, so
/// the result is exact. macOS has no public way to reset the peak, so the
/// window samples the process footprint every millisecond and a spike shorter
/// than that can be missed. Treat the macOS value as functional evidence, not
/// as a benchmark measurement.
///
/// Windows cannot overlap on Linux. Starting one resets a mark shared by the
/// whole process, which would lower the result of a window already open.
pub struct PeakWindow(WindowImpl);

impl PeakWindow {
    /// Starts measuring.
    ///
    /// # Errors
    /// Returns [`PlatformError`] when this host has no implementation or the
    /// host refuses to start the window.
    pub fn start() -> Result<Self, PlatformError> {
        WindowImpl::start().map(Self)
    }

    /// Stops measuring and returns the peak in bytes since [`PeakWindow::start`].
    ///
    /// # Errors
    /// Returns [`PlatformError`] when the host fails the final read.
    pub fn finish(self) -> Result<u64, PlatformError> {
        self.0.finish()
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

    /// On Linux a window resets a mark shared by the whole process, so tests that
    /// open one run one at a time.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    static WINDOW_TESTS: std::sync::Mutex<()> = std::sync::Mutex::new(());

    #[cfg(target_os = "linux")]
    #[test]
    fn a_window_does_not_count_an_earlier_peak() {
        const BYTES: usize = 64 * 1024 * 1024;
        let _serial = WINDOW_TESTS
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        let block = vec![1_u8; BYTES];
        assert_eq!(block.iter().filter(|byte| **byte == 1).count(), BYTES);
        drop(block);
        let peak = PeakWindow::start().unwrap().finish().unwrap();
        assert!(
            peak < BYTES as u64,
            "peak {peak} still includes the allocation made before the window"
        );
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn a_touched_allocation_raises_the_peak_window() {
        const BYTES: usize = 64 * 1024 * 1024;
        let _serial = WINDOW_TESTS
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        let idle = PeakWindow::start().unwrap();
        let baseline = idle.finish().unwrap();

        let window = PeakWindow::start().unwrap();
        let block = vec![1_u8; BYTES];
        // Hold the allocation live long enough for the 1 ms macOS sampler to
        // be scheduled and see it, even on a busy machine.
        std::thread::sleep(std::time::Duration::from_millis(150));
        assert_eq!(block.iter().filter(|byte| **byte == 1).count(), BYTES);
        drop(block);
        let peak = window.finish().unwrap();

        let margin = 16 * 1024 * 1024;
        assert!(
            peak >= baseline + (BYTES - margin) as u64,
            "peak {peak} did not rise from the idle {baseline} by the allocation"
        );
        assert!(peak >= BYTES as u64, "peak {peak} is below the allocation");
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn the_process_peak_covers_its_current_footprint() {
        assert!(peak_memory_bytes(std::process::id()).unwrap() > 0);
    }

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
