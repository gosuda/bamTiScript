//! Windows backend: process regions through `VirtualQueryEx` and peak memory
//! through `GetProcessMemoryInfo`.
//!
//! The crate takes no dependency that declares the Win32 calls, so the few it
//! needs are declared here by hand, and every unsafe block says why it is sound.
//! The pure parts, the permission letters and the NT-to-DOS path mapping, build
//! on every host so their tests run everywhere.

#[cfg(target_os = "windows")]
use std::collections::HashMap;
#[cfg(target_os = "windows")]
use std::mem::size_of;
#[cfg(target_os = "windows")]
use std::sync::Arc;
#[cfg(target_os = "windows")]
use std::sync::atomic::{AtomicBool, Ordering};
#[cfg(target_os = "windows")]
use std::thread;
#[cfg(target_os = "windows")]
use std::time::Duration;

#[cfg(target_os = "windows")]
use crate::{MemoryRegion, PlatformError};

#[cfg(target_os = "windows")]
type Result<T> = std::result::Result<T, PlatformError>;

/// `MEMORY_BASIC_INFORMATION::State` of pages that are backed by memory or the
/// paging file. Reserved and free address space is not mapped.
#[cfg(target_os = "windows")]
const MEM_COMMIT: u32 = 0x1000;
/// `MEMORY_BASIC_INFORMATION::Type` of an executable image or one of its sections.
const MEM_IMAGE: u32 = 0x0100_0000;
/// `MEMORY_BASIC_INFORMATION::Type` of a mapped file or shared section.
const MEM_MAPPED: u32 = 0x0004_0000;

const PAGE_READONLY: u32 = 0x02;
const PAGE_READWRITE: u32 = 0x04;
const PAGE_WRITECOPY: u32 = 0x08;
const PAGE_EXECUTE: u32 = 0x10;
const PAGE_EXECUTE_READ: u32 = 0x20;
const PAGE_EXECUTE_READWRITE: u32 = 0x40;
const PAGE_EXECUTE_WRITECOPY: u32 = 0x80;
/// A guard page faults on first touch, so no access is possible until then.
const PAGE_GUARD: u32 = 0x100;
/// The protection modes sit in the low byte; higher bits are modifiers.
const PAGE_MODE_MASK: u32 = 0xFF;

/// Formats Windows page protection in the `rwxp` style of `/proc/<pid>/maps`.
///
/// Copy-on-write pages count as writable: a write through them succeeds. A guard
/// page and `PAGE_NOACCESS` are `---p`, as a guard page is on Linux.
#[cfg(any(target_os = "windows", test))]
fn permissions_string(protect: u32) -> String {
    if protect & PAGE_GUARD != 0 {
        return "---p".to_owned();
    }
    let (read, write, execute) = match protect & PAGE_MODE_MASK {
        PAGE_READONLY => (true, false, false),
        PAGE_READWRITE | PAGE_WRITECOPY => (true, true, false),
        PAGE_EXECUTE => (false, false, true),
        PAGE_EXECUTE_READ => (true, false, true),
        PAGE_EXECUTE_READWRITE | PAGE_EXECUTE_WRITECOPY => (true, true, true),
        _ => (false, false, false),
    };
    let flag = |present: bool, letter: char| if present { letter } else { '-' };
    format!(
        "{}{}{}p",
        flag(read, 'r'),
        flag(write, 'w'),
        flag(execute, 'x')
    )
}

/// What backs a committed region, for its identity.
#[cfg(any(target_os = "windows", test))]
fn kind_name(kind: u32) -> &'static str {
    match kind {
        MEM_IMAGE => "image",
        MEM_MAPPED => "mapped",
        _ => "private",
    }
}

/// One drive letter and the NT device it names, such as `C:` and
/// `\Device\HarddiskVolume7`.
#[cfg(any(target_os = "windows", test))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct DosDevice {
    drive: String,
    target: String,
}

/// Turns the NT path that `GetMappedFileName` returns into the path a program
/// opens, such as `C:\Windows\System32\sort.exe`.
///
/// A path on a device with no drive letter keeps its NT spelling: it still names
/// the backing file, and a made-up drive would not.
#[cfg(any(target_os = "windows", test))]
fn dos_path(nt_path: &str, devices: &[DosDevice]) -> String {
    let under_device = |device: &DosDevice| {
        let prefix = nt_path.get(..device.target.len())?;
        let rest = nt_path.get(device.target.len()..)?;
        (prefix.eq_ignore_ascii_case(&device.target) && rest.starts_with('\\'))
            .then(|| format!("{}{rest}", device.drive))
    };
    if let Some(path) = devices.iter().find_map(under_device) {
        return path;
    }
    const MUP: &str = "\\Device\\Mup\\";
    match nt_path.get(..MUP.len()) {
        Some(prefix) if prefix.eq_ignore_ascii_case(MUP) => {
            format!("\\\\{}", &nt_path[MUP.len()..])
        }
        _ => nt_path.to_owned(),
    }
}

/// Names a region by its address range first, as every host does, then by the
/// allocation it belongs to and what backs it.
#[cfg(any(target_os = "windows", test))]
fn region_identity(start: u64, end: u64, allocation_base: u64, kind: u32, path: &str) -> String {
    format!(
        "{start:x}-{end:x} {allocation_base:x} {} {path}",
        kind_name(kind)
    )
}

#[cfg(target_os = "windows")]
mod ffi {
    use std::ffi::c_void;

    pub(super) type Handle = *mut c_void;

    /// `MEMORY_BASIC_INFORMATION`. `PartitionId` exists in the 64-bit layout only.
    #[repr(C)]
    #[derive(Default)]
    pub(super) struct MemoryBasicInformation {
        pub(super) base_address: usize,
        pub(super) allocation_base: usize,
        pub(super) _allocation_protect: u32,
        #[cfg(target_pointer_width = "64")]
        pub(super) _partition_id: u16,
        pub(super) region_size: usize,
        pub(super) state: u32,
        pub(super) protect: u32,
        pub(super) kind: u32,
    }

    /// `PROCESS_MEMORY_COUNTERS`.
    #[repr(C)]
    #[derive(Default)]
    pub(super) struct ProcessMemoryCounters {
        pub(super) cb: u32,
        pub(super) _page_fault_count: u32,
        pub(super) peak_working_set_size: usize,
        pub(super) working_set_size: usize,
        pub(super) _quota_peak_paged_pool_usage: usize,
        pub(super) _quota_paged_pool_usage: usize,
        pub(super) _quota_peak_non_paged_pool_usage: usize,
        pub(super) _quota_non_paged_pool_usage: usize,
        pub(super) _pagefile_usage: usize,
        pub(super) _peak_pagefile_usage: usize,
    }

    // Sizes measured from the SDK headers. A layout drift fails the build here,
    // not at the kernel boundary.
    #[cfg(target_pointer_width = "64")]
    const _: () = assert!(size_of::<MemoryBasicInformation>() == 48);
    #[cfg(target_pointer_width = "64")]
    const _: () = assert!(size_of::<ProcessMemoryCounters>() == 72);
    #[cfg(target_pointer_width = "32")]
    const _: () = assert!(size_of::<MemoryBasicInformation>() == 28);
    #[cfg(target_pointer_width = "32")]
    const _: () = assert!(size_of::<ProcessMemoryCounters>() == 40);

    #[link(name = "kernel32")]
    #[allow(unsafe_code)]
    unsafe extern "system" {
        pub(super) fn OpenProcess(
            desired_access: u32,
            inherit_handle: i32,
            process_id: u32,
        ) -> Handle;
        pub(super) fn CloseHandle(object: Handle) -> i32;
        pub(super) fn WaitForSingleObject(object: Handle, milliseconds: u32) -> u32;
        pub(super) fn GetCurrentProcess() -> Handle;
        pub(super) fn VirtualQueryEx(
            process: Handle,
            address: *const c_void,
            buffer: *mut MemoryBasicInformation,
            length: usize,
        ) -> usize;
        pub(super) fn K32GetMappedFileNameW(
            process: Handle,
            address: *mut c_void,
            file_name: *mut u16,
            size: u32,
        ) -> u32;
        pub(super) fn K32GetProcessMemoryInfo(
            process: Handle,
            counters: *mut ProcessMemoryCounters,
            size: u32,
        ) -> i32;
        pub(super) fn QueryDosDeviceW(
            device_name: *const u16,
            target_path: *mut u16,
            max: u32,
        ) -> u32;
    }
}

/// `ERROR_ACCESS_DENIED`: what a process that has exited, or is exiting, answers
/// to a read through a handle that is still open.
#[cfg(target_os = "windows")]
const ERROR_ACCESS_DENIED: i32 = 5;
/// `ERROR_INVALID_PARAMETER`: no process has this id, and no region starts at or
/// after an address past the last one.
#[cfg(target_os = "windows")]
const ERROR_INVALID_PARAMETER: i32 = 87;
/// `ERROR_PARTIAL_COPY`: the process went away in the middle of a read.
#[cfg(target_os = "windows")]
const ERROR_PARTIAL_COPY: i32 = 299;

/// `PROCESS_QUERY_INFORMATION | PROCESS_VM_READ | SYNCHRONIZE`.
#[cfg(target_os = "windows")]
const PROCESS_ACCESS: u32 = 0x0400 | 0x0010 | 0x0010_0000;
#[cfg(target_os = "windows")]
const WAIT_OBJECT_0: u32 = 0;
#[cfg(target_os = "windows")]
const WAIT_TIMEOUT: u32 = 0x102;

#[cfg(target_os = "windows")]
const OPEN_SOURCE: &str = "OpenProcess";
#[cfg(target_os = "windows")]
const REGION_SOURCE: &str = "VirtualQueryEx";
#[cfg(target_os = "windows")]
const MEMORY_SOURCE: &str = "GetProcessMemoryInfo";

#[cfg(target_os = "windows")]
fn read_error(source: &str, error: &std::io::Error) -> PlatformError {
    PlatformError::Read {
        source: source.to_owned(),
        detail: error.to_string(),
    }
}

/// An open process handle, closed on drop.
#[cfg(target_os = "windows")]
struct Process {
    handle: ffi::Handle,
    pid: u32,
}

#[cfg(target_os = "windows")]
impl Process {
    fn open(pid: u32) -> Result<Self> {
        // SAFETY: `OpenProcess` takes three integers and returns a new handle
        // that this value owns, or null.
        #[allow(unsafe_code)]
        let handle = unsafe { ffi::OpenProcess(PROCESS_ACCESS, 0, pid) };
        if handle.is_null() {
            let error = std::io::Error::last_os_error();
            return Err(if error.raw_os_error() == Some(ERROR_INVALID_PARAMETER) {
                PlatformError::ProcessGone(pid)
            } else {
                read_error(OPEN_SOURCE, &error)
            });
        }
        Ok(Self { handle, pid })
    }

    /// Whether the process has ended. The host keeps answering reads for a process
    /// that has exited for as long as anyone holds a handle to it, so a caller that
    /// waits for `ProcessGone` would wait for the parent to close its own handle.
    fn has_exited(&self) -> Result<bool> {
        // SAFETY: `self.handle` is a live handle with the `SYNCHRONIZE` right, and
        // a zero timeout makes the call return at once.
        #[allow(unsafe_code)]
        let wait = unsafe { ffi::WaitForSingleObject(self.handle, 0) };
        match wait {
            WAIT_OBJECT_0 => Ok(true),
            WAIT_TIMEOUT => Ok(false),
            _ => Err(read_error(OPEN_SOURCE, &std::io::Error::last_os_error())),
        }
    }

    /// Classifies a failed read: the process has gone, it has no address space
    /// right now, or the host failed the read.
    fn failure(&self, source: &str, error: &std::io::Error) -> PlatformError {
        match self.has_exited() {
            Ok(true) => PlatformError::ProcessGone(self.pid),
            Ok(false)
                if matches!(
                    error.raw_os_error(),
                    Some(ERROR_ACCESS_DENIED | ERROR_PARTIAL_COPY)
                ) =>
            {
                PlatformError::NoAddressSpace(self.pid)
            }
            Ok(false) => read_error(source, error),
            Err(wait_error) => wait_error,
        }
    }

    /// Reads the region that starts at or after `address`, or `None` past the last.
    fn query(
        &self,
        address: usize,
    ) -> std::result::Result<Option<ffi::MemoryBasicInformation>, std::io::Error> {
        let mut info = ffi::MemoryBasicInformation::default();
        // SAFETY: `info` is a live, writable `MEMORY_BASIC_INFORMATION` and its
        // size is the length the host is told. The host keeps no pointer to it.
        #[allow(unsafe_code)]
        let written = unsafe {
            ffi::VirtualQueryEx(
                self.handle,
                address as *const std::ffi::c_void,
                &raw mut info,
                size_of::<ffi::MemoryBasicInformation>(),
            )
        };
        if written != 0 {
            return Ok(Some(info));
        }
        let error = std::io::Error::last_os_error();
        if error.raw_os_error() == Some(ERROR_INVALID_PARAMETER) {
            Ok(None)
        } else {
            Err(error)
        }
    }

    /// The NT path of the file that backs the allocation at `address`.
    fn mapped_file(&self, address: usize, buffer: &mut [u16]) -> Option<String> {
        let capacity = u32::try_from(buffer.len()).ok()?;
        // SAFETY: `buffer` is live and writable for `capacity` UTF-16 units, the
        // size the host is told. `address` is only looked up, never read.
        #[allow(unsafe_code)]
        let written = unsafe {
            ffi::K32GetMappedFileNameW(
                self.handle,
                address as *mut std::ffi::c_void,
                buffer.as_mut_ptr(),
                capacity,
            )
        };
        // Zero is no name. A full buffer was cut short, and a cut name names nothing.
        let written = usize::try_from(written).ok()?;
        (written != 0 && written < buffer.len())
            .then(|| String::from_utf16_lossy(&buffer[..written]))
    }

    fn memory_counters(&self) -> std::result::Result<ffi::ProcessMemoryCounters, std::io::Error> {
        counters_of(self.handle)
    }
}

#[cfg(target_os = "windows")]
impl Drop for Process {
    fn drop(&mut self) {
        // SAFETY: `self.handle` came from `OpenProcess` and is closed only here.
        #[allow(unsafe_code)]
        unsafe {
            ffi::CloseHandle(self.handle);
        }
    }
}

#[cfg(target_os = "windows")]
fn counters_of(
    handle: ffi::Handle,
) -> std::result::Result<ffi::ProcessMemoryCounters, std::io::Error> {
    let mut counters = ffi::ProcessMemoryCounters::default();
    let size = u32::try_from(size_of::<ffi::ProcessMemoryCounters>())
        .expect("the counters record fits a DWORD");
    counters.cb = size;
    // SAFETY: `counters` is a live, writable `PROCESS_MEMORY_COUNTERS` whose size
    // is both in `cb` and the length the host is told. `handle` is a process
    // handle, or the pseudo-handle of the calling process, which needs no closing.
    #[allow(unsafe_code)]
    let status = unsafe { ffi::K32GetProcessMemoryInfo(handle, &raw mut counters, size) };
    if status == 0 {
        Err(std::io::Error::last_os_error())
    } else {
        Ok(counters)
    }
}

/// Maps each drive letter to its NT device, so a mapped file name can be shown as
/// the path a program opens. A letter with no device is left out.
#[cfg(target_os = "windows")]
fn dos_devices() -> Vec<DosDevice> {
    let mut buffer = [0_u16; 1024];
    let mut devices = Vec::new();
    for letter in 'A'..='Z' {
        let drive = format!("{letter}:");
        let name: Vec<u16> = drive.encode_utf16().chain(std::iter::once(0)).collect();
        let capacity = u32::try_from(buffer.len()).expect("the buffer fits a DWORD");
        // SAFETY: `name` is NUL-terminated and `buffer` is live and writable for
        // `capacity` UTF-16 units, the size the host is told.
        #[allow(unsafe_code)]
        let written = unsafe { ffi::QueryDosDeviceW(name.as_ptr(), buffer.as_mut_ptr(), capacity) };
        if written == 0 {
            continue;
        }
        // The answer is a list of NUL-terminated names; the first is the current one.
        let first = buffer
            .iter()
            .position(|unit| *unit == 0)
            .unwrap_or(buffer.len());
        devices.push(DosDevice {
            drive,
            target: String::from_utf16_lossy(&buffer[..first]),
        });
    }
    devices
}

#[cfg(target_os = "windows")]
pub(crate) fn process_regions(pid: u32) -> Result<Vec<MemoryRegion>> {
    let process = Process::open(pid)?;
    let devices = dos_devices();
    let mut name_buffer = vec![0_u16; 32 * 1024];
    // One lookup per allocation: the sections of an image share their allocation.
    let mut names: HashMap<usize, Option<String>> = HashMap::new();
    let mut regions = Vec::new();
    let mut address = 0_usize;
    loop {
        let info = match process.query(address) {
            Ok(Some(info)) => info,
            Ok(None) => break,
            Err(error) => return Err(process.failure(REGION_SOURCE, &error)),
        };
        let next = info
            .base_address
            .checked_add(info.region_size)
            .filter(|next| *next > address)
            .ok_or_else(|| PlatformError::Malformed {
                source: REGION_SOURCE.to_owned(),
                detail: "region walk does not advance".to_owned(),
            })?;
        address = next;
        if info.state != MEM_COMMIT {
            continue;
        }
        let backed = info.kind == MEM_IMAGE || info.kind == MEM_MAPPED;
        let path = if backed {
            names
                .entry(info.allocation_base)
                .or_insert_with(|| {
                    process
                        .mapped_file(info.allocation_base, &mut name_buffer)
                        .map(|nt_path| dos_path(&nt_path, &devices))
                })
                .clone()
        } else {
            None
        };
        regions.push(MemoryRegion {
            identity: region_identity(
                info.base_address as u64,
                next as u64,
                info.allocation_base as u64,
                info.kind,
                path.as_deref().unwrap_or(""),
            ),
            permissions: permissions_string(info.protect),
            pathname: path,
        });
    }
    if regions.is_empty() {
        return Err(if process.has_exited()? {
            PlatformError::ProcessGone(pid)
        } else {
            PlatformError::NoAddressSpace(pid)
        });
    }
    Ok(regions)
}

#[cfg(target_os = "windows")]
pub(crate) fn peak_memory_bytes(pid: u32) -> Result<u64> {
    let process = Process::open(pid)?;
    // The counters of a process that has exited stay readable while a handle to it
    // is open. Stop here so that `ProcessGone` does not wait for that handle.
    if process.has_exited()? {
        return Err(PlatformError::ProcessGone(pid));
    }
    match process.memory_counters() {
        Ok(counters) => Ok(counters.peak_working_set_size as u64),
        Err(error) => Err(process.failure(MEMORY_SOURCE, &error)),
    }
}

/// The working set of this process now, in bytes.
#[cfg(target_os = "windows")]
fn working_set_bytes() -> Result<u64> {
    // SAFETY: `GetCurrentProcess` takes no arguments and returns a pseudo-handle
    // for the calling process.
    #[allow(unsafe_code)]
    let current = unsafe { ffi::GetCurrentProcess() };
    counters_of(current)
        .map(|counters| counters.working_set_size as u64)
        .map_err(|error| read_error(MEMORY_SOURCE, &error))
}

/// Samples the working set of this process while the window is open. Windows has
/// no way to reset the peak working set, so a spike shorter than the sampling
/// interval can be missed.
#[cfg(target_os = "windows")]
pub(crate) struct Window {
    stop: Arc<AtomicBool>,
    sampler: Option<thread::JoinHandle<u64>>,
}

#[cfg(target_os = "windows")]
impl Window {
    const INTERVAL: Duration = Duration::from_millis(1);

    pub(crate) fn start() -> Result<Self> {
        let first = working_set_bytes()?;
        let stop = Arc::new(AtomicBool::new(false));
        let flag = Arc::clone(&stop);
        let sampler = thread::Builder::new()
            .name("bamts-peak-window".to_owned())
            .spawn(move || {
                let mut peak = first;
                while !flag.load(Ordering::Acquire) {
                    if let Ok(bytes) = working_set_bytes() {
                        peak = peak.max(bytes);
                    }
                    thread::sleep(Self::INTERVAL);
                }
                peak
            })
            .map_err(|error| PlatformError::Read {
                source: "peak memory sampler thread".to_owned(),
                detail: error.to_string(),
            })?;
        Ok(Self {
            stop,
            sampler: Some(sampler),
        })
    }

    pub(crate) fn finish(mut self) -> Result<u64> {
        self.stop.store(true, Ordering::Release);
        let sampled = self
            .sampler
            .take()
            .expect("the sampler is present until the window finishes")
            .join()
            .map_err(|_| PlatformError::Read {
                source: "peak memory sampler thread".to_owned(),
                detail: "the sampler panicked".to_owned(),
            })?;
        Ok(sampled.max(working_set_bytes()?))
    }
}

#[cfg(target_os = "windows")]
impl Drop for Window {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::Release);
        if let Some(sampler) = self.sampler.take() {
            let _ = sampler.join();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn volume(drive: &str, target: &str) -> DosDevice {
        DosDevice {
            drive: drive.to_owned(),
            target: target.to_owned(),
        }
    }

    #[test]
    fn protection_modes_become_rwx_letters() {
        for (protect, expected) in [
            (0x01, "---p"),
            (0x02, "r--p"),
            (0x04, "rw-p"),
            (0x08, "rw-p"),
            (0x10, "--xp"),
            (0x20, "r-xp"),
            (0x40, "rwxp"),
            (0x80, "rwxp"),
            // Modifier bits do not change the mode.
            (0x204, "rw-p"),
            (0x0200_0020, "r-xp"),
            (0, "---p"),
        ] {
            assert_eq!(permissions_string(protect), expected, "{protect:#x}");
        }
    }

    #[test]
    fn a_guard_page_allows_no_access() {
        assert_eq!(permissions_string(0x104), "---p");
        assert_eq!(permissions_string(0x140), "---p");
    }

    #[test]
    fn a_mapped_file_name_loses_its_nt_device() {
        let devices = [
            volume("C:", "\\Device\\HarddiskVolume7"),
            volume("D:", "\\Device\\HarddiskVolume70"),
        ];
        assert_eq!(
            dos_path(
                "\\Device\\HarddiskVolume7\\Windows\\System32\\sort.exe",
                &devices
            ),
            "C:\\Windows\\System32\\sort.exe"
        );
        // A device whose name only starts the same is another device.
        assert_eq!(
            dos_path("\\Device\\HarddiskVolume70\\data\\a.bin", &devices),
            "D:\\data\\a.bin"
        );
        assert_eq!(
            dos_path("\\device\\harddiskvolume7\\Users\\me\\a.exe", &devices),
            "C:\\Users\\me\\a.exe"
        );
    }

    #[test]
    fn a_network_share_becomes_a_unc_path() {
        assert_eq!(
            dos_path("\\Device\\Mup\\server\\share\\dir\\a.dll", &[]),
            "\\\\server\\share\\dir\\a.dll"
        );
    }

    #[test]
    fn a_device_without_a_drive_letter_keeps_its_nt_path() {
        let devices = [volume("C:", "\\Device\\HarddiskVolume7")];
        let path = "\\Device\\HarddiskVolume9\\x.dll";
        assert_eq!(dos_path(path, &devices), path);
        // A path that ends at the device name is not under it.
        assert_eq!(
            dos_path("\\Device\\HarddiskVolume7", &devices),
            "\\Device\\HarddiskVolume7"
        );
        assert_eq!(dos_path("", &devices), "");
    }

    #[test]
    fn a_region_identity_starts_with_its_address_range() {
        let identity = region_identity(
            0x7ff6_606d_0000,
            0x7ff6_606d_1000,
            0x7ff6_606d_0000,
            MEM_IMAGE,
            "C:\\a b\\x.exe",
        );
        let range = identity.split_whitespace().next().expect("a first field");
        assert_eq!(range, "7ff6606d0000-7ff6606d1000");
        assert!(identity.ends_with("image C:\\a b\\x.exe"), "{identity}");
        assert!(region_identity(1, 2, 1, 0, "").contains(" private"));
    }

    #[cfg(target_os = "windows")]
    mod live {
        use std::io::Write;
        use std::process::{Command, Stdio};

        use super::super::*;

        /// A child that stays alive until its standard input closes.
        fn waiting_child() -> std::process::Child {
            let system = std::env::var_os("SystemRoot").expect("SystemRoot is set on Windows");
            Command::new(
                std::path::PathBuf::from(system)
                    .join("System32")
                    .join("sort.exe"),
            )
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("start sort.exe")
        }

        fn permissions_at(regions: &[MemoryRegion], address: usize) -> Option<&str> {
            regions.iter().find_map(|region| {
                let range = region.identity.split_whitespace().next()?;
                let (start, end) = range.split_once('-')?;
                let start = usize::from_str_radix(start, 16).ok()?;
                let end = usize::from_str_radix(end, 16).ok()?;
                (start <= address && address < end).then_some(region.permissions.as_str())
            })
        }

        #[test]
        fn this_process_shows_code_as_executable_and_data_as_writable() {
            let regions = process_regions(std::process::id()).expect("own regions");
            let code_address =
                this_process_shows_code_as_executable_and_data_as_writable as fn() as usize;
            let code = permissions_at(&regions, code_address).expect("code is mapped");
            assert!(code.contains('x') && !code.contains('w'), "{code}");
            let data = Box::new([0_u8; 64]);
            let regions = process_regions(std::process::id()).expect("own regions");
            let heap_address = std::ptr::from_ref::<[u8; 64]>(&data) as usize;
            let heap = permissions_at(&regions, heap_address).expect("heap is mapped");
            assert!(heap.contains('w') && !heap.contains('x'), "{heap}");
        }

        #[test]
        fn a_live_child_shows_its_image_under_a_dos_path() {
            let mut child = waiting_child();
            let regions = process_regions(child.id()).expect("child regions");
            let image = regions
                .iter()
                .filter_map(|region| region.pathname.as_deref())
                .find(|path| path.to_ascii_lowercase().ends_with("\\sort.exe"))
                .expect("the image is mapped");
            assert!(image.as_bytes()[1] == b':', "{image}");
            assert!(peak_memory_bytes(child.id()).expect("child peak") > 0);

            drop(child.stdin.take());
            child.wait().expect("child exits");
        }

        #[test]
        fn an_exited_child_is_gone_while_the_parent_still_holds_its_handle() {
            let mut child = waiting_child();
            let pid = child.id();
            child.stdin.take().expect("stdin").flush().expect("flush");
            drop(child.stdin.take());
            child.wait().expect("child exits");

            assert_eq!(peak_memory_bytes(pid), Err(PlatformError::ProcessGone(pid)));
            assert_eq!(process_regions(pid), Err(PlatformError::ProcessGone(pid)));
        }

        #[test]
        fn a_process_that_does_not_exist_is_gone() {
            let pid = 0x7FFF_FFF0;
            assert_eq!(peak_memory_bytes(pid), Err(PlatformError::ProcessGone(pid)));
            assert_eq!(process_regions(pid), Err(PlatformError::ProcessGone(pid)));
        }
    }
}
