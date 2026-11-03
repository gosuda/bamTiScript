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
use crate::{MachineFacts, MemoryRegion, PlatformError, ThreadPlacement, UNAVAILABLE};

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
fn kind_name(kind: u32) -> &'static str {
    match kind {
        MEM_IMAGE => "image",
        MEM_MAPPED => "mapped",
        _ => "private",
    }
}

/// One drive letter and the NT device it names, such as `C:` and
/// `\Device\HarddiskVolume7`.
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
fn region_identity(start: u64, end: u64, allocation_base: u64, kind: u32, path: &str) -> String {
    format!(
        "{start:x}-{end:x} {allocation_base:x} {} {path}",
        kind_name(kind)
    )
}

/// Formats CPU numbers as a kernel CPU list, such as `0-3,5,7-9`.
fn cpu_list(cpus: impl IntoIterator<Item = u32>) -> String {
    let cpus: std::collections::BTreeSet<u32> = cpus.into_iter().collect();
    let mut parts = Vec::new();
    let mut remaining = cpus.into_iter().peekable();
    while let Some(first) = remaining.next() {
        let mut last = first;
        while last
            .checked_add(1)
            .is_some_and(|next| remaining.peek() == Some(&next))
        {
            last = remaining.next().unwrap_or(last);
        }
        parts.push(if first == last {
            first.to_string()
        } else {
            format!("{first}-{last}")
        });
    }
    parts.join(",")
}

/// The CPUs that `mask` sets in a processor group whose first CPU is numbered
/// `first_cpu` across the machine.
fn mask_cpus(first_cpu: u32, mask: u64) -> Vec<u32> {
    (0..u64::BITS)
        .filter(|bit| mask >> bit & 1 == 1)
        .map(|bit| first_cpu + bit)
        .collect()
}

/// `LOGICAL_PROCESSOR_RELATIONSHIP` of a physical core.
const RELATION_PROCESSOR_CORE: u32 = 0;
/// `LOGICAL_PROCESSOR_RELATIONSHIP` of a processor package, which is a socket.
const RELATION_PROCESSOR_PACKAGE: u32 = 3;

/// `LOGICAL_PROCESSOR_RELATIONSHIP` of a NUMA node.
const RELATION_NUMA_NODE: u32 = 1;

/// Splits the records that `GetLogicalProcessorInformationEx` returns into
/// `(relationship, whole record)`.
///
/// Each record starts with its relationship and its own size, both `u32`.
fn split_records(records: &[u8]) -> std::result::Result<Vec<(u32, &[u8])>, String> {
    let mut found = Vec::new();
    let mut offset = 0_usize;
    while offset < records.len() {
        let header = records
            .get(offset..offset + 8)
            .ok_or_else(|| format!("a record header is cut short at byte {offset}"))?;
        let relationship = u32::from_le_bytes([header[0], header[1], header[2], header[3]]);
        let size = u32::from_le_bytes([header[4], header[5], header[6], header[7]]);
        let size = usize::try_from(size).unwrap_or(usize::MAX);
        let end = offset
            .checked_add(size)
            .filter(|end| size >= 8 && *end <= records.len());
        let Some(end) = end else {
            return Err(format!("the record at byte {offset} has size {size}"));
        };
        found.push((relationship, &records[offset..end]));
        offset = end;
    }
    Ok(found)
}

/// Reads `(packages, cores per package)` from the records.
///
/// The cores must divide evenly across the packages, or the host describes a
/// machine this fact cannot state.
fn packages_and_cores(records: &[u8]) -> std::result::Result<(u32, u32), String> {
    let (mut packages, mut cores) = (0_u32, 0_u32);
    for (relationship, _) in split_records(records)? {
        match relationship {
            RELATION_PROCESSOR_PACKAGE => packages += 1,
            RELATION_PROCESSOR_CORE => cores += 1,
            _ => {}
        }
    }
    if packages == 0 || cores == 0 || cores % packages != 0 {
        return Err(format!(
            "{cores} physical cores do not divide across {packages} packages"
        ));
    }
    Ok((packages, cores / packages))
}

/// Reads the NUMA node numbers from the records, sorted. A node record holds its
/// number right after the header.
fn numa_nodes(records: &[u8]) -> std::result::Result<Vec<u32>, String> {
    let mut nodes = std::collections::BTreeSet::new();
    for (relationship, record) in split_records(records)? {
        if relationship != RELATION_NUMA_NODE {
            continue;
        }
        let number = record
            .get(8..12)
            .ok_or_else(|| "a NUMA node record is cut short".to_owned())?;
        nodes.insert(u32::from_le_bytes([
            number[0], number[1], number[2], number[3],
        ]));
    }
    if nodes.is_empty() {
        return Err("the host reports no NUMA node".to_owned());
    }
    Ok(nodes.into_iter().collect())
}

/// The Windows version as `major.minor.build.revision`, such as `10.0.26200.9711`.
fn version_text(major: u32, minor: u32, build: u32, revision: u32) -> String {
    format!("{major}.{minor}.{build}.{revision}")
}

/// The microcode revision as Linux prints it, such as `0x8701030`.
///
/// The `Update Revision` registry value is the revision register of the CPU. A
/// four-byte value holds the revision itself. Any other length is a form this
/// reader has not checked against a host, so it gives `None` rather than a guess.
fn microcode_text(value: &[u8]) -> Option<String> {
    let bytes: [u8; 4] = value.try_into().ok()?;
    Some(format!("0x{:x}", u32::from_le_bytes(bytes)))
}

/// Decodes a registry string: UTF-16 up to the first NUL, without the padding that
/// CPU vendors put around the name.
fn registry_text(bytes: &[u8]) -> String {
    let units: Vec<u16> = bytes
        .chunks_exact(2)
        .map(|pair| u16::from_le_bytes([pair[0], pair[1]]))
        .take_while(|unit| *unit != 0)
        .collect();
    String::from_utf16_lossy(&units).trim().to_owned()
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

    /// `RTL_OSVERSIONINFOW`.
    #[repr(C)]
    pub(super) struct OsVersionInfo {
        pub(super) size: u32,
        pub(super) major: u32,
        pub(super) minor: u32,
        pub(super) build: u32,
        pub(super) _platform: u32,
        pub(super) _service_pack: [u16; 128],
    }

    /// `GROUP_AFFINITY`.
    #[repr(C)]
    #[derive(Default)]
    pub(super) struct GroupAffinity {
        pub(super) mask: usize,
        pub(super) group: u16,
        pub(super) _reserved: [u16; 3],
    }

    /// `PERFORMANCE_INFORMATION`.
    #[repr(C)]
    #[derive(Default)]
    pub(super) struct PerformanceInformation {
        pub(super) cb: u32,
        pub(super) _commit_total: usize,
        pub(super) _commit_limit: usize,
        pub(super) _commit_peak: usize,
        pub(super) _physical_total: usize,
        pub(super) _physical_available: usize,
        pub(super) _system_cache: usize,
        pub(super) _kernel_total: usize,
        pub(super) _kernel_paged: usize,
        pub(super) _kernel_non_paged: usize,
        pub(super) page_size: usize,
        pub(super) _handle_count: u32,
        pub(super) _process_count: u32,
        pub(super) _thread_count: u32,
    }

    /// `ENUM_PAGE_FILE_INFORMATION`.
    #[repr(C)]
    pub(super) struct EnumPageFileInformation {
        pub(super) _size: u32,
        pub(super) _reserved: u32,
        pub(super) total_size: usize,
        pub(super) _total_in_use: usize,
        pub(super) _peak_usage: usize,
    }

    /// `PENUM_PAGE_FILE_CALLBACKW`.
    pub(super) type PageFileCallback =
        unsafe extern "system" fn(*mut c_void, *const EnumPageFileInformation, *const u16) -> i32;

    // Sizes measured from the SDK headers. A layout drift fails the build here,
    // not at the kernel boundary.
    #[cfg(target_pointer_width = "64")]
    const _: () = assert!(size_of::<MemoryBasicInformation>() == 48);
    #[cfg(target_pointer_width = "64")]
    const _: () = assert!(size_of::<ProcessMemoryCounters>() == 72);
    #[cfg(target_pointer_width = "64")]
    const _: () = assert!(size_of::<GroupAffinity>() == 16);
    #[cfg(target_pointer_width = "64")]
    const _: () = assert!(size_of::<PerformanceInformation>() == 104);
    #[cfg(target_pointer_width = "64")]
    const _: () = assert!(size_of::<EnumPageFileInformation>() == 32);
    #[cfg(target_pointer_width = "32")]
    const _: () = assert!(size_of::<MemoryBasicInformation>() == 28);
    #[cfg(target_pointer_width = "32")]
    const _: () = assert!(size_of::<ProcessMemoryCounters>() == 40);
    const _: () = assert!(size_of::<OsVersionInfo>() == 276);

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
        pub(super) fn GetLogicalDrives() -> u32;
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
        pub(super) fn GetCurrentThread() -> Handle;
        pub(super) fn GetThreadGroupAffinity(thread: Handle, affinity: *mut GroupAffinity) -> i32;
        pub(super) fn GetActiveProcessorCount(group: u16) -> u32;
        pub(super) fn GetLogicalProcessorInformationEx(
            relationship: u32,
            buffer: *mut c_void,
            length: *mut u32,
        ) -> i32;
        pub(super) fn K32GetPerformanceInfo(info: *mut PerformanceInformation, size: u32) -> i32;
        pub(super) fn K32EnumPageFilesW(callback: PageFileCallback, context: *mut c_void) -> i32;
    }

    #[link(name = "ntdll")]
    #[allow(unsafe_code)]
    unsafe extern "system" {
        pub(super) fn RtlGetVersion(info: *mut OsVersionInfo) -> i32;
    }

    #[link(name = "advapi32")]
    #[allow(unsafe_code)]
    unsafe extern "system" {
        pub(super) fn RegGetValueW(
            key: Handle,
            sub_key: *const u16,
            value: *const u16,
            flags: u32,
            kind: *mut u32,
            data: *mut c_void,
            size: *mut u32,
        ) -> i32;
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
const WAIT_SOURCE: &str = "WaitForSingleObject";
#[cfg(target_os = "windows")]
const REGION_SOURCE: &str = "VirtualQueryEx";
#[cfg(target_os = "windows")]
const MEMORY_SOURCE: &str = "GetProcessMemoryInfo";
#[cfg(target_os = "windows")]
const SAMPLER_SOURCE: &str = "peak memory sampler thread";

/// The host failed to answer a read.
#[cfg(target_os = "windows")]
fn read_failed(source: impl Into<String>, detail: impl Into<String>) -> PlatformError {
    PlatformError::Read {
        source: source.into(),
        detail: detail.into(),
    }
}

#[cfg(target_os = "windows")]
fn read_error(source: &str, error: &std::io::Error) -> PlatformError {
    read_failed(source, error.to_string())
}

/// The host answered, but not with data of the shape this reader expects.
#[cfg(target_os = "windows")]
fn malformed(source: impl Into<String>, detail: impl Into<String>) -> PlatformError {
    PlatformError::Malformed {
        source: source.into(),
        detail: detail.into(),
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
            _ => Err(read_error(WAIT_SOURCE, &std::io::Error::last_os_error())),
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

/// UTF-16 text with the NUL terminator that Win32 calls expect.
#[cfg(target_os = "windows")]
fn wide(text: &str) -> Vec<u16> {
    text.encode_utf16().chain(std::iter::once(0)).collect()
}

/// Maps each drive letter to its NT device, so a mapped file name can be shown as
/// the path a program opens. A letter with no device is left out.
///
/// Only the letters that `GetLogicalDrives` reports are asked. If it reports none,
/// every letter is asked, as a host that cannot list its drives may still map them.
#[cfg(target_os = "windows")]
fn dos_devices() -> Vec<DosDevice> {
    // SAFETY: `GetLogicalDrives` takes no arguments and returns a bit mask, with
    // bit 0 for `A:`.
    #[allow(unsafe_code)]
    let logical_drives = unsafe { ffi::GetLogicalDrives() };
    let mut buffer = [0_u16; 1024];
    let mut devices = Vec::new();
    for (bit, letter) in ('A'..='Z').enumerate() {
        if logical_drives != 0 && logical_drives & (1 << bit) == 0 {
            continue;
        }
        let drive = format!("{letter}:");
        let name = wide(&drive);
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
            .ok_or_else(|| malformed(REGION_SOURCE, "region walk does not advance"))?;
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
            .map_err(|error| read_error(SAMPLER_SOURCE, &error))?;
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
            .map_err(|_| read_failed(SAMPLER_SOURCE, "the sampler panicked"))?;
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

/// `RRF_RT_REG_SZ`, `RRF_RT_REG_BINARY` and `RRF_RT_REG_DWORD`: the registry value
/// types `RegGetValueW` may return.
#[cfg(target_os = "windows")]
const RRF_RT_REG_SZ: u32 = 0x0000_0002;
#[cfg(target_os = "windows")]
const RRF_RT_REG_BINARY: u32 = 0x0000_0008;
#[cfg(target_os = "windows")]
const RRF_RT_REG_DWORD: u32 = 0x0000_0010;
/// `ERROR_FILE_NOT_FOUND`: the registry has no such value.
#[cfg(target_os = "windows")]
const ERROR_FILE_NOT_FOUND: i32 = 2;
/// `ERROR_INSUFFICIENT_BUFFER`: the answer to a size query.
#[cfg(target_os = "windows")]
const ERROR_INSUFFICIENT_BUFFER: i32 = 122;
/// `RelationAll` and `ALL_PROCESSOR_GROUPS`.
#[cfg(target_os = "windows")]
const RELATION_ALL: u32 = 0xFFFF;
#[cfg(target_os = "windows")]
const ALL_PROCESSOR_GROUPS: u16 = 0xFFFF;

#[cfg(target_os = "windows")]
const PROCESSOR_KEY: &str = "HARDWARE\\DESCRIPTION\\System\\CentralProcessor\\0";
#[cfg(target_os = "windows")]
const VERSION_KEY: &str = "SOFTWARE\\Microsoft\\Windows NT\\CurrentVersion";

/// Reads one value of `HKEY_LOCAL_MACHINE`. `Ok(None)` means the value does not exist.
#[cfg(target_os = "windows")]
fn registry_value(
    sub_key: &str,
    value: &str,
    flags: u32,
    capacity: usize,
) -> Result<Option<Vec<u8>>> {
    let (sub_key_wide, value_wide) = (wide(sub_key), wide(value));
    let mut data = vec![0_u8; capacity];
    let mut size = u32::try_from(capacity).expect("the capacity fits a DWORD");
    // `HKEY_LOCAL_MACHINE` is `0x80000002` sign-extended to a pointer.
    let local_machine = 0x8000_0002_u32 as i32 as isize as ffi::Handle;
    // SAFETY: both names are NUL-terminated and live for the call. `data` is live
    // and writable for `size` bytes, and `size` is the length the host is told.
    #[allow(unsafe_code)]
    let status = unsafe {
        ffi::RegGetValueW(
            local_machine,
            sub_key_wide.as_ptr(),
            value_wide.as_ptr(),
            flags,
            std::ptr::null_mut(),
            data.as_mut_ptr().cast::<std::ffi::c_void>(),
            &raw mut size,
        )
    };
    match status {
        0 => {
            data.truncate(size as usize);
            Ok(Some(data))
        }
        ERROR_FILE_NOT_FOUND => Ok(None),
        _ => Err(read_error(
            &registry_source(sub_key, value),
            &std::io::Error::from_raw_os_error(status),
        )),
    }
}

/// Names a registry value in an error, the way `source` names the call elsewhere.
#[cfg(target_os = "windows")]
fn registry_source(sub_key: &str, value: &str) -> String {
    format!("RegGetValueW {sub_key}\\{value}")
}

/// A registry value that this host has to have.
#[cfg(target_os = "windows")]
fn required_registry_value(
    sub_key: &str,
    value: &str,
    flags: u32,
    capacity: usize,
) -> Result<Vec<u8>> {
    registry_value(sub_key, value, flags, capacity)?
        .ok_or_else(|| malformed(registry_source(sub_key, value), "the value does not exist"))
}

/// The Windows version `(major, minor, build)`. `RtlGetVersion` tells the real
/// version; the documented `GetVersionEx` reports what the manifest of the caller
/// asks for.
#[cfg(target_os = "windows")]
fn windows_version() -> Result<(u32, u32, u32)> {
    let mut info = ffi::OsVersionInfo {
        size: u32::try_from(size_of::<ffi::OsVersionInfo>()).expect("the record fits a DWORD"),
        major: 0,
        minor: 0,
        build: 0,
        _platform: 0,
        _service_pack: [0; 128],
    };
    // SAFETY: `info` is a live, writable `RTL_OSVERSIONINFOW` whose size field
    // holds its size, as the call requires.
    #[allow(unsafe_code)]
    let status = unsafe { ffi::RtlGetVersion(&raw mut info) };
    if status != 0 {
        return Err(read_failed(
            "RtlGetVersion",
            format!("NTSTATUS {status:#x}"),
        ));
    }
    Ok((info.major, info.minor, info.build))
}

#[cfg(target_os = "windows")]
const TOPOLOGY_SOURCE: &str = "GetLogicalProcessorInformationEx";

/// Reads the topology records of the host, for every relationship.
#[cfg(target_os = "windows")]
fn processor_records() -> Result<Vec<u8>> {
    const SOURCE: &str = TOPOLOGY_SOURCE;
    let mut length = 0_u32;
    // SAFETY: a null buffer with a zero length asks the host for the size it
    // needs; it writes only `length`.
    #[allow(unsafe_code)]
    let sized = unsafe {
        ffi::GetLogicalProcessorInformationEx(RELATION_ALL, std::ptr::null_mut(), &raw mut length)
    };
    let error = std::io::Error::last_os_error();
    if sized != 0 || error.raw_os_error() != Some(ERROR_INSUFFICIENT_BUFFER) {
        return Err(read_error(SOURCE, &error));
    }
    // The records hold pointer-sized fields, so the buffer is aligned for them.
    let mut buffer = vec![0_u64; (length as usize).div_ceil(size_of::<u64>())];
    // SAFETY: `buffer` is live and writable for at least `length` bytes, the size
    // the host asked for and is told again.
    #[allow(unsafe_code)]
    let read = unsafe {
        ffi::GetLogicalProcessorInformationEx(
            RELATION_ALL,
            buffer.as_mut_ptr().cast::<std::ffi::c_void>(),
            &raw mut length,
        )
    };
    if read == 0 {
        return Err(read_error(SOURCE, &std::io::Error::last_os_error()));
    }
    let mut records: Vec<u8> = buffer.iter().flat_map(|word| word.to_ne_bytes()).collect();
    records.truncate(length as usize);
    Ok(records)
}

/// Reads `(packages, cores per package)` from the host.
#[cfg(target_os = "windows")]
fn processor_topology() -> Result<(u32, u32)> {
    packages_and_cores(&processor_records()?).map_err(|detail| malformed(TOPOLOGY_SOURCE, detail))
}

/// The NUMA nodes of the host. A Windows process is not bound to a subset of
/// them, so these are the nodes its memory may come from.
#[cfg(target_os = "windows")]
pub(crate) fn numa_memory_nodes() -> Result<Vec<u32>> {
    numa_nodes(&processor_records()?).map_err(|detail| malformed(TOPOLOGY_SOURCE, detail))
}

#[cfg(target_os = "windows")]
pub(crate) fn machine_facts() -> Result<MachineFacts> {
    let (major, minor, build) = windows_version()?;
    let revision = u32::from_le_bytes(
        required_registry_value(VERSION_KEY, "UBR", RRF_RT_REG_DWORD, 4)?
            .try_into()
            .map_err(|_| {
                malformed(
                    registry_source(VERSION_KEY, "UBR"),
                    "the revision is not a DWORD",
                )
            })?,
    );
    let cpu_model = registry_text(&required_registry_value(
        PROCESSOR_KEY,
        "ProcessorNameString",
        RRF_RT_REG_SZ,
        1024,
    )?);
    let microcode = registry_value(PROCESSOR_KEY, "Update Revision", RRF_RT_REG_BINARY, 16)?
        .and_then(|value| microcode_text(&value))
        .unwrap_or_else(|| UNAVAILABLE.to_owned());
    let (sockets, cores_per_socket) = processor_topology()?;
    Ok(MachineFacts {
        kernel_release: format!("{major}.{minor}.{build}"),
        kernel_version: version_text(major, minor, build, revision),
        cpu_model,
        sockets,
        cores_per_socket,
        microcode,
        governor: UNAVAILABLE.to_owned(),
        swap_total_kib: swap_total_kib()?,
    })
}

/// The size of one page, from `GetPerformanceInfo`.
#[cfg(target_os = "windows")]
fn page_size_bytes() -> Result<u64> {
    let size =
        u32::try_from(size_of::<ffi::PerformanceInformation>()).expect("the record fits a DWORD");
    let mut info = ffi::PerformanceInformation {
        cb: size,
        ..ffi::PerformanceInformation::default()
    };
    // SAFETY: `info` is a live, writable `PERFORMANCE_INFORMATION` whose size is
    // both in `cb` and the length the host is told.
    #[allow(unsafe_code)]
    let status = unsafe { ffi::K32GetPerformanceInfo(&raw mut info, size) };
    if status == 0 {
        return Err(read_error(
            "GetPerformanceInfo",
            &std::io::Error::last_os_error(),
        ));
    }
    Ok(info.page_size as u64)
}

/// Adds the size of one page file, in pages, to the total behind `context`.
///
/// # Safety
/// `context` must point to the `u64` that `swap_total_kib` passed, and `info` to a
/// record the host owns for the length of the call. `K32EnumPageFilesW` upholds this.
#[cfg(target_os = "windows")]
#[allow(unsafe_code)]
unsafe extern "system" fn add_page_file(
    context: *mut std::ffi::c_void,
    info: *const ffi::EnumPageFileInformation,
    _name: *const u16,
) -> i32 {
    // SAFETY: the contract of this function; the total outlives the enumeration.
    #[allow(unsafe_code)]
    unsafe {
        *context.cast::<u64>() += (*info).total_size as u64;
    }
    1
}

#[cfg(target_os = "windows")]
pub(crate) fn swap_total_kib() -> Result<u64> {
    const SOURCE: &str = "EnumPageFiles";
    let page = page_size_bytes()?;
    let mut pages = 0_u64;
    // SAFETY: the callback and the total outlive the call, and the callback only
    // adds the sizes the host hands it to the total.
    #[allow(unsafe_code)]
    let status = unsafe { ffi::K32EnumPageFilesW(add_page_file, (&raw mut pages).cast()) };
    if status == 0 {
        return Err(read_error(SOURCE, &std::io::Error::last_os_error()));
    }
    pages
        .checked_mul(page)
        .map(|bytes| bytes / 1024)
        .ok_or_else(|| malformed(SOURCE, "the page file size overflows"))
}

/// How many logical CPUs are active in `group`, or in all groups.
#[cfg(target_os = "windows")]
fn active_processors(group: u16) -> Result<u32> {
    // SAFETY: `GetActiveProcessorCount` takes a group number and returns a count.
    #[allow(unsafe_code)]
    let count = unsafe { ffi::GetActiveProcessorCount(group) };
    if count == 0 {
        return Err(read_error(
            "GetActiveProcessorCount",
            &std::io::Error::last_os_error(),
        ));
    }
    Ok(count)
}

#[cfg(target_os = "windows")]
pub(crate) fn online_cpu_list() -> Result<String> {
    Ok(cpu_list(0..active_processors(ALL_PROCESSOR_GROUPS)?))
}

/// The CPUs the calling thread may run on, numbered across processor groups.
#[cfg(target_os = "windows")]
pub(crate) fn cpu_affinity() -> Result<String> {
    const SOURCE: &str = "GetThreadGroupAffinity";
    let mut affinity = ffi::GroupAffinity::default();
    // SAFETY: `GetCurrentThread` returns a pseudo-handle that needs no closing,
    // and `affinity` is a live, writable `GROUP_AFFINITY`.
    #[allow(unsafe_code)]
    let status = unsafe { ffi::GetThreadGroupAffinity(ffi::GetCurrentThread(), &raw mut affinity) };
    if status == 0 {
        return Err(read_error(SOURCE, &std::io::Error::last_os_error()));
    }
    let mut first_cpu = 0_u32;
    for group in 0..affinity.group {
        first_cpu += active_processors(group)?;
    }
    let cpus = mask_cpus(first_cpu, affinity.mask as u64);
    if cpus.is_empty() {
        return Err(malformed(SOURCE, "the thread may run on no CPU"));
    }
    Ok(cpu_list(cpus))
}

/// A Windows thread has a CPU affinity to read, and the host lists its NUMA nodes.
/// The memory policy is `numactl`'s notion and has no Windows reader, so it is
/// [`UNAVAILABLE`].
#[cfg(target_os = "windows")]
pub(crate) fn thread_placement() -> Result<ThreadPlacement> {
    Ok(ThreadPlacement {
        cpu_affinity: cpu_affinity()?,
        memory_policy: UNAVAILABLE.to_owned(),
        memory_nodes: cpu_list(numa_memory_nodes()?),
    })
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
    fn cpu_lists_join_runs_and_keep_gaps() {
        assert_eq!(cpu_list([0, 1, 2, 3]), "0-3");
        assert_eq!(cpu_list([5, 0, 1, 7, 8, 9, 3, 3]), "0-1,3,5,7-9");
        assert_eq!(cpu_list([4]), "4");
        assert_eq!(cpu_list(std::iter::empty()), "");
        // The last number of the range type does not overflow the run test.
        assert_eq!(
            cpu_list([u32::MAX - 1, u32::MAX]),
            format!("{}-{}", u32::MAX - 1, u32::MAX)
        );
    }

    #[test]
    fn a_group_mask_lists_its_cpus_across_groups() {
        assert_eq!(mask_cpus(0, 0b1011), vec![0, 1, 3]);
        assert_eq!(mask_cpus(64, 0b101), vec![64, 66]);
        assert_eq!(mask_cpus(0, u64::MAX).len(), 64);
        assert!(mask_cpus(0, 0).is_empty());
    }

    /// A record as `GetLogicalProcessorInformationEx` returns it: the relationship
    /// and the size, then the rest of the record.
    fn record(relationship: u32, size: u32) -> Vec<u8> {
        let mut bytes = Vec::new();
        bytes.extend(relationship.to_le_bytes());
        bytes.extend(size.to_le_bytes());
        bytes.resize(size as usize, 0);
        bytes
    }

    fn records(parts: &[(u32, u32)]) -> Vec<u8> {
        parts
            .iter()
            .flat_map(|(relationship, size)| record(*relationship, *size))
            .collect()
    }

    #[test]
    fn the_topology_counts_packages_and_cores_among_other_records() {
        let one = records(&[
            (RELATION_PROCESSOR_PACKAGE, 32),
            (RELATION_PROCESSOR_CORE, 48),
            (RELATION_PROCESSOR_CORE, 48),
            (2, 64),
            (4, 24),
            (RELATION_PROCESSOR_CORE, 48),
            (RELATION_PROCESSOR_CORE, 48),
        ]);
        assert_eq!(packages_and_cores(&one), Ok((1, 4)));

        let two = records(&[
            (RELATION_PROCESSOR_PACKAGE, 32),
            (RELATION_PROCESSOR_PACKAGE, 32),
            (RELATION_PROCESSOR_CORE, 48),
            (RELATION_PROCESSOR_CORE, 48),
            (RELATION_PROCESSOR_CORE, 48),
            (RELATION_PROCESSOR_CORE, 48),
        ]);
        assert_eq!(packages_and_cores(&two), Ok((2, 2)));
    }

    #[test]
    fn a_topology_that_cannot_be_stated_is_an_error() {
        let uneven = records(&[
            (RELATION_PROCESSOR_PACKAGE, 32),
            (RELATION_PROCESSOR_PACKAGE, 32),
            (RELATION_PROCESSOR_CORE, 48),
            (RELATION_PROCESSOR_CORE, 48),
            (RELATION_PROCESSOR_CORE, 48),
        ]);
        assert!(packages_and_cores(&uneven).is_err());
        assert!(packages_and_cores(&records(&[(RELATION_PROCESSOR_CORE, 48)])).is_err());
        assert!(packages_and_cores(&[]).is_err());
        // A header cut short, and a size past the end. A size below the header is
        // the subject of a test of its own.
        assert!(packages_and_cores(&[3, 0, 0, 0, 8]).is_err());
        assert!(packages_and_cores(&records(&[(RELATION_PROCESSOR_PACKAGE, 4)])).is_err());
        let mut overrun = record(RELATION_PROCESSOR_PACKAGE, 32);
        overrun.truncate(20);
        assert!(packages_and_cores(&overrun).is_err());
    }

    #[test]
    fn a_record_smaller_than_its_header_ends_the_walk_with_an_error() {
        // The header is whole and its size field is below the size of a header. A
        // size of zero would leave the offset where it is and the walk would not end.
        for size in [0_u32, 4, 7] {
            let mut header = Vec::new();
            header.extend(RELATION_PROCESSOR_PACKAGE.to_le_bytes());
            header.extend(size.to_le_bytes());
            let error = split_records(&header).unwrap_err();
            assert!(error.contains(&format!("has size {size}")), "{error}");
        }
    }

    #[test]
    fn the_numa_nodes_are_read_from_their_records_sorted_and_once() {
        let mut records = Vec::new();
        for node in [1_u32, 0, 1] {
            let mut record = record(RELATION_NUMA_NODE, 64);
            record[8..12].copy_from_slice(&node.to_le_bytes());
            records.extend(record);
        }
        records.extend(record(RELATION_PROCESSOR_CORE, 48));
        assert_eq!(numa_nodes(&records), Ok(vec![0, 1]));

        // No node record, and a node record without room for its number.
        assert!(numa_nodes(&record(RELATION_PROCESSOR_CORE, 48)).is_err());
        assert!(numa_nodes(&record(RELATION_NUMA_NODE, 8)).is_err());
        assert!(numa_nodes(&[]).is_err());
    }
    #[test]
    fn the_version_and_the_microcode_read_like_the_linux_facts() {
        assert_eq!(version_text(10, 0, 26200, 9711), "10.0.26200.9711");
        assert_eq!(
            microcode_text(&[0x30, 0x10, 0x70, 0x08]),
            Some("0x8701030".to_owned())
        );
        // A form this reader has not seen on a host is not decoded.
        assert_eq!(microcode_text(&[1, 2, 3, 4, 5, 6, 7, 8]), None);
        assert_eq!(microcode_text(&[]), None);
    }

    #[test]
    fn a_registry_string_loses_its_padding_and_its_terminator() {
        let bytes: Vec<u8> = "  AMD Ryzen 7   \0left over"
            .encode_utf16()
            .flat_map(u16::to_le_bytes)
            .collect();
        assert_eq!(registry_text(&bytes), "AMD Ryzen 7");
        assert_eq!(registry_text(&[]), "");
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

        fn parse_cpu_list(text: &str) -> std::collections::BTreeSet<u32> {
            text.split(',')
                .flat_map(|part| match part.split_once('-') {
                    Some((first, last)) => {
                        first.parse::<u32>().expect("a number")..=last.parse().expect("a number")
                    }
                    None => {
                        let cpu = part.parse::<u32>().expect("a number");
                        cpu..=cpu
                    }
                })
                .collect()
        }

        #[test]
        fn this_host_describes_itself() {
            let facts = machine_facts().expect("machine facts");

            let release: Vec<&str> = facts.kernel_release.split('.').collect();
            assert_eq!(release.len(), 3, "{}", facts.kernel_release);
            assert!(release.iter().all(|part| part.parse::<u32>().is_ok()));
            assert!(
                facts
                    .kernel_version
                    .starts_with(&format!("{}.", facts.kernel_release)),
                "{} / {}",
                facts.kernel_release,
                facts.kernel_version
            );
            assert!(!facts.cpu_model.is_empty());
            assert_eq!(facts.cpu_model, facts.cpu_model.trim());
            assert!(facts.sockets >= 1 && facts.cores_per_socket >= 1);
            assert!(facts.microcode == UNAVAILABLE || facts.microcode.starts_with("0x"));
            assert_eq!(facts.governor, UNAVAILABLE);
            assert_eq!(facts.swap_total_kib, swap_total_kib().expect("swap"));
        }

        #[test]
        fn the_online_list_covers_every_logical_cpu_and_the_thread_runs_inside_it() {
            let online = parse_cpu_list(&online_cpu_list().expect("online CPUs"));
            let logical = std::thread::available_parallelism().expect("parallelism");
            // Parallelism follows the affinity of the process, the list does not.
            assert!(online.len() >= logical.get(), "{online:?}");
            assert_eq!(online.first(), Some(&0));
            assert_eq!(
                online.last().copied(),
                Some(u32::try_from(online.len()).expect("a small count") - 1),
                "the online CPUs are numbered without gaps"
            );

            let affinity = parse_cpu_list(&cpu_affinity().expect("affinity"));
            assert!(
                !affinity.is_empty() && affinity.is_subset(&online),
                "{affinity:?}"
            );
            let nodes = numa_memory_nodes().expect("NUMA nodes");
            assert!(
                !nodes.is_empty() && nodes.windows(2).all(|pair| pair[0] < pair[1]),
                "{nodes:?}"
            );
            let placement = thread_placement().expect("placement");
            assert_eq!(parse_cpu_list(&placement.cpu_affinity), affinity);
            assert_eq!(placement.memory_policy, UNAVAILABLE);
            assert_eq!(placement.memory_nodes, cpu_list(nodes));
        }

        #[test]
        fn a_thread_pinned_to_one_cpu_reports_that_cpu() {
            // Rust's standard library has no affinity call, so pin through the host.
            #[link(name = "kernel32")]
            #[allow(unsafe_code)]
            unsafe extern "system" {
                fn SetThreadAffinityMask(thread: ffi::Handle, mask: usize) -> usize;
            }
            std::thread::spawn(|| {
                // SAFETY: the pseudo-handle of the calling thread needs no closing,
                // and the mask names one CPU of the first group.
                #[allow(unsafe_code)]
                let before = unsafe { SetThreadAffinityMask(ffi::GetCurrentThread(), 1) };
                assert_ne!(before, 0, "the host refused to pin the thread");
                assert_eq!(cpu_affinity().expect("affinity"), "0");
            })
            .join()
            .expect("the pinned thread");
        }

        #[test]
        fn a_process_that_does_not_exist_is_gone() {
            let pid = 0x7FFF_FFF0;
            assert_eq!(peak_memory_bytes(pid), Err(PlatformError::ProcessGone(pid)));
            assert_eq!(process_regions(pid), Err(PlatformError::ProcessGone(pid)));
        }
    }
}
