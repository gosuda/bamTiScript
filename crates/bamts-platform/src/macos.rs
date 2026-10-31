//! macOS backend: `sysctl` and `libproc`.

#[cfg(target_os = "macos")]
use std::mem::{MaybeUninit, size_of};
#[cfg(target_os = "macos")]
use std::process::Command;

use crate::PlatformError;
#[cfg(target_os = "macos")]
use crate::{MachineFacts, MemoryRegion, ThreadPlacement, UNAVAILABLE};

type Result<T> = std::result::Result<T, PlatformError>;

fn malformed(source: &str, detail: impl Into<String>) -> PlatformError {
    PlatformError::Malformed {
        source: source.to_owned(),
        detail: detail.into(),
    }
}

#[cfg(target_os = "macos")]
const SYSCTL: &str = "/usr/sbin/sysctl";

#[cfg(target_os = "macos")]
fn sysctl(key: &str) -> Result<String> {
    let source = format!("sysctl {key}");
    let output = Command::new(SYSCTL)
        .args(["-n", key])
        .output()
        .map_err(|error| PlatformError::Read {
            source: source.clone(),
            detail: error.to_string(),
        })?;
    if !output.status.success() {
        return Err(PlatformError::Read {
            source,
            detail: format!("exited with {}", output.status),
        });
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

#[cfg(target_os = "macos")]
fn sysctl_u32(key: &str) -> Result<u32> {
    sysctl(key)?
        .parse()
        .map_err(|_| malformed(&format!("sysctl {key}"), "not a number"))
}

/// Parses the swap total in KiB from `sysctl vm.swapusage`, such as
/// `total = 4096.00M  used = 3601.38M  free = 494.62M  (encrypted)`.
fn parse_swap_total_kib(text: &str) -> Result<u64> {
    const SOURCE: &str = "sysctl vm.swapusage";
    let token = text
        .split("total =")
        .nth(1)
        .and_then(|rest| rest.split_whitespace().next())
        .ok_or_else(|| malformed(SOURCE, "missing total"))?;
    let split = token.len().saturating_sub(1);
    if !token.is_char_boundary(split) {
        return Err(malformed(SOURCE, "total has no unit"));
    }
    let (number, unit) = token.split_at(split);
    let value: f64 = number
        .parse()
        .map_err(|_| malformed(SOURCE, "total is not a number"))?;
    if !value.is_finite() || value < 0.0 {
        return Err(malformed(SOURCE, "total is out of range"));
    }
    let kib_per_unit = match unit {
        "K" => 1.0,
        "M" => 1024.0,
        "G" => 1024.0 * 1024.0,
        _ => return Err(malformed(SOURCE, format!("unknown unit `{unit}`"))),
    };
    Ok((value * kib_per_unit).round() as u64)
}

#[cfg(target_os = "macos")]
pub(crate) fn machine_facts() -> Result<MachineFacts> {
    let packages = sysctl_u32("hw.packages")?;
    let physical = sysctl_u32("hw.physicalcpu")?;
    if packages == 0 || physical % packages != 0 {
        return Err(malformed(
            "sysctl hw.packages",
            format!("{physical} physical cores do not divide across {packages} packages"),
        ));
    }
    Ok(MachineFacts {
        kernel_release: sysctl("kern.osrelease")?,
        kernel_version: sysctl("kern.version")?,
        cpu_model: sysctl("machdep.cpu.brand_string")?,
        sockets: packages,
        cores_per_socket: physical / packages,
        microcode: UNAVAILABLE.to_owned(),
        governor: UNAVAILABLE.to_owned(),
        swap_total_kib: parse_swap_total_kib(&sysctl("vm.swapusage")?)?,
    })
}

#[cfg(target_os = "macos")]
pub(crate) fn thread_placement() -> Result<ThreadPlacement> {
    Ok(ThreadPlacement {
        cpu_affinity: UNAVAILABLE.to_owned(),
        memory_policy: UNAVAILABLE.to_owned(),
        memory_nodes: UNAVAILABLE.to_owned(),
    })
}

/// Formats Mach VM protection bits in the `rwxp` style of `/proc/<pid>/maps`.
fn permissions_string(protection: u32) -> String {
    const READ: u32 = 0x01;
    const WRITE: u32 = 0x02;
    const EXECUTE: u32 = 0x04;
    let flag = |bit: u32, letter: char| if protection & bit != 0 { letter } else { '-' };
    format!(
        "{}{}{}p",
        flag(READ, 'r'),
        flag(WRITE, 'w'),
        flag(EXECUTE, 'x')
    )
}

/// `PROC_PIDREGIONPATHINFO` in `<sys/proc_info.h>`.
#[cfg(target_os = "macos")]
const PROC_PIDREGIONPATHINFO: libc::c_int = 8;

/// Mirrors `struct proc_regioninfo` in `<sys/proc_info.h>`. The `libc` crate
/// declares `proc_pidinfo` and `vnode_info_path` but not the region structs.
#[cfg(target_os = "macos")]
#[repr(C)]
struct ProcRegionInfo {
    pri_protection: u32,
    pri_max_protection: u32,
    pri_inheritance: u32,
    pri_flags: u32,
    pri_offset: u64,
    pri_behavior: u32,
    pri_user_wired_count: u32,
    pri_user_tag: u32,
    pri_pages_resident: u32,
    pri_pages_shared_now_private: u32,
    pri_pages_swapped_out: u32,
    pri_pages_dirtied: u32,
    pri_ref_count: u32,
    pri_shadow_depth: u32,
    pri_share_mode: u32,
    pri_private_pages_resident: u32,
    pri_shared_pages_resident: u32,
    pri_obj_id: u32,
    pri_depth: u32,
    pri_address: u64,
    pri_size: u64,
}

/// Mirrors `struct proc_regionwithpathinfo` in `<sys/proc_info.h>`.
#[cfg(target_os = "macos")]
#[repr(C)]
struct ProcRegionWithPathInfo {
    prp_prinfo: ProcRegionInfo,
    prp_vip: libc::vnode_info_path,
}

// Sizes measured from the macOS SDK headers with `sizeof`. A layout drift
// fails the build here, not at the kernel boundary.
#[cfg(target_os = "macos")]
const _: () = assert!(size_of::<ProcRegionInfo>() == 96);
#[cfg(target_os = "macos")]
const _: () = assert!(size_of::<ProcRegionWithPathInfo>() == 1272);

#[cfg(target_os = "macos")]
const REGION_SOURCE: &str = "proc_pidinfo(PROC_PIDREGIONPATHINFO)";

/// Decodes `vip_path`, which `libc` declares as an array of arrays.
#[cfg(target_os = "macos")]
fn region_path(field: &[[libc::c_char; 32]; 32]) -> Result<String> {
    let field = field.as_flattened();
    let length = field
        .iter()
        .position(|byte| *byte == 0)
        .ok_or_else(|| malformed(REGION_SOURCE, "region path is not NUL-terminated"))?;
    let bytes: Vec<u8> = field[..length].iter().map(|byte| *byte as u8).collect();
    Ok(String::from_utf8_lossy(&bytes).into_owned())
}

#[cfg(target_os = "macos")]
fn region_from(info: &ProcRegionWithPathInfo) -> Result<MemoryRegion> {
    let path = region_path(&info.prp_vip.vip_path)?;
    let region = &info.prp_prinfo;
    let end = region
        .pri_address
        .checked_add(region.pri_size)
        .ok_or_else(|| malformed(REGION_SOURCE, "region end overflows the address space"))?;
    Ok(MemoryRegion {
        identity: format!(
            "{:x}-{end:x} {:x} {:x} {path}",
            region.pri_address, region.pri_offset, region.pri_obj_id
        ),
        permissions: permissions_string(region.pri_protection),
        pathname: (!path.is_empty()).then_some(path),
    })
}

/// One answer from the kernel, as a walk needs it.
#[cfg(target_os = "macos")]
struct WalkedRegion {
    start: u64,
    size: u64,
    region: MemoryRegion,
}

/// Reads the first region at or after `address`, or `None` when the kernel has
/// no region there.
#[cfg(target_os = "macos")]
fn region_at(raw_pid: libc::c_int, pid: u32, address: u64) -> Result<Option<WalkedRegion>> {
    const BUFFER_SIZE: libc::c_int = 1272;
    let mut info = MaybeUninit::<ProcRegionWithPathInfo>::zeroed();
    // SAFETY: `info` is a live, writable buffer of exactly `BUFFER_SIZE` bytes,
    // the size the kernel is told. `proc_pidinfo` writes at most that many
    // bytes and keeps no pointer to it after returning.
    #[allow(unsafe_code)]
    let written = unsafe {
        libc::proc_pidinfo(
            raw_pid,
            PROC_PIDREGIONPATHINFO,
            address,
            info.as_mut_ptr().cast::<libc::c_void>(),
            BUFFER_SIZE,
        )
    };
    if written != BUFFER_SIZE {
        let error = std::io::Error::last_os_error();
        return match (written, error.raw_os_error()) {
            (0, Some(libc::EINVAL)) => Ok(None),
            // Measured on macOS 27: never seen on a live process, in 363
            // verdicts taken while one execed.
            (0, Some(libc::ESRCH)) => Err(PlatformError::ProcessGone(pid)),
            (0, _) => Err(PlatformError::Read {
                source: REGION_SOURCE.to_owned(),
                detail: error.to_string(),
            }),
            _ => Err(malformed(
                REGION_SOURCE,
                format!("short read of {written} bytes, expected {BUFFER_SIZE}"),
            )),
        };
    }
    // SAFETY: the buffer was zeroed and the kernel then wrote it. Every field
    // is an integer or an array of integers, so any bytes are a valid value.
    #[allow(unsafe_code)]
    let info = unsafe { info.assume_init() };
    Ok(Some(WalkedRegion {
        start: info.prp_prinfo.pri_address,
        size: info.prp_prinfo.pri_size,
        region: region_from(&info)?,
    }))
}

/// Walks regions through `read_at` until it runs out.
///
/// Running out is ambiguous. It ends every walk, but a process also reads this
/// way for a moment when it exits or execs: the kernel takes the address space
/// away, and has no region to report until the process is gone or has its new
/// image. A process with an address space always has a region at or after
/// address 0, so reading there again tells a finished walk from a lost one.
///
/// A walk that crosses an exec between reads, without seeing that moment, lists
/// regions from both images.
#[cfg(target_os = "macos")]
fn walk_regions(
    pid: u32,
    mut read_at: impl FnMut(u64) -> Result<Option<WalkedRegion>>,
) -> Result<Vec<MemoryRegion>> {
    let mut regions = Vec::new();
    let mut address = 0_u64;
    while let Some(found) = read_at(address)? {
        let next = found
            .start
            .checked_add(found.size)
            .filter(|next| *next > address)
            .ok_or_else(|| malformed(REGION_SOURCE, "region walk does not advance"))?;
        regions.push(found.region);
        address = next;
    }
    if regions.is_empty() || read_at(0)?.is_none() {
        return Err(PlatformError::NoAddressSpace(pid));
    }
    Ok(regions)
}

#[cfg(target_os = "macos")]
pub(crate) fn process_regions(pid: u32) -> Result<Vec<MemoryRegion>> {
    let raw_pid = libc::c_int::try_from(pid).map_err(|_| {
        malformed(
            REGION_SOURCE,
            format!("pid {pid} does not fit the host pid type"),
        )
    })?;
    walk_regions(pid, |address| region_at(raw_pid, pid, address))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_swap_total_in_every_unit() {
        let text = "total = 4096.00M  used = 3601.38M  free = 494.62M  (encrypted)";
        assert_eq!(parse_swap_total_kib(text).unwrap(), 4_194_304);
        assert_eq!(
            parse_swap_total_kib("total = 0.00M  used = 0.00M").unwrap(),
            0
        );
        assert_eq!(
            parse_swap_total_kib("total = 1.50G  used = 0.00M").unwrap(),
            1_572_864
        );
        assert_eq!(
            parse_swap_total_kib("total = 512.00K  used = 0.00K").unwrap(),
            512
        );
    }

    #[test]
    fn rejects_malformed_swap_totals() {
        for text in [
            "",
            "nonsense",
            "total =",
            "total = 12",
            "total = 12X",
            "total = -3.00M",
            "total = abcM",
        ] {
            assert!(parse_swap_total_kib(text).is_err(), "{text:?}");
        }
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn reads_live_machine_facts() {
        let facts = machine_facts().unwrap();
        let release = Command::new("/usr/bin/uname").arg("-r").output().unwrap();
        assert_eq!(
            facts.kernel_release,
            String::from_utf8_lossy(&release.stdout).trim()
        );
        assert!(facts.kernel_version.starts_with("Darwin Kernel Version"));
        assert!(!facts.cpu_model.is_empty());
        assert!(facts.sockets >= 1);
        assert!(facts.cores_per_socket >= 1);
        assert_eq!(facts.microcode, UNAVAILABLE);
        assert_eq!(facts.governor, UNAVAILABLE);
    }

    #[test]
    fn formats_protection_bits_like_proc_maps() {
        assert_eq!(permissions_string(0), "---p");
        assert_eq!(permissions_string(1), "r--p");
        assert_eq!(permissions_string(3), "rw-p");
        assert_eq!(permissions_string(5), "r-xp");
        assert_eq!(permissions_string(7), "rwxp");
    }

    #[cfg(target_os = "macos")]
    fn region(start: u64, size: u64) -> Option<WalkedRegion> {
        Some(WalkedRegion {
            start,
            size,
            region: MemoryRegion {
                identity: String::new(),
                permissions: permissions_string(0),
                pathname: None,
            },
        })
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn reads_a_region_path_across_the_inner_arrays() {
        let path = format!("/{}", "a".repeat(63));
        let mut field = [[0; 32]; 32];
        for (slot, byte) in field.as_flattened_mut().iter_mut().zip(path.bytes()) {
            *slot = byte as libc::c_char;
        }
        assert_eq!(region_path(&field).unwrap(), path);
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn a_region_path_without_a_terminator_is_malformed() {
        let field = [[b'a' as libc::c_char; 32]; 32];
        assert!(matches!(
            region_path(&field),
            Err(PlatformError::Malformed { .. })
        ));
    }

    /// The anonymous-executable check tests only `is_none`, so a path that is
    /// not UTF-8 must stay a path.
    #[cfg(target_os = "macos")]
    #[test]
    fn a_region_path_that_is_not_utf8_is_still_a_path() {
        let mut field = [[0; 32]; 32];
        field[0][0] = 0xFF_u8 as libc::c_char;
        assert_eq!(region_path(&field).unwrap(), "\u{FFFD}");
    }

    /// Runs a walk against scripted kernel answers, and returns its result with
    /// the addresses it asked for.
    #[cfg(target_os = "macos")]
    fn scripted_walk(
        script: Vec<Result<Option<WalkedRegion>>>,
    ) -> (Result<Vec<MemoryRegion>>, Vec<u64>) {
        let mut asked = Vec::new();
        let mut answers = script.into_iter();
        let result = walk_regions(7, |address| {
            asked.push(address);
            answers.next().expect("the walk read past its script")
        });
        (result, asked)
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn a_finished_walk_confirms_the_process_still_has_regions() {
        let (result, asked) = scripted_walk(vec![
            Ok(region(0, 16)),
            Ok(region(16, 16)),
            Ok(None),
            Ok(region(0, 16)),
        ]);
        assert_eq!(result.unwrap().len(), 2);
        assert_eq!(asked, [0, 16, 32, 0]);
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn a_walk_cut_short_by_an_exit_is_not_a_complete_list() {
        // The address space went away after the first region. Measured on
        // macOS 27: a walk ended this way after 6 regions of a larger map.
        let (result, _) = scripted_walk(vec![Ok(region(0, 16)), Ok(None), Ok(None)]);
        assert_eq!(result, Err(PlatformError::NoAddressSpace(7)));
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn a_process_with_no_regions_has_no_address_space() {
        let (result, _) = scripted_walk(vec![Ok(None)]);
        assert_eq!(result, Err(PlatformError::NoAddressSpace(7)));
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn an_exit_during_the_confirming_read_is_process_gone() {
        let (result, _) = scripted_walk(vec![
            Ok(region(0, 16)),
            Ok(None),
            Err(PlatformError::ProcessGone(7)),
        ]);
        assert_eq!(result, Err(PlatformError::ProcessGone(7)));
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn a_walk_that_stops_advancing_is_malformed() {
        let (result, _) = scripted_walk(vec![Ok(region(16, 0)), Ok(region(16, 0))]);
        assert!(matches!(result, Err(PlatformError::Malformed { .. })));
    }

    /// The page tests map and unmap at the kernel's choice of address. Running
    /// one at a time keeps another test from being handed a freed address.
    #[cfg(target_os = "macos")]
    static PAGE_TESTS: std::sync::Mutex<()> = std::sync::Mutex::new(());

    #[cfg(target_os = "macos")]
    fn region_containing(regions: &[MemoryRegion], address: usize) -> Option<&MemoryRegion> {
        regions.iter().find(|region| {
            let range = region.identity.split_whitespace().next().unwrap();
            let (start, end) = range.split_once('-').unwrap();
            let start = usize::from_str_radix(start, 16).unwrap();
            let end = usize::from_str_radix(end, 16).unwrap();
            (start..end).contains(&address)
        })
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn reads_a_live_child_then_reports_it_gone() {
        use std::io::Write;
        use std::process::Stdio;
        let mut child = Command::new("/bin/cat")
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .spawn()
            .unwrap();
        let pid = child.id();
        let regions = process_regions(pid).unwrap();
        assert!(
            regions
                .iter()
                .any(|r| r.permissions == "r-xp" && r.pathname.as_deref() == Some("/bin/cat")),
            "{regions:#?}"
        );
        assert!(regions.iter().all(|r| !r.permissions.contains("rwx")));
        assert!(
            regions
                .iter()
                .all(|r| !(r.permissions.contains('x') && r.pathname.is_none()))
        );
        child.stdin.take().unwrap().flush().unwrap();
        child.wait().unwrap();
        assert_eq!(process_regions(pid), Err(PlatformError::ProcessGone(pid)));
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn rejects_a_pid_that_does_not_fit() {
        assert!(matches!(
            process_regions(u32::MAX),
            Err(PlatformError::Malformed { .. })
        ));
    }

    #[cfg(target_os = "macos")]
    #[allow(unsafe_code)]
    #[test]
    fn sees_an_anonymous_executable_page_come_and_go() {
        let _serial = PAGE_TESTS
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        // SAFETY: one anonymous page is mapped, protected, inspected by address
        // only, and unmapped. Nothing in it is executed.
        unsafe {
            let size = libc::sysconf(libc::_SC_PAGESIZE) as usize;
            let page = libc::mmap(
                std::ptr::null_mut(),
                size,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_ANON | libc::MAP_PRIVATE,
                -1,
                0,
            );
            assert_ne!(page, libc::MAP_FAILED);
            assert_eq!(
                libc::mprotect(page, size, libc::PROT_READ | libc::PROT_EXEC),
                0
            );
            let regions = process_regions(std::process::id()).unwrap();
            let region = region_containing(&regions, page as usize).unwrap();
            assert_eq!(region.permissions, "r-xp");
            assert_eq!(region.pathname, None);
            assert_eq!(libc::munmap(page, size), 0);
            let regions = process_regions(std::process::id()).unwrap();
            assert!(region_containing(&regions, page as usize).is_none());
        }
    }

    #[cfg(target_os = "macos")]
    #[allow(unsafe_code)]
    #[test]
    fn sees_a_map_jit_page_as_read_write_execute() {
        let _serial = PAGE_TESTS
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        // SAFETY: as above. `MAP_JIT` is what makes the OS allow this mapping.
        unsafe {
            let size = libc::sysconf(libc::_SC_PAGESIZE) as usize;
            let page = libc::mmap(
                std::ptr::null_mut(),
                size,
                libc::PROT_READ | libc::PROT_WRITE | libc::PROT_EXEC,
                libc::MAP_ANON | libc::MAP_PRIVATE | libc::MAP_JIT,
                -1,
                0,
            );
            assert_ne!(page, libc::MAP_FAILED);
            let regions = process_regions(std::process::id()).unwrap();
            assert_eq!(
                region_containing(&regions, page as usize)
                    .unwrap()
                    .permissions,
                "rwxp"
            );
            assert_eq!(libc::munmap(page, size), 0);
        }
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn thread_placement_is_unavailable_on_macos() {
        let placement = thread_placement().unwrap();
        assert_eq!(placement.cpu_affinity, UNAVAILABLE);
        assert_eq!(placement.memory_policy, UNAVAILABLE);
        assert_eq!(placement.memory_nodes, UNAVAILABLE);
    }
}
