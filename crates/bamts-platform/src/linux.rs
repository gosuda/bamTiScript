//! Linux backend: `/proc`, `/sys`, and `get_mempolicy(2)`.

use std::collections::{BTreeMap, BTreeSet};
#[cfg(target_os = "linux")]
use std::fs;

#[cfg(target_os = "linux")]
use crate::{MachineFacts, ThreadPlacement};
use crate::{MemoryRegion, PlatformError, UNAVAILABLE};

type Result<T> = std::result::Result<T, PlatformError>;

fn malformed(source: &str, detail: impl Into<String>) -> PlatformError {
    PlatformError::Malformed {
        source: source.to_owned(),
        detail: detail.into(),
    }
}

#[cfg(target_os = "linux")]
fn read_evidence(path: &str) -> Result<String> {
    fs::read_to_string(path).map_err(|error| PlatformError::Read {
        source: path.to_owned(),
        detail: error.to_string(),
    })
}

/// Parses the kernel release and build-version tail from `/proc/version`.
fn parse_proc_version(content: &str) -> Result<(String, String)> {
    let mut tokens = content.split_whitespace();
    // Expected: "Linux version <release> ..."
    let release = tokens
        .nth(2)
        .ok_or_else(|| malformed("/proc/version", "missing kernel release"))?
        .to_owned();
    let version = content
        .find('#')
        .map(|start| content[start..].trim_end().to_owned())
        .unwrap_or_default();
    Ok((release, version))
}

/// Parses `(cpu_model, sockets, cores_per_socket, microcode)` from cpuinfo.
fn parse_proc_cpuinfo(content: &str) -> Result<(String, u32, u32, String)> {
    let mut model = None;
    let mut microcode = None;
    let mut cores_per_socket = None;
    let mut sockets = BTreeSet::new();

    for line in content.lines() {
        let Some((key, value)) = line.split_once(':') else {
            continue;
        };
        let (key, value) = (key.trim(), value.trim());
        match key {
            "model name" if model.is_none() => model = Some(value.to_owned()),
            "microcode" if microcode.is_none() => microcode = Some(value.to_owned()),
            "cpu cores" if cores_per_socket.is_none() => cores_per_socket = value.parse().ok(),
            "physical id" => {
                sockets.insert(value.to_owned());
            }
            _ => {}
        }
    }

    let model = model.ok_or_else(|| malformed("/proc/cpuinfo", "missing model name"))?;
    let microcode = microcode.ok_or_else(|| malformed("/proc/cpuinfo", "missing microcode"))?;
    let cores_per_socket =
        cores_per_socket.ok_or_else(|| malformed("/proc/cpuinfo", "missing cpu cores"))?;
    let socket_count = u32::try_from(sockets.len())
        .map_err(|_| malformed("/proc/cpuinfo", "socket count overflow"))?
        .max(1);
    Ok((model, socket_count, cores_per_socket, microcode))
}

/// Parses `/proc/<pid>/maps` into regions.
fn parse_process_maps(text: &str) -> Result<Vec<MemoryRegion>> {
    const SOURCE: &str = "/proc/<pid>/maps";
    text.lines()
        .map(|line| {
            let mut fields = line.split_whitespace();
            let range = fields
                .next()
                .ok_or_else(|| malformed(SOURCE, "mapping lacks range"))?;
            let permissions = fields
                .next()
                .ok_or_else(|| malformed(SOURCE, "mapping lacks permissions"))?
                .to_owned();
            let offset = fields
                .next()
                .ok_or_else(|| malformed(SOURCE, "mapping lacks offset"))?;
            let device = fields
                .next()
                .ok_or_else(|| malformed(SOURCE, "mapping lacks device"))?;
            let inode = fields
                .next()
                .ok_or_else(|| malformed(SOURCE, "mapping lacks inode"))?;
            let pathname = fields.next().map(str::to_owned);
            Ok(MemoryRegion {
                identity: format!(
                    "{range} {offset} {device} {inode} {}",
                    pathname.as_deref().unwrap_or("")
                ),
                permissions,
                pathname,
            })
        })
        .collect()
}

/// Classifies a failed read of a `/proc/<pid>` file. A process reaped before
/// `open` is `ENOENT`, and one reaped between `open` and `read` is `ESRCH`.
fn process_read_error(pid: u32, source: String, error: &std::io::Error) -> PlatformError {
    if error.kind() == std::io::ErrorKind::NotFound || error.raw_os_error() == Some(libc::ESRCH) {
        PlatformError::ProcessGone(pid)
    } else {
        PlatformError::Read {
            source,
            detail: error.to_string(),
        }
    }
}

/// A process with an empty map has released its address space.
fn regions_from_maps(pid: u32, text: &str) -> Result<Vec<MemoryRegion>> {
    let regions = parse_process_maps(text)?;
    if regions.is_empty() {
        return Err(PlatformError::NoAddressSpace(pid));
    }
    Ok(regions)
}

#[cfg(target_os = "linux")]
pub(crate) fn process_regions(pid: u32) -> Result<Vec<MemoryRegion>> {
    let path = format!("/proc/{pid}/maps");
    match fs::read_to_string(&path) {
        Ok(text) => regions_from_maps(pid, &text),
        Err(error) => Err(process_read_error(pid, path, &error)),
    }
}

/// Parses the peak resident set (`VmHWM`) in bytes from a
/// `/proc/<pid>/status` document.
fn parse_peak_memory_bytes(status: &str) -> Result<u64> {
    const SOURCE: &str = "/proc/<pid>/status";
    let rest = status
        .lines()
        .find_map(|line| line.strip_prefix("VmHWM:"))
        .ok_or_else(|| malformed(SOURCE, "VmHWM field not found"))?;
    let kib: u64 = rest
        .split_whitespace()
        .next()
        .ok_or_else(|| malformed(SOURCE, "VmHWM has no value"))?
        .parse()
        .map_err(|error| malformed(SOURCE, format!("VmHWM is not a number: {error}")))?;
    kib.checked_mul(1024)
        .ok_or_else(|| malformed(SOURCE, "VmHWM overflows"))
}

/// The kernel prints `VmHWM` only for a task that holds an address space. A
/// process drops it early in exit, long before it becomes a zombie, and its
/// state can still read as running. So a status with a `State:` line and no
/// `VmHWM` line is a process that is exiting.
fn has_left_its_address_space(status: &str) -> bool {
    let has_field = |name| status.lines().any(|line| line.starts_with(name));
    has_field("State:") && !has_field("VmHWM:")
}

fn peak_from_status(pid: u32, status: &str) -> Result<u64> {
    if has_left_its_address_space(status) {
        return Err(PlatformError::ProcessGone(pid));
    }
    parse_peak_memory_bytes(status)
}

#[cfg(target_os = "linux")]
pub(crate) fn peak_memory_bytes(pid: u32) -> Result<u64> {
    let path = format!("/proc/{pid}/status");
    let status =
        fs::read_to_string(&path).map_err(|error| process_read_error(pid, path, &error))?;
    peak_from_status(pid, &status)
}

/// Resets the kernel's high-water mark when it starts, so the final read is
/// the peak since then.
#[cfg(target_os = "linux")]
pub(crate) struct Window;

#[cfg(target_os = "linux")]
impl Window {
    pub(crate) fn start() -> Result<Self> {
        const SOURCE: &str = "/proc/self/clear_refs";
        fs::write(SOURCE, "5").map_err(|error| PlatformError::Read {
            source: SOURCE.to_owned(),
            detail: error.to_string(),
        })?;
        Ok(Self)
    }

    pub(crate) fn finish(self) -> Result<u64> {
        peak_memory_bytes(std::process::id())
    }
}

/// Builds the CPU identity from cpuinfo. A `model name` line selects the
/// original parser, so x86 hosts read exactly what they always have. A host
/// without it but with ARM identification fields takes its model from those
/// fields and its socket and core counts from the sysfs topology.
fn cpu_identity(
    content: &str,
    topology: impl FnOnce() -> Result<Vec<(i64, i64)>>,
) -> Result<(String, u32, u32, String)> {
    let has_model_name = content
        .lines()
        .filter_map(|line| line.split_once(':'))
        .any(|(key, _)| key.trim() == "model name");
    if !has_model_name && let Some(model) = parse_arm_cpu_model(content) {
        let (sockets, cores_per_socket) = sockets_and_cores(&topology()?)?;
        return Ok((model, sockets, cores_per_socket, UNAVAILABLE.to_owned()));
    }
    parse_proc_cpuinfo(content)
}

/// Names an ARM CPU from the identification fields cpuinfo does print.
fn parse_arm_cpu_model(content: &str) -> Option<String> {
    let mut implementer = None;
    let mut part = None;
    for (key, value) in content.lines().filter_map(|line| line.split_once(':')) {
        let (key, value) = (key.trim(), value.trim());
        match key {
            "CPU implementer" if implementer.is_none() => implementer = Some(value),
            "CPU part" if part.is_none() => part = Some(value),
            _ => {}
        }
    }
    Some(format!("arm64 implementer={} part={}", implementer?, part?))
}

/// Counts sockets and cores per socket from one `(package id, core id)` pair
/// per online CPU.
fn sockets_and_cores(cpus: &[(i64, i64)]) -> Result<(u32, u32)> {
    const SOURCE: &str = "/sys/devices/system/cpu topology";
    let mut packages: BTreeMap<i64, BTreeSet<i64>> = BTreeMap::new();
    for &(package, core) in cpus {
        if package < 0 {
            return Err(malformed(SOURCE, format!("negative package id {package}")));
        }
        packages.entry(package).or_default().insert(core);
    }
    let mut counts = packages.values().map(BTreeSet::len);
    let first = counts.next().ok_or_else(|| malformed(SOURCE, "no CPUs"))?;
    if counts.any(|count| count != first) {
        return Err(malformed(SOURCE, "packages have different core counts"));
    }
    let sockets =
        u32::try_from(packages.len()).map_err(|_| malformed(SOURCE, "socket count overflow"))?;
    let cores = u32::try_from(first).map_err(|_| malformed(SOURCE, "core count overflow"))?;
    Ok((sockets, cores))
}

#[cfg(target_os = "linux")]
fn read_topology() -> Result<Vec<(i64, i64)>> {
    const ROOT: &str = "/sys/devices/system/cpu";
    let read_error = |error: std::io::Error| PlatformError::Read {
        source: ROOT.to_owned(),
        detail: error.to_string(),
    };
    let mut cpus = Vec::new();
    for entry in fs::read_dir(ROOT).map_err(read_error)? {
        let entry = entry.map_err(read_error)?;
        let name = entry.file_name();
        let name = name.to_string_lossy();
        let Some(number) = name.strip_prefix("cpu") else {
            continue;
        };
        if number.is_empty() || !number.bytes().all(|byte| byte.is_ascii_digit()) {
            continue;
        }
        let topology = entry.path().join("topology");
        // An offline CPU has no topology directory.
        let (Ok(package), Ok(core)) = (
            fs::read_to_string(topology.join("physical_package_id")),
            fs::read_to_string(topology.join("core_id")),
        ) else {
            continue;
        };
        let parse = |text: &str, field: &str| {
            text.trim()
                .parse::<i64>()
                .map_err(|_| malformed(ROOT, format!("{field} is not a number")))
        };
        cpus.push((
            parse(&package, "physical_package_id")?,
            parse(&core, "core_id")?,
        ));
    }
    Ok(cpus)
}

/// Parses `SwapTotal` (KiB) from `/proc/meminfo`.
fn parse_proc_meminfo_swap(content: &str) -> Result<u64> {
    for line in content.lines() {
        if let Some(rest) = line.strip_prefix("SwapTotal:") {
            let value = rest
                .split_whitespace()
                .next()
                .ok_or_else(|| malformed("/proc/meminfo", "SwapTotal malformed"))?;
            return value
                .parse()
                .map_err(|_| malformed("/proc/meminfo", "SwapTotal not a number"));
        }
    }
    Err(malformed("/proc/meminfo", "missing SwapTotal"))
}

fn parse_cpu_affinity(status: &str) -> Result<String> {
    status
        .lines()
        .find_map(|line| line.strip_prefix("Cpus_allowed_list:"))
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(str::to_owned)
        .ok_or_else(|| malformed("/proc/thread-self/status", "missing Cpus_allowed_list"))
}

#[cfg(target_os = "linux")]
const NUMA_MASK_BITS: usize = 1024;
#[cfg(target_os = "linux")]
const NUMA_MASK_WORDS: usize = NUMA_MASK_BITS.div_ceil(libc::c_ulong::BITS as usize);

#[cfg(target_os = "linux")]
fn format_memory_nodes(mask: &[libc::c_ulong]) -> String {
    let mut ranges = Vec::new();
    let mut start = None;
    for node in 0..NUMA_MASK_BITS {
        let word = node / libc::c_ulong::BITS as usize;
        let bit = node % libc::c_ulong::BITS as usize;
        let is_set = mask[word] & (1 as libc::c_ulong) << bit != 0;
        if is_set && start.is_none() {
            start = Some(node);
        } else if !is_set && start.is_some() {
            let first = start.take().expect("checked above");
            let last = node - 1;
            ranges.push(if first == last {
                first.to_string()
            } else {
                format!("{first}-{last}")
            });
        }
    }
    if let Some(first) = start {
        let last = NUMA_MASK_BITS - 1;
        ranges.push(if first == last {
            first.to_string()
        } else {
            format!("{first}-{last}")
        });
    }
    ranges.join(",")
}

#[cfg(target_os = "linux")]
fn decode_memory_policy(mode: libc::c_int, mask: &[libc::c_ulong]) -> Result<(String, String)> {
    let mode_flags = libc::MPOL_F_STATIC_NODES | libc::MPOL_F_RELATIVE_NODES;
    let base_mode = mode & !mode_flags;
    let mut policy = match base_mode {
        libc::MPOL_DEFAULT => "default".to_owned(),
        libc::MPOL_PREFERRED => "preferred".to_owned(),
        libc::MPOL_BIND => "bind".to_owned(),
        libc::MPOL_INTERLEAVE => "interleave".to_owned(),
        libc::MPOL_LOCAL => "local".to_owned(),
        _ => {
            return Err(malformed(
                "get_mempolicy(2)",
                format!("returned unsupported mode {mode}"),
            ));
        }
    };
    if mode & libc::MPOL_F_STATIC_NODES != 0 {
        policy.push_str("|static");
    }
    if mode & libc::MPOL_F_RELATIVE_NODES != 0 {
        policy.push_str("|relative");
    }
    Ok((policy, format_memory_nodes(mask)))
}

#[cfg(target_os = "linux")]
#[allow(unsafe_code)]
fn read_memory_policy() -> Result<(String, String)> {
    let mut mode = 0 as libc::c_int;
    let mut mask = [0 as libc::c_ulong; NUMA_MASK_WORDS];
    // SAFETY: get_mempolicy writes one c_int and at most NUMA_MASK_BITS into
    // the two live buffers. flags=0 and addr=NULL request this thread's
    // default policy, as required by get_mempolicy(2).
    let status = unsafe {
        libc::syscall(
            libc::SYS_get_mempolicy,
            std::ptr::addr_of_mut!(mode),
            mask.as_mut_ptr(),
            NUMA_MASK_BITS as libc::c_ulong,
            std::ptr::null::<libc::c_void>(),
            0 as libc::c_ulong,
        )
    };
    if status != 0 {
        return Err(PlatformError::Read {
            source: "get_mempolicy(2)".to_owned(),
            detail: std::io::Error::last_os_error().to_string(),
        });
    }
    decode_memory_policy(mode, &mask)
}

#[cfg(target_os = "linux")]
pub(crate) fn machine_facts() -> Result<MachineFacts> {
    let version = read_evidence("/proc/version")?;
    let cpuinfo = read_evidence("/proc/cpuinfo")?;
    let meminfo = read_evidence("/proc/meminfo")?;
    let governor = read_evidence("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor")
        .map(|text| text.trim().to_owned())
        .unwrap_or_else(|_| "unknown".to_owned());

    let (kernel_release, kernel_version) = parse_proc_version(&version)?;
    let (cpu_model, sockets, cores_per_socket, microcode) = cpu_identity(&cpuinfo, read_topology)?;
    let swap_total_kib = parse_proc_meminfo_swap(&meminfo)?;

    Ok(MachineFacts {
        kernel_release,
        kernel_version,
        cpu_model,
        sockets,
        cores_per_socket,
        microcode,
        governor,
        swap_total_kib,
    })
}

#[cfg(target_os = "linux")]
pub(crate) fn thread_placement() -> Result<ThreadPlacement> {
    let status = read_evidence("/proc/thread-self/status")?;
    let cpu_affinity = parse_cpu_affinity(&status)?;
    let (memory_policy, memory_nodes) = read_memory_policy()?;
    Ok(ThreadPlacement {
        cpu_affinity,
        memory_policy,
        memory_nodes,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_proc_version_extracts_release_and_tail() {
        let content = "Linux version 7.0.0-28-generic (buildd@lcy02) (gcc 15) #28-Ubuntu SMP PREEMPT_DYNAMIC Sun Jun 21 01:01:36 UTC 2026\n";
        let (release, version) = parse_proc_version(content).unwrap();
        assert_eq!(release, "7.0.0-28-generic");
        assert!(version.starts_with("#28-Ubuntu SMP PREEMPT_DYNAMIC"));
    }

    #[test]
    fn parse_proc_cpuinfo_counts_sockets_and_cores() {
        let content = "model name\t: Intel(R) Xeon(R) Gold 6138 CPU @ 2.00GHz\nmicrocode\t: 0x2007006\ncpu cores\t: 20\nphysical id\t: 0\n\nphysical id\t: 1\ncpu cores\t: 20\n";
        let (model, sockets, cores, micro) = parse_proc_cpuinfo(content).unwrap();
        assert_eq!(model, "Intel(R) Xeon(R) Gold 6138 CPU @ 2.00GHz");
        assert_eq!(sockets, 2);
        assert_eq!(cores, 20);
        assert_eq!(micro, "0x2007006");
    }

    const ARM_CPUINFO: &str = "processor\t: 0\nBogoMIPS\t: 48.00\nFeatures\t: fp asimd\nCPU implementer\t: 0x61\nCPU architecture: 8\nCPU variant\t: 0x0\nCPU part\t: 0x000\nCPU revision\t: 0\n";
    const X86_CPUINFO: &str = "model name\t: Intel(R) Xeon(R) Gold 6138 CPU @ 2.00GHz\nmicrocode\t: 0x2007006\ncpu cores\t: 20\nphysical id\t: 0\n\nphysical id\t: 1\ncpu cores\t: 20\n";

    #[test]
    fn arm_cpu_model_comes_from_identification_fields() {
        assert_eq!(
            parse_arm_cpu_model(ARM_CPUINFO).as_deref(),
            Some("arm64 implementer=0x61 part=0x000")
        );
        assert_eq!(parse_arm_cpu_model("CPU implementer\t: 0x61\n"), None);
        assert_eq!(parse_arm_cpu_model(X86_CPUINFO), None);
    }

    #[test]
    fn cpu_identity_keeps_the_x86_path_and_its_errors() {
        let unreached = || unreachable!("an x86 host never reads the topology");
        assert_eq!(
            cpu_identity(X86_CPUINFO, unreached).unwrap(),
            parse_proc_cpuinfo(X86_CPUINFO).unwrap()
        );
        let no_microcode = "model name\t: Intel(R) Xeon(R)\ncpu cores\t: 4\n";
        assert!(
            cpu_identity(no_microcode, unreached)
                .unwrap_err()
                .to_string()
                .contains("missing microcode")
        );
        assert!(
            cpu_identity("", unreached)
                .unwrap_err()
                .to_string()
                .contains("missing model name")
        );
    }

    #[test]
    fn cpu_identity_reads_the_topology_for_arm() {
        let cpus = (0..8).map(|core| (0, core)).collect::<Vec<_>>();
        assert_eq!(
            cpu_identity(ARM_CPUINFO, || Ok(cpus)).unwrap(),
            (
                "arm64 implementer=0x61 part=0x000".to_owned(),
                1,
                8,
                UNAVAILABLE.to_owned()
            )
        );
        assert!(cpu_identity(ARM_CPUINFO, || Ok(Vec::new())).is_err());
    }

    #[test]
    fn counts_sockets_and_cores_per_socket() {
        assert_eq!(
            sockets_and_cores(&[(0, 0), (0, 1), (0, 2), (0, 3)]).unwrap(),
            (1, 4)
        );
        assert_eq!(
            sockets_and_cores(&[(0, 0), (0, 1), (1, 0), (1, 1)]).unwrap(),
            (2, 2)
        );
        // SMT siblings share a core id and must not be counted twice.
        assert_eq!(
            sockets_and_cores(&[(0, 0), (0, 0), (0, 1), (0, 1)]).unwrap(),
            (1, 2)
        );
        for bad in [
            &[][..],
            &[(0, 0), (0, 1), (1, 0)][..],
            &[(-1, 0), (-1, 1)][..],
        ] {
            assert!(sockets_and_cores(bad).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn parses_process_maps_into_regions() {
        let text = "55d0c8a00000-55d0c8a21000 r-xp 00000000 fd:01 1048 /usr/bin/cat\n7f1c2a000000-7f1c2a021000 rwxp 00000000 00:00 0\n";
        let regions = parse_process_maps(text).unwrap();
        assert_eq!(regions.len(), 2);
        assert_eq!(
            regions[0],
            MemoryRegion {
                identity: "55d0c8a00000-55d0c8a21000 00000000 fd:01 1048 /usr/bin/cat".to_owned(),
                permissions: "r-xp".to_owned(),
                pathname: Some("/usr/bin/cat".to_owned()),
            }
        );
        assert_eq!(regions[1].permissions, "rwxp");
        assert_eq!(regions[1].pathname, None);
        assert!(parse_process_maps("55d0c8a00000-55d0c8a21000\n").is_err());
    }

    #[test]
    fn an_empty_map_is_no_address_space() {
        assert_eq!(
            regions_from_maps(7, ""),
            Err(PlatformError::NoAddressSpace(7))
        );
    }

    #[test]
    fn a_process_reaped_around_a_read_is_gone() {
        for errno in [libc::ENOENT, libc::ESRCH] {
            let error = std::io::Error::from_raw_os_error(errno);
            assert_eq!(
                process_read_error(7, "/proc/7/maps".to_owned(), &error),
                PlatformError::ProcessGone(7)
            );
        }
        let denied = std::io::Error::from_raw_os_error(libc::EACCES);
        assert!(matches!(
            process_read_error(7, "/proc/7/maps".to_owned(), &denied),
            PlatformError::Read { .. }
        ));
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn reads_this_process_regions() {
        let regions = process_regions(std::process::id()).unwrap();
        assert!(
            regions
                .iter()
                .any(|region| region.permissions.contains('x') && region.pathname.is_some())
        );
        assert!(
            regions
                .iter()
                .all(|region| !region.permissions.contains("rwx"))
        );
    }

    #[test]
    fn peak_memory_is_the_high_water_mark_not_the_current_set() {
        let status = "VmPeak:\t  900000 kB\nVmHWM:\t   32000 kB\nVmRSS:\t   20000 kB\n";
        assert_eq!(parse_peak_memory_bytes(status).unwrap(), 32_768_000);
        for bad in [
            "VmRSS:\t 20000 kB\n",
            "VmHWM:\n",
            "VmHWM:\t abc kB\n",
            "VmHWM:\t 18446744073709551615 kB\n",
        ] {
            assert!(parse_peak_memory_bytes(bad).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn a_process_without_an_address_space_is_gone() {
        // Measured on Linux 6.8: an exiting process reads `R (running)` with no
        // `VmHWM` line for most of its exit, before it becomes a zombie.
        for state in ["R (running)", "D (disk sleep)", "Z (zombie)"] {
            let status = format!("Name:\tcat\nState:\t{state}\nPid:\t7\n");
            assert_eq!(
                peak_from_status(7, &status),
                Err(PlatformError::ProcessGone(7)),
                "{state}"
            );
        }
    }

    #[test]
    fn a_live_process_reports_its_peak() {
        let status = "State:\tS (sleeping)\nVmHWM:\t   32000 kB\n";
        assert_eq!(peak_from_status(7, status), Ok(32_768_000));
    }

    #[test]
    fn a_status_without_a_state_is_malformed_not_gone() {
        assert!(matches!(
            peak_from_status(7, "Name:\tcat\n"),
            Err(PlatformError::Malformed { .. })
        ));
    }

    #[test]
    fn parse_proc_meminfo_reads_swap_total() {
        let content = "MemTotal:  791180784 kB\nSwapTotal:      0 kB\n";
        assert_eq!(parse_proc_meminfo_swap(content).unwrap(), 0);
    }

    #[test]
    fn parses_thread_cpu_affinity() {
        let status =
            "Name:\tperf_budget\nCpus_allowed:\t00000000,000fffff\nCpus_allowed_list:\t0-19\n";
        assert_eq!(parse_cpu_affinity(status).unwrap(), "0-19");
        assert!(parse_cpu_affinity("Name:\tperf_budget\n").is_err());
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn decodes_memory_policy_and_node_ranges() {
        let mut mask = [0 as libc::c_ulong; NUMA_MASK_WORDS];
        mask[0] = 0b1_1111;
        assert_eq!(
            decode_memory_policy(libc::MPOL_BIND, &mask).unwrap(),
            ("bind".to_owned(), "0-4".to_owned())
        );
        assert!(decode_memory_policy(-1, &mask).is_err());
    }
}
