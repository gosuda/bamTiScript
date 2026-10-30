//! Linux backend: `/proc`, `/sys`, and `get_mempolicy(2)`.

use std::collections::BTreeSet;
#[cfg(target_os = "linux")]
use std::fs;

use crate::PlatformError;
#[cfg(target_os = "linux")]
use crate::{MachineFacts, ThreadPlacement};

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
    let (cpu_model, sockets, cores_per_socket, microcode) = parse_proc_cpuinfo(&cpuinfo)?;
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
