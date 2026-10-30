//! macOS backend: `sysctl`.

#[cfg(target_os = "macos")]
use std::process::Command;

use crate::PlatformError;
#[cfg(target_os = "macos")]
use crate::{MachineFacts, ThreadPlacement, UNAVAILABLE};

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

    #[cfg(target_os = "macos")]
    #[test]
    fn thread_placement_is_unavailable_on_macos() {
        let placement = thread_placement().unwrap();
        assert_eq!(placement.cpu_affinity, UNAVAILABLE);
        assert_eq!(placement.memory_policy, UNAVAILABLE);
        assert_eq!(placement.memory_nodes, UNAVAILABLE);
    }
}
