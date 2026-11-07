//! Reads what an object or linked image declares about itself.
//!
//! Target-cell evidence states facts about a file, so they are read from the
//! file's own headers rather than from the flags it was linked with.

use crate::{ErrorCode, Result, VerificationError};

const PT_LOAD: u32 = 1;
const PT_DYNAMIC: u32 = 2;
const PT_GNU_STACK: u32 = 0x6474_e551;
const PT_GNU_RELRO: u32 = 0x6474_e552;
const ELF_WRITE: u32 = 2;
const ELF_EXECUTE: u32 = 1;
const ELF_PROGRAM_HEADER_BYTES: usize = 56;

const MH_MAGIC_64: u32 = 0xfeed_facf;
const MH_OBJECT: u32 = 1;
const MH_EXECUTE: u32 = 2;
const MH_PIE: u32 = 0x0020_0000;
const LC_SEGMENT_64: u32 = 0x19;
const VM_PROT_WRITE: u32 = 2;
const VM_PROT_EXECUTE: u32 = 4;

/// What one object or image declares in its headers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImageFacts {
    pub object_format: &'static str,
    pub object_type: &'static str,
    pub machine: &'static str,
    /// Mapped regions that are both writable and executable.
    pub writable_executable_regions: usize,
    /// `key=value` evidence specific to this format, in evidence order.
    pub format_evidence: Vec<(&'static str, String)>,
}

/// Parses the headers of an ELF64 or Mach-O 64 file.
///
/// # Errors
///
/// Returns [`ErrorCode::Schema`] when `bytes` is not a complete 64-bit ELF or
/// Mach-O file of a known machine and type.
pub fn inspect_image(bytes: &[u8]) -> Result<ImageFacts> {
    if bytes.starts_with(b"\x7fELF") {
        inspect_elf(bytes)
    } else if read_u32(bytes, 0, false)? == MH_MAGIC_64 {
        inspect_macho(bytes)
    } else {
        Err(malformed("not an ELF64 or Mach-O 64 file"))
    }
}

fn inspect_elf(bytes: &[u8]) -> Result<ImageFacts> {
    if bytes.get(4) != Some(&2) {
        return Err(malformed("ELF file is not 64-bit"));
    }
    let big_endian = match bytes.get(5) {
        Some(1) => false,
        Some(2) => true,
        _ => return Err(malformed("ELF file declares no byte order")),
    };
    let object_type = match read_u16(bytes, 16, big_endian)? {
        1 => "relocatable",
        2 | 3 => "executable",
        other => return Err(malformed(&format!("ELF type {other} is not supported"))),
    };
    let machine = match read_u16(bytes, 18, big_endian)? {
        62 => "x86_64",
        183 => "aarch64",
        22 => "s390x",
        243 => "riscv64",
        other => return Err(malformed(&format!("ELF machine {other} is not a target"))),
    };

    let table = usize::try_from(read_u64(bytes, 32, big_endian)?)
        .map_err(|_| malformed("ELF program header offset does not fit"))?;
    let entry_size = usize::from(read_u16(bytes, 54, big_endian)?);
    let entries = usize::from(read_u16(bytes, 56, big_endian)?);
    let table_end = table.checked_add(entries * entry_size);
    if entries > 0 && (entry_size < ELF_PROGRAM_HEADER_BYTES || table_end > Some(bytes.len())) {
        return Err(malformed("ELF program header table does not fit the file"));
    }
    let mut regions = 0;
    let mut dynamic = false;
    let mut relro = false;
    let mut stack = None;
    for index in 0..entries {
        let header = table + index * entry_size;
        let kind = read_u32(bytes, header, big_endian)?;
        let flags = read_u32(bytes, header + 4, big_endian)?;
        match kind {
            PT_LOAD if flags & ELF_WRITE != 0 && flags & ELF_EXECUTE != 0 => regions += 1,
            PT_DYNAMIC => dynamic = true,
            PT_GNU_RELRO => relro = true,
            PT_GNU_STACK => stack = Some(flags),
            _ => {}
        }
    }
    let stack_is_rw = stack == Some(6);
    Ok(ImageFacts {
        object_format: "elf",
        object_type,
        machine,
        writable_executable_regions: regions,
        format_evidence: vec![
            ("relro", relro.to_string()),
            // With no dynamic section nothing is bound lazily, so all of it is bound now.
            ("now", (!dynamic).to_string()),
            ("noexecstack", stack_is_rw.to_string()),
            (
                "gnu_stack",
                if stack_is_rw { "RW" } else { "other" }.to_owned(),
            ),
            (
                "dynamic_section",
                if dynamic { "present" } else { "absent" }.to_owned(),
            ),
        ],
    })
}

fn inspect_macho(bytes: &[u8]) -> Result<ImageFacts> {
    let machine = match read_u32(bytes, 4, false)? {
        0x0100_000c => "aarch64",
        0x0100_0007 => "x86_64",
        other => return Err(malformed(&format!("Mach-O CPU {other:#x} is not a target"))),
    };
    let object_type = match read_u32(bytes, 12, false)? {
        MH_OBJECT => "relocatable",
        MH_EXECUTE => "executable",
        other => return Err(malformed(&format!("Mach-O type {other} is not supported"))),
    };
    let flags = read_u32(bytes, 24, false)?;

    let mut regions = 0;
    let mut command = 32;
    for _ in 0..read_u32(bytes, 16, false)? {
        let kind = read_u32(bytes, command, false)?;
        let size = usize::try_from(read_u32(bytes, command + 4, false)?)
            .map_err(|_| malformed("Mach-O load command size does not fit"))?;
        if size < 8 {
            return Err(malformed("Mach-O load command is shorter than its header"));
        }
        if kind == LC_SEGMENT_64 {
            let protection = read_u32(bytes, command + 56, false)?;
            if protection & VM_PROT_WRITE != 0 && protection & VM_PROT_EXECUTE != 0 {
                regions += 1;
            }
        }
        command += size;
    }
    Ok(ImageFacts {
        object_format: "macho",
        object_type,
        machine,
        writable_executable_regions: regions,
        format_evidence: vec![("pie", (flags & MH_PIE != 0).to_string())],
    })
}

fn slice<const N: usize>(bytes: &[u8], offset: usize) -> Result<[u8; N]> {
    offset
        .checked_add(N)
        .and_then(|end| bytes.get(offset..end))
        .and_then(|field| field.try_into().ok())
        .ok_or_else(|| malformed("file ends inside a header"))
}

fn read_u16(bytes: &[u8], offset: usize, big_endian: bool) -> Result<u16> {
    let field = slice(bytes, offset)?;
    Ok(if big_endian {
        u16::from_be_bytes(field)
    } else {
        u16::from_le_bytes(field)
    })
}

fn read_u32(bytes: &[u8], offset: usize, big_endian: bool) -> Result<u32> {
    let field = slice(bytes, offset)?;
    Ok(if big_endian {
        u32::from_be_bytes(field)
    } else {
        u32::from_le_bytes(field)
    })
}

fn read_u64(bytes: &[u8], offset: usize, big_endian: bool) -> Result<u64> {
    let field = slice(bytes, offset)?;
    Ok(if big_endian {
        u64::from_be_bytes(field)
    } else {
        u64::from_le_bytes(field)
    })
}

fn malformed(detail: &str) -> VerificationError {
    VerificationError::new(ErrorCode::Schema, format!("image headers: {detail}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A minimal ELF64 header with these program headers as (type, flags).
    fn elf(big_endian: bool, machine: u16, kind: u16, headers: &[(u32, u32)]) -> Vec<u8> {
        let u16b = |value: u16| {
            if big_endian {
                value.to_be_bytes()
            } else {
                value.to_le_bytes()
            }
        };
        let u32b = |value: u32| {
            if big_endian {
                value.to_be_bytes()
            } else {
                value.to_le_bytes()
            }
        };
        let u64b = |value: u64| {
            if big_endian {
                value.to_be_bytes()
            } else {
                value.to_le_bytes()
            }
        };
        let mut bytes = vec![0u8; 64];
        bytes[..4].copy_from_slice(b"\x7fELF");
        bytes[4] = 2;
        bytes[5] = if big_endian { 2 } else { 1 };
        bytes[16..18].copy_from_slice(&u16b(kind));
        bytes[18..20].copy_from_slice(&u16b(machine));
        bytes[32..40].copy_from_slice(&u64b(64));
        bytes[54..56].copy_from_slice(&u16b(56));
        let count = u16::try_from(headers.len()).expect("header count");
        bytes[56..58].copy_from_slice(&u16b(count));
        for (kind, flags) in headers {
            let mut header = [0u8; 56];
            header[..4].copy_from_slice(&u32b(*kind));
            header[4..8].copy_from_slice(&u32b(*flags));
            bytes.extend_from_slice(&header);
        }
        bytes
    }

    /// A minimal Mach-O 64 header with one LC_SEGMENT_64 per `protections` entry.
    fn macho(cpu: u32, kind: u32, flags: u32, protections: &[u32]) -> Vec<u8> {
        let mut bytes = vec![0u8; 32];
        bytes[..4].copy_from_slice(&MH_MAGIC_64.to_le_bytes());
        bytes[4..8].copy_from_slice(&cpu.to_le_bytes());
        bytes[12..16].copy_from_slice(&kind.to_le_bytes());
        let count = u32::try_from(protections.len()).expect("command count");
        bytes[16..20].copy_from_slice(&count.to_le_bytes());
        bytes[24..28].copy_from_slice(&flags.to_le_bytes());
        for protection in protections {
            let mut command = [0u8; 72];
            command[..4].copy_from_slice(&LC_SEGMENT_64.to_le_bytes());
            command[4..8].copy_from_slice(&72u32.to_le_bytes());
            command[56..60].copy_from_slice(&protection.to_le_bytes());
            bytes.extend_from_slice(&command);
        }
        bytes
    }

    fn evidence(facts: &ImageFacts, key: &str) -> String {
        facts
            .format_evidence
            .iter()
            .find(|(name, _)| *name == key)
            .map(|(_, value)| value.clone())
            .unwrap_or_default()
    }

    #[test]
    fn a_hardened_static_elf_reads_as_hardened() {
        let headers = [
            (PT_LOAD, 5),
            (PT_LOAD, 6),
            (PT_GNU_RELRO, 4),
            (PT_GNU_STACK, 6),
        ];
        let facts = inspect_image(&elf(false, 62, 2, &headers)).expect("elf");
        assert_eq!(facts.object_format, "elf");
        assert_eq!(facts.object_type, "executable");
        assert_eq!(facts.machine, "x86_64");
        assert_eq!(facts.writable_executable_regions, 0);
        assert_eq!(evidence(&facts, "relro"), "true");
        assert_eq!(evidence(&facts, "now"), "true");
        assert_eq!(evidence(&facts, "noexecstack"), "true");
        assert_eq!(evidence(&facts, "gnu_stack"), "RW");
        assert_eq!(evidence(&facts, "dynamic_section"), "absent");
    }

    #[test]
    fn an_unhardened_elf_says_so() {
        let headers = [(PT_LOAD, 7), (PT_DYNAMIC, 6), (PT_GNU_STACK, 7)];
        let facts = inspect_image(&elf(false, 183, 2, &headers)).expect("elf");
        assert_eq!(facts.machine, "aarch64");
        assert_eq!(facts.writable_executable_regions, 1);
        assert_eq!(evidence(&facts, "relro"), "false");
        assert_eq!(evidence(&facts, "now"), "false");
        assert_eq!(evidence(&facts, "noexecstack"), "false");
        assert_eq!(evidence(&facts, "dynamic_section"), "present");
    }

    #[test]
    fn a_missing_stack_header_is_not_a_safe_stack() {
        let facts = inspect_image(&elf(false, 62, 2, &[(PT_LOAD, 5)])).expect("elf");
        assert_eq!(evidence(&facts, "noexecstack"), "false");
    }

    #[test]
    fn big_endian_elf_reads_correctly() {
        let facts = inspect_image(&elf(true, 22, 1, &[(PT_LOAD, 7)])).expect("s390x");
        assert_eq!(facts.machine, "s390x");
        assert_eq!(facts.object_type, "relocatable");
        assert_eq!(facts.writable_executable_regions, 1);
    }

    #[test]
    fn a_macho_executable_reads_its_pie_flag_and_regions() {
        let image = macho(0x0100_000c, MH_EXECUTE, MH_PIE, &[5, 3]);
        let facts = inspect_image(&image).expect("macho");
        assert_eq!(facts.object_format, "macho");
        assert_eq!(facts.object_type, "executable");
        assert_eq!(facts.machine, "aarch64");
        assert_eq!(facts.writable_executable_regions, 0);
        assert_eq!(evidence(&facts, "pie"), "true");

        let open = macho(0x0100_0007, MH_EXECUTE, 0, &[7]);
        let facts = inspect_image(&open).expect("macho");
        assert_eq!(facts.machine, "x86_64");
        assert_eq!(facts.writable_executable_regions, 1);
        assert_eq!(evidence(&facts, "pie"), "false");
    }

    #[test]
    fn a_truncated_or_foreign_file_is_an_error() {
        let mut truncated = elf(false, 62, 2, &[(PT_LOAD, 5)]);
        truncated.truncate(100);
        for bytes in [truncated, vec![0; 8], Vec::new()] {
            assert_eq!(
                inspect_image(&bytes).map_err(|error| error.code()),
                Err(ErrorCode::Schema)
            );
        }
        let unknown = elf(false, 3, 2, &[]);
        assert!(inspect_image(&unknown).is_err(), "32-bit x86 is no target");
    }
}
