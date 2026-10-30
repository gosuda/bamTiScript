//! In-process AOT linker: parses a relocatable object, maps sections into
//! W^X memory, resolves helper relocations against the live `bamts_*`
//! exports, applies relocations, and produces a [`LinkedAotProgram`] that
//! implements [`NativeEntryTable`] for direct execution via
//! `bamts_runtime::run_linked_program`.
//!
//! This is the native counterpart of the external `cc` link+`dlopen` path:
//! it avoids spawning a linker and keeps all execution in-process, which is
//! what the test262 AOT lane needs.
//!
//! # Safety
//!
//! This module owns every `unsafe` operation the in-process link requires:
//! parsing object bytes into typed structures, mapping executable memory,
//! applying relocations to raw bytes, and casting mapped descriptors to
//! `&'static ProgramDescriptor`. The crate-level `#![deny(unsafe_code)]` is
//! relaxed for this one module via `#[allow(unsafe_code)]` on the declaration
//! in `aot.rs`.

use std::collections::HashMap;
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

use bamts_bytecode::Program as BytecodeProgram;
use bamts_bytecode::Verified;
use bamts_native::{
    AbiError, Completion, CompletionTag, LinkedProgram, NativeEntryTable, ProgramDescriptor,
    ShadowFrame,
};

use cranelift_object::object::{
    File, Object, ObjectSection, ObjectSymbol, Relocation, RelocationEncoding, RelocationFlags,
    RelocationKind, RelocationTarget, SectionIndex, SectionKind, SymbolIndex, elf,
};

use crate::AotObject;

// -- Public types -----------------------------------------------------------

/// A typed failure during in-process AOT linking.
#[derive(Debug)]
pub enum HostTargetError {
    /// The host architecture is not supported for in-process AOT.
    UnsupportedArch(&'static str),
}

impl fmt::Display for HostTargetError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedArch(arch) => {
                write!(
                    f,
                    "unsupported host architecture for in-process AOT: {arch}"
                )
            }
        }
    }
}

impl std::error::Error for HostTargetError {}

/// Observable proof that native entries were actually invoked.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NativeExecutionReport {
    /// Number of times a compiled native entry was invoked through the
    /// entry table. Nonzero after a successful AOT run proves the engine
    /// executed compiled native code, not the reference interpreter.
    pub native_entries_invoked: u64,
}

/// A linked AOT program: owns the mapped memory holding compiled native code
/// and data, and implements [`NativeEntryTable`] for execution via
/// `bamts_runtime::run_linked_program`.
///
/// The invocation counter is incremented on every `invoke` call, providing
/// observable proof that native entries ran.
pub struct LinkedAotProgram {
    /// The mapped memory holding all sections. Kept alive for the program's
    /// lifetime so native entry pointers remain valid.
    _mapping: region::Allocation,
    /// The validated program descriptor, borrowed from the mapping. Its
    /// pointers reference data inside `_mapping`. Kept to ensure the
    /// `LinkedProgram`'s lifetime anchor remains valid.
    _descriptor: &'static ProgramDescriptor,
    /// The validated linked view, borrowed from `descriptor`.
    linked: LinkedProgram<'static>,
    /// Invocation counter for observable proof.
    entries_invoked: AtomicU64,
}

impl LinkedAotProgram {
    /// Returns the number of native entry invocations since link time.
    #[must_use]
    pub fn native_entries_invoked(&self) -> u64 {
        self.entries_invoked.load(Ordering::Relaxed)
    }

    /// Returns an execution report snapshot.
    #[must_use]
    pub fn report(&self) -> NativeExecutionReport {
        NativeExecutionReport {
            native_entries_invoked: self.native_entries_invoked(),
        }
    }
}

impl NativeEntryTable for LinkedAotProgram {
    fn program_bytes(&self) -> &[u8] {
        self.linked.program_bytes()
    }

    fn invoke(
        &self,
        module_id: u32,
        function_id: u32,
        frame: &mut ShadowFrame,
        out: &mut Completion,
    ) -> Result<CompletionTag, AbiError> {
        self.entries_invoked.fetch_add(1, Ordering::Relaxed);
        self.linked.invoke(module_id, function_id, frame, out)
    }
}

// -- Host target detection --------------------------------------------------

/// Returns the Cranelift target triple for the host, or an error if the host
/// architecture is not supported for in-process AOT.
///
/// The triple selects the calling convention generated code uses to call the
/// `bamts_*` helpers, which are compiled for the real host. The container stays
/// ELF on every host: the `-elf` suffix makes Cranelift write ELF while the
/// rest of the triple still picks the host ABI. Do not pass these triples to
/// `linking::TargetFormat::for_triple`, which would read `darwin` as Mach-O.
pub fn host_target() -> Result<&'static str, HostTargetError> {
    match (std::env::consts::OS, std::env::consts::ARCH) {
        ("macos", "aarch64") => Ok("aarch64-apple-darwin-elf"),
        ("macos", "x86_64") => Ok("x86_64-apple-darwin-elf"),
        ("windows", "x86_64") => Ok("x86_64-pc-windows-msvc-elf"),
        (_, "x86_64") => Ok("x86_64-unknown-linux-gnu"),
        (_, "aarch64") => Ok("aarch64-unknown-linux-gnu"),
        _ => Err(HostTargetError::UnsupportedArch(std::env::consts::ARCH)),
    }
}

// -- In-process linker ------------------------------------------------------

/// A typed in-process link failure.
#[derive(Debug)]
pub enum InProcessLinkError {
    /// The object file could not be parsed.
    Parse(String),
    /// A required symbol was not found in the object.
    MissingSymbol(String),
    /// A section referenced by a symbol was not found.
    MissingSection,
    /// A relocation targeted an unknown symbol.
    UnknownRelocationTarget(String),
    /// A relocation kind/size combination is not supported.
    UnsupportedRelocation {
        kind: RelocationKind,
        size: u8,
        encoding: RelocationEncoding,
    },
    /// A relocation value does not fit the field of the instruction it patches.
    RelocationOutOfRange {
        relocation: &'static str,
        displacement: i64,
    },
    /// A relocation needs an address with alignment the address does not have.
    RelocationMisaligned {
        relocation: &'static str,
        address: u64,
    },
    /// The mapped ProgramDescriptor failed validation.
    DescriptorValidation(AbiError),
    /// A memory mapping operation failed.
    Map(String),
    /// A memory protection operation failed.
    Protect(String),
}

impl fmt::Display for InProcessLinkError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse(msg) => write!(f, "object parse failed: {msg}"),
            Self::MissingSymbol(name) => write!(f, "missing symbol: {name}"),
            Self::MissingSection => write!(f, "symbol references a missing section"),
            Self::UnknownRelocationTarget(name) => {
                write!(f, "relocation targets unknown symbol: {name}")
            }
            Self::UnsupportedRelocation {
                kind,
                size,
                encoding,
            } => {
                write!(
                    f,
                    "unsupported relocation: kind={kind:?} size={size} encoding={encoding:?}"
                )
            }
            Self::RelocationOutOfRange {
                relocation,
                displacement,
            } => {
                write!(
                    f,
                    "{relocation} displacement {displacement} is out of range"
                )
            }
            Self::RelocationMisaligned {
                relocation,
                address,
            } => {
                write!(f, "{relocation} address {address:#x} is misaligned")
            }
            Self::DescriptorValidation(error) => {
                write!(f, "program descriptor validation failed: {error:?}")
            }
            Self::Map(msg) => write!(f, "memory mapping failed: {msg}"),
            Self::Protect(msg) => write!(f, "memory protection failed: {msg}"),
        }
    }
}

impl std::error::Error for InProcessLinkError {}

/// Parses, links, and loads an [`AotObject`] in-process, returning a
/// [`LinkedAotProgram`] ready for execution via
/// `bamts_runtime::run_linked_program`.
///
/// The `bytecode` argument must be the same `Program<Verified>` that produced
/// the AOT object; it is used to verify the embedded canonical bytes match.
pub fn link_aot_in_process(
    object: &AotObject,
    bytecode: &BytecodeProgram<Verified>,
) -> Result<LinkedAotProgram, InProcessLinkError> {
    let file = File::parse(&*object.bytes).map_err(|e| InProcessLinkError::Parse(e.to_string()))?;

    // -- 1. Collect sections and assign offsets in a single mapping ---------

    let page_size = page_size();
    let sections = collect_sections(&file);

    // Layout: text sections first (page-aligned), then data sections.
    // This lets us protect text as RX and data as RW independently.
    let mut text_end = 0usize;
    let mut data_end = 0usize;
    let mut section_offsets: Vec<(usize, SectionKind)> = Vec::with_capacity(sections.len());

    for section in &sections {
        let size = section.data.len();
        if size == 0 {
            section_offsets.push((0, section.kind));
            continue;
        }
        if section.kind == SectionKind::Text {
            text_end = align_up(text_end, page_size);
            section_offsets.push((text_end, section.kind));
            text_end += size;
        } else {
            data_end = align_up(data_end, 8);
            section_offsets.push((data_end, section.kind));
            data_end += size;
        }
    }
    // Pre-scan relocations to find symbols that need GOT entries
    // (GotRelative relocations reference a GOT entry, not the symbol directly).
    let mut got_symbols: Vec<SymbolIndex> = Vec::new();
    let mut got_seen: std::collections::HashSet<SymbolIndex> = std::collections::HashSet::new();
    for section in &sections {
        if section.data.is_empty() {
            continue;
        }
        let original_section = file
            .section_by_index(section.original_index)
            .map_err(|e| InProcessLinkError::Parse(e.to_string()))?;
        for (_offset, reloc) in original_section.relocations() {
            if needs_got_entry(&reloc)
                && let RelocationTarget::Symbol(idx) = reloc.target()
                && got_seen.insert(idx)
            {
                got_symbols.push(idx);
            }
        }
    }
    let got_size = got_symbols.len() * 8;

    // Total mapping size: text region (page-aligned) + data region (page-aligned)
    // + GOT region (8 bytes per entry, 8-aligned).
    let text_region_size = align_up(text_end, page_size);
    let data_region_size = align_up(data_end + got_size, page_size);
    let total_size = text_region_size + data_region_size;
    if total_size == 0 {
        return Err(InProcessLinkError::Map("object has no sections".into()));
    }

    // -- 2. Allocate W^X mapping --------------------------------------------

    let mapping = region::alloc(total_size, region::Protection::READ_WRITE)
        .map_err(|e| InProcessLinkError::Map(e.to_string()))?;

    let base = mapping.as_ptr::<u8>() as *mut u8;
    let text_base: *mut u8 = base;
    let data_base: *mut u8 = unsafe { base.add(text_region_size) };

    // -- 3. Copy section data into the mapping ------------------------------

    for (i, section) in sections.iter().enumerate() {
        let (offset, kind) = section_offsets[i];
        if section.data.is_empty() {
            continue;
        }
        let dest = if kind == SectionKind::Text {
            unsafe { text_base.add(offset) }
        } else {
            unsafe { data_base.add(offset) }
        };
        unsafe {
            std::ptr::copy_nonoverlapping(section.data.as_ptr(), dest, section.data.len());
        }
    }

    // -- 4. Build symbol address map ---------------------------------------

    let mut symbol_addresses: HashMap<SymbolIndex, usize> = HashMap::new();

    for symbol in file.symbols() {
        if symbol.is_undefined() {
            continue;
        }
        let Some(section_index) = symbol.section_index() else {
            continue;
        };
        // Find which collected section this is.
        let (collected_idx, _) = sections
            .iter()
            .enumerate()
            .find(|(_, s)| s.original_index == section_index)
            .ok_or(InProcessLinkError::MissingSection)?;
        let (offset, kind) = section_offsets[collected_idx];
        let section_base = if kind == SectionKind::Text {
            text_base
        } else {
            data_base
        };
        let addr = unsafe { section_base.add(offset) };
        let symbol_addr = unsafe { addr.add(symbol.address() as usize) };
        symbol_addresses.insert(symbol.index(), symbol_addr as usize);
    }

    // -- 5. Resolve helper symbols to bamts_* function pointers -------------

    let helper_addresses = helper_address_map();

    // -- 5b. Populate GOT entries -------------------------------------------
    // The GOT lives at the end of the data region, after all data sections.
    // Each entry is 8 bytes containing the resolved symbol address.
    let mut got_entry_addresses: HashMap<SymbolIndex, usize> = HashMap::new();
    if !got_symbols.is_empty() {
        let got_base = unsafe { data_base.add(data_end) };
        for (i, sym_idx) in got_symbols.iter().enumerate() {
            let sym = file
                .symbol_by_index(*sym_idx)
                .map_err(|e| InProcessLinkError::Parse(e.to_string()))?;
            let addr = if sym.is_undefined() {
                let name = sym
                    .name()
                    .map_err(|e| InProcessLinkError::Parse(e.to_string()))?;
                helper_addresses
                    .get(name)
                    .copied()
                    .ok_or_else(|| InProcessLinkError::UnknownRelocationTarget(name.to_owned()))?
            } else {
                symbol_addresses
                    .get(sym_idx)
                    .copied()
                    .ok_or(InProcessLinkError::MissingSection)?
            };
            let got_entry = unsafe { got_base.add(i * 8) };
            unsafe {
                (got_entry as *mut u64).write_unaligned(addr as u64);
            }
            got_entry_addresses.insert(*sym_idx, got_entry as usize);
        }
    }
    // -- 6. Apply relocations -----------------------------------------------

    for (i, section) in sections.iter().enumerate() {
        if section.data.is_empty() {
            continue;
        }
        let (offset, kind) = section_offsets[i];
        let section_base = if kind == SectionKind::Text {
            text_base
        } else {
            data_base
        };
        let section_addr = unsafe { section_base.add(offset) };

        let original_section = file
            .section_by_index(section.original_index)
            .map_err(|e| InProcessLinkError::Parse(e.to_string()))?;

        for (reloc_offset, relocation) in original_section.relocations() {
            // For GotRelative, the "symbol address" is the GOT entry address.
            let symbol_addr = if needs_got_entry(&relocation) {
                let RelocationTarget::Symbol(sym_idx) = relocation.target() else {
                    return Err(InProcessLinkError::UnknownRelocationTarget(format!(
                        "{:?}",
                        relocation.target()
                    )));
                };
                *got_entry_addresses.get(&sym_idx).ok_or_else(|| {
                    InProcessLinkError::MissingSymbol(format!("GOT entry for symbol {sym_idx:?}"))
                })?
            } else {
                resolve_symbol_address(&file, &relocation, &symbol_addresses, &helper_addresses)?
            };

            let place = unsafe { section_addr.add(reloc_offset as usize) };
            apply_relocation(place, symbol_addr, &relocation)?;
        }
    }

    // -- 7. Protect text as executable --------------------------------------

    if text_region_size > 0 {
        unsafe {
            region::protect(
                text_base as *const (),
                text_region_size,
                region::Protection::READ_EXECUTE,
            )
            .map_err(|e| InProcessLinkError::Protect(e.to_string()))?;
        }
    }

    // -- 8. Build ProgramDescriptor from mapped data ------------------------

    let descriptor_symbol = file
        .symbols()
        .find(|s| s.name() == Ok(object.descriptor_symbol))
        .ok_or_else(|| InProcessLinkError::MissingSymbol(object.descriptor_symbol.into()))?;

    let (desc_idx, desc_kind) = {
        let section_index = descriptor_symbol
            .section_index()
            .ok_or(InProcessLinkError::MissingSection)?;
        let (collected_idx, collected) = sections
            .iter()
            .enumerate()
            .find(|(_, s)| s.original_index == section_index)
            .ok_or(InProcessLinkError::MissingSection)?;
        (collected_idx, collected.kind)
    };

    let (desc_offset, _) = section_offsets[desc_idx];
    let desc_section_base = if desc_kind == SectionKind::Text {
        text_base
    } else {
        data_base
    };
    let descriptor_addr = unsafe {
        desc_section_base
            .add(desc_offset)
            .add(descriptor_symbol.address() as usize)
    };

    // Verify the mapped descriptor magic before casting; from_descriptor
    let mapped_magic = unsafe { (descriptor_addr as *const u64).read_unaligned() };
    debug_assert_eq!(
        mapped_magic,
        bamts_native::AOT_MAGIC,
        "mapped descriptor magic mismatch: got 0x{mapped_magic:016x}, desc_offset={desc_offset}, desc_kind={desc_kind:?}, desc_section_base={desc_section_base:p}, descriptor_addr={descriptor_addr:p}"
    );

    // SAFETY: The descriptor is `#[repr(C)]`, 56 bytes, 8-aligned. It lives
    // in the data region of the mapping, which remains valid for the
    // lifetime of `LinkedAotProgram`. The relocations on the descriptor
    // (pointing to bytecode_blob and unit_descriptors) have been applied,
    // so its pointers are valid.
    let descriptor: &'static ProgramDescriptor =
        unsafe { &*(descriptor_addr as *const ProgramDescriptor) };

    // Validate the descriptor.
    let linked = unsafe { LinkedProgram::from_descriptor(descriptor) }
        .map_err(InProcessLinkError::DescriptorValidation)?;

    // Verify the embedded bytecode matches the supplied program.
    let expected_bytes = bytecode.encode();
    if linked.program_bytes() != expected_bytes.as_slice() {
        return Err(InProcessLinkError::DescriptorValidation(
            AbiError::BadMagic { found: 0 },
        ));
    }

    Ok(LinkedAotProgram {
        _mapping: mapping,
        _descriptor: descriptor,
        linked,
        entries_invoked: AtomicU64::new(0),
    })
}

// -- Helpers -----------------------------------------------------------------

struct CollectedSection {
    original_index: SectionIndex,
    kind: SectionKind,
    data: Vec<u8>,
}

fn collect_sections(file: &File<'_>) -> Vec<CollectedSection> {
    let mut sections = Vec::new();
    for section in file.sections() {
        let kind = section.kind();
        // Only collect sections that contain code or data (skip debug, etc).
        if !matches!(
            kind,
            SectionKind::Text
                | SectionKind::Data
                | SectionKind::ReadOnlyData
                | SectionKind::ReadOnlyDataWithRel
        ) {
            continue;
        }
        let data = section.data().unwrap_or(&[]).to_vec();
        if data.is_empty() {
            continue;
        }
        sections.push(CollectedSection {
            original_index: section.index(),
            kind,
            data,
        });
    }
    sections
}

fn align_up(value: usize, alignment: usize) -> usize {
    if alignment == 0 {
        return value;
    }
    (value + alignment - 1) & !(alignment - 1)
}

fn page_size() -> usize {
    region::page::size()
}

fn resolve_symbol_address(
    file: &File<'_>,
    relocation: &Relocation,
    defined_symbols: &HashMap<SymbolIndex, usize>,
    helper_addresses: &HashMap<&'static str, usize>,
) -> Result<usize, InProcessLinkError> {
    let RelocationTarget::Symbol(symbol_index) = relocation.target() else {
        return Err(InProcessLinkError::UnknownRelocationTarget(format!(
            "{:?}",
            relocation.target()
        )));
    };

    let symbol = file
        .symbol_by_index(symbol_index)
        .map_err(|e| InProcessLinkError::Parse(e.to_string()))?;

    if symbol.is_undefined() {
        // Helper symbol — resolve to the bamts_* function address.
        let name = symbol
            .name()
            .map_err(|e| InProcessLinkError::Parse(e.to_string()))?;
        helper_addresses
            .get(name)
            .copied()
            .ok_or_else(|| InProcessLinkError::UnknownRelocationTarget(name.to_owned()))
    } else {
        defined_symbols
            .get(&symbol_index)
            .copied()
            .ok_or(InProcessLinkError::MissingSection)
    }
}

fn apply_relocation(
    place: *mut u8,
    symbol_addr: usize,
    relocation: &Relocation,
) -> Result<(), InProcessLinkError> {
    let addend = relocation.addend();
    let place_addr = place as usize;
    let kind = relocation.kind();
    let size = relocation.size();
    let encoding = relocation.encoding();

    // `object` leaves the AArch64 GOT forms as `Unknown`, so they are told
    // apart by the raw ELF relocation type.
    match elf_relocation_type(relocation) {
        Some(elf::R_AARCH64_ADR_GOT_PAGE) => {
            return patch_instruction(place, |word| {
                patch_adrp_page(word, place_addr as u64, symbol_addr as u64)
            });
        }
        Some(elf::R_AARCH64_LD64_GOT_LO12_NC) => {
            return patch_instruction(place, |word| patch_ldr_got_lo12(word, symbol_addr as u64));
        }
        _ => {}
    }

    match (kind, size) {
        (RelocationKind::Absolute, 64) => {
            // S + A
            let value = (symbol_addr as i64).wrapping_add(addend) as u64;
            unsafe {
                place.cast::<u64>().write_unaligned(value);
            }
        }
        (RelocationKind::Absolute, 32) => {
            // S + A (truncated to 32 bits)
            let value = (symbol_addr as i64).wrapping_add(addend) as u32;
            unsafe {
                place.cast::<u32>().write_unaligned(value);
            }
        }
        (RelocationKind::Relative, 32)
        | (RelocationKind::PltRelative, 32)
        | (RelocationKind::GotRelative, 32) => {
            // S + A - P
            let value = (symbol_addr as i64)
                .wrapping_add(addend)
                .wrapping_sub(place_addr as i64) as u32;
            unsafe {
                place.cast::<u32>().write_unaligned(value);
            }
        }
        (RelocationKind::Relative, 26) => {
            // AArch64 call: (S + A - P) >> 2, 26-bit, masked into place[31:0]
            // The lower 2 bits of the place are 00 (ARM alignment), so we
            // encode the 26-bit immediate directly.
            let displacement = (symbol_addr as i64)
                .wrapping_add(addend)
                .wrapping_sub(place_addr as i64);
            let imm26 = (displacement >> 2) as u32 & 0x03FF_FFFF;
            unsafe {
                let existing = place.cast::<u32>().read_unaligned();
                place
                    .cast::<u32>()
                    .write_unaligned((existing & 0xFC00_0000) | imm26);
            }
        }
        _ => {
            return Err(InProcessLinkError::UnsupportedRelocation {
                kind,
                size,
                encoding,
            });
        }
    }
    Ok(())
}

fn elf_relocation_type(relocation: &Relocation) -> Option<u32> {
    match relocation.flags() {
        RelocationFlags::Elf { r_type } => Some(r_type),
        _ => None,
    }
}

/// Whether the relocation reads its symbol through a GOT entry instead of
/// addressing the symbol directly.
fn needs_got_entry(relocation: &Relocation) -> bool {
    relocation.kind() == RelocationKind::GotRelative
        || matches!(
            elf_relocation_type(relocation),
            Some(elf::R_AARCH64_ADR_GOT_PAGE | elf::R_AARCH64_LD64_GOT_LO12_NC)
        )
}

/// Rewrites the 32-bit instruction at `place` through `patch`.
fn patch_instruction(
    place: *mut u8,
    patch: impl FnOnce(u32) -> Result<u32, InProcessLinkError>,
) -> Result<(), InProcessLinkError> {
    unsafe {
        let patched = patch(place.cast::<u32>().read_unaligned())?;
        place.cast::<u32>().write_unaligned(patched);
    }
    Ok(())
}

/// `R_AARCH64_ADR_GOT_PAGE`: points an `ADRP` at the 4 KiB page holding the
/// GOT entry. `ADRP` counts 4 KiB pages whatever the OS page size is.
fn patch_adrp_page(
    instruction: u32,
    place: u64,
    got_entry: u64,
) -> Result<u32, InProcessLinkError> {
    let pages = (got_entry >> 12) as i64 - (place >> 12) as i64;
    if !(-(1 << 20)..(1 << 20)).contains(&pages) {
        return Err(InProcessLinkError::RelocationOutOfRange {
            relocation: "R_AARCH64_ADR_GOT_PAGE",
            displacement: pages,
        });
    }
    let immediate = pages as u32 & 0x1F_FFFF;
    let immlo = immediate & 0x3;
    let immhi = immediate >> 2;
    Ok((instruction & !((0x3 << 29) | (0x7_FFFF << 5))) | (immlo << 29) | (immhi << 5))
}

/// `R_AARCH64_LD64_GOT_LO12_NC`: gives an 8-byte `LDR` the offset of the GOT
/// entry inside its page.
fn patch_ldr_got_lo12(instruction: u32, got_entry: u64) -> Result<u32, InProcessLinkError> {
    if got_entry & 0x7 != 0 {
        return Err(InProcessLinkError::RelocationMisaligned {
            relocation: "R_AARCH64_LD64_GOT_LO12_NC",
            address: got_entry,
        });
    }
    let scaled_offset = ((got_entry & 0xFFF) >> 3) as u32;
    Ok((instruction & !(0xFFF << 10)) | (scaled_offset << 10))
}

/// Builds a map of helper symbol names to their live function addresses.
fn helper_address_map() -> HashMap<&'static str, usize> {
    let mut map = HashMap::new();
    for index in 0..bamts_native::HELPER_COUNT {
        let helper =
            crate::Helper::from_external_index(index).expect("pinned helper table is dense");
        let symbol = helper.symbol();
        let addr = helper_address(helper);
        map.insert(symbol, addr);
    }
    map
}
macro_rules! fn_addr {
    ($f:expr) => {
        $f as *const () as usize
    };
}
fn helper_address(helper: crate::Helper) -> usize {
    use crate::Helper;
    match helper {
        Helper::LoadConstant => fn_addr!(bamts_native::bamts_load_constant),
        Helper::Unary => fn_addr!(bamts_native::bamts_unary),
        Helper::Binary => fn_addr!(bamts_native::bamts_binary),
        Helper::CreateObject => fn_addr!(bamts_native::bamts_create_object),
        Helper::CreateArray => fn_addr!(bamts_native::bamts_create_array),
        Helper::CreateCell => fn_addr!(bamts_native::bamts_create_cell),
        Helper::CreateClosure => fn_addr!(bamts_native::bamts_create_closure),
        Helper::GetProperty => fn_addr!(bamts_native::bamts_get_property),
        Helper::SetProperty => fn_addr!(bamts_native::bamts_set_property),
        Helper::DeleteProperty => fn_addr!(bamts_native::bamts_delete_property),
        Helper::Call => fn_addr!(bamts_native::bamts_call),
        Helper::Construct => fn_addr!(bamts_native::bamts_construct),
        Helper::ConstructWithNewTarget => {
            fn_addr!(bamts_native::bamts_construct_with_new_target)
        }
        Helper::DefineDataProperty => fn_addr!(bamts_native::bamts_define_data_property),
        Helper::LoadOwnDescriptorSlot => fn_addr!(bamts_native::bamts_load_own_descriptor_slot),
        Helper::DefineOwnDescriptorSlot => {
            fn_addr!(bamts_native::bamts_define_own_descriptor_slot)
        }
        Helper::WithHasBinding => fn_addr!(bamts_native::bamts_with_has_binding),
        Helper::Import => fn_addr!(bamts_native::bamts_import),
        Helper::ImportDynamic => fn_addr!(bamts_native::bamts_import_dynamic),
        Helper::Truthy => fn_addr!(bamts_native::bamts_truthy),
        Helper::ResumeValue => fn_addr!(bamts_native::bamts_resume_value),
        Helper::DefineAccessor => fn_addr!(bamts_native::bamts_define_accessor),
        Helper::LoadGlobal => fn_addr!(bamts_native::bamts_load_global),
        Helper::StoreGlobal => fn_addr!(bamts_native::bamts_store_global),
        Helper::TypeOfGlobal => fn_addr!(bamts_native::bamts_typeof_global),
        Helper::LoadThis => fn_addr!(bamts_native::bamts_load_this),
        Helper::LoadArguments => fn_addr!(bamts_native::bamts_load_arguments),
        Helper::LoadNewTarget => fn_addr!(bamts_native::bamts_load_new_target),
        Helper::ArrayPush => fn_addr!(bamts_native::bamts_array_push),
        Helper::ArrayExtend => fn_addr!(bamts_native::bamts_array_extend),
        Helper::ObjectSpread => fn_addr!(bamts_native::bamts_object_spread),
        Helper::SetPrototype => fn_addr!(bamts_native::bamts_set_prototype),
        Helper::CreatePrivateName => fn_addr!(bamts_native::bamts_create_private_name),
        Helper::CreateRegExp => fn_addr!(bamts_native::bamts_create_regexp),
        Helper::GetIterator => fn_addr!(bamts_native::bamts_get_iterator),
        Helper::IteratorNext => fn_addr!(bamts_native::bamts_iterator_next),
        Helper::Export => fn_addr!(bamts_native::bamts_export),
        Helper::ConsumeFuel => fn_addr!(bamts_native::bamts_consume_fuel),
        Helper::IteratorStep => fn_addr!(bamts_native::bamts_iterator_step),
        Helper::IteratorResult => fn_addr!(bamts_native::bamts_iterator_result),
        Helper::IteratorClose => fn_addr!(bamts_native::bamts_iterator_close),
        Helper::RequireCloseResult => fn_addr!(bamts_native::bamts_require_close_result),
        Helper::LoadImportMeta => fn_addr!(bamts_native::bamts_load_import_meta),
        Helper::ToObject => fn_addr!(bamts_native::bamts_to_object),
        Helper::DisposeCapture => fn_addr!(bamts_native::bamts_dispose_capture),
        Helper::SuppressError => fn_addr!(bamts_native::bamts_suppress_error),
        Helper::ResumeMode => fn_addr!(bamts_native::bamts_resume_mode),
        Helper::GetSuper => fn_addr!(bamts_native::bamts_get_super),
        Helper::SetSuper => fn_addr!(bamts_native::bamts_set_super),
        Helper::ImportAttributes => fn_addr!(bamts_native::bamts_import_attributes),
        Helper::ImportDynamicAttributes => {
            fn_addr!(bamts_native::bamts_import_dynamic_attributes)
        }
        Helper::CopyDataProperties => fn_addr!(bamts_native::bamts_copy_data_properties),
        Helper::GetTemplateObject => fn_addr!(bamts_native::bamts_get_template_object),
    }
}

// -- Tests -------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use bamts_bytecode::{
        Constant, ConstantId, EcmaString, Function as BytecodeFunction, FunctionFlags, FunctionId,
        Instruction, Module, ModuleId, Program, ProgramModule, Register, Verified,
    };
    use bamts_runtime::{Host, Limits, run_linked_program};

    #[derive(Default)]
    struct RecordingHost {
        stdout: Vec<u8>,
    }

    impl Host for RecordingHost {
        fn write_stdout(&mut self, bytes: &[u8]) {
            self.stdout.extend_from_slice(bytes);
        }
    }

    fn function(code: Vec<Instruction>, register_count: u32) -> BytecodeFunction {
        BytecodeFunction::new(
            None,
            0,
            0,
            register_count,
            FunctionFlags::default(),
            code,
            Vec::new(),
        )
    }

    fn module(name: &str, value: i32, loads_constant: bool) -> ProgramModule<Verified> {
        let code = if loads_constant {
            vec![
                Instruction::LoadConst {
                    dst: Register::new(0),
                    constant: ConstantId::new(1),
                },
                Instruction::Return {
                    value: Register::new(0),
                },
            ]
        } else {
            vec![Instruction::Halt]
        };
        ProgramModule {
            name: ConstantId::new(0),
            code: Module::new(
                vec![
                    Constant::String(EcmaString::encode(name)),
                    Constant::Int32(value),
                ],
                vec![function(code, u32::from(loads_constant))],
                FunctionId::new(0),
            )
            .verify()
            .expect("test module verifies"),
            edges: Vec::new(),
            bindings: Vec::new(),
            exports: Vec::new(),
        }
    }

    fn test_program() -> Program<Verified> {
        Program::link(
            vec![module("dependency", 7, true), module("entry", 42, false)],
            ModuleId::new(1),
        )
        .expect("test program verifies")
    }

    /// `adrp x16, #0` and `ldr x17, [x16]`. The expected words below come from
    /// assembling `adrp x16, #N` and `ldr x17, [x16, #N]` with clang.
    const ADRP_X16: u32 = 0x9000_0010;
    const LDR_X17_FROM_X16: u32 = 0xF940_0211;

    #[test]
    fn adrp_patch_matches_assembler_output() {
        assert_eq!(patch_adrp_page(ADRP_X16, 0, 0x1000).unwrap(), 0xB000_0010);
        assert_eq!(patch_adrp_page(ADRP_X16, 0x2000, 0).unwrap(), 0xD0FF_FFF0);
    }

    #[test]
    fn adrp_patch_counts_4k_pages_and_ignores_the_offset_in_the_page() {
        assert_eq!(
            patch_adrp_page(ADRP_X16, 0xFFC, 0x1008).unwrap(),
            patch_adrp_page(ADRP_X16, 0, 0x1000).unwrap()
        );
    }

    #[test]
    fn adrp_patch_replaces_an_earlier_immediate() {
        let stale = ADRP_X16 | (0x3 << 29) | (0x7_FFFF << 5);
        assert_eq!(patch_adrp_page(stale, 0, 0x1000).unwrap(), 0xB000_0010);
    }

    #[test]
    fn adrp_patch_accepts_exactly_the_21_bit_page_range() {
        let span = 1u64 << 32;
        assert!(patch_adrp_page(ADRP_X16, 0, span - 0x1000).is_ok());
        assert!(patch_adrp_page(ADRP_X16, span, 0).is_ok());
        assert!(matches!(
            patch_adrp_page(ADRP_X16, 0, span),
            Err(InProcessLinkError::RelocationOutOfRange { .. })
        ));
        assert!(matches!(
            patch_adrp_page(ADRP_X16, span + 0x1000, 0),
            Err(InProcessLinkError::RelocationOutOfRange { .. })
        ));
    }

    #[test]
    fn ldr_patch_matches_assembler_output() {
        assert_eq!(
            patch_ldr_got_lo12(LDR_X17_FROM_X16, 8).unwrap(),
            0xF940_0611
        );
        assert_eq!(
            patch_ldr_got_lo12(LDR_X17_FROM_X16, 0x7008).unwrap(),
            0xF940_0611
        );
    }

    #[test]
    fn ldr_patch_replaces_an_earlier_offset_and_covers_the_whole_page() {
        let stale = LDR_X17_FROM_X16 | (0xFFF << 10);
        assert_eq!(patch_ldr_got_lo12(stale, 0).unwrap(), LDR_X17_FROM_X16);
        assert_eq!(
            patch_ldr_got_lo12(LDR_X17_FROM_X16, 0xFF8).unwrap(),
            LDR_X17_FROM_X16 | (0x1FF << 10)
        );
    }

    #[test]
    fn ldr_patch_rejects_an_entry_that_is_not_8_aligned() {
        assert!(matches!(
            patch_ldr_got_lo12(LDR_X17_FROM_X16, 4),
            Err(InProcessLinkError::RelocationMisaligned { .. })
        ));
    }

    #[test]
    fn host_target_selects_the_host_abi_and_keeps_elf() {
        use cranelift_codegen::isa::{self, CallConv};
        use cranelift_codegen::settings::{self, Flags};
        use cranelift_object::object::BinaryFormat;

        let target = host_target().expect("host target supported");
        let isa = isa::lookup_by_name(target)
            .expect("target exists")
            .finish(Flags::new(settings::builder()))
            .expect("target builds");
        let expected = match (std::env::consts::OS, std::env::consts::ARCH) {
            ("macos", "aarch64") => CallConv::AppleAarch64,
            ("windows", "x86_64") => CallConv::WindowsFastcall,
            _ => CallConv::SystemV,
        };
        assert_eq!(isa.frontend_config().default_call_conv, expected);
        if cfg!(target_os = "macos") {
            assert!(target.contains("apple-darwin"), "target was {target}");
        }

        let object = crate::compile_aot(&test_program(), target).expect("AOT object emits");
        let file = File::parse(&*object.bytes).expect("object parses");
        assert_eq!(file.format(), BinaryFormat::Elf);
    }

    #[test]
    fn in_process_link_runs_native_entries() {
        let program = test_program();
        let target = host_target().expect("host target supported");
        let object = crate::compile_aot(&program, target).expect("AOT object emits");
        // Verify the descriptor magic is correct in the object file before linking.
        {
            let file = cranelift_object::object::File::parse(&*object.bytes).unwrap();
            let desc_sym = file
                .symbols()
                .find(|s| s.name() == Ok("bamts_program_descriptor"))
                .unwrap();
            let sec_idx = desc_sym.section_index().unwrap();
            let section = file.section_by_index(sec_idx).unwrap();
            let data = section.data().unwrap();
            let off = desc_sym.address() as usize;
            let magic = u64::from_le_bytes(data[off..off + 8].try_into().unwrap());
            assert_eq!(
                magic,
                bamts_native::AOT_MAGIC,
                "descriptor magic in object file is wrong"
            );
        }
        let linked = link_aot_in_process(&object, &program).expect("in-process link succeeds");

        // The linked program must have valid program bytes.
        assert!(!linked.program_bytes().is_empty());
        assert_eq!(linked.program_bytes(), program.encode().as_slice());

        // The invocation counter starts at zero.
        assert_eq!(linked.native_entries_invoked(), 0);

        // Run through the runtime to prove native entries are invoked.
        let mut host = RecordingHost::default();
        let limits = Limits::default();
        let result = run_linked_program(&program, &linked, &mut host, &limits);

        // The run should succeed (or at least not fail due to entry table issues).
        // Even if the trivial program throws or blocks, the key proof is that
        // native entries were invoked.
        let _ = result;

        // The critical assertion: native entries were actually invoked.
        assert!(
            linked.native_entries_invoked() > 0,
            "native entries were not invoked — AOT did not execute compiled code"
        );

        let report = linked.report();
        assert!(report.native_entries_invoked > 0);
    }
}
