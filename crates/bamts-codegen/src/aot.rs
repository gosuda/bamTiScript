//! Ahead-of-time object emission for verified BamTS bytecode.

use std::error::Error;
use std::fmt;

use bamts_bytecode::{Program as BytecodeProgram, Verified};
use bamts_cancel::{CancellationToken, Cancelled};
use cranelift_codegen::Context;
use cranelift_codegen::ir::{ExternalName, Function, UserExternalName};
use cranelift_codegen::isa;
use cranelift_codegen::settings::{self, Configurable, Flags};
use cranelift_module::{DataDescription, FuncId, Linkage, Module, default_libcall_names};
use cranelift_object::{ObjectBuilder, ObjectModule};

use crate::{
    HELPER_NAMESPACE, Helper, LowerError, LoweredProgram, ProgramLowerError, function_symbol,
    lower_program_with_cancel,
};

mod emission;
// Mapping a linked image into executable memory is the `host-jit` tier's
// capability; `aot` alone only emits objects for an external linker.
#[cfg(feature = "host-jit")]
#[allow(unsafe_code)]
mod in_process_link;
mod linking;
mod reproducible;

#[cfg(feature = "host-jit")]
pub use in_process_link::{
    HostTargetError, LinkedAotProgram, NativeExecutionReport, host_target, link_aot_in_process,
};

pub use emission::{
    EmissionError, EmittedObject, SUPPORTED_TARGET_TRIPLES, TargetDescriptor, content_digest,
    emit_for_target, emit_for_target_with_cancel, emit_for_targets, require_matching_target,
};
pub use linking::{
    LinkCacheKey, LinkError, LinkFlags, LinkInput, LinkInputRole, LinkPlan, LinkProvenance,
    TargetFormat, plan_link, resolve_symbols, validate_linked_image,
};
pub use reproducible::{
    BuildCacheKey, REPRODUCIBLE_FILE_NAME, ReproducibleArtifact, ReproducibleError,
    canonical_object_metadata, emit_reproducible,
};

const HELPER_COUNT: u32 = bamts_native::HELPER_COUNT;
const AOT_MAGIC: u64 = u64::from_le_bytes(*b"BMTSAOT1");
const AOT_ABI_VERSION: u32 = 4;
const UNIT_DESCRIPTOR_BYTES: usize = 16;
const PROGRAM_DESCRIPTOR_BYTES: usize = 56;

const BYTECODE_SYMBOL: &str = "bamts_bytecode_blob";
const UNITS_SYMBOL: &str = "bamts_unit_descriptors";
/// The exported descriptor symbol consumed by `bamts-native`.
pub const PROGRAM_DESCRIPTOR_SYMBOL: &str = "bamts_program_descriptor";

/// An emitted AOT object and the information a linker driver needs to consume it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AotObject {
    /// Relocatable object-file bytes. This crate never invokes a linker.
    pub bytes: Vec<u8>,
    /// The normalized target triple recorded by Cranelift.
    pub target: String,
    /// Exported descriptor symbol that roots the embedded program image.
    pub descriptor_symbol: &'static str,
    /// Canonical module id of the program entry.
    pub entry_module: u32,
    /// Bytecode function id local to `entry_module`.
    pub entry_function: u32,
    /// Native symbol implementing `entry_function`.
    pub entry_symbol: String,
    /// Runtime helper symbols referenced by the emitted functions, in ABI order.
    pub required_helpers: Vec<&'static str>,
}

/// A typed AOT-emission failure.
#[derive(Debug)]
pub enum AotError {
    /// Cranelift does not support the requested target name.
    TargetLookup(String),
    /// The target ISA could not be configured.
    TargetBuild(String),
    /// The target does not expose a usable byte order.
    TargetEndianness(String),
    /// Shared program lowering failed.
    Lower(ProgramLowerError),
    /// The lowered module violated a backend invariant.
    InvalidLoweredModule(String),
    /// A Cranelift module declaration or definition failed.
    Module(String),
    /// Serializing the completed object failed.
    Emit(String),
    /// A caller-supplied cancellation token was triggered at a checkpoint.
    Cancelled,
}

impl From<Cancelled> for AotError {
    fn from(_: Cancelled) -> Self {
        Self::Cancelled
    }
}

impl fmt::Display for AotError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TargetLookup(message) => write!(f, "unsupported AOT target: {message}"),
            Self::TargetBuild(message) => write!(f, "could not configure AOT target: {message}"),
            Self::TargetEndianness(target) => {
                write!(f, "AOT target has no known byte order: {target}")
            }
            Self::Lower(error) => write!(f, "AOT lowering failed: {error}"),
            Self::InvalidLoweredModule(message) => {
                write!(f, "invalid lowered module for AOT emission: {message}")
            }
            Self::Module(message) => write!(f, "AOT object definition failed: {message}"),
            Self::Emit(message) => write!(f, "AOT object serialization failed: {message}"),
            Self::Cancelled => f.write_str("operation cancelled"),
        }
    }
}

impl Error for AotError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Lower(error) => Some(error),
            _ => None,
        }
    }
}

impl From<ProgramLowerError> for AotError {
    fn from(error: ProgramLowerError) -> Self {
        Self::Lower(error)
    }
}

fn require_64_bit_pointer_width(bits: u8) -> Result<(), LowerError> {
    if bits != 64 {
        Err(LowerError::UnsupportedPointerWidth { bits })
    } else {
        Ok(())
    }
}

/// Compiles every module of one verified canonical program into one relocatable
/// object for `target`. Module-local pools and ids remain module-local.
///
/// The object contains every lowered function, the canonical bytecode encoding,
/// a `UnitDescriptor` record for every function, and the exported
/// `bamts_program_descriptor`. Runtime helpers remain ordinary undefined
/// symbols for the final linker to resolve; no linker is invoked here.
///
/// This is a convenience wrapper that uses a fresh, never-cancelled token; for
/// cancellation support use [`compile_aot_with_cancel`].
///
/// # Errors
///
/// Returns [`AotError`] when the target is unsupported, lowering fails, the
/// object module rejects a declaration or definition, or object serialization
/// fails.
pub fn compile_aot(
    bytecode: &BytecodeProgram<Verified>,
    target: &str,
) -> Result<AotObject, AotError> {
    compile_aot_with_cancel(bytecode, target, &CancellationToken::new())
}

/// [`compile_aot`] with cooperative cancellation.
///
/// Cancellation is checked at the entry, after lowering, before/after every
/// Cranelift `declare_function`/`define_function`/`define_data`/`finish`/`emit`
/// call, and per lowered function/data item.
pub fn compile_aot_with_cancel(
    bytecode: &BytecodeProgram<Verified>,
    target: &str,
    cancel: &CancellationToken,
) -> Result<AotObject, AotError> {
    cancel.check()?;
    let mut flag_builder = settings::builder();
    flag_builder
        .set("is_pic", "true")
        .map_err(|error| AotError::TargetBuild(error.to_string()))?;
    let flags = Flags::new(flag_builder);
    let isa_builder =
        isa::lookup_by_name(target).map_err(|error| AotError::TargetLookup(error.to_string()))?;
    cancel.check()?;
    let isa = isa_builder
        .finish(flags)
        .map_err(|error| AotError::TargetBuild(error.to_string()))?;
    require_64_bit_pointer_width(isa.frontend_config().pointer_bits()).map_err(|kind| {
        AotError::Lower(ProgramLowerError {
            module: bamts_bytecode::ModuleId::new(0),
            kind,
        })
    })?;
    cancel.check()?;
    let target_endianness = isa
        .triple()
        .endianness()
        .map_err(|()| AotError::TargetEndianness(isa.triple().to_string()))?;
    let little_endianness = isa::lookup_by_name("x86_64")
        .expect("the all-native-arch build includes x86-64")
        .triple()
        .endianness()
        .expect("x86-64 has a defined byte order");
    let little_endian = target_endianness == little_endianness;
    let lowered = lower_program_with_cancel(bytecode, isa.frontend_config(), cancel)?;
    crate::validate_lowered_program(&lowered)
        .map_err(|error| AotError::InvalidLoweredModule(error.to_string()))?;
    let normalized_target = isa.triple().to_string();
    let call_conv = isa.frontend_config().default_call_conv;
    cancel.check()?;
    let builder = ObjectBuilder::new(isa, "bamts", default_libcall_names())
        .map_err(|error| AotError::Module(error.to_string()))?;
    let mut object = ObjectModule::new(builder);

    let function_ids = declare_functions(&mut object, &lowered, cancel)?;
    let helper_ids = declare_helpers(&mut object, call_conv, cancel)?;
    define_functions(&mut object, &lowered, &function_ids, &helper_ids, cancel)?;
    define_program_data(
        &mut object,
        &lowered,
        &function_ids,
        bytecode.encode(),
        little_endian,
        cancel,
    )?;

    let required_helpers = (0..HELPER_COUNT)
        .filter_map(Helper::from_external_index)
        .filter(|helper| {
            lowered.modules.iter().any(|module| {
                module
                    .functions
                    .iter()
                    .any(|function| function.helpers.contains(helper))
            })
        })
        .map(Helper::symbol)
        .collect();
    let entry_module = lowered.entry_module.get();
    let entry_function = lowered.entry_function.get();
    cancel.check()?;
    let finished = object.finish();
    cancel.check()?;
    let bytes = finished
        .emit()
        .map_err(|error| AotError::Emit(error.to_string()))?;
    cancel.check()?;

    Ok(AotObject {
        bytes,
        target: normalized_target,
        descriptor_symbol: PROGRAM_DESCRIPTOR_SYMBOL,
        entry_module,
        entry_function,
        entry_symbol: function_symbol(entry_module, entry_function),
        required_helpers,
    })
}

struct DeclaredUnit {
    module_id: u32,
    function_id: u32,
    function: FuncId,
}

fn declare_functions(
    object: &mut ObjectModule,
    lowered: &LoweredProgram,
    cancel: &CancellationToken,
) -> Result<Vec<DeclaredUnit>, AotError> {
    let function_count = lowered
        .modules
        .iter()
        .map(|module| module.functions.len())
        .sum();
    let mut units = Vec::with_capacity(function_count);
    for module in &lowered.modules {
        cancel.check()?;
        for function in &module.functions {
            cancel.check()?;
            let func_id = object
                .declare_function(&function.symbol, Linkage::Export, &function.signature)
                .map_err(|error| AotError::Module(error.to_string()))?;
            cancel.check()?;
            units.push(DeclaredUnit {
                module_id: module.id.get(),
                function_id: function.id.get(),
                function: func_id,
            });
        }
    }
    Ok(units)
}

fn declare_helpers(
    object: &mut ObjectModule,
    call_conv: cranelift_codegen::isa::CallConv,
    cancel: &CancellationToken,
) -> Result<Vec<FuncId>, AotError> {
    let mut helpers = Vec::with_capacity(HELPER_COUNT as usize);
    for index in 0..HELPER_COUNT {
        cancel.check()?;
        let helper = Helper::from_external_index(index).ok_or_else(|| {
            AotError::InvalidLoweredModule(format!("missing helper ABI index {index}"))
        })?;
        cancel.check()?;
        let func_id = object
            .declare_function(
                helper.symbol(),
                Linkage::Import,
                &helper.signature(call_conv),
            )
            .map_err(|error| AotError::Module(error.to_string()))?;
        cancel.check()?;
        helpers.push(func_id);
    }
    Ok(helpers)
}

fn define_functions(
    object: &mut ObjectModule,
    lowered: &LoweredProgram,
    units: &[DeclaredUnit],
    helper_ids: &[FuncId],
    cancel: &CancellationToken,
) -> Result<(), AotError> {
    let mut declared_functions = std::collections::HashMap::with_capacity(units.len());
    for unit in units {
        declared_functions.insert((unit.module_id, unit.function_id), unit.function);
    }

    for module in &lowered.modules {
        cancel.check()?;
        for lowered_function in &module.functions {
            cancel.check()?;
            let declared = declared_functions
                .get(&(module.id.get(), lowered_function.id.get()))
                .copied()
                .ok_or_else(|| {
                    AotError::InvalidLoweredModule(format!(
                        "missing declaration for module {} function {}",
                        module.id.get(),
                        lowered_function.id.get()
                    ))
                })?;
            let mut function = lowered_function.clif.clone();
            remap_helper_names(&mut function, helper_ids)?;
            let mut context = Context::for_function(function);
            cancel.check()?;
            object
                .define_function(declared, &mut context)
                .map_err(|error| AotError::Module(error.to_string()))?;
            cancel.check()?;
        }
    }
    Ok(())
}

fn remap_helper_names(function: &mut Function, helper_ids: &[FuncId]) -> Result<(), AotError> {
    let external_functions: Vec<_> = function.dfg.ext_funcs.keys().collect();
    for function_ref in external_functions {
        let ExternalName::User(name_ref) = function.dfg.ext_funcs[function_ref].name else {
            continue;
        };
        let name = &function.params.user_named_funcs()[name_ref];
        if name.namespace != HELPER_NAMESPACE {
            continue;
        }
        let helper_id = helper_ids.get(name.index as usize).ok_or_else(|| {
            AotError::InvalidLoweredModule(format!(
                "function references unknown helper index {}",
                name.index
            ))
        })?;
        let replacement = function.declare_imported_user_function(UserExternalName {
            namespace: 0,
            index: helper_id.as_u32(),
        });
        function.dfg.ext_funcs[function_ref].name = ExternalName::user(replacement);
    }
    Ok(())
}

fn define_program_data(
    object: &mut ObjectModule,
    lowered: &LoweredProgram,
    function_ids: &[DeclaredUnit],
    bytecode: Vec<u8>,
    little_endian: bool,
    cancel: &CancellationToken,
) -> Result<(), AotError> {
    let unit_bytes = function_ids
        .len()
        .checked_mul(UNIT_DESCRIPTOR_BYTES)
        .ok_or_else(|| AotError::InvalidLoweredModule("unit table size overflow".to_string()))?;
    if unit_bytes > u32::MAX as usize {
        return Err(AotError::InvalidLoweredModule(
            "unit table exceeds the relocation offset range".to_string(),
        ));
    }

    cancel.check()?;
    let bytecode_id = object
        .declare_data(BYTECODE_SYMBOL, Linkage::Local, false, false)
        .map_err(|error| AotError::Module(error.to_string()))?;
    let mut bytecode_data = DataDescription::new();
    bytecode_data.define(bytecode.into_boxed_slice());
    bytecode_data.set_align(1);
    cancel.check()?;
    object
        .define_data(bytecode_id, &bytecode_data)
        .map_err(|error| AotError::Module(error.to_string()))?;
    cancel.check()?;

    let units_id = object
        .declare_data(UNITS_SYMBOL, Linkage::Local, false, false)
        .map_err(|error| AotError::Module(error.to_string()))?;
    let mut unit_contents = vec![0; unit_bytes];
    for (index, unit) in function_ids.iter().enumerate() {
        let offset = index * UNIT_DESCRIPTOR_BYTES;
        write_u32(&mut unit_contents, offset, unit.function_id, little_endian);
        write_u32(
            &mut unit_contents,
            offset + 4,
            unit.module_id,
            little_endian,
        );
    }
    let mut units_data = DataDescription::new();
    units_data.define(unit_contents.into_boxed_slice());
    units_data.set_align(8);
    for (index, unit) in function_ids.iter().enumerate() {
        let function_ref = object.declare_func_in_data(unit.function, &mut units_data);
        units_data.write_function_addr((index * UNIT_DESCRIPTOR_BYTES + 8) as u32, function_ref);
    }
    cancel.check()?;
    object
        .define_data(units_id, &units_data)
        .map_err(|error| AotError::Module(error.to_string()))?;
    cancel.check()?;

    let descriptor_id = object
        .declare_data(PROGRAM_DESCRIPTOR_SYMBOL, Linkage::Export, false, false)
        .map_err(|error| AotError::Module(error.to_string()))?;
    let mut descriptor = vec![0; PROGRAM_DESCRIPTOR_BYTES];
    write_u64(&mut descriptor, 0, AOT_MAGIC, little_endian);
    write_u32(&mut descriptor, 8, AOT_ABI_VERSION, little_endian);
    write_u64(
        &mut descriptor,
        24,
        bytecode_data.init.size() as u64,
        little_endian,
    );
    write_u64(
        &mut descriptor,
        40,
        function_ids.len() as u64,
        little_endian,
    );
    write_u32(
        &mut descriptor,
        48,
        lowered.entry_function.get(),
        little_endian,
    );
    write_u32(
        &mut descriptor,
        52,
        lowered.entry_module.get(),
        little_endian,
    );

    let mut descriptor_data = DataDescription::new();
    descriptor_data.define(descriptor.into_boxed_slice());
    descriptor_data.set_align(8);
    descriptor_data.set_used(true);
    let bytecode_ref = object.declare_data_in_data(bytecode_id, &mut descriptor_data);
    descriptor_data.write_data_addr(16, bytecode_ref, 0);
    let units_ref = object.declare_data_in_data(units_id, &mut descriptor_data);
    descriptor_data.write_data_addr(32, units_ref, 0);
    cancel.check()?;
    object
        .define_data(descriptor_id, &descriptor_data)
        .map_err(|error| AotError::Module(error.to_string()))
}

fn write_u32(bytes: &mut [u8], offset: usize, value: u32, little_endian: bool) {
    let encoded = if little_endian {
        value.to_le_bytes()
    } else {
        value.to_be_bytes()
    };
    bytes[offset..offset + encoded.len()].copy_from_slice(&encoded);
}

fn write_u64(bytes: &mut [u8], offset: usize, value: u64, little_endian: bool) {
    let encoded = if little_endian {
        value.to_le_bytes()
    } else {
        value.to_be_bytes()
    };
    bytes[offset..offset + encoded.len()].copy_from_slice(&encoded);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower_program;
    use bamts_bytecode::{
        Constant, ConstantId, EcmaString, Function as BytecodeFunction, FunctionFlags, FunctionId,
        Instruction, Module, ModuleId, Program, ProgramDecodeLimits, ProgramModule, Register,
        decode_verified_program,
    };
    use cranelift_object::object::{
        Object, ObjectSection, ObjectSymbol, RelocationKind, RelocationTarget, SectionKind,
        SymbolIndex,
    };

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

    /// Mirrors `host_target`, which needs the `host-jit` feature these tests
    /// do not enable: the triple picks the host ABI and the container stays ELF.
    fn target() -> &'static str {
        match (std::env::consts::OS, std::env::consts::ARCH) {
            ("macos", "aarch64") => "aarch64-apple-darwin-elf",
            ("macos", "x86_64") => "x86_64-apple-darwin-elf",
            ("windows", "x86_64") => "x86_64-pc-windows-msvc-elf",
            (_, "x86_64") => "x86_64-unknown-linux-gnu",
            (_, "aarch64") => "aarch64-unknown-linux-gnu",
            _ => panic!("AOT object test needs a supported 64-bit host architecture"),
        }
    }

    fn symbol_bytes<'a>(
        file: &'a cranelift_object::object::File<'a>,
        symbol_name: &str,
    ) -> (&'a [u8], SymbolIndex) {
        let symbol = file
            .symbols()
            .find(|symbol| symbol.name() == Ok(symbol_name))
            .unwrap_or_else(|| panic!("missing symbol {symbol_name}"));
        let section_index = symbol.section_index().expect("defined symbol section");
        let section = file
            .section_by_index(section_index)
            .expect("symbol section");
        let section_data = section.data().expect("section data");
        let start = usize::try_from(symbol.address() - section.address()).expect("symbol offset");
        let size = usize::try_from(symbol.size()).expect("symbol size");
        (&section_data[start..start + size], symbol.index())
    }

    fn relocation_targets(
        file: &cranelift_object::object::File<'_>,
        owner: SymbolIndex,
    ) -> Vec<String> {
        let owner = file.symbol_by_index(owner).expect("owner symbol");
        let section = file
            .section_by_index(owner.section_index().expect("owner section"))
            .expect("owner section data");
        let start = owner.address() - section.address();
        let end = start + owner.size();
        section
            .relocations()
            .filter(|(offset, _)| (start..end).contains(offset))
            .filter_map(|(_, relocation)| match relocation.target() {
                RelocationTarget::Symbol(index) => file
                    .symbol_by_index(index)
                    .ok()
                    .and_then(|symbol| symbol.name().ok())
                    .map(str::to_owned),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn emits_two_module_tuple_units_and_canonical_program() {
        let program = test_program();
        let canonical = program.encode();
        let emitted = compile_aot(&program, target()).expect("AOT object emits");
        let file = cranelift_object::object::File::parse(&*emitted.bytes).expect("object parses");

        let (descriptor, descriptor_index) = symbol_bytes(&file, PROGRAM_DESCRIPTOR_SYMBOL);
        assert_eq!(descriptor.len(), PROGRAM_DESCRIPTOR_BYTES);
        assert_eq!(&descriptor[0..8], b"BMTSAOT1");
        assert_eq!(u32::from_le_bytes(descriptor[8..12].try_into().unwrap()), 4);
        assert_eq!(
            u64::from_le_bytes(descriptor[24..32].try_into().unwrap()),
            canonical.len() as u64
        );
        assert_eq!(
            u64::from_le_bytes(descriptor[40..48].try_into().unwrap()),
            2
        );
        assert_eq!(
            u32::from_le_bytes(descriptor[48..52].try_into().unwrap()),
            0
        );
        assert_eq!(
            u32::from_le_bytes(descriptor[52..56].try_into().unwrap()),
            1
        );
        assert_eq!(
            relocation_targets(&file, descriptor_index),
            [BYTECODE_SYMBOL.to_string(), UNITS_SYMBOL.to_string()]
        );

        let (embedded, _) = symbol_bytes(&file, BYTECODE_SYMBOL);
        assert_eq!(embedded, canonical);
        let decoded = decode_verified_program(embedded, &ProgramDecodeLimits::default())
            .expect("embedded canonical program decodes");
        assert_eq!(decoded, program);
        assert_eq!(decoded.encode(), embedded);

        let (units, units_index) = symbol_bytes(&file, UNITS_SYMBOL);
        assert_eq!(units.len(), 2 * UNIT_DESCRIPTOR_BYTES);
        assert_eq!(u32::from_le_bytes(units[0..4].try_into().unwrap()), 0);
        assert_eq!(u32::from_le_bytes(units[4..8].try_into().unwrap()), 0);
        assert_eq!(u32::from_le_bytes(units[16..20].try_into().unwrap()), 0);
        assert_eq!(u32::from_le_bytes(units[20..24].try_into().unwrap()), 1);
        assert_eq!(
            relocation_targets(&file, units_index),
            [function_symbol(0, 0), function_symbol(1, 0)]
        );
        assert!(file.symbols().any(|symbol| {
            symbol.name() == Ok(emitted.entry_symbol.as_str()) && !symbol.is_undefined()
        }));
        assert_eq!(
            emitted.required_helpers,
            [Helper::LoadConstant.symbol(), Helper::ConsumeFuel.symbol()]
        );
        assert!(file.symbols().any(|symbol| {
            symbol.name() == Ok(Helper::ConsumeFuel.symbol()) && symbol.is_undefined()
        }));
        assert_eq!((emitted.entry_module, emitted.entry_function), (1, 0));
        assert_eq!(emitted.entry_symbol, function_symbol(1, 0));
    }

    #[test]
    fn executable_sections_have_no_absolute_relocations() {
        let emitted = compile_aot(&test_program(), target()).expect("AOT object emits");
        let file = cranelift_object::object::File::parse(&*emitted.bytes).expect("object parses");
        for section in file
            .sections()
            .filter(|section| section.kind() == SectionKind::Text)
        {
            for (offset, relocation) in section.relocations() {
                assert_ne!(
                    relocation.kind(),
                    RelocationKind::Absolute,
                    "absolute relocation at {offset:#x} in executable section"
                );
            }
        }
    }

    #[test]
    fn object_emission_is_deterministic() {
        let program = test_program();
        let first = compile_aot(&program, target()).expect("first AOT object emits");
        let second = compile_aot(&program, target()).expect("second AOT object emits");
        assert_eq!(first, second);
    }

    #[test]
    fn define_functions_rejects_mismatched_declared_identity() {
        let flags = Flags::new(settings::builder());
        let isa = isa::lookup_by_name(target())
            .expect("test target exists")
            .finish(flags)
            .expect("test target builds");
        let call_conv = isa.frontend_config().default_call_conv;
        let program = test_program();
        let mut lowered = lower_program(&program, isa.frontend_config()).expect("program lowers");
        let builder = ObjectBuilder::new(isa, "bamts-test", default_libcall_names())
            .expect("object builder constructs");
        let mut object = ObjectModule::new(builder);
        let cancel = CancellationToken::new();
        let units = declare_functions(&mut object, &lowered, &cancel).expect("functions declare");
        let helpers = declare_helpers(&mut object, call_conv, &cancel).expect("helpers declare");
        lowered.modules[0].functions[0].id = FunctionId::new(1);

        assert!(matches!(
            define_functions(&mut object, &lowered, &units, &helpers, &cancel),
            Err(AotError::InvalidLoweredModule(message))
                if message.contains("missing declaration for module 0 function 1")
        ));
    }

    #[test]
    fn require_64_bit_pointer_width_rejects_32() {
        assert!(matches!(
            require_64_bit_pointer_width(32),
            Err(LowerError::UnsupportedPointerWidth { bits: 32 })
        ));
    }

    #[test]
    fn require_64_bit_pointer_width_accepts_64() {
        assert!(require_64_bit_pointer_width(64).is_ok());
    }

    #[test]
    fn compile_aot_rejects_i686_without_panic() {
        let error = compile_aot(&test_program(), "i686-unknown-linux-gnu")
            .expect_err("i686 AOT target is rejected");
        assert!(matches!(error, AotError::TargetLookup(_)));
    }

    #[test]
    fn pre_cancelled_token_aborts_compile_aot() {
        let cancel = bamts_cancel::CancellationToken::new();
        cancel.cancel();
        let result = compile_aot_with_cancel(&test_program(), target(), &cancel);
        assert!(matches!(result, Err(AotError::Cancelled)));
    }
}
