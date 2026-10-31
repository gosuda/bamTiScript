//! Host-native Cranelift JIT backend.

use std::error::Error;
use std::fmt;
use std::time::Instant;

use bamts_bytecode::{Program as BytecodeProgram, Verified};
use bamts_cancel::{CancellationToken, Cancelled};
use bamts_native::{
    AbiError, Completion, CompletionTag, JitEntry, NativeEntryTable, NativeHelper, ShadowFrame,
    require_frame_module_id,
};
use cranelift_codegen::Context;
use cranelift_codegen::ir::{ExternalName, Function, UserExternalName};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module, ModuleError, default_libcall_names};

use crate::jit_memory::{FinalizedMemory, WxByteTotals, WxMemoryHandle, WxMemoryProvider};
use crate::{
    HELPER_NAMESPACE, Helper, LoweredProgram, ProgramLowerError, lower_program_with_cancel,
};

/// A typed host-JIT compilation failure.
#[derive(Debug)]
pub enum JitError {
    /// Backend-neutral program lowering failed.
    Lower(ProgramLowerError),
    /// The lowered program violated the canonical module/function identity order.
    InvalidLoweredModule(String),
    /// Cranelift could not declare, compile, or finalize the module.
    Module(Box<ModuleError>),
    /// Lowered IR named a runtime helper not present in the runtime helper table.
    UnknownHelper { index: u32 },
    /// A caller-supplied cancellation token was triggered at a checkpoint.
    Cancelled,
}

impl fmt::Display for JitError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            JitError::Lower(error) => write!(
                formatter,
                "could not lower program for the host JIT: {error}"
            ),
            JitError::InvalidLoweredModule(message) => {
                write!(formatter, "invalid lowered module for host JIT: {message}")
            }
            JitError::Module(error) => write!(formatter, "host JIT compilation failed: {error}"),
            JitError::UnknownHelper { index } => {
                write!(
                    formatter,
                    "lowered IR imports unknown runtime helper u1:{index}"
                )
            }
            JitError::Cancelled => formatter.write_str("operation cancelled"),
        }
    }
}

impl From<Cancelled> for JitError {
    fn from(_: Cancelled) -> Self {
        Self::Cancelled
    }
}

impl Error for JitError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            JitError::Lower(error) => Some(error),
            JitError::InvalidLoweredModule(_)
            | JitError::UnknownHelper { .. }
            | JitError::Cancelled => None,
            JitError::Module(error) => Some(error.as_ref()),
        }
    }
}

impl From<ProgramLowerError> for JitError {
    fn from(error: ProgramLowerError) -> Self {
        JitError::Lower(error)
    }
}

impl From<ModuleError> for JitError {
    fn from(error: ModuleError) -> Self {
        JitError::Module(Box::new(error))
    }
}

/// One module-qualified native entry in tuple order.
struct JitUnit {
    module_id: u32,
    function_id: u32,
    function: FuncId,
}

/// A finalized host-native program. It owns its [`JITModule`] *and* the
/// `FinalizedMemory` receipt proving every owned mapping reached its exact
/// final protection. Entries are callable only through [`NativeEntryTable`],
/// reached through the receipt-owning program; its module remains private.
pub struct JitProgram {
    module: JITModule,
    /// Proof that every mapping finalized before this program was published.
    _memory: FinalizedMemory,
    functions: Vec<JitUnit>,
    program_bytes: Vec<u8>,
    entry_module: u32,
    entry_function: u32,
}

impl JitProgram {
    /// The canonical module id used as the program entry.
    #[must_use]
    pub const fn entry_module(&self) -> u32 {
        self.entry_module
    }

    /// The bytecode function id local to the entry module.
    #[must_use]
    pub const fn entry_function(&self) -> u32 {
        self.entry_function
    }
}

impl NativeEntryTable for JitProgram {
    fn program_bytes(&self) -> &[u8] {
        &self.program_bytes
    }

    fn invoke(
        &self,
        module_id: u32,
        function_id: u32,
        frame: &mut ShadowFrame,
        out: &mut Completion,
    ) -> Result<CompletionTag, AbiError> {
        let index = self
            .functions
            .binary_search_by_key(&(module_id, function_id), |entry| {
                (entry.module_id, entry.function_id)
            })
            .map_err(|_| AbiError::UnknownFunction {
                module_id,
                function_id,
            })?;
        let entry = &self.functions[index];
        require_frame_module_id(frame, entry.module_id)?;
        Ok(JitEntry::new(&self.module, entry.function).invoke(frame, out))
    }
}

/// Wall time and W^X memory footprint observed while compiling a program.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct JitTelemetry {
    /// Wall time spent lowering, compiling, and finalizing, in fractional
    /// milliseconds.
    pub jit_compile_wall_ms: f64,
    /// Page-rounded bytes finalized as executable code.
    pub code_bytes: u64,
    /// Page-rounded bytes finalized as read-only data.
    pub readonly_bytes: u64,
    /// Page-rounded bytes kept writable.
    pub readwrite_bytes: u64,
    /// Total page-rounded bytes allocated across every mapping kind.
    pub total_allocated_bytes: u64,
}

/// Lowers, compiles, and finalizes every module of a verified canonical program
/// for the current host. Module-local ids remain local and native entries are
/// keyed by `(module_id, function_id)`.
///
/// This is a convenience wrapper that uses a fresh, never-cancelled token; for
/// cancellation support use [`compile_jit_with_cancel`].
pub fn compile_jit(bytecode: &BytecodeProgram<Verified>) -> Result<JitProgram, JitError> {
    compile_jit_with_telemetry(bytecode).map(|(program, _telemetry)| program)
}

/// [`compile_jit`] plus compile-wall and page-rounded W^X memory telemetry.
///
/// The returned [`JitProgram`] is identical to what [`compile_jit`] produces;
/// the [`JitTelemetry`] times the whole lower/compile/finalize path and reports
/// the page-rounded bytes the W^X provider allocated for each mapping kind.
///
/// This is a convenience wrapper that uses a fresh, never-cancelled token; for
/// cancellation support use [`compile_jit_with_telemetry_cancel`].
pub fn compile_jit_with_telemetry(
    bytecode: &BytecodeProgram<Verified>,
) -> Result<(JitProgram, JitTelemetry), JitError> {
    compile_jit_with_telemetry_cancel(bytecode, &CancellationToken::new())
}

/// [`compile_jit`] with cooperative cancellation.
///
/// Cancellation is checked at the entry, after lowering, before/after every
/// Cranelift `declare_function`/`define_function`/`finalize_definitions` call,
/// and per lowered function/data item.
pub fn compile_jit_with_cancel(
    bytecode: &BytecodeProgram<Verified>,
    cancel: &CancellationToken,
) -> Result<JitProgram, JitError> {
    compile_jit_with_telemetry_cancel(bytecode, cancel).map(|(program, _telemetry)| program)
}

/// [`compile_jit_with_cancel`] plus compile-wall and page-rounded W^X memory
/// telemetry.
pub fn compile_jit_with_telemetry_cancel(
    bytecode: &BytecodeProgram<Verified>,
    cancel: &CancellationToken,
) -> Result<(JitProgram, JitTelemetry), JitError> {
    cancel.check()?;
    let started = Instant::now();
    let (module, memory, program_bytes) = build_module(bytecode, cancel)?;
    let lowered = lower_program_with_cancel(bytecode, module.target_config(), cancel)?;
    // Keep a handle clone so byte totals stay readable after `compile_lowered`
    // consumes its own; both observe the same shared lifecycle counters.
    let memory_view = memory.clone();
    let program = compile_lowered(module, memory, lowered, program_bytes, cancel)?;
    let bytes: WxByteTotals = memory_view.byte_totals();
    let telemetry = JitTelemetry {
        jit_compile_wall_ms: started.elapsed().as_secs_f64() * 1_000.0,
        code_bytes: bytes.code,
        readonly_bytes: bytes.readonly,
        readwrite_bytes: bytes.readwrite,
        total_allocated_bytes: bytes.total(),
    };
    Ok((program, telemetry))
}

/// Builds a `JITModule` with the W^X memory provider installed *before*
/// [`JITModule::new`], and returns the lifecycle handle that mints the
/// publication receipt once finalization completes.
///
/// The handle is held outside the module because `JITModule` consumes the
/// provider: the provider moves into the module and is unreachable afterward,
/// but everything `compile_lowered` needs (the receipt) is observable through
/// the handle.
fn build_module(
    bytecode: &BytecodeProgram<Verified>,
    cancel: &CancellationToken,
) -> Result<(JITModule, WxMemoryHandle, Vec<u8>), JitError> {
    cancel.check()?;
    let program_bytes = bytecode.encode();
    let mut builder = JITBuilder::new(default_libcall_names())?;
    let (provider, memory) = WxMemoryProvider::new();
    // Install the W^X provider before construction so no executable mapping is
    // ever created through the default `SystemMemoryProvider` ceiling.
    builder.memory_provider(Box::new(provider));
    bind_runtime_helpers(&mut builder);
    let module = JITModule::new(builder);
    Ok((module, memory, program_bytes))
}

fn compile_lowered(
    mut module: JITModule,
    memory: WxMemoryHandle,
    lowered: LoweredProgram,
    program_bytes: Vec<u8>,
    cancel: &CancellationToken,
) -> Result<JitProgram, JitError> {
    cancel.check()?;
    let units = crate::validate_lowered_program(&lowered)
        .map_err(|error| JitError::InvalidLoweredModule(error.to_string()))?;
    let mut functions = Vec::with_capacity(units.len());
    let mut declared_functions = std::collections::HashMap::with_capacity(units.len());
    for (module_id, function_id) in units {
        cancel.check()?;
        let function = &lowered.modules[module_id as usize].functions[function_id as usize];
        let declared =
            module.declare_function(&function.symbol, Linkage::Local, &function.signature)?;
        cancel.check()?;
        declared_functions.insert((module_id, function_id), declared);
        functions.push(JitUnit {
            module_id,
            function_id,
            function: declared,
        });
    }

    let call_conv = module.target_config().default_call_conv;
    let mut helpers = Vec::with_capacity(bamts_native::HELPER_COUNT as usize);
    for index in 0..bamts_native::HELPER_COUNT {
        cancel.check()?;
        let helper = Helper::from_external_index(index).ok_or(JitError::UnknownHelper { index })?;
        cancel.check()?;
        helpers.push(module.declare_function(
            helper.symbol(),
            Linkage::Import,
            &helper.signature(call_conv),
        )?);
    }

    for lowered_module in lowered.modules {
        cancel.check()?;
        for function in lowered_module.functions {
            cancel.check()?;
            let declared = declared_functions
                .get(&(lowered_module.id.get(), function.id.get()))
                .copied()
                .ok_or_else(|| {
                    JitError::InvalidLoweredModule(format!(
                        "missing declaration for module {} function {}",
                        lowered_module.id.get(),
                        function.id.get()
                    ))
                })?;
            let mut clif = function.clif;
            rebind_helper_imports(&mut clif, &helpers)?;
            let mut context = Context::for_function(clif);
            cancel.check()?;
            module.define_function(declared, &mut context)?;
            cancel.check()?;
        }
    }
    cancel.check()?;
    module.finalize_definitions()?;
    cancel.check()?;

    // Publication requires the receipt. `finalize_definitions` returned `Ok`, so
    // the provider reached `Executable` only after every owned mapping
    // transitioned to its exact final protection; `require_finalized` is then
    // infallible in practice. No receipt exists in `Writable` or `Freed`, so a
    // partially-finalized module (which errors above) can never publish.
    let receipt = memory.require_finalized();

    Ok(JitProgram {
        module,
        _memory: receipt,
        functions,
        program_bytes,
        entry_module: lowered.entry_module.get(),
        entry_function: lowered.entry_function.get(),
    })
}

fn rebind_helper_imports(clif: &mut Function, helpers: &[FuncId]) -> Result<(), JitError> {
    let imports: Vec<_> = clif
        .dfg
        .ext_funcs
        .iter()
        .filter_map(|(reference, data)| match data.name {
            ExternalName::User(name_ref) => {
                let name = &clif.params.user_named_funcs()[name_ref];
                (name.namespace == HELPER_NAMESPACE).then_some((reference, name.index))
            }
            _ => None,
        })
        .collect();

    for (reference, index) in imports {
        let function = helpers
            .get(index as usize)
            .ok_or(JitError::UnknownHelper { index })?;
        let name = clif.declare_imported_user_function(UserExternalName::new(0, function.as_u32()));
        clif.dfg.ext_funcs[reference].name = ExternalName::user(name);
    }
    Ok(())
}

fn bind_runtime_helpers(builder: &mut JITBuilder) {
    for index in 0..bamts_native::HELPER_COUNT {
        let helper = Helper::from_external_index(index).expect("pinned helper table is dense");
        builder.symbol(helper.symbol(), helper_address(helper));
    }
}

fn helper_address(helper: Helper) -> *const u8 {
    match helper {
        Helper::LoadConstant => bamts_native::bamts_load_constant as *const u8,
        Helper::Unary => bamts_native::bamts_unary as *const u8,
        Helper::Binary => bamts_native::bamts_binary as *const u8,
        Helper::CreateObject => bamts_native::bamts_create_object as *const u8,
        Helper::CreateArray => bamts_native::bamts_create_array as *const u8,
        Helper::CreateCell => bamts_native::bamts_create_cell as *const u8,
        Helper::CreateClosure => bamts_native::bamts_create_closure as *const u8,
        Helper::GetProperty => bamts_native::bamts_get_property as *const u8,
        Helper::SetProperty => bamts_native::bamts_set_property as *const u8,
        Helper::DeleteProperty => bamts_native::bamts_delete_property as *const u8,
        Helper::Call => bamts_native::bamts_call as *const u8,
        Helper::Construct => bamts_native::bamts_construct as *const u8,
        Helper::ConstructWithNewTarget => {
            bamts_native::bamts_construct_with_new_target as *const u8
        }
        Helper::DefineDataProperty => bamts_native::bamts_define_data_property as *const u8,
        Helper::LoadOwnDescriptorSlot => bamts_native::bamts_load_own_descriptor_slot as *const u8,
        Helper::DefineOwnDescriptorSlot => {
            bamts_native::bamts_define_own_descriptor_slot as *const u8
        }
        Helper::WithHasBinding => bamts_native::bamts_with_has_binding as *const u8,
        Helper::Import => bamts_native::bamts_import as *const u8,
        Helper::ImportDynamic => bamts_native::bamts_import_dynamic as *const u8,
        Helper::Truthy => bamts_native::bamts_truthy as *const u8,
        Helper::ResumeValue => bamts_native::bamts_resume_value as *const u8,
        Helper::DefineAccessor => bamts_native::bamts_define_accessor as *const u8,
        Helper::LoadGlobal => bamts_native::bamts_load_global as *const u8,
        Helper::StoreGlobal => bamts_native::bamts_store_global as *const u8,
        Helper::TypeOfGlobal => bamts_native::bamts_typeof_global as *const u8,
        Helper::LoadThis => bamts_native::bamts_load_this as *const u8,
        Helper::LoadArguments => bamts_native::bamts_load_arguments as *const u8,
        Helper::LoadNewTarget => bamts_native::bamts_load_new_target as *const u8,
        Helper::ArrayPush => bamts_native::bamts_array_push as *const u8,
        Helper::ArrayExtend => bamts_native::bamts_array_extend as *const u8,
        Helper::ObjectSpread => bamts_native::bamts_object_spread as *const u8,
        Helper::SetPrototype => bamts_native::bamts_set_prototype as *const u8,
        Helper::CreatePrivateName => bamts_native::bamts_create_private_name as *const u8,
        Helper::CreateRegExp => bamts_native::bamts_create_regexp as *const u8,
        Helper::GetIterator => bamts_native::bamts_get_iterator as *const u8,
        Helper::IteratorNext => bamts_native::bamts_iterator_next as *const u8,
        Helper::Export => bamts_native::bamts_export as *const u8,
        Helper::ConsumeFuel => bamts_native::bamts_consume_fuel as *const u8,
        Helper::IteratorStep => bamts_native::bamts_iterator_step as *const u8,
        Helper::IteratorResult => bamts_native::bamts_iterator_result as *const u8,
        Helper::IteratorClose => bamts_native::bamts_iterator_close as *const u8,
        Helper::RequireCloseResult => bamts_native::bamts_require_close_result as *const u8,
        Helper::LoadImportMeta => bamts_native::bamts_load_import_meta as *const u8,
        Helper::ToObject => bamts_native::bamts_to_object as *const u8,
        Helper::DisposeCapture => bamts_native::bamts_dispose_capture as *const u8,
        Helper::SuppressError => bamts_native::bamts_suppress_error as *const u8,
        Helper::ResumeMode => bamts_native::bamts_resume_mode as *const u8,
        Helper::GetSuper => bamts_native::bamts_get_super as *const u8,
        Helper::SetSuper => bamts_native::bamts_set_super as *const u8,
        Helper::ImportAttributes => bamts_native::bamts_import_attributes as *const u8,
        Helper::ImportDynamicAttributes => {
            bamts_native::bamts_import_dynamic_attributes as *const u8
        }
        Helper::CopyDataProperties => bamts_native::bamts_copy_data_properties as *const u8,
        Helper::GetTemplateObject => bamts_native::bamts_get_template_object as *const u8,
    }
}

const _: () = {
    let mut index = 0;
    while index < bamts_native::HELPER_COUNT {
        let helper = Helper::from_external_index(index).expect("codegen helper table is dense");
        let native = NativeHelper::from_u32(index).expect("native helper table is dense");
        assert!(helper.external_index() == native.as_u32());
        index += 1;
    }
};

#[cfg(test)]
mod tests {
    use bamts_bytecode::{
        BinaryOp, Binding, BindingKind, Constant, ConstantId, EcmaString, Edge, EdgeKind,
        EdgeTarget, ExceptionHandler, Export, ExportSource, Function as BytecodeFunction,
        FunctionFlags, FunctionId, Instruction, Module, ModuleId, Pc, Program, ProgramModule,
        Register,
    };
    use bamts_native::{
        AbiError, Completion, CompletionTag, HelperCall, HelperResult, NativeEntryTable,
        NativeFrame, NativeHelper, NativeOps, ShadowFrame, Value, with_native_ops,
    };
    use bamts_runtime::{
        Host, Limits, Machine, NativeError, RuntimeError, RuntimeErrorKind, run_linked_program,
    };
    use cranelift_module::Module as _;

    use crate::{Helper, JitError, lower_program};

    use super::{
        JitProgram, build_module, compile_jit, compile_jit_with_cancel, compile_jit_with_telemetry,
        compile_jit_with_telemetry_cancel, compile_lowered,
    };
    use crate::jit_memory::WxPhase;
    use bamts_cancel::CancellationToken;

    struct SilentHost;

    impl Host for SilentHost {}

    struct FatalResume;

    impl NativeOps for FatalResume {
        fn truthy(&self, _frame: &mut NativeFrame<'_>, _value: Value) -> bool {
            unreachable!("resume fixture never tests truthiness")
        }

        fn dispatch(&self, _frame: &mut NativeFrame<'_>, call: HelperCall) -> HelperResult {
            assert_eq!(call, HelperCall::ResumeValue);
            HelperResult {
                tag: CompletionTag::FatalTrap,
                value: Value::int32(99),
            }
        }
    }

    #[derive(Default)]
    struct RecordingHost {
        stdout: Vec<u8>,
    }

    impl Host for RecordingHost {
        fn write_stdout(&mut self, bytes: &[u8]) {
            self.stdout.extend_from_slice(bytes);
        }
    }

    fn module(name: &str) -> ProgramModule<bamts_bytecode::Verified> {
        ProgramModule {
            name: ConstantId::new(0),
            code: Module::new(
                vec![Constant::String(EcmaString::encode(name))],
                vec![BytecodeFunction::new(
                    None,
                    0,
                    0,
                    0,
                    FunctionFlags::default(),
                    vec![Instruction::Halt],
                    Vec::new(),
                )],
                FunctionId::new(0),
            )
            .verify()
            .expect("test module verifies"),
            edges: Vec::new(),
            bindings: Vec::new(),
            exports: Vec::new(),
        }
    }

    fn two_module_program() -> Program<bamts_bytecode::Verified> {
        Program::link(vec![module("first"), module("entry")], ModuleId::new(1))
            .expect("test program verifies")
    }

    fn one_function_program(
        constants: Vec<Constant>,
        register_count: u32,
        code: Vec<Instruction>,
        handlers: Vec<ExceptionHandler>,
    ) -> Program<bamts_bytecode::Verified> {
        let module = ProgramModule {
            name: ConstantId::new(0),
            code: Module::new(
                constants,
                vec![BytecodeFunction::new(
                    None,
                    0,
                    0,
                    register_count,
                    FunctionFlags::default(),
                    code,
                    handlers,
                )],
                FunctionId::new(0),
            )
            .verify()
            .expect("metering fixture verifies"),
            edges: Vec::new(),
            bindings: Vec::new(),
            exports: Vec::new(),
        };
        Program::link(vec![module], ModuleId::new(0)).expect("metering fixture links")
    }

    fn callback_reentry_program() -> Program<bamts_bytecode::Verified> {
        let constants = vec![
            Constant::String(EcmaString::encode("entry")),
            Constant::String(EcmaString::encode("Array")),
            Constant::String(EcmaString::encode("prototype")),
            Constant::String(EcmaString::encode("map")),
            Constant::Int32(1),
        ];
        let entry = BytecodeFunction::new(
            None,
            0,
            0,
            11,
            FunctionFlags::default(),
            vec![
                Instruction::LoadGlobal {
                    dst: Register::new(0),
                    name: ConstantId::new(1),
                },
                Instruction::LoadConst {
                    dst: Register::new(1),
                    constant: ConstantId::new(2),
                },
                Instruction::GetProperty {
                    dst: Register::new(2),
                    object: Register::new(0),
                    key: Register::new(1),
                },
                Instruction::LoadConst {
                    dst: Register::new(3),
                    constant: ConstantId::new(3),
                },
                Instruction::GetProperty {
                    dst: Register::new(4),
                    object: Register::new(2),
                    key: Register::new(3),
                },
                Instruction::CreateArray {
                    dst: Register::new(5),
                },
                Instruction::LoadConst {
                    dst: Register::new(6),
                    constant: ConstantId::new(4),
                },
                Instruction::ArrayPush {
                    array: Register::new(5),
                    value: Register::new(6),
                },
                Instruction::CreateArray {
                    dst: Register::new(7),
                },
                Instruction::CreateClosure {
                    dst: Register::new(8),
                    function: FunctionId::new(1),
                    captures: Register::new(7),
                },
                Instruction::CreateArray {
                    dst: Register::new(9),
                },
                Instruction::ArrayPush {
                    array: Register::new(9),
                    value: Register::new(8),
                },
                Instruction::Call {
                    dst: Register::new(10),
                    callee: Register::new(4),
                    this_value: Register::new(5),
                    arguments: Register::new(9),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        );
        let callback = BytecodeFunction::new(
            None,
            0,
            0,
            1,
            FunctionFlags::default(),
            vec![Instruction::Halt],
            Vec::new(),
        );
        let module = ProgramModule {
            name: ConstantId::new(0),
            code: Module::new(constants, vec![entry, callback], FunctionId::new(0))
                .verify()
                .expect("callback fixture verifies"),
            edges: Vec::new(),
            bindings: Vec::new(),
            exports: Vec::new(),
        };
        Program::link(vec![module], ModuleId::new(0)).expect("callback fixture links")
    }

    fn assert_fuel_exhausted(
        result: Result<bamts_runtime::ExecutionOutcome, NativeError>,
        limit: u64,
    ) -> RuntimeError {
        let Err(NativeError::Runtime(error)) = result else {
            panic!("expected fuel exhaustion at limit {limit}, got {result:?}");
        };
        assert_eq!(error.kind, RuntimeErrorKind::FuelExhausted { limit });
        error
    }

    #[test]
    fn codegen_and_native_helper_tables_are_identical() {
        for index in 0..bamts_native::HELPER_COUNT {
            let helper = Helper::from_external_index(index).expect("codegen helper exists");
            let native = NativeHelper::from_u32(index).expect("native helper exists");
            assert_eq!(helper.external_index(), native.as_u32());
            assert_eq!(helper.symbol(), native.symbol());
        }
    }

    #[test]
    fn compiles_duplicate_local_function_ids_and_reports_entry_tuple() {
        let program = compile_jit(&two_module_program()).expect("host JIT compiles every module");
        assert_eq!(program.entry_module(), 1);
        assert_eq!(program.entry_function(), 0);

        for module_id in [0, 1] {
            let mut register = Value::UNINITIALIZED;
            let mut frame = ShadowFrame::new(core::ptr::null_mut(), 0, module_id, &mut register, 1);
            let mut out = Completion::new(Value::UNDEFINED);
            // Direct entry invocation has no NativeOps dispatcher installed, so
            // the mandatory pre-Halt fuel helper reports a fatal trap. Reaching
            // it proves both local function-id tuples were compiled and bound.
            assert_eq!(
                program.invoke(module_id, 0, &mut frame, &mut out),
                Ok(CompletionTag::FatalTrap)
            );
        }

        let mut register = Value::UNINITIALIZED;
        let mut mismatched_frame = ShadowFrame::new(core::ptr::null_mut(), 0, 1, &mut register, 1);
        let mut mismatched_out = Completion::new(Value::int32(123));
        assert_eq!(
            program.invoke(0, 0, &mut mismatched_frame, &mut mismatched_out),
            Err(AbiError::FrameModuleMismatch {
                selected_module_id: 0,
                frame_module_id: 1,
            })
        );
        assert_eq!(mismatched_out.value.as_int32(), Some(123));
    }

    #[test]
    fn compile_jit_with_telemetry_reports_wall_and_page_rounded_memory() {
        let bytecode = two_module_program();
        let (program, telemetry) =
            compile_jit_with_telemetry(&bytecode).expect("host JIT compiles with telemetry");

        // The program is exactly what `compile_jit` yields.
        assert_eq!(program.entry_module(), 1);
        assert_eq!(program.program_bytes(), bytecode.encode());

        // The compile wall is a finite, non-negative measurement.
        assert!(telemetry.jit_compile_wall_ms >= 0.0);
        assert!(telemetry.jit_compile_wall_ms.is_finite());

        // Finalized code exists, so at least one executable page was allocated,
        // and the total is the exact sum of the per-kind, page-rounded bytes.
        assert!(telemetry.code_bytes > 0, "generated code was allocated");
        let page = region::page::size() as u64;
        assert_eq!(
            telemetry.code_bytes % page,
            0,
            "code bytes are page-rounded"
        );
        assert_eq!(
            telemetry.total_allocated_bytes,
            telemetry.code_bytes + telemetry.readonly_bytes + telemetry.readwrite_bytes,
        );
        assert!(telemetry.total_allocated_bytes >= telemetry.code_bytes);
    }

    #[test]
    fn matched_jit_program_runs_through_linked_runtime() {
        let bytecode = two_module_program();
        let program = compile_jit(&bytecode).expect("host JIT compiles every module");
        assert_eq!(program.program_bytes(), bytecode.encode());

        let mut host = SilentHost;
        let outcome = run_linked_program(&bytecode, &program, &mut host, &Limits::default())
            .expect("matching JIT program runs");
        assert_eq!(outcome.exit_code, 0);
        assert!(outcome.stdout.is_empty());
    }

    #[test]
    fn jit_charges_each_mixed_instruction_once_at_exact_boundaries() {
        let bytecode = one_function_program(
            vec![
                Constant::String(EcmaString::encode("entry")),
                Constant::Int32(1),
            ],
            3,
            vec![
                Instruction::LoadConst {
                    dst: Register::new(0),
                    constant: ConstantId::new(1),
                },
                Instruction::Move {
                    dst: Register::new(1),
                    src: Register::new(0),
                },
                Instruction::Binary {
                    dst: Register::new(2),
                    op: BinaryOp::Add,
                    left: Register::new(0),
                    right: Register::new(1),
                },
                Instruction::Jump { target: Pc::new(4) },
                Instruction::Halt,
            ],
            Vec::new(),
        );
        let compiled = compile_jit(&bytecode).expect("mixed program compiles");

        for (fuel, pc) in [(0, 0), (4, 4)] {
            let mut host = SilentHost;
            let result = run_linked_program(
                &bytecode,
                &compiled,
                &mut host,
                &Limits {
                    fuel,
                    ..Limits::default()
                },
            );
            assert_eq!(assert_fuel_exhausted(result, fuel).pc, Pc::new(pc));
        }

        let mut host = SilentHost;
        let result = run_linked_program(
            &bytecode,
            &compiled,
            &mut host,
            &Limits {
                fuel: 5,
                ..Limits::default()
            },
        );
        assert!(
            result.is_ok(),
            "five instructions fit fuel five: {result:?}"
        );
    }

    #[test]
    fn resumed_helper_failure_reports_suspend_pc() {
        let bytecode = one_function_program(
            vec![
                Constant::String(EcmaString::encode("entry")),
                Constant::Null,
            ],
            1,
            vec![
                Instruction::LoadConst {
                    dst: Register::new(0),
                    constant: ConstantId::new(1),
                },
                Instruction::Suspend {
                    dst: Register::new(0),
                    src: Register::new(0),
                    resume: Pc::new(2),
                    mode: Register::new(0),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        );
        let program = compile_jit(&bytecode).expect("suspend program compiles");
        let mut register = Value::UNINITIALIZED;
        let mut frame = ShadowFrame::new(core::ptr::null_mut(), 2, 0, &mut register, 1);
        let mut completion = Completion::new(Value::UNDEFINED);
        let mut ops = FatalResume;

        let tag = with_native_ops(&mut ops, || {
            program.invoke(0, 0, &mut frame, &mut completion)
        })
        .expect("compiled entry is registered");

        assert_eq!(tag, CompletionTag::FatalTrap);
        assert_eq!(frame.bytecode_pc, 1);
    }
    /// A resume dispatcher that records the helper-call order and returns fixed
    /// values for the resume prologue.
    struct RecordingResume {
        calls: std::cell::RefCell<Vec<HelperCall>>,
        resumed_value: Value,
        mode_value: Value,
    }

    impl RecordingResume {
        fn new(resumed_value: Value, mode_value: Value) -> Self {
            Self {
                calls: std::cell::RefCell::new(Vec::new()),
                resumed_value,
                mode_value,
            }
        }
    }

    impl NativeOps for RecordingResume {
        fn truthy(&self, _frame: &mut NativeFrame<'_>, _value: Value) -> bool {
            unreachable!("resume prologue fixture never tests truthiness")
        }

        fn dispatch(&self, _frame: &mut NativeFrame<'_>, call: HelperCall) -> HelperResult {
            self.calls.borrow_mut().push(call);
            match call {
                HelperCall::LoadConstant { .. } => HelperResult::normal(Value::NULL),
                HelperCall::ConsumeFuel { .. } => HelperResult::normal(Value::UNDEFINED),
                HelperCall::ResumeValue => HelperResult::normal(self.resumed_value),
                HelperCall::ResumeMode => HelperResult::normal(self.mode_value),
                _ => panic!("unexpected helper call in resume prologue fixture: {call:?}"),
            }
        }
    }

    #[test]
    fn jit_resume_prologue_calls_resume_value_then_resume_mode() {
        let bytecode = one_function_program(
            vec![
                Constant::String(EcmaString::encode("entry")),
                Constant::Null,
            ],
            2,
            vec![
                Instruction::LoadConst {
                    dst: Register::new(0),
                    constant: ConstantId::new(1),
                },
                Instruction::Suspend {
                    dst: Register::new(0),
                    src: Register::new(0),
                    resume: Pc::new(2),
                    mode: Register::new(1),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        );
        let program = compile_jit(&bytecode).expect("suspend program compiles");
        let mut registers = [Value::UNINITIALIZED; 2];
        let mut frame = ShadowFrame::new(core::ptr::null_mut(), 0, 0, registers.as_mut_ptr(), 2);
        let mut completion = Completion::new(Value::UNDEFINED);
        let mut ops = RecordingResume::new(Value::int32(42), Value::int32(2));

        // Fresh call: token 0 yields the value and suspends.
        let tag = with_native_ops(&mut ops, || {
            program.invoke(0, 0, &mut frame, &mut completion)
        })
        .expect("compiled entry is registered");
        assert_eq!(tag, CompletionTag::Suspend);

        // Resume: token 2 enters the resume prologue.
        frame.bytecode_pc = 2;
        let mut completion = Completion::new(Value::UNDEFINED);
        let tag = with_native_ops(&mut ops, || {
            program.invoke(0, 0, &mut frame, &mut completion)
        })
        .expect("compiled resume entry is registered");
        assert_eq!(tag, CompletionTag::Normal);

        let calls = ops.calls.into_inner();
        let value_pos = calls
            .iter()
            .position(|c| matches!(c, HelperCall::ResumeValue))
            .expect("ResumeValue called");
        let mode_pos = calls
            .iter()
            .position(|c| matches!(c, HelperCall::ResumeMode))
            .expect("ResumeMode called");
        assert!(
            value_pos < mode_pos,
            "ResumeValue must be called before ResumeMode:\n{calls:?}"
        );
        assert_eq!(
            calls
                .iter()
                .filter(|c| matches!(c, HelperCall::ResumeValue))
                .count(),
            1,
            "ResumeValue called exactly once"
        );
        assert_eq!(
            calls
                .iter()
                .filter(|c| matches!(c, HelperCall::ResumeMode))
                .count(),
            1,
            "ResumeMode called exactly once"
        );
        assert!(
            calls
                .iter()
                .any(|c| matches!(c, HelperCall::LoadConstant { .. }))
        );
        assert!(
            calls
                .iter()
                .any(|c| matches!(c, HelperCall::ConsumeFuel { .. }))
        );
        assert_eq!(
            registers[0],
            Value::int32(42),
            "resumed value stored into dst"
        );
        assert_eq!(
            registers[1],
            Value::int32(2),
            "resume mode stored into mode"
        );
        assert_eq!(frame.bytecode_pc, 2, "resume continues at the resume pc");
    }

    #[test]
    fn jit_jump_to_self_exhausts_fuel() {
        let bytecode = one_function_program(
            vec![Constant::String(EcmaString::encode("entry"))],
            0,
            vec![Instruction::Jump { target: Pc::new(0) }],
            Vec::new(),
        );
        let compiled = compile_jit(&bytecode).expect("spin loop compiles");
        let mut host = SilentHost;
        let result = run_linked_program(
            &bytecode,
            &compiled,
            &mut host,
            &Limits {
                fuel: 3,
                ..Limits::default()
            },
        );
        assert_fuel_exhausted(result, 3);
    }

    #[test]
    fn jit_builtin_callback_reentry_shares_all_machine_budgets() {
        let bytecode = callback_reentry_program();
        let compiled = compile_jit(&bytecode).expect("callback program compiles");

        let mut host = SilentHost;
        let exact = run_linked_program(
            &bytecode,
            &compiled,
            &mut host,
            &Limits {
                fuel: 15,
                max_call_depth: 2,
                max_total_registers: 12,
                ..Limits::default()
            },
        );
        assert!(
            exact.is_ok(),
            "entry plus callback fit exact shared limits: {exact:?}"
        );

        let mut host = SilentHost;
        assert_fuel_exhausted(
            run_linked_program(
                &bytecode,
                &compiled,
                &mut host,
                &Limits {
                    fuel: 14,
                    max_call_depth: 2,
                    max_total_registers: 12,
                    ..Limits::default()
                },
            ),
            14,
        );

        let mut host = SilentHost;
        let depth = run_linked_program(
            &bytecode,
            &compiled,
            &mut host,
            &Limits {
                max_call_depth: 1,
                max_total_registers: 12,
                ..Limits::default()
            },
        );
        assert!(matches!(
            depth,
            Err(NativeError::Runtime(RuntimeError {
                kind: RuntimeErrorKind::CallDepthExceeded { limit: 1 },
                ..
            }))
        ));

        let mut host = SilentHost;
        let registers = run_linked_program(
            &bytecode,
            &compiled,
            &mut host,
            &Limits {
                max_call_depth: 2,
                max_total_registers: 11,
                ..Limits::default()
            },
        );
        assert!(matches!(
            registers,
            Err(NativeError::Runtime(RuntimeError {
                kind: RuntimeErrorKind::RegisterLimitExceeded { limit: 11 },
                ..
            }))
        ));
    }

    #[test]
    fn jit_fuel_exhaustion_bypasses_bytecode_handler() {
        let bytecode = one_function_program(
            vec![
                Constant::String(EcmaString::encode("entry")),
                Constant::Undefined,
            ],
            1,
            vec![
                Instruction::LoadConst {
                    dst: Register::new(0),
                    constant: ConstantId::new(1),
                },
                Instruction::Throw {
                    value: Register::new(0),
                },
                Instruction::Halt,
            ],
            vec![ExceptionHandler {
                start: Pc::new(1),
                end: Pc::new(2),
                handler: Pc::new(2),
                catch_register: Register::new(0),
            }],
        );
        let compiled = compile_jit(&bytecode).expect("handler program compiles");
        let mut host = SilentHost;
        let result = run_linked_program(
            &bytecode,
            &compiled,
            &mut host,
            &Limits {
                fuel: 1,
                ..Limits::default()
            },
        );
        assert_fuel_exhausted(result, 1);
    }

    #[test]
    fn jit_zero_fuel_prevents_stdout_side_effects() {
        let bytecode = one_function_program(
            vec![
                Constant::String(EcmaString::encode("entry")),
                Constant::String(EcmaString::encode("console")),
                Constant::String(EcmaString::encode("log")),
                Constant::String(EcmaString::encode("hello")),
            ],
            6,
            vec![
                Instruction::LoadGlobal {
                    dst: Register::new(0),
                    name: ConstantId::new(1),
                },
                Instruction::LoadConst {
                    dst: Register::new(1),
                    constant: ConstantId::new(2),
                },
                Instruction::GetProperty {
                    dst: Register::new(2),
                    object: Register::new(0),
                    key: Register::new(1),
                },
                Instruction::LoadConst {
                    dst: Register::new(3),
                    constant: ConstantId::new(3),
                },
                Instruction::CreateArray {
                    dst: Register::new(4),
                },
                Instruction::ArrayPush {
                    array: Register::new(4),
                    value: Register::new(3),
                },
                Instruction::Call {
                    dst: Register::new(5),
                    callee: Register::new(2),
                    this_value: Register::new(0),
                    arguments: Register::new(4),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        );
        let compiled = compile_jit(&bytecode).expect("stdout fixture compiles");
        let mut host = RecordingHost::default();
        let result = run_linked_program(
            &bytecode,
            &compiled,
            &mut host,
            &Limits {
                fuel: 0,
                ..Limits::default()
            },
        );
        assert_fuel_exhausted(result, 0);
        assert!(host.stdout.is_empty(), "fuel failure precedes console.log");
    }

    /// The permissions of the region that contains `address`, as the host's
    /// process map reports them. A region's `identity` begins with its hex
    /// address range, `start-end`, on every host.
    fn permissions_at(regions: &[bamts_platform::MemoryRegion], address: usize) -> Option<&str> {
        regions.iter().find_map(|region| {
            let range = region.identity.split_whitespace().next()?;
            let (start, end) = range.split_once('-')?;
            let start = usize::from_str_radix(start, 16).ok()?;
            let end = usize::from_str_radix(end, 16).ok()?;
            (start <= address && address < end).then_some(region.permissions.as_str())
        })
    }

    fn own_regions() -> Vec<bamts_platform::MemoryRegion> {
        bamts_platform::process_regions(std::process::id()).expect("process regions are readable")
    }

    /// The lookup above is the oracle for the next test, so it has to tell code
    /// from data on a real process before its verdict on JIT code means anything.
    #[test]
    fn the_region_lookup_tells_code_from_data() {
        let code = the_region_lookup_tells_code_from_data as fn() as usize;
        let data = Box::new(0_u8);
        let data = std::ptr::from_ref::<u8>(&data) as usize;
        let regions = own_regions();

        let code_permissions = permissions_at(&regions, code).expect("code is mapped");
        assert!(code_permissions.contains('x'), "{code_permissions}");
        assert!(!code_permissions.contains('w'), "{code_permissions}");
        let data_permissions = permissions_at(&regions, data).expect("data is mapped");
        assert!(data_permissions.contains('w'), "{data_permissions}");
        assert!(!data_permissions.contains('x'), "{data_permissions}");
    }

    #[test]
    fn finalized_jit_code_is_executable_and_not_writable() {
        let program = compile_jit(&two_module_program()).expect("host JIT compiles");
        let regions = own_regions();

        // Every compiled function address is executable and not writable, as an
        // independent smoke test against the host's process map.
        for unit in &program.functions {
            let address = program.module.get_finalized_function(unit.function) as usize;
            let permissions = permissions_at(&regions, address)
                .unwrap_or_else(|| panic!("finalized function at {address:#x} has no mapped page"));

            // `finalize_definitions` must publish code with an RW -> RX transition.
            assert!(permissions.contains('x'), "{permissions}");
            assert!(!permissions.contains('w'), "{permissions}");
        }
    }

    #[test]
    fn compiled_jit_program_owns_executable_receipt_and_drops_to_freed() {
        let bytecode = two_module_program();
        let cancel = CancellationToken::new();
        let (module, memory, program_bytes) =
            build_module(&bytecode, &cancel).expect("module builds");
        let lowered = lower_program(&bytecode, module.target_config()).expect("program lowers");
        let program = compile_lowered(module, memory.clone(), lowered, program_bytes, &cancel)
            .expect("host JIT compiles");

        // The program was published, so it owns an executable receipt.
        assert_eq!(memory.phase(), WxPhase::Executable);
        drop(program);
        // Dropping the program drops the module, whose provider marks `Freed`
        // and unmaps every owned mapping exactly once.
        assert_eq!(memory.phase(), WxPhase::Freed);
    }

    /// Compile-time proof that `JitProgram` is not `Sync`. `JITModule` carries a
    /// `RefCell` and is not `Sync`; that guarantee is the ownership rule letting
    /// `invoke(&self)` borrow the program safely without an active-call counter.
    /// If `JitProgram: Sync` ever held, the trait resolution below would become
    /// ambiguous and fail the build.
    trait AmbiguousIfSync<A> {
        #[allow(dead_code)]
        fn token() {}
    }
    impl<T: ?Sized> AmbiguousIfSync<()> for T {}
    impl<T: ?Sized + Sync> AmbiguousIfSync<u8> for T {}

    #[test]
    fn jit_program_is_not_sync() {
        // If `JitProgram: Sync`, both impls apply and `A` is ambiguous.
        let _ = <JitProgram as AmbiguousIfSync<_>>::token;
    }

    #[test]
    fn unknown_module_and_function_tuples_are_rejected() {
        let program = compile_jit(&two_module_program()).expect("host JIT compiles");
        let mut register = Value::UNINITIALIZED;
        let mut frame = ShadowFrame::new(core::ptr::null_mut(), 0, 0, &mut register, 1);
        let mut out = Completion::new(Value::UNDEFINED);

        for (module_id, function_id) in [(7, 0), (0, 7)] {
            assert_eq!(
                program.invoke(module_id, function_id, &mut frame, &mut out),
                Err(AbiError::UnknownFunction {
                    module_id,
                    function_id,
                })
            );
        }
    }

    #[test]
    fn compile_lowered_rejects_out_of_order_function_identity() {
        let bytecode = callback_reentry_program();
        let cancel = CancellationToken::new();
        let (module, memory, program_bytes) =
            build_module(&bytecode, &cancel).expect("module builds");
        let mut lowered = lower_program(&bytecode, module.target_config()).expect("program lowers");
        lowered.modules[0].functions.swap(0, 1);

        assert!(matches!(
            compile_lowered(module, memory, lowered, program_bytes, &cancel),
            Err(super::JitError::InvalidLoweredModule(message))
                if message.contains("function 1 appears at local index 0")
        ));
    }

    #[test]
    fn jit_import_dynamic_instruction_matches_interpreter() {
        let root = ProgramModule {
            name: ConstantId::new(0),
            code: Module::new(
                vec![
                    Constant::String(EcmaString::encode("root")),
                    Constant::String(EcmaString::encode("./target")),
                    Constant::String(EcmaString::encode("then")),
                    Constant::String(EcmaString::encode("console")),
                    Constant::String(EcmaString::encode("log")),
                    Constant::Int32(0),
                    Constant::String(EcmaString::encode("value")),
                ],
                vec![
                    BytecodeFunction::new(
                        None,
                        0,
                        0,
                        8,
                        FunctionFlags::default(),
                        vec![
                            Instruction::LoadConst {
                                dst: Register::new(0),
                                constant: ConstantId::new(1),
                            },
                            Instruction::ImportDynamic {
                                dst: Register::new(1),
                                specifier: Register::new(0),
                            },
                            Instruction::LoadConst {
                                dst: Register::new(2),
                                constant: ConstantId::new(2),
                            },
                            Instruction::GetProperty {
                                dst: Register::new(3),
                                object: Register::new(1),
                                key: Register::new(2),
                            },
                            Instruction::CreateArray {
                                dst: Register::new(4),
                            },
                            Instruction::CreateClosure {
                                dst: Register::new(5),
                                function: FunctionId::new(1),
                                captures: Register::new(4),
                            },
                            Instruction::CreateArray {
                                dst: Register::new(6),
                            },
                            Instruction::ArrayPush {
                                array: Register::new(6),
                                value: Register::new(5),
                            },
                            Instruction::Call {
                                dst: Register::new(7),
                                callee: Register::new(3),
                                this_value: Register::new(1),
                                arguments: Register::new(6),
                            },
                            Instruction::Halt,
                        ],
                        Vec::new(),
                    ),
                    BytecodeFunction::new(
                        None,
                        0,
                        1,
                        10,
                        FunctionFlags::default(),
                        vec![
                            Instruction::LoadArguments {
                                dst: Register::new(0),
                            },
                            Instruction::LoadConst {
                                dst: Register::new(1),
                                constant: ConstantId::new(5),
                            },
                            Instruction::GetProperty {
                                dst: Register::new(2),
                                object: Register::new(0),
                                key: Register::new(1),
                            },
                            Instruction::LoadConst {
                                dst: Register::new(3),
                                constant: ConstantId::new(6),
                            },
                            Instruction::GetProperty {
                                dst: Register::new(4),
                                object: Register::new(2),
                                key: Register::new(3),
                            },
                            Instruction::LoadGlobal {
                                dst: Register::new(5),
                                name: ConstantId::new(3),
                            },
                            Instruction::LoadConst {
                                dst: Register::new(6),
                                constant: ConstantId::new(4),
                            },
                            Instruction::GetProperty {
                                dst: Register::new(7),
                                object: Register::new(5),
                                key: Register::new(6),
                            },
                            Instruction::CreateArray {
                                dst: Register::new(8),
                            },
                            Instruction::ArrayPush {
                                array: Register::new(8),
                                value: Register::new(4),
                            },
                            Instruction::Call {
                                dst: Register::new(9),
                                callee: Register::new(7),
                                this_value: Register::new(5),
                                arguments: Register::new(8),
                            },
                            Instruction::Halt,
                        ],
                        Vec::new(),
                    ),
                ],
                FunctionId::new(0),
            )
            .verify()
            .expect("dynamic import root verifies"),
            edges: vec![Edge {
                specifier: ConstantId::new(1),
                target: EdgeTarget::Local(ModuleId::new(1)),
                kind: EdgeKind::Dynamic,
            }],
            bindings: Vec::new(),
            exports: Vec::new(),
        };
        let target = ProgramModule {
            name: ConstantId::new(0),
            code: Module::new(
                vec![
                    Constant::String(EcmaString::encode("target")),
                    Constant::Int32(7),
                    Constant::String(EcmaString::encode("value")),
                ],
                vec![BytecodeFunction::new(
                    None,
                    0,
                    0,
                    1,
                    FunctionFlags::default(),
                    vec![
                        Instruction::LoadConst {
                            dst: Register::new(0),
                            constant: ConstantId::new(1),
                        },
                        Instruction::StoreGlobal {
                            name: ConstantId::new(2),
                            value: Register::new(0),
                        },
                        Instruction::Halt,
                    ],
                    Vec::new(),
                )],
                FunctionId::new(0),
            )
            .verify()
            .expect("dynamic import target verifies"),
            edges: Vec::new(),
            bindings: vec![Binding {
                name: ConstantId::new(2),
                kind: BindingKind::Hoisted,
            }],
            exports: vec![Export {
                name: ConstantId::new(2),
                source: ExportSource::Local(bamts_bytecode::BindingId::new(0)),
            }],
        };
        let bytecode = Program::link(vec![root, target], ModuleId::new(0))
            .expect("dynamic import fixture links");

        let mut interpreter_host = RecordingHost::default();
        let interpreter = Machine::new(&bytecode, &mut interpreter_host, Limits::default())
            .run()
            .expect("interpreter resolves local ImportDynamic");
        assert_eq!(interpreter.outcome.exit_code, 0);
        assert_eq!(interpreter_host.stdout, b"7\n");

        let compiled = compile_jit(&bytecode).expect("JIT compiles ImportDynamic");
        let mut jit_host = RecordingHost::default();
        let outcome = run_linked_program(&bytecode, &compiled, &mut jit_host, &Limits::default())
            .expect("JIT resolves local ImportDynamic");
        assert_eq!(outcome.exit_code, interpreter.outcome.exit_code);
        assert_eq!(jit_host.stdout, interpreter_host.stdout);
    }

    #[test]
    fn pre_cancelled_token_aborts_compile_jit() {
        let bytecode = two_module_program();
        let cancel = CancellationToken::new();
        cancel.cancel();
        let result = compile_jit_with_cancel(&bytecode, &cancel);
        assert!(matches!(result, Err(JitError::Cancelled)));
    }

    #[test]
    fn pre_cancelled_token_aborts_compile_jit_with_telemetry() {
        let bytecode = two_module_program();
        let cancel = CancellationToken::new();
        cancel.cancel();
        let result = compile_jit_with_telemetry_cancel(&bytecode, &cancel);
        assert!(matches!(result, Err(JitError::Cancelled)));
    }
}
