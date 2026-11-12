//! Shared, backend-neutral Cranelift lowering for verified BamTS bytecode.
//!
//! This crate turns a canonical [`bamts_bytecode::Program<Verified>`] into
//! Cranelift IR through [`lower_program`]. It retains one [`LoweredModule`] per
//! program module, with module-local pools and module-qualified native symbols,
//! for both feature-gated backends:
//!
//! * a `host-jit` backend that finalizes each `ir::Function` into executable
//!   memory, and
//! * an `aot` backend that emits each `ir::Function` into an object file.
//!
//! This slice performs **no** executable-memory allocation and **no** object
//! linking; it only builds and verifies IR. Both later backends supply their
//! own `isa::TargetFrontendConfig` (via `isa.frontend_config()`), so the ISA
//! choice, calling convention, and pointer type stay outside this crate.
//!
//! # Entry ABI
//!
//! Every lowered function has the native-entry signature from the canonical
//! execution plan (N5), matching `bamts_native::ShadowFrame` and
//! `bamts_native::Completion`:
//!
//! ```text
//! extern "C" fn(frame: *mut ShadowFrame, out: *mut Completion) -> u32
//! ```
//!
//! * `frame` points at the register frame; `frame.handles` (offset 16) is the
//!   `*mut Value` register array. `frame.bytecode_pc` (offset 8) records the
//!   active instruction and carries the resume token after
//!   [`Suspend`](#suspendawait-and-the-resume-helper).
//! * `out` receives the completion value; the returned `u32` is a
//!   `bamts_native::CompletionTag` discriminant (`Normal`/`Throw`/`Suspend`/
//!   `FatalTrap`).
//!
//! # Register addressing convention
//!
//! Register `r[i]` lives at `frame.handles + i * 8` (one `Value`/`u64` slot).
//! Every access derives the byte offset as `i64::from(register.get()) * 8`; the
//! validation pass (`validate_slots`) proves this offset fits the `Offset32`
//! used by loads and stores, so `u32` register ids and CLIF addresses never mix
//! widths inconsistently. This holds for register ids well past 127: a slot
//! offset is a full 32-bit displacement, not a signed byte.
//!
//! # Dynamic operands: no fixed windows, no constant-keyed properties
//!
//! The production ISA carries no fixed argument window and no constant-keyed
//! property access. Calls and constructs take a single **arguments array** in a
//! register (`Call`/`Construct` `arguments`), so spread and any arity flow
//! through one `Value` handle with no pointer arithmetic. Property access takes
//! its **key from a register** (`GetProperty`/`SetProperty`/`DeleteProperty`
//! `key`), a `Value` the runtime coerces to a property key (string, symbol, or
//! private name). Closures capture through an array register
//! (`CreateClosure` `captures`), again a single `Value` handle.
//!
//! # Value semantics: the explicit helper ABI
//!
//! The bytecode algebra ([`bamts_bytecode::Instruction`]) is structural: the
//! verifier proves definite initialization and CFG validity but assigns no
//! value meaning. The NaN-boxed runtime `Value` requires tag dispatch that this
//! IR-only slice must not open-code, so every operation whose result depends on
//! runtime value semantics is lowered to a call into a declared [`Helper`]
//! (`u1:<index>` external names a backend resolves to a C symbol). This crate
//! declares each helper's ABI and control-flow contract; it never defines the
//! helper body.
//!
//! Every value-producing helper follows one **completion ABI**:
//! `fn(frame, <operands…>, out: *mut Completion) -> u32(tag)`. On
//! `Normal` (0) the result is in `out.value`; on `Throw` the thrown handle is in
//! `out.value` and control routes to a covering handler; `FatalTrap` always
//! propagates to the runtime. Two exceptions to the "result in `out.value`"
//! rule:
//!
//! * [`Helper::Truthy`] performs the total ToBoolean coercion and returns the
//!   truth value directly as `0`/`1`; it never writes `out` and never throws.
//! * [`Helper::IteratorNext`] and [`Helper::IteratorResult`] write **two**
//!   registers — they receive the `done` and `value` register indices and, on
//!   `Normal`, write both slots in the frame directly (a single completion
//!   channel cannot carry two results); `out.value` is used only to carry a
//!   thrown handle on `Throw`.
//!
//! A subset of the completion helpers is **total** (`Normal` only, never
//! `Throw`/`FatalTrap`): [`Helper::TypeOfGlobal`], [`Helper::LoadThis`],
//! [`Helper::LoadArguments`], [`Helper::LoadNewTarget`], and
//! [`Helper::CreatePrivateName`]. They still use the completion ABI (result in
//! `out.value`) but their abnormal edge is unreachable, so they never mark a
//! handler block reachable.
//!
//! ## Opcode ledger (every variant has an explicit path)
//!
//! | Opcode              | Lowering                                                     |
//! |---------------------|-------------------------------------------------------------|
//! | `LoadConst`         | [`Helper::LoadConstant`] by `ConstantId` → `dst`            |
//! | `Move`              | inline copy `handles[src]` → `handles[dst]`                 |
//! | `Unary`             | [`Helper::Unary`] with the operator selector               |
//! | `Binary`            | [`Helper::Binary`] with the operator selector              |
//! | `CreateObject`      | [`Helper::CreateObject`] → `dst`                            |
//! | `ToObject`          | [`Helper::ToObject`] (`src`) → `dst`; throws on nullish    |
//! | `CreateArray`       | [`Helper::CreateArray`] → `dst`                             |
//! | `CreateCell`        | [`Helper::CreateCell`] → `dst`                             |
//! | `CreateClosure`     | [`Helper::CreateClosure`] (`function`, `captures` array)→dst|
//! | `GetProperty`       | [`Helper::GetProperty`] (`object`, register `key`) → `dst`  |
//! | `SetProperty`       | [`Helper::SetProperty`] (`object`, register `key`, `value`) |
//! | `DefineDataProperty`| [`Helper::DefineDataProperty`] (`object`, register `key`, `value`) |
//! | `LoadOwnDescriptorSlot` | [`Helper::LoadOwnDescriptorSlot`] (`object`, register `key`, slot) → `dst` |
//! | `DefineOwnDescriptorSlot` | [`Helper::DefineOwnDescriptorSlot`] (`object`, register `key`, `src`, slot) |
//! | `WithHasBinding`    | [`Helper::WithHasBinding`] (`object`, register `key`) → `dst` |
//! | `DeleteProperty`    | [`Helper::DeleteProperty`] (`object`, register `key`) → dst |
//! | `DefineAccessor`    | [`Helper::DefineAccessor`] (`object`, `key`, `accessor`, kind)|
//! | `Call`              | [`Helper::Call`] (`callee`, `this`, `arguments` array) → dst|
//! | `Construct`         | [`Helper::Construct`] (`callee`, `arguments` array) → `dst` |
//! | `ConstructWithNewTarget` | [`Helper::ConstructWithNewTarget`] (`callee`, `new_target`, `arguments` array) → `dst` |
//! | `LoadGlobal`        | [`Helper::LoadGlobal`] by string `name` → `dst`            |
//! | `StoreGlobal`       | [`Helper::StoreGlobal`] (string `name`, `value`)          |
//! | `TypeOfGlobal`      | [`Helper::TypeOfGlobal`] by string `name` → `dst` (total)  |
//! | `LoadThis`          | [`Helper::LoadThis`] → `dst` (total)                       |
//! | `LoadArguments`     | [`Helper::LoadArguments`] → `dst` (total)                  |
//! | `LoadNewTarget`     | [`Helper::LoadNewTarget`] → `dst` (total)                  |
//! | `ArrayPush`         | [`Helper::ArrayPush`] (`array`, `value`)                   |
//! | `ArrayExtend`       | [`Helper::ArrayExtend`] (`array`, `iterable`)              |
//! | `ObjectSpread`      | [`Helper::ObjectSpread`] (`target`, `source`)             |
//! | `SetPrototype`      | [`Helper::SetPrototype`] (`object`, `prototype`)          |
//! | `CreatePrivateName` | [`Helper::CreatePrivateName`] by `description` → dst (total)|
//! | `CreateRegExp`      | [`Helper::CreateRegExp`] (`pattern`, `flags`) → `dst`      |
//! | `GetIterator`       | [`Helper::GetIterator`] (`src`, kind) → `dst`             |
//! | `IteratorNext`      | [`Helper::IteratorNext`] (`iterator`) → `done` + `value`   |
//! | `IteratorStep`      | [`Helper::IteratorStep`] (`iterator`) → `dst` (raw result) |
//! | `IteratorResult`    | [`Helper::IteratorResult`] (`result`) → `done` + `value`   |
//! | `IteratorClose`     | [`Helper::IteratorClose`] (`iterator`, mode) → `result` + `called` |
//! | `RequireCloseResult` | [`Helper::RequireCloseResult`] (`result`, `called`)               |
//! | `DisposeCapture`    | [`Helper::DisposeCapture`] (`src`, hint) → `method` + `kind`       |
//! | `SuppressError`     | [`Helper::SuppressError`] (`error`, `suppressed`) → `dst`               |
//! | `Import`            | [`Helper::Import`] by string `specifier` → `dst`          |
//! | `Export`            | [`Helper::Export`] (string `name`, `src`)                 |
//! | `Jump`              | unconditional branch                                       |
//! | `JumpIfTrue`        | [`Helper::Truthy`] then conditional branch                |
//! | `JumpIfFalse`       | [`Helper::Truthy`] then conditional branch                |
//! | `Return`            | `handles[value]` → `out.value`, return `Normal`           |
//! | `Throw`             | route to covering handler (bind `catch_register`) or       |
//! |                     | `out.value` + return `Throw`                              |
//! | `Suspend`           | yield path + resume path via [`Helper::ResumeValue`]/[`Helper::ResumeMode`] |
//! | `Await`             | same value resume as `Suspend`; no mode helper            |
//! | `Halt`              | `undefined` → `out.value`, return `Normal`               |
//!
//! No opcode is silently dropped and none is lowered to a placeholder no-op.
//!
//! # Exceptions
//!
//! When a completion-helper call returns `Throw` and a bytecode handler covers
//! the current pc, control branches to that handler's block after storing the
//! thrown value (`out.value`) into the handler's `catch_register` slot; the
//! explicit `Throw` opcode binds its operand into `catch_register` directly.
//! `FatalTrap` bypasses handlers. When no handler covers the pc, the completion
//! is returned to the caller.
//!
//! # Suspend/Await and the resume helper
//!
//! `Suspend { dst, src, resume, mode }` (the `yield` form) and
//! `Await { dst, src, resume }` (the `await` form) share one suspension ABI:
//! yield `src` and, when resumed, deliver the resumed value into `dst` and the
//! completion mode into `mode` before continuing at `resume`. The native entry
//! ABI carries no resume input (`out.value` is the *yielded* value, not an
//! input), so the resumed value and mode are obtained through an explicit
//! runtime contract rather than invented:
//!
//! * **Yield path** — store this suspension's resume token into `frame.bytecode_pc`
//!   (`0` is a fresh call; the `Suspend`/`Await` at bytecode pc `P` uses token
//!   `P + 1`, so tokens never collide with a fresh entry or with each other),
//!   write `src` into `out.value`, and return `Suspend`.
//! * **Resume path** — the dispatch prologue for token `P + 1` calls
//!   [`Helper::ResumeValue`], which the runtime resolves to write the resumed
//!   completion value for this frame into `out.value` (it may return `Throw` for
//!   `generator.throw`, routed to a covering handler, or `FatalTrap`); the
//!   resumed value is then stored into `dst`. For [`Instruction::Suspend`] only,
//!   the prologue then calls [`Helper::ResumeMode`], which writes the mode
//!   (`0` = Next, `1` = Throw, `2` = Return) into `out.value` and stores it
//!   into `mode` before continuing at `resume`.
//!
//! `bamts_bytecode` currently exposes no ABI for the resume input, so
//! [`Helper::ResumeValue`] and [`Helper::ResumeMode`] are **new required
//! contracts** the runtime must provide for any module that suspends.

#![deny(unsafe_code)]

#[cfg(feature = "host-jit")]
#[path = "jit/helpers.rs"]
pub mod helpers;
#[cfg(feature = "host-jit")]
mod jit;
#[cfg(feature = "host-jit")]
#[allow(unsafe_code)]
mod jit_memory;
#[cfg(feature = "host-jit")]
pub use jit::{
    JitError, JitProgram, JitTelemetry, compile_jit, compile_jit_with_cancel,
    compile_jit_with_telemetry, compile_jit_with_telemetry_cancel,
};

#[cfg(feature = "aot")]
mod aot;
#[cfg(feature = "aot")]
pub use aot::{
    AotError, AotObject, BuildCacheKey, EmissionError, EmittedObject, LinkCacheKey, LinkError,
    LinkFlags, LinkInput, LinkInputRole, LinkPlan, LinkProvenance, PROGRAM_DESCRIPTOR_SYMBOL,
    REPRODUCIBLE_FILE_NAME, ReproducibleArtifact, ReproducibleError, SUPPORTED_TARGET_TRIPLES,
    TargetDescriptor, TargetFormat, canonical_object_metadata, compile_aot,
    compile_aot_with_cancel, content_digest, emit_for_target, emit_for_target_with_cancel,
    emit_for_targets, emit_reproducible, plan_link, require_matching_target, resolve_symbols,
    validate_linked_image,
};
#[cfg(all(feature = "aot", feature = "host-jit"))]
pub use aot::{
    HostTargetError, LinkedAotProgram, NativeExecutionReport, host_target, link_aot_in_process,
};

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use bamts_bytecode::{
    AccessorKind, BinaryOp, DescriptorSlot, DisposeHint, ExceptionHandler, FunctionId, Instruction,
    IteratorCloseMode, IteratorKind, Module, ModuleId, Pc, Program, Register, UnaryOp, Verified,
};
use bamts_cancel::{CancellationToken, Cancelled};

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{
    AbiParam, Block, ExtFuncData, ExternalName, Function, InstBuilder, MemFlagsData, Signature,
    Type, UserExternalName, UserFuncName, Value, types,
};
use cranelift_codegen::isa::{CallConv, TargetFrontendConfig};
use cranelift_codegen::settings::{self, Flags};
use cranelift_codegen::verifier::verify_function;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};

// -- ABI layout (grounded in bamts_native::ShadowFrame / Completion / Value) --

/// Byte offset of `ShadowFrame.bytecode_pc` (a `u32`).
const SHADOW_FRAME_PC_OFFSET: i32 = 8;
/// Byte offset of `ShadowFrame.module_id` (a `u32`).
#[cfg(feature = "host-jit")]
const SHADOW_FRAME_MODULE_OFFSET: i32 = 12;
/// Byte offset of `ShadowFrame.handles` (a `*mut Value`).
const SHADOW_FRAME_HANDLES_OFFSET: i32 = 16;
/// Byte offset of `Completion.value` within the out-parameter.
const COMPLETION_VALUE_OFFSET: i32 = 0;
/// Size, in bytes, of one register slot (`Value` is a `u64`).
const VALUE_BYTES: i64 = 8;

/// Canonical `undefined`, matching `bamts_native::Value::UNDEFINED`
/// (`boxed(TAG_UNDEFINED=3, 0)` = `0x7ff8… | 3<<48`).
const UNDEFINED_BITS: i64 = 0x7ffb_0000_0000_0000;

/// `TrapRecordId` written to `out.value` when resumed at an unknown token.
const TRAP_INVALID_RESUME: i64 = 1;

/// [`CompletionTag::Normal`] discriminant.
const TAG_NORMAL: i64 = 0;
/// [`CompletionTag::Throw`] discriminant.
const TAG_THROW: i64 = 1;
/// [`CompletionTag::Suspend`] discriminant.
const TAG_SUSPEND: i64 = 2;
/// [`CompletionTag::FatalTrap`] discriminant.
const TAG_FATAL_TRAP: i64 = 3;

/// Cranelift external-name namespace for lowered bytecode functions: a name
/// `u0:<index>` refers to the lowered function whose [`FunctionId`] is `index`.
pub const FUNCTION_NAMESPACE: u32 = 0;
/// Cranelift external-name namespace for runtime helper imports: a name
/// `u1:<index>` refers to the [`Helper`] with [`Helper::external_index`]
/// equal to `index`.
pub const HELPER_NAMESPACE: u32 = 1;

// When the native crate is present, prove the hardcoded ABI facts still match
// its authoritative definitions. This slice's default build does not depend on
// bamts-native, so these are compiled only under the JIT-entry feature.
#[cfg(feature = "host-jit")]
const _: () = {
    use core::mem::offset_of;
    assert!(offset_of!(bamts_native::ShadowFrame, bytecode_pc) == SHADOW_FRAME_PC_OFFSET as usize);
    assert!(
        offset_of!(bamts_native::ShadowFrame, module_id) == SHADOW_FRAME_MODULE_OFFSET as usize
    );
    assert!(offset_of!(bamts_native::ShadowFrame, handles) == SHADOW_FRAME_HANDLES_OFFSET as usize);
    assert!(core::mem::size_of::<bamts_native::Completion>() == VALUE_BYTES as usize);
    assert!(bamts_native::Value::UNDEFINED.to_bits() == UNDEFINED_BITS as u64);
    assert!(bamts_native::CompletionTag::Normal.as_u32() as i64 == TAG_NORMAL);
    assert!(bamts_native::CompletionTag::Throw.as_u32() as i64 == TAG_THROW);
    assert!(bamts_native::CompletionTag::Suspend.as_u32() as i64 == TAG_SUSPEND);
    assert!(bamts_native::CompletionTag::FatalTrap.as_u32() as i64 == TAG_FATAL_TRAP);
};

// -- Runtime helpers ---------------------------------------------------------

/// A runtime routine the lowered code calls but does not define. Backends
/// resolve each [`Helper::symbol`] to an address (JIT) or relocation (AOT).
///
/// # Stable helper table
///
/// The variant order below is the canonical `external_index` order and the
/// public contract a backend and the runtime link against. `frame` (`i64`)
/// leads and `out` (`*mut Completion`, `i64`) trails every completion helper;
/// runtime `Value`s are `i64`; small integer selectors and indices are `i32`.
///
/// | idx | variant             | params after `frame` (before `out`)          |
/// |-----|---------------------|----------------------------------------------|
/// |  0  | `LoadConstant`      | `const_id: i32`                              |
/// |  1  | `Unary`             | `op: i32, operand: i64`                      |
/// |  2  | `Binary`            | `op: i32, left: i64, right: i64`            |
/// |  3  | `CreateObject`      | —                                            |
/// |  4  | `CreateArray`       | —                                            |
/// |  5  | `CreateClosure`     | `function_id: i32, captures: i64`           |
/// |  6  | `GetProperty`       | `object: i64, key: i64`                     |
/// |  7  | `SetProperty`       | `object: i64, key: i64, value: i64`         |
/// |  8  | `DeleteProperty`    | `object: i64, key: i64`                     |
/// |  9  | `Call`              | `callee: i64, this: i64, arguments: i64`    |
/// | 10  | `Construct`         | `callee: i64, arguments: i64`               |
/// | 11  | `Import`            | `specifier: i32`                            |
/// | 12  | `Truthy`            | `value: i64` → `i32` (no `out`, total)      |
/// | 13  | `ResumeValue`       | —                                            |
/// | 14  | `DefineAccessor`    | `object: i64, key: i64, accessor: i64, kind: i32` |
/// | 15  | `LoadGlobal`        | `name: i32`                                 |
/// | 16  | `StoreGlobal`       | `name: i32, value: i64`                     |
/// | 17  | `TypeOfGlobal`      | `name: i32` (total)                         |
/// | 18  | `LoadThis`          | — (total)                                   |
/// | 19  | `LoadArguments`     | — (total)                                   |
/// | 20  | `LoadNewTarget`     | — (total)                                   |
/// | 21  | `ArrayPush`         | `array: i64, value: i64`                    |
/// | 22  | `ArrayExtend`       | `array: i64, iterable: i64`                 |
/// | 23  | `ObjectSpread`      | `target: i64, source: i64`                  |
/// | 24  | `SetPrototype`      | `object: i64, prototype: i64`               |
/// | 25  | `CreatePrivateName` | `description: i32` (total)                  |
/// | 26  | `CreateRegExp`      | `pattern: i32, flags: i32`                  |
/// | 27  | `GetIterator`       | `src: i64, kind: i32`                        |
/// | 28  | `IteratorNext`      | `iterator: i64, done_reg: i32, value_reg: i32` (two-write) |
/// | 29  | `Export`            | `name: i32, src: i64`                        |
/// | 30  | `ConsumeFuel`       | `amount: i32` (total except `FatalTrap`)     |
/// | 31 | `CreateCell`        | —                                            |
/// | 32 | `IteratorStep`      | `iterator: i64` (raw, possibly-promised result) |
/// | 33 | `IteratorResult`    | `result: i64, done_reg: i32, value_reg: i32` (two-write) |
/// | 34 | `IteratorClose`     | `iterator: i64, mode: i32, called_reg: i32`  |
/// | 35 | `RequireCloseResult` | `result: i64, called: i64`                  |
/// | 39 | `DisposeCapture`    | `src: i64, hint: i32, kind_reg: i32`        |
/// | 40 | `SuppressError`     | `error: i64, suppressed: i64`              |
/// | 41 | `ConstructWithNewTarget` | `callee: i64, new_target: i64, arguments: i64` |
/// | 42 | `DefineDataProperty` | `object: i64, key: i64, value: i64`         |
/// | 43 | `LoadOwnDescriptorSlot` | `object: i64, key: i64, slot: i32`      |
/// | 44 | `DefineOwnDescriptorSlot` | `object: i64, key: i64, src: i64, slot: i32` |
/// | 45 | `WithHasBinding`    | `object: i64, key: i64`                     |
/// | 46 | `ResumeMode`        | —                                            |
///
/// Every helper except [`Helper::Truthy`] returns a
/// `bamts_native::CompletionTag`. [`Helper::Truthy`] returns `0`/`1`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Helper {
    /// `bamts_load_constant(frame, const_id, out)`: materialize the module
    /// constant named by `const_id` into `out.value`.
    LoadConstant,
    /// `bamts_unary(frame, op, operand, out)`: apply the unary operator `op`
    /// (see `unary_op_selector`) to `operand`.
    Unary,
    /// `bamts_binary(frame, op, left, right, out)`: apply the binary operator
    /// `op` (see `binary_op_selector`) to `left` and `right`.
    Binary,
    /// `bamts_create_object(frame, out)`: fresh empty object into `out.value`.
    CreateObject,
    /// `bamts_create_array(frame, out)`: fresh empty array into `out.value`.
    CreateArray,
    /// `bamts_create_cell(frame, out)`: fresh compiler-private TDZ cell.
    CreateCell,
    /// `bamts_create_closure(frame, function_id, captures, out)`: materialize a
    /// closure over the named function, binding the captured cells held in the
    /// `captures` array value, into `out.value`. The runtime reads the callee's
    /// `capture_count` to copy the leading capture registers.
    CreateClosure,
    /// `bamts_get_property(frame, object, key, out)`: `out.value = object[key]`,
    /// with `key` a runtime value coerced to a property key.
    GetProperty,
    /// `bamts_set_property(frame, object, key, value, out)`: `object[key] = value`.
    SetProperty,
    /// `bamts_delete_property(frame, object, key, out)`:
    /// `out.value = delete object[key]`.
    DeleteProperty,
    /// `bamts_call(frame, callee, this, arguments, out)`: call `callee` with
    /// receiver `this` over the dynamic `arguments` array value.
    Call,
    /// `bamts_construct(frame, callee, arguments, out)`: construct with `callee`
    /// over the dynamic `arguments` array value.
    Construct,
    /// `bamts_import(frame, specifier, out)`: import the module named by the
    /// string constant `specifier` into `out.value`.
    Import,
    /// `bamts_truthy(frame, value) -> u32`: the total ToBoolean coercion,
    /// returning `1` when `value` is truthy and `0` otherwise. Never throws and
    /// never writes `out`.
    Truthy,
    /// `bamts_resume_value(frame, out)`: write the verified resumed value for
    /// `frame` into `out.value`. The helper only reports the value;
    /// [`Helper::ResumeMode`] supplies and consumes the resume completion.
    ResumeValue,
    /// `bamts_define_accessor(frame, object, key, accessor, kind, out)`: install
    /// a getter or setter (`kind`, see `accessor_kind_selector`) under `key`.
    DefineAccessor,
    /// `bamts_load_global(frame, name, out)`: `out.value = globalThis[name]`;
    /// throws a `ReferenceError` for an undeclared global.
    LoadGlobal,
    /// `bamts_store_global(frame, name, value, out)`: `globalThis[name] = value`.
    StoreGlobal,
    /// `bamts_typeof_global(frame, name, out)`: `out.value = typeof
    /// globalThis[name]`; total, yielding `"undefined"` for an undeclared global.
    TypeOfGlobal,
    /// `bamts_load_this(frame, out)`: load the `this` binding into `out.value`.
    /// Total.
    LoadThis,
    /// `bamts_load_arguments(frame, out)`: load the `arguments` object into
    /// `out.value`. Total.
    LoadArguments,
    /// `bamts_load_new_target(frame, out)`: load `new.target` into `out.value`.
    /// Total.
    LoadNewTarget,
    /// `bamts_array_push(frame, array, value, out)`: append `value` to `array`.
    ArrayPush,
    /// `bamts_array_extend(frame, array, iterable, out)`: spread `iterable` onto
    /// the end of `array`.
    ArrayExtend,
    /// `bamts_object_spread(frame, target, source, out)`: copy the own
    /// enumerable properties of `source` onto `target`.
    ObjectSpread,
    /// `bamts_set_prototype(frame, object, prototype, out)`: set the
    /// `[[Prototype]]` of `object`.
    SetPrototype,
    /// `bamts_create_private_name(frame, description, out)`: create a fresh
    /// private name into `out.value`. Total.
    CreatePrivateName,
    /// `bamts_create_regexp(frame, pattern, flags, out)`: build a `RegExp` from
    /// the string-constant `pattern` and `flags` into `out.value`.
    CreateRegExp,
    /// `bamts_get_iterator(frame, src, kind, out)`: acquire an iterator over
    /// `src` using protocol `kind` (see `iterator_kind_selector`).
    GetIterator,
    /// `bamts_iterator_next(frame, iterator, done_reg, value_reg, out)`: advance
    /// `iterator`, writing the done flag into `handles[done_reg]` and the
    /// produced value into `handles[value_reg]` directly (two writes). On
    /// `Throw`, the thrown handle is in `out.value` and neither slot is written.
    IteratorNext,
    /// `bamts_export(frame, name, src, out)`: export the local value `src` under
    /// the string constant `name`.
    Export,
    /// `bamts_consume_fuel(frame, amount, out)`: reserve `amount` bytecode
    /// instructions from the shared machine budget. Returns `FatalTrap` on
    /// exhaustion and never routes through a bytecode exception handler.
    ConsumeFuel,
    /// `bamts_iterator_step(frame, iterator, out)`: advance `iterator`,
    /// writing the raw iterator result object (possibly a promise for an
    /// async iterator) into `out.value`. `for await` suspends on that result
    /// before [`Helper::IteratorResult`] reads it.
    IteratorStep,
    /// `bamts_iterator_result(frame, result, done_reg, value_reg, out)`:
    /// validate the iterator result object `result`, writing the done flag
    /// into `handles[done_reg]` and the produced value into
    /// `handles[value_reg]` directly (two writes), exactly like
    /// [`Helper::IteratorNext`]. On `Throw`, the thrown handle is in
    /// `out.value` and neither slot is written.
    IteratorResult,
    /// `bamts_iterator_close(frame, iterator, mode, called_reg, out)`: close
    /// `iterator`, writing whether callable `return` was invoked into
    /// `handles[called_reg]` before invocation and the raw close result into
    /// `out.value`; `mode` selects whether a user close throw propagates or
    /// preserves an existing abrupt completion.
    IteratorClose,
    /// `bamts_require_close_result(frame, result, called, out)`: throw when
    /// `called` is true and `result` is not an object.
    RequireCloseResult,
    /// `bamts_to_object(frame, value, out)`: ECMAScript ToObject coercion.
    ToObject,
    /// `bamts_import_dynamic(frame, specifier, out)`: runtime expression import.
    ImportDynamic,
    /// `bamts_load_import_meta(frame, out)`: load the current module's cached import-meta object.
    LoadImportMeta,
    /// `bamts_dispose_capture(frame, src, hint, kind_reg, out)`: capture a
    /// callable disposal method into `out.value` and write its kind directly
    /// into `handles[kind_reg]` on normal completion.
    DisposeCapture,
    /// `bamts_suppress_error(frame, error, suppressed, out)`: allocate the
    /// intrinsic SuppressedError chain node without consulting the global binding.
    SuppressError,
    /// `bamts_construct_with_new_target(frame, callee, new_target, arguments, out)`:
    /// construct with `callee` over the dynamic `arguments` array value,
    /// installing the explicit `new_target` instead of `callee`.
    ConstructWithNewTarget,
    /// `bamts_define_data_property(frame, object, key, value, out)`: define an own
    /// data property on `object` at register `key` with `value` (fixed descriptor).
    DefineDataProperty,
    /// `bamts_load_own_descriptor_slot(frame, object, key, slot, out)`: read one
    /// own-descriptor slot (`slot`, see `descriptor_slot_selector`) of
    /// `object[key]` into `out.value` without invoking accessors or walking the
    /// prototype chain. Codegen transports `key` once as a raw `i64` Value; the
    /// Machine helper coerces it to a property key.
    LoadOwnDescriptorSlot,
    /// `bamts_define_own_descriptor_slot(frame, object, key, src, slot, out)`:
    /// write `src` into one own-descriptor slot (`slot`, see
    /// `descriptor_slot_selector`) of `object[key]`, preserving sibling
    /// attributes and the opposite accessor half. Codegen transports `key` once
    /// as a raw `i64` Value; the Machine helper coerces it to a property key.
    DefineOwnDescriptorSlot,
    /// `bamts_with_has_binding(frame, object, key, out)`: Object Environment
    /// Record `HasBinding` for a `with` binding object. Uses the realm-owned
    /// `%Symbol.unscopables%` intrinsic and writes a Boolean into `out.value`.
    WithHasBinding,
    /// `bamts_resume_mode(frame, out)`: write the resumed completion mode for
    /// `frame` into `out.value`, consuming the pending completion after
    /// [`Helper::ResumeValue`] observed it.
    ResumeMode,
    /// `bamts_get_super(frame, home, receiver, key, out)`: read `key` through
    /// `home`'s prototype with `receiver` as the receiver.
    GetSuper,
    /// `bamts_set_super(frame, home, receiver, key, value, out)`: write `key`
    /// through `home`'s prototype with `receiver` as the receiver.
    SetSuper,
    /// `bamts_import_attributes(frame, specifier, attributes, out)`: import the
    /// module named by `specifier` with the supplied attributes object.
    ImportAttributes,
    /// `bamts_import_dynamic_attributes(frame, specifier, attributes, out)`:
    /// evaluate `import(specifier, { with: attributes })`.
    ImportDynamicAttributes,
    /// `bamts_copy_data_properties(frame, target, source, excluded, out)`: copy
    /// own enumerable data properties from `source` to `target`.
    CopyDataProperties,
    /// `bamts_get_template_object(frame, cooked, raw, out)`: return the
    /// template object interned by cooked-array identity.
    GetTemplateObject,
    /// `bamts_require_global_binding(frame, name, out)`: throw a
    /// `ReferenceError` unless the global `name` is bound, reading no value.
    RequireGlobalBinding,
}

impl Helper {
    /// The C symbol the backend links against.
    #[must_use]
    pub const fn symbol(self) -> &'static str {
        match self {
            Helper::LoadConstant => "bamts_load_constant",
            Helper::Unary => "bamts_unary",
            Helper::Binary => "bamts_binary",
            Helper::CreateObject => "bamts_create_object",
            Helper::CreateArray => "bamts_create_array",
            Helper::CreateClosure => "bamts_create_closure",
            Helper::GetProperty => "bamts_get_property",
            Helper::SetProperty => "bamts_set_property",
            Helper::DeleteProperty => "bamts_delete_property",
            Helper::Call => "bamts_call",
            Helper::Construct => "bamts_construct",
            Helper::Import => "bamts_import",
            Helper::Truthy => "bamts_truthy",
            Helper::ResumeValue => "bamts_resume_value",
            Helper::DefineAccessor => "bamts_define_accessor",
            Helper::LoadGlobal => "bamts_load_global",
            Helper::StoreGlobal => "bamts_store_global",
            Helper::TypeOfGlobal => "bamts_typeof_global",
            Helper::LoadThis => "bamts_load_this",
            Helper::LoadArguments => "bamts_load_arguments",
            Helper::LoadNewTarget => "bamts_load_new_target",
            Helper::ArrayPush => "bamts_array_push",
            Helper::ArrayExtend => "bamts_array_extend",
            Helper::ObjectSpread => "bamts_object_spread",
            Helper::SetPrototype => "bamts_set_prototype",
            Helper::CreatePrivateName => "bamts_create_private_name",
            Helper::CreateRegExp => "bamts_create_regexp",
            Helper::GetIterator => "bamts_get_iterator",
            Helper::IteratorNext => "bamts_iterator_next",
            Helper::IteratorStep => "bamts_iterator_step",
            Helper::IteratorResult => "bamts_iterator_result",
            Helper::IteratorClose => "bamts_iterator_close",
            Helper::RequireCloseResult => "bamts_require_close_result",
            Helper::ToObject => "bamts_to_object",
            Helper::ImportDynamic => "bamts_import_dynamic",
            Helper::LoadImportMeta => "bamts_load_import_meta",
            Helper::DisposeCapture => "bamts_dispose_capture",
            Helper::SuppressError => "bamts_suppress_error",
            Helper::ConstructWithNewTarget => "bamts_construct_with_new_target",
            Helper::DefineDataProperty => "bamts_define_data_property",
            Helper::LoadOwnDescriptorSlot => "bamts_load_own_descriptor_slot",
            Helper::DefineOwnDescriptorSlot => "bamts_define_own_descriptor_slot",
            Helper::WithHasBinding => "bamts_with_has_binding",
            Helper::Export => "bamts_export",
            Helper::ConsumeFuel => "bamts_consume_fuel",
            Helper::CreateCell => "bamts_create_cell",
            Helper::ResumeMode => "bamts_resume_mode",
            Helper::GetSuper => "bamts_get_super",
            Helper::SetSuper => "bamts_set_super",
            Helper::ImportAttributes => "bamts_import_attributes",
            Helper::ImportDynamicAttributes => "bamts_import_dynamic_attributes",
            Helper::CopyDataProperties => "bamts_copy_data_properties",
            Helper::GetTemplateObject => "bamts_get_template_object",
            Helper::RequireGlobalBinding => "bamts_require_global_binding",
        }
    }

    /// The stable helper index within [`HELPER_NAMESPACE`]; the `index` of the
    /// `u1:<index>` external name a backend must resolve to [`Helper::symbol`].
    #[must_use]
    pub const fn external_index(self) -> u32 {
        match self {
            Helper::LoadConstant => 0,
            Helper::Unary => 1,
            Helper::Binary => 2,
            Helper::CreateObject => 3,
            Helper::CreateArray => 4,
            Helper::CreateClosure => 5,
            Helper::GetProperty => 6,
            Helper::SetProperty => 7,
            Helper::DeleteProperty => 8,
            Helper::Call => 9,
            Helper::Construct => 10,
            Helper::Import => 11,
            Helper::Truthy => 12,
            Helper::ResumeValue => 13,
            Helper::DefineAccessor => 14,
            Helper::LoadGlobal => 15,
            Helper::StoreGlobal => 16,
            Helper::TypeOfGlobal => 17,
            Helper::LoadThis => 18,
            Helper::LoadArguments => 19,
            Helper::LoadNewTarget => 20,
            Helper::ArrayPush => 21,
            Helper::ArrayExtend => 22,
            Helper::ObjectSpread => 23,
            Helper::SetPrototype => 24,
            Helper::CreatePrivateName => 25,
            Helper::CreateRegExp => 26,
            Helper::GetIterator => 27,
            Helper::IteratorNext => 28,
            Helper::Export => 29,
            Helper::ConsumeFuel => 30,
            Helper::CreateCell => 31,
            Helper::IteratorStep => 32,
            Helper::IteratorResult => 33,
            Helper::IteratorClose => 34,
            Helper::RequireCloseResult => 35,
            Helper::ToObject => 36,
            Helper::ImportDynamic => 37,
            Helper::LoadImportMeta => 38,
            Helper::DisposeCapture => 39,
            Helper::SuppressError => 40,
            Helper::ConstructWithNewTarget => 41,
            Helper::DefineDataProperty => 42,
            Helper::LoadOwnDescriptorSlot => 43,
            Helper::DefineOwnDescriptorSlot => 44,
            Helper::WithHasBinding => 45,
            Helper::ResumeMode => 46,
            Helper::GetSuper => 47,
            Helper::SetSuper => 48,
            Helper::ImportAttributes => 49,
            Helper::ImportDynamicAttributes => 50,
            Helper::CopyDataProperties => 51,
            Helper::GetTemplateObject => 52,
            Helper::RequireGlobalBinding => 53,
        }
    }

    /// The helper for a [`HELPER_NAMESPACE`] external-name index, inverting
    /// [`Helper::external_index`]. Returns `None` for an unknown index.
    #[must_use]
    pub const fn from_external_index(index: u32) -> Option<Helper> {
        match index {
            0 => Some(Helper::LoadConstant),
            1 => Some(Helper::Unary),
            2 => Some(Helper::Binary),
            3 => Some(Helper::CreateObject),
            4 => Some(Helper::CreateArray),
            5 => Some(Helper::CreateClosure),
            6 => Some(Helper::GetProperty),
            7 => Some(Helper::SetProperty),
            8 => Some(Helper::DeleteProperty),
            9 => Some(Helper::Call),
            10 => Some(Helper::Construct),
            11 => Some(Helper::Import),
            12 => Some(Helper::Truthy),
            13 => Some(Helper::ResumeValue),
            14 => Some(Helper::DefineAccessor),
            15 => Some(Helper::LoadGlobal),
            16 => Some(Helper::StoreGlobal),
            17 => Some(Helper::TypeOfGlobal),
            18 => Some(Helper::LoadThis),
            19 => Some(Helper::LoadArguments),
            20 => Some(Helper::LoadNewTarget),
            21 => Some(Helper::ArrayPush),
            22 => Some(Helper::ArrayExtend),
            23 => Some(Helper::ObjectSpread),
            24 => Some(Helper::SetPrototype),
            25 => Some(Helper::CreatePrivateName),
            26 => Some(Helper::CreateRegExp),
            27 => Some(Helper::GetIterator),
            28 => Some(Helper::IteratorNext),
            29 => Some(Helper::Export),
            30 => Some(Helper::ConsumeFuel),
            31 => Some(Helper::CreateCell),
            32 => Some(Helper::IteratorStep),
            33 => Some(Helper::IteratorResult),
            34 => Some(Helper::IteratorClose),
            35 => Some(Helper::RequireCloseResult),
            36 => Some(Helper::ToObject),
            37 => Some(Helper::ImportDynamic),
            38 => Some(Helper::LoadImportMeta),
            39 => Some(Helper::DisposeCapture),
            40 => Some(Helper::SuppressError),
            41 => Some(Helper::ConstructWithNewTarget),
            42 => Some(Helper::DefineDataProperty),
            43 => Some(Helper::LoadOwnDescriptorSlot),
            44 => Some(Helper::DefineOwnDescriptorSlot),
            45 => Some(Helper::WithHasBinding),
            46 => Some(Helper::ResumeMode),
            47 => Some(Helper::GetSuper),
            48 => Some(Helper::SetSuper),
            49 => Some(Helper::ImportAttributes),
            50 => Some(Helper::ImportDynamicAttributes),
            51 => Some(Helper::CopyDataProperties),
            52 => Some(Helper::GetTemplateObject),
            53 => Some(Helper::RequireGlobalBinding),
            _ => None,
        }
    }

    /// The helper parameter types, in order. `frame` and `out` pointers and
    /// runtime `Value`s are `i64`; small integer selectors and indices are
    /// `i32`.
    const fn param_types(self) -> &'static [Type] {
        match self {
            // (frame, const_id, out)
            Helper::LoadConstant => &[types::I64, types::I32, types::I64],
            // (frame, op, operand, out)
            Helper::Unary => &[types::I64, types::I32, types::I64, types::I64],
            // (frame, op, left, right, out)
            Helper::Binary => &[types::I64, types::I32, types::I64, types::I64, types::I64],
            // (frame, out)
            Helper::CreateObject
            | Helper::CreateArray
            | Helper::CreateCell
            | Helper::ResumeValue
            | Helper::ResumeMode
            | Helper::LoadThis
            | Helper::LoadArguments
            | Helper::LoadNewTarget
            | Helper::LoadImportMeta => &[types::I64, types::I64],
            // (frame, index, out)
            Helper::Import
            | Helper::LoadGlobal
            | Helper::TypeOfGlobal
            | Helper::RequireGlobalBinding
            | Helper::CreatePrivateName
            | Helper::ConsumeFuel => &[types::I64, types::I32, types::I64],
            // (frame, value, out)
            Helper::ImportDynamic => &[types::I64, types::I64, types::I64],
            // (frame, function_id, captures, out)
            Helper::CreateClosure => &[types::I64, types::I32, types::I64, types::I64],
            // (frame, object, key, out)
            Helper::DeleteProperty | Helper::WithHasBinding => {
                &[types::I64, types::I64, types::I64, types::I64]
            }
            // (frame, object, key, site, out)
            Helper::GetProperty => &[
                types::I64,
                types::I64,
                types::I64,
                types::I32,
                types::I64,
            ],
            // (frame, object, key, value, out)
            Helper::DefineDataProperty => {
                &[types::I64, types::I64, types::I64, types::I64, types::I64]
            }
            // (frame, object, key, value, site, out)
            Helper::SetProperty => &[
                types::I64,
                types::I64,
                types::I64,
                types::I64,
                types::I32,
                types::I64,
            ],
            // (frame, object, key, accessor, kind, out) or
            // (frame, object, key, src, slot, out)
            Helper::DefineAccessor | Helper::DefineOwnDescriptorSlot => &[
                types::I64,
                types::I64,
                types::I64,
                types::I64,
                types::I32,
                types::I64,
            ],
            // (frame, object, key, slot, out)
            Helper::LoadOwnDescriptorSlot => {
                &[types::I64, types::I64, types::I64, types::I32, types::I64]
            }
            // (frame, callee, this/new_target, arguments, out)
            Helper::Call | Helper::ConstructWithNewTarget => {
                &[types::I64, types::I64, types::I64, types::I64, types::I64]
            }
            // (frame, callee, arguments, out)
            Helper::Construct => &[types::I64, types::I64, types::I64, types::I64],
            // (frame, a, b, out): array/object mutations over two value operands
            Helper::ArrayPush
            | Helper::ArrayExtend
            | Helper::ObjectSpread
            | Helper::SetPrototype => &[types::I64, types::I64, types::I64, types::I64],
            // (frame, name/selector, value, out): string-constant selector then value
            Helper::StoreGlobal | Helper::Export => {
                &[types::I64, types::I32, types::I64, types::I64]
            }
            // (frame, pattern, flags, out)
            Helper::CreateRegExp => &[types::I64, types::I32, types::I32, types::I64],
            // (frame, src, kind, out)
            Helper::GetIterator => &[types::I64, types::I64, types::I32, types::I64],
            // (frame, iterator, out)
            Helper::IteratorStep => &[types::I64, types::I64, types::I64],
            // (frame, value, out)
            Helper::ToObject => &[types::I64, types::I64, types::I64],
            // (frame, iterator/result, done_reg, value_reg, out)
            Helper::IteratorNext | Helper::IteratorResult => {
                &[types::I64, types::I64, types::I32, types::I32, types::I64]
            }
            // (frame, iterator, mode, called_reg, out) or
            // (frame, src, hint, kind_reg, out)
            Helper::IteratorClose | Helper::DisposeCapture => {
                &[types::I64, types::I64, types::I32, types::I32, types::I64]
            }
            // (frame, result, called, out)
            Helper::RequireCloseResult
            // (frame, error, suppressed, out)
            | Helper::SuppressError => &[types::I64, types::I64, types::I64, types::I64],
            // (frame, home, receiver, key, out)
            Helper::GetSuper => &[types::I64, types::I64, types::I64, types::I64, types::I64],
            // (frame, home, receiver, key, value, out)
            Helper::SetSuper => &[
                types::I64,
                types::I64,
                types::I64,
                types::I64,
                types::I64,
                types::I64,
            ],
            // (frame, specifier, attributes, out)
            Helper::ImportAttributes => &[types::I64, types::I32, types::I64, types::I64],
            // (frame, specifier, attributes, out)
            Helper::ImportDynamicAttributes => &[types::I64, types::I64, types::I64, types::I64],
            // (frame, target, source, excluded, out)
            Helper::CopyDataProperties => &[types::I64, types::I64, types::I64, types::I64, types::I64],
            // (frame, cooked, raw, out)
            Helper::GetTemplateObject => &[types::I64, types::I64, types::I64, types::I64],
            // (frame, value)
            Helper::Truthy => &[types::I64, types::I64],
        }
    }

    /// The helper's Cranelift signature under `call_conv`. Every helper returns
    /// an `i32` (a completion tag, or the `0`/`1` truth value for
    /// [`Helper::Truthy`]).
    fn signature(self, call_conv: CallConv) -> Signature {
        let mut signature = Signature::new(call_conv);
        for &ty in self.param_types() {
            signature.params.push(AbiParam::new(ty));
        }
        signature.returns.push(AbiParam::new(types::I32));
        signature
    }
}

/// The ABI operator selector for a unary operator, passed as the `op` argument
/// to [`Helper::Unary`]. This is the stable codegen-side operator encoding.
const fn unary_op_selector(op: UnaryOp) -> i64 {
    match op {
        UnaryOp::Void => 0,
        UnaryOp::TypeOf => 1,
        UnaryOp::Plus => 2,
        UnaryOp::Negate => 3,
        UnaryOp::BitwiseNot => 4,
        UnaryOp::LogicalNot => 5,
        UnaryOp::ToString => 6,
        UnaryOp::ToPropertyKey => 7,
    }
}

/// The ABI operator selector for a binary operator, passed as the `op` argument
/// to [`Helper::Binary`]. This is the stable codegen-side operator encoding.
const fn binary_op_selector(op: BinaryOp) -> i64 {
    match op {
        BinaryOp::Add => 0,
        BinaryOp::Subtract => 1,
        BinaryOp::Multiply => 2,
        BinaryOp::Divide => 3,
        BinaryOp::Remainder => 4,
        BinaryOp::Exponent => 5,
        BinaryOp::BitAnd => 6,
        BinaryOp::BitOr => 7,
        BinaryOp::BitXor => 8,
        BinaryOp::ShiftLeft => 9,
        BinaryOp::ShiftRight => 10,
        BinaryOp::UnsignedShiftRight => 11,
        BinaryOp::Equal => 12,
        BinaryOp::NotEqual => 13,
        BinaryOp::StrictEqual => 14,
        BinaryOp::StrictNotEqual => 15,
        BinaryOp::LessThan => 16,
        BinaryOp::LessThanOrEqual => 17,
        BinaryOp::GreaterThan => 18,
        BinaryOp::GreaterThanOrEqual => 19,
        BinaryOp::InstanceOf => 20,
        BinaryOp::In => 21,
    }
}

/// The ABI selector for an iterator protocol, passed as the `kind` argument to
/// [`Helper::GetIterator`]. This is the stable codegen-side encoding.
const fn iterator_kind_selector(kind: IteratorKind) -> i64 {
    match kind {
        IteratorKind::Sync => 0,
        IteratorKind::Async => 1,
        IteratorKind::Keys => 2,
    }
}

/// The ABI selector for iterator close behavior, passed as the `mode` argument
/// to [`Helper::IteratorClose`]. This is the stable codegen-side encoding.
const fn iterator_close_mode_selector(mode: IteratorCloseMode) -> i64 {
    match mode {
        IteratorCloseMode::Propagate => 0,
        IteratorCloseMode::PreserveAbrupt => 1,
    }
}

/// The ABI selector for a disposal hint, passed as `hint` to
/// [`Helper::DisposeCapture`].
const fn dispose_hint_selector(hint: DisposeHint) -> i64 {
    match hint {
        DisposeHint::Sync => 0,
        DisposeHint::Async => 1,
    }
}

/// The ABI selector for an accessor half, passed as the `kind` argument to
/// [`Helper::DefineAccessor`]. This is the stable codegen-side encoding.
const fn accessor_kind_selector(kind: AccessorKind) -> i64 {
    match kind {
        AccessorKind::Getter => 0,
        AccessorKind::Setter => 1,
        AccessorKind::ClassGetter => 2,
        AccessorKind::ClassSetter => 3,
    }
}

/// The ABI selector for an own-descriptor slot, passed as the `slot` argument
/// to [`Helper::LoadOwnDescriptorSlot`] / [`Helper::DefineOwnDescriptorSlot`].
const fn descriptor_slot_selector(slot: DescriptorSlot) -> i64 {
    match slot {
        DescriptorSlot::Value => 0,
        DescriptorSlot::Getter => 1,
        DescriptorSlot::Setter => 2,
        DescriptorSlot::Entire => 4,
    }
}

// -- Errors ------------------------------------------------------------------

/// A deterministic, typed lowering failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LowerError {
    /// The target is not 64-bit.
    UnsupportedPointerWidth {
        /// The offending pointer width in bits.
        bits: u8,
    },
    /// The module has more functions than a `u32` can index.
    TooManyFunctions {
        /// The offending function count.
        count: usize,
    },
    /// A function's register file cannot be addressed with 32-bit slot offsets.
    RegisterFileTooLarge {
        /// The offending function.
        function: FunctionId,
        /// Its register count.
        register_count: u32,
    },
    /// A lowered function's entry signature differs from the native ABI.
    EntrySignatureMismatch {
        /// The offending function.
        function: FunctionId,
    },
    /// Cranelift's IR verifier rejected a lowered function.
    IrVerification {
        /// The offending function.
        function: FunctionId,
        /// The verifier's diagnostics.
        message: String,
    },
    /// A caller-supplied cancellation token was triggered at a checkpoint.
    Cancelled,
}

impl From<Cancelled> for LowerError {
    fn from(_: Cancelled) -> Self {
        Self::Cancelled
    }
}

impl fmt::Display for LowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LowerError::UnsupportedPointerWidth { bits } => {
                write!(f, "target must be 64-bit, got {bits}-bit")
            }
            LowerError::TooManyFunctions { count } => {
                write!(f, "module has {count} functions, exceeding u32 index range")
            }
            LowerError::RegisterFileTooLarge {
                function,
                register_count,
            } => write!(
                f,
                "function {} register file of {register_count} slots is not 32-bit addressable",
                function.get()
            ),
            LowerError::EntrySignatureMismatch { function } => write!(
                f,
                "function {} lowered to a non-native entry signature",
                function.get()
            ),
            LowerError::IrVerification { function, message } => {
                write!(
                    f,
                    "function {} failed IR verification: {message}",
                    function.get()
                )
            }
            LowerError::Cancelled => f.write_str("operation cancelled"),
        }
    }
}

impl Error for LowerError {}

/// A deterministic lowering failure anchored to its canonical program module.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramLowerError {
    /// The module whose bytecode could not be lowered.
    pub module: ModuleId,
    /// The module-local lowering failure.
    pub kind: LowerError,
}

impl fmt::Display for ProgramLowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "module {} could not be lowered: {}",
            self.module.get(),
            self.kind
        )
    }
}

impl Error for ProgramLowerError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.kind)
    }
}

// -- Lowered records ---------------------------------------------------------

/// One lowered function: its Cranelift IR plus the metadata a backend needs to
/// compile and link it without re-deriving anything.
#[derive(Clone)]
pub struct LoweredFunction {
    /// The bytecode function this lowering corresponds to.
    pub id: FunctionId,
    /// The linker symbol for this function.
    pub symbol: String,
    /// The native-entry signature `(frame, out) -> tag`.
    pub signature: Signature,
    /// The verified Cranelift IR.
    pub clif: Function,
    /// The resume-dispatch tokens the entry accepts (`0` plus each `P + 1`).
    pub entry_points: Vec<u32>,
    /// The runtime helpers this function imports, in a stable order.
    pub helpers: Vec<Helper>,
    /// The count of leading capture-cell registers the runtime seeds from a
    /// `CreateClosure` captures array before parameters (from
    /// [`bamts_bytecode::Function::capture_count`]). Codegen surfaces it as
    /// metadata; the entry-init copy is a runtime concern.
    pub capture_count: u32,
}

impl fmt::Debug for LoweredFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LoweredFunction")
            .field("id", &self.id)
            .field("symbol", &self.symbol)
            .field("entry_points", &self.entry_points)
            .field("helpers", &self.helpers)
            .field("capture_count", &self.capture_count)
            .finish_non_exhaustive()
    }
}

/// The complete lowering of one verified module within a program.
#[derive(Clone)]
pub struct LoweredModule {
    /// The canonical program-local module id.
    pub id: ModuleId,
    /// One lowered function per bytecode function, in module-local index order.
    pub functions: Vec<LoweredFunction>,
    /// The module entry function.
    pub entry: FunctionId,
    /// The calling convention every lowered function uses.
    pub call_conv: CallConv,
}

impl fmt::Debug for LoweredModule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LoweredModule")
            .field("id", &self.id)
            .field("functions", &self.functions)
            .field("entry", &self.entry)
            .field("call_conv", &self.call_conv)
            .finish()
    }
}

/// The shared lowering of one canonical verified program.
#[derive(Clone, Debug)]
pub struct LoweredProgram {
    /// One lowering per program module, in canonical module-id order.
    pub modules: Vec<LoweredModule>,
    /// The program entry module.
    pub entry_module: ModuleId,
    /// The entry function local to `entry_module`.
    pub entry_function: FunctionId,
}

/// A deterministic failure from validating the structure of a lowered program.
#[cfg(any(test, feature = "aot", feature = "host-jit"))]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum LoweredProgramError {
    /// A module's canonical id does not match its position in the program.
    ModuleIndexMismatch {
        /// The expected id (the vector index).
        expected: u32,
        /// The id stored on the module.
        found: u32,
    },
    /// A function's canonical id does not match its position in its module.
    FunctionIndexMismatch {
        /// The id of the containing module.
        module: u32,
        /// The expected id (the vector index).
        expected: u32,
        /// The id stored on the function.
        found: u32,
    },
}

#[cfg(any(test, feature = "aot", feature = "host-jit"))]
impl fmt::Display for LoweredProgramError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ModuleIndexMismatch { expected, found } => {
                write!(f, "module {found} appears at index {expected}")
            }
            Self::FunctionIndexMismatch {
                module,
                expected,
                found,
            } => write!(
                f,
                "module {module} function {found} appears at local index {expected}"
            ),
        }
    }
}

#[cfg(any(test, feature = "aot", feature = "host-jit"))]
impl Error for LoweredProgramError {}

/// Validates that `lowered` has dense, identity-ordered modules and functions.
///
/// The returned vector lists every `(module_id, function_id)` in the canonical
/// tuple order that the JIT binary search and the AOT unit descriptor table rely
/// on. A mismatch between an id and its vector index is reported as a typed
/// error so each backend can map it to its own public error variant.
#[cfg(any(test, feature = "aot", feature = "host-jit"))]
pub(crate) fn validate_lowered_program(
    lowered: &LoweredProgram,
) -> Result<Vec<(u32, u32)>, LoweredProgramError> {
    let mut units = Vec::with_capacity(
        lowered
            .modules
            .iter()
            .map(|module| module.functions.len())
            .sum(),
    );
    for (module_index, module) in lowered.modules.iter().enumerate() {
        let module_id = module.id.get();
        let expected_module_id = module_index as u32;
        if module_id != expected_module_id {
            return Err(LoweredProgramError::ModuleIndexMismatch {
                expected: expected_module_id,
                found: module_id,
            });
        }
        for (function_index, function) in module.functions.iter().enumerate() {
            let function_id = function.id.get();
            let expected_function_id = function_index as u32;
            if function_id != expected_function_id {
                return Err(LoweredProgramError::FunctionIndexMismatch {
                    module: module_id,
                    expected: expected_function_id,
                    found: function_id,
                });
            }
            units.push((module_id, function_id));
        }
    }
    Ok(units)
}

/// The collision-free linker symbol for a module-qualified lowered function.
#[must_use]
pub fn function_symbol(module_id: u32, function_id: u32) -> String {
    format!("bamts_m{module_id}_fn_{function_id}")
}

// -- Lowering entry point ----------------------------------------------------

/// Lowers every function of every module in a verified canonical program.
///
/// Modules remain separate: function and constant ids are never flattened or
/// renumbered. Each error carries the module id whose lowering failed. This is
/// a convenience wrapper that uses a fresh, never-cancelled token; for
/// cancellation support use [`lower_program_with_cancel`].
pub fn lower_program(
    program: &Program<Verified>,
    config: TargetFrontendConfig,
) -> Result<LoweredProgram, ProgramLowerError> {
    lower_program_with_cancel(program, config, &CancellationToken::new())
}

/// Lowers every function of every module with cooperative cancellation checks.
///
/// Cancellation is checked at the entry, before each module, before each
/// function, and immediately before/after Cranelift's IR verifier.
pub fn lower_program_with_cancel(
    program: &Program<Verified>,
    config: TargetFrontendConfig,
    cancel: &CancellationToken,
) -> Result<LoweredProgram, ProgramLowerError> {
    cancel.check().map_err(|_| ProgramLowerError {
        module: program.entry(),
        kind: LowerError::Cancelled,
    })?;
    let mut modules = Vec::with_capacity(program.modules().len());
    for (index, module) in program.modules().iter().enumerate() {
        let module_id = ModuleId::new(index as u32);
        modules.push(
            lower_code_module_with_cancel(module_id, module.code(), config, cancel).map_err(
                |kind| ProgramLowerError {
                    module: module_id,
                    kind,
                },
            )?,
        );
    }
    let entry_module = program.entry();
    let entry_function = program
        .module(entry_module)
        .expect("verified program entry module exists")
        .code()
        .entry();
    Ok(LoweredProgram {
        modules,
        entry_module,
        entry_function,
    })
}

#[cfg(test)]
fn lower_code_module(
    module_id: ModuleId,
    module: &Module<Verified>,
    config: TargetFrontendConfig,
) -> Result<LoweredModule, LowerError> {
    lower_code_module_with_cancel(module_id, module, config, &CancellationToken::new())
}

fn lower_code_module_with_cancel(
    module_id: ModuleId,
    module: &Module<Verified>,
    config: TargetFrontendConfig,
    cancel: &CancellationToken,
) -> Result<LoweredModule, LowerError> {
    cancel.check()?;
    if config.pointer_bits() != 64 {
        return Err(LowerError::UnsupportedPointerWidth {
            bits: config.pointer_bits(),
        });
    }
    let function_count = module.functions().len();
    if u32::try_from(function_count).is_err() {
        return Err(LowerError::TooManyFunctions {
            count: function_count,
        });
    }

    let call_conv = config.default_call_conv;
    let entry_signature = entry_signature(call_conv);
    let flags = Flags::new(settings::builder());
    let mut builder_context = FunctionBuilderContext::new();
    let mut context = LowerFunctionContext {
        module_id,
        entry_signature: &entry_signature,
        config,
        flags: &flags,
        builder_context: &mut builder_context,
        cancel,
    };

    let mut functions = Vec::with_capacity(function_count);
    for (index, function) in module.functions().iter().enumerate() {
        // Bounds checked above.
        let id = FunctionId::new(index as u32);
        cancel.check()?;
        functions.push(lower_function(id, function, &mut context)?);
    }

    Ok(LoweredModule {
        id: module_id,
        functions,
        entry: module.entry(),
        call_conv,
    })
}

/// The shared native-entry signature: `(frame, out) -> tag`.
fn entry_signature(call_conv: CallConv) -> Signature {
    let mut signature = Signature::new(call_conv);
    signature.params.push(AbiParam::new(types::I64)); // *mut ShadowFrame
    signature.params.push(AbiParam::new(types::I64)); // *mut Completion
    signature.returns.push(AbiParam::new(types::I32)); // CompletionTag
    signature
}

/// Validates that a function's register file is addressable with the 32-bit
/// slot offsets used by every frame load and store. The bytecode verifier
/// proves register references stay within `register_count`; this proves
/// `register_count` itself fits the CLIF addressing convention.
fn validate_slots(id: FunctionId, function: &bamts_bytecode::Function) -> Result<(), LowerError> {
    let register_count = function.register_count();
    let addressable = i64::from(register_count)
        .checked_mul(VALUE_BYTES)
        .is_some_and(|bytes| i32::try_from(bytes).is_ok());
    if addressable {
        Ok(())
    } else {
        Err(LowerError::RegisterFileTooLarge {
            function: id,
            register_count,
        })
    }
}
struct LowerFunctionContext<'a> {
    module_id: ModuleId,
    entry_signature: &'a Signature,
    config: TargetFrontendConfig,
    flags: &'a Flags,
    builder_context: &'a mut FunctionBuilderContext,
    cancel: &'a CancellationToken,
}

fn lower_function(
    id: FunctionId,
    function: &bamts_bytecode::Function,
    context: &mut LowerFunctionContext<'_>,
) -> Result<LoweredFunction, LowerError> {
    validate_slots(id, function)?;

    let code = function.code();
    let handlers = function.handlers();
    let reachable = reachable_pcs(code, handlers);
    let entry_points = resume_tokens(code, &reachable);

    let name = UserFuncName::user(FUNCTION_NAMESPACE, id.get());
    let mut clif = Function::with_name_signature(name, context.entry_signature.clone());

    let helpers = {
        let builder = FunctionBuilder::new(&mut clif, context.builder_context);
        let mut lowering = Lowering::new(
            builder,
            code.len(),
            handlers,
            context.config.default_call_conv,
        );
        lowering.build(code, &reachable);
        lowering.finish(context.config)
    };

    // Signature validation: the produced entry ABI must be identical to the
    // shared native-entry signature (params and returns), independent of the
    // structural IR checks Cranelift performs below.
    if clif.signature != *context.entry_signature {
        return Err(LowerError::EntrySignatureMismatch { function: id });
    }

    context.cancel.check()?;
    verify_function(&clif, context.flags).map_err(|errors| LowerError::IrVerification {
        function: id,
        message: errors.to_string(),
    })?;
    context.cancel.check()?;

    Ok(LoweredFunction {
        id,
        symbol: function_symbol(context.module_id.get(), id.get()),
        signature: context.entry_signature.clone(),
        clif,
        entry_points,
        helpers,
        capture_count: function.capture_count(),
    })
}

// -- Per-function lowering ---------------------------------------------------

struct Lowering<'a> {
    builder: FunctionBuilder<'a>,
    /// One block per reachable bytecode pc; `None` for unreachable pcs, which
    /// are never emitted (keeping every block dominated by the entry block).
    pc_blocks: Vec<Option<Block>>,
    /// The resume prologue block for each reachable `Suspend`/`Await`, keyed
    /// by the suspension's bytecode pc.
    resume_blocks: BTreeMap<usize, Block>,
    handlers: &'a [ExceptionHandler],
    call_conv: CallConv,
    frame: Value,
    out: Value,
    helper_refs: BTreeMap<Helper, cranelift_codegen::ir::FuncRef>,
}

impl<'a> Lowering<'a> {
    fn new(
        mut builder: FunctionBuilder<'a>,
        code_len: usize,
        handlers: &'a [ExceptionHandler],
        call_conv: CallConv,
    ) -> Self {
        let pc_blocks = vec![None; code_len];
        // The entry/dispatch block owns the function parameters. Reachable pc
        // blocks are created up front in ascending order for deterministic IR.
        let dispatch = builder.create_block();
        builder.append_block_params_for_function_params(dispatch);
        builder.switch_to_block(dispatch);
        let frame = builder.block_params(dispatch)[0];
        let out = builder.block_params(dispatch)[1];
        Self {
            builder,
            pc_blocks,
            resume_blocks: BTreeMap::new(),
            handlers,
            call_conv,
            frame,
            out,
            helper_refs: BTreeMap::new(),
        }
    }

    fn build(&mut self, code: &[Instruction], reachable: &BTreeSet<usize>) {
        for &pc in reachable {
            self.pc_blocks[pc] = Some(self.builder.create_block());
        }
        for &pc in reachable {
            if let Instruction::Suspend { .. } | Instruction::Await { .. } = code[pc] {
                let block = self.builder.create_block();
                self.resume_blocks.insert(pc, block);
            }
        }
        self.emit_dispatch(code, reachable);
        for &pc in reachable {
            self.emit_instruction(pc, code[pc]);
        }
        for &pc in reachable {
            match code[pc] {
                Instruction::Suspend {
                    dst, resume, mode, ..
                } => {
                    self.emit_resume_prologue(pc, dst, resume, Some(mode));
                }
                Instruction::Await { dst, resume, .. } => {
                    self.emit_resume_prologue(pc, dst, resume, None);
                }
                _ => {}
            }
        }
        self.builder.seal_all_blocks();
    }

    /// Consumes the builder, returning the imported helpers in a stable order.
    fn finish(self, config: TargetFrontendConfig) -> Vec<Helper> {
        let helpers = self.helper_refs.keys().copied().collect();
        self.builder.finalize(config);
        helpers
    }

    fn emit_dispatch(&mut self, code: &[Instruction], reachable: &BTreeSet<usize>) {
        let loop_headers = self.loop_headers(code, reachable);
        if self.resume_blocks.is_empty() && loop_headers.is_empty() {
            let target = self.pc_blocks[0].expect("entry pc is reachable");
            self.builder.ins().jump(target, &[]);
            return;
        }
        let token = self.builder.ins().load(
            types::I32,
            MemFlagsData::trusted(),
            self.frame,
            SHADOW_FRAME_PC_OFFSET,
        );
        let fresh = self.pc_blocks[0].expect("entry pc is reachable");
        let after_fresh = self.builder.create_block();
        let is_fresh = self.builder.ins().icmp_imm_u(IntCC::Equal, token, 0);
        self.builder
            .ins()
            .brif(is_fresh, fresh, &[], after_fresh, &[]);
        self.builder.switch_to_block(after_fresh);
        let resume: Vec<(usize, Block)> = self
            .resume_blocks
            .iter()
            .map(|(&pc, &block)| (pc, block))
            .collect();
        for (pc, block) in resume {
            let token_value = i64::from(u32::try_from(pc).expect("reachable pc fits in u32") + 1);
            let matches = self
                .builder
                .ins()
                .icmp_imm_u(IntCC::Equal, token, token_value);
            let next = self.builder.create_block();
            self.builder.ins().brif(matches, block, &[], next, &[]);
            self.builder.switch_to_block(next);
        }
        for header in loop_headers {
            let target = self.pc_blocks[header].expect("loop header is reachable");
            let header_u32 = u32::try_from(header).expect("reachable pc fits in u32");
            let token_value = i64::from(0x8000_0000u32 | header_u32);
            let matches = self
                .builder
                .ins()
                .icmp_imm_u(IntCC::Equal, token, token_value);
            let next = self.builder.create_block();
            self.builder.ins().brif(matches, target, &[], next, &[]);
            self.builder.switch_to_block(next);
        }
        self.emit_trap(TRAP_INVALID_RESUME);
    }

    fn loop_headers(&self, code: &[Instruction], reachable: &BTreeSet<usize>) -> Vec<usize> {
        let mut headers = BTreeSet::new();
        for &pc in reachable {
            let target = match code[pc] {
                Instruction::Jump { target } => Some(target.get() as usize),
                Instruction::JumpIfTrue { target, .. }
                | Instruction::JumpIfFalse { target, .. } => Some(target.get() as usize),
                _ => None,
            };
            if let Some(target) = target
                && target <= pc
                && reachable.contains(&target)
            {
                headers.insert(target);
            }
        }
        headers.into_iter().collect()
    }

    fn emit_instruction(&mut self, pc: usize, instruction: Instruction) {
        let block = self.pc_blocks[pc].expect("reachable pc has a block");
        self.builder.switch_to_block(block);
        let current_pc = self.iconst32(i64::from(pc as u32));
        self.builder.ins().store(
            MemFlagsData::trusted(),
            current_pc,
            self.frame,
            SHADOW_FRAME_PC_OFFSET,
        );
        if is_inline_instruction(instruction) {
            self.emit_consume_fuel();
        }
        match instruction {
            Instruction::LoadConst { dst, constant } => {
                let const_id = self.iconst32(i64::from(constant.get()));
                let tag = self.call_helper(Helper::LoadConstant, &[self.frame, const_id, self.out]);
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::Move { dst, src } => {
                let handles = self.load_handles();
                let value = self.load_register(handles, src);
                self.store_register(handles, dst, value);
                self.jump_to_next(pc);
            }
            Instruction::Unary { dst, op, operand } => {
                let handles = self.load_handles();
                let operand_value = self.load_register(handles, operand);
                let selector = self.iconst32(unary_op_selector(op));
                let tag = self.call_helper(
                    Helper::Unary,
                    &[self.frame, selector, operand_value, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::Binary {
                dst,
                op,
                left,
                right,
            } => {
                let handles = self.load_handles();
                let left_value = self.load_register(handles, left);
                let right_value = self.load_register(handles, right);
                let selector = self.iconst32(binary_op_selector(op));
                let tag = self.call_helper(
                    Helper::Binary,
                    &[self.frame, selector, left_value, right_value, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::CreateObject { dst } => {
                let tag = self.call_helper(Helper::CreateObject, &[self.frame, self.out]);
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::ToObject { dst, src } => {
                let handles = self.load_handles();
                let value = self.load_register(handles, src);
                let tag = self.call_helper(Helper::ToObject, &[self.frame, value, self.out]);
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::CreateArray { dst } => {
                let tag = self.call_helper(Helper::CreateArray, &[self.frame, self.out]);
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::CreateCell { dst } => {
                let tag = self.call_helper(Helper::CreateCell, &[self.frame, self.out]);
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::CreateClosure {
                dst,
                function,
                captures,
            } => {
                let handles = self.load_handles();
                let captures_value = self.load_register(handles, captures);
                let function_id = self.iconst32(i64::from(function.get()));
                let tag = self.call_helper(
                    Helper::CreateClosure,
                    &[self.frame, function_id, captures_value, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::GetProperty { dst, object, key } => {
                let handles = self.load_handles();
                let object_value = self.load_register(handles, object);
                let key_value = self.load_register(handles, key);
                let site = i64::from(u32::try_from(pc).unwrap_or(u32::MAX));
                let site_word = self.iconst32(site);
                let tag = self.call_helper(
                    Helper::GetProperty,
                    &[self.frame, object_value, key_value, site_word, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::SetProperty { object, key, value } => {
                let handles = self.load_handles();
                let object_value = self.load_register(handles, object);
                let key_value = self.load_register(handles, key);
                let value_value = self.load_register(handles, value);
                let site = i64::from(u32::try_from(pc).unwrap_or(u32::MAX));
                let site_word = self.iconst32(site);
                let tag = self.call_helper(
                    Helper::SetProperty,
                    &[
                        self.frame,
                        object_value,
                        key_value,
                        value_value,
                        site_word,
                        self.out,
                    ],
                );
                self.route_completion(pc, tag, None);
            }
            Instruction::DefineDataProperty { object, key, value } => {
                let handles = self.load_handles();
                let object_value = self.load_register(handles, object);
                let key_value = self.load_register(handles, key);
                let value_value = self.load_register(handles, value);
                let tag = self.call_helper(
                    Helper::DefineDataProperty,
                    &[self.frame, object_value, key_value, value_value, self.out],
                );
                self.route_completion(pc, tag, None);
            }
            Instruction::LoadOwnDescriptorSlot {
                dst,
                object,
                key,
                slot,
            } => {
                let handles = self.load_handles();
                let object_value = self.load_register(handles, object);
                let key_value = self.load_register(handles, key);
                let selector = self.iconst32(descriptor_slot_selector(slot));
                let tag = self.call_helper(
                    Helper::LoadOwnDescriptorSlot,
                    &[self.frame, object_value, key_value, selector, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::DefineOwnDescriptorSlot {
                object,
                key,
                src,
                slot,
            } => {
                let handles = self.load_handles();
                let object_value = self.load_register(handles, object);
                let key_value = self.load_register(handles, key);
                let src_value = self.load_register(handles, src);
                let selector = self.iconst32(descriptor_slot_selector(slot));
                let tag = self.call_helper(
                    Helper::DefineOwnDescriptorSlot,
                    &[
                        self.frame,
                        object_value,
                        key_value,
                        src_value,
                        selector,
                        self.out,
                    ],
                );
                self.route_completion(pc, tag, None);
            }
            Instruction::WithHasBinding { dst, object, key } => {
                let handles = self.load_handles();
                let object_value = self.load_register(handles, object);
                let key_value = self.load_register(handles, key);
                let tag = self.call_helper(
                    Helper::WithHasBinding,
                    &[self.frame, object_value, key_value, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::DeleteProperty { dst, object, key } => {
                let handles = self.load_handles();
                let object_value = self.load_register(handles, object);
                let key_value = self.load_register(handles, key);
                let tag = self.call_helper(
                    Helper::DeleteProperty,
                    &[self.frame, object_value, key_value, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::DefineAccessor {
                object,
                key,
                accessor,
                kind,
            } => {
                let handles = self.load_handles();
                let object_value = self.load_register(handles, object);
                let key_value = self.load_register(handles, key);
                let accessor_value = self.load_register(handles, accessor);
                let selector = self.iconst32(accessor_kind_selector(kind));
                let tag = self.call_helper(
                    Helper::DefineAccessor,
                    &[
                        self.frame,
                        object_value,
                        key_value,
                        accessor_value,
                        selector,
                        self.out,
                    ],
                );
                self.route_completion(pc, tag, None);
            }
            Instruction::Call {
                dst,
                callee,
                this_value,
                arguments,
            } => {
                let handles = self.load_handles();
                let callee_value = self.load_register(handles, callee);
                let this = self.load_register(handles, this_value);
                let args = self.load_register(handles, arguments);
                let tag = self.call_helper(
                    Helper::Call,
                    &[self.frame, callee_value, this, args, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::ConstructWithNewTarget {
                dst,
                callee,
                new_target,
                arguments,
            } => {
                let handles = self.load_handles();
                let callee_value = self.load_register(handles, callee);
                let new_target_value = self.load_register(handles, new_target);
                let args = self.load_register(handles, arguments);
                let tag = self.call_helper(
                    Helper::ConstructWithNewTarget,
                    &[self.frame, callee_value, new_target_value, args, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::Construct {
                dst,
                callee,
                arguments,
            } => {
                let handles = self.load_handles();
                let callee_value = self.load_register(handles, callee);
                let args = self.load_register(handles, arguments);
                let tag = self.call_helper(
                    Helper::Construct,
                    &[self.frame, callee_value, args, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::LoadGlobal { dst, name } => {
                let name_id = self.iconst32(i64::from(name.get()));
                let tag = self.call_helper(Helper::LoadGlobal, &[self.frame, name_id, self.out]);
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::StoreGlobal { name, value } => {
                let handles = self.load_handles();
                let value_value = self.load_register(handles, value);
                let name_id = self.iconst32(i64::from(name.get()));
                let tag = self.call_helper(
                    Helper::StoreGlobal,
                    &[self.frame, name_id, value_value, self.out],
                );
                self.route_completion(pc, tag, None);
            }
            Instruction::RequireGlobalBinding { name } => {
                let name_id = self.iconst32(i64::from(name.get()));
                let tag = self.call_helper(
                    Helper::RequireGlobalBinding,
                    &[self.frame, name_id, self.out],
                );
                self.route_completion(pc, tag, None);
            }
            Instruction::TypeOfGlobal { dst, name } => {
                let name_id = self.iconst32(i64::from(name.get()));
                let tag = self.call_helper(Helper::TypeOfGlobal, &[self.frame, name_id, self.out]);
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::LoadThis { dst } => {
                let tag = self.call_helper(Helper::LoadThis, &[self.frame, self.out]);
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::LoadArguments { dst } => {
                let tag = self.call_helper(Helper::LoadArguments, &[self.frame, self.out]);
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::LoadNewTarget { dst } => {
                let tag = self.call_helper(Helper::LoadNewTarget, &[self.frame, self.out]);
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::LoadImportMeta { dst } => {
                let tag = self.call_helper(Helper::LoadImportMeta, &[self.frame, self.out]);
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::ArrayPush { array, value } => {
                let handles = self.load_handles();
                let array_value = self.load_register(handles, array);
                let value_value = self.load_register(handles, value);
                let tag = self.call_helper(
                    Helper::ArrayPush,
                    &[self.frame, array_value, value_value, self.out],
                );
                self.route_completion(pc, tag, None);
            }
            Instruction::ArrayExtend { array, iterable } => {
                let handles = self.load_handles();
                let array_value = self.load_register(handles, array);
                let iterable_value = self.load_register(handles, iterable);
                let tag = self.call_helper(
                    Helper::ArrayExtend,
                    &[self.frame, array_value, iterable_value, self.out],
                );
                self.route_completion(pc, tag, None);
            }
            Instruction::ObjectSpread { target, source } => {
                let handles = self.load_handles();
                let target_value = self.load_register(handles, target);
                let source_value = self.load_register(handles, source);
                let tag = self.call_helper(
                    Helper::ObjectSpread,
                    &[self.frame, target_value, source_value, self.out],
                );
                self.route_completion(pc, tag, None);
            }
            Instruction::SetPrototype { object, prototype } => {
                let handles = self.load_handles();
                let object_value = self.load_register(handles, object);
                let prototype_value = self.load_register(handles, prototype);
                let tag = self.call_helper(
                    Helper::SetPrototype,
                    &[self.frame, object_value, prototype_value, self.out],
                );
                self.route_completion(pc, tag, None);
            }
            Instruction::CreatePrivateName { dst, description } => {
                let description_id = self.iconst32(i64::from(description.get()));
                let tag = self.call_helper(
                    Helper::CreatePrivateName,
                    &[self.frame, description_id, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::CreateRegExp {
                dst,
                pattern,
                flags,
            } => {
                let pattern_id = self.iconst32(i64::from(pattern.get()));
                let flags_id = self.iconst32(i64::from(flags.get()));
                let tag = self.call_helper(
                    Helper::CreateRegExp,
                    &[self.frame, pattern_id, flags_id, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::GetIterator { dst, src, kind } => {
                let handles = self.load_handles();
                let src_value = self.load_register(handles, src);
                let selector = self.iconst32(iterator_kind_selector(kind));
                let tag = self.call_helper(
                    Helper::GetIterator,
                    &[self.frame, src_value, selector, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::IteratorNext {
                done,
                value,
                iterator,
            } => {
                let handles = self.load_handles();
                let iterator_value = self.load_register(handles, iterator);
                let done_reg = self.iconst32(i64::from(done.get()));
                let value_reg = self.iconst32(i64::from(value.get()));
                // Two-write: the helper writes both `done` and `value` slots
                // directly from the frame on Normal, so no `dst` store here.
                let tag = self.call_helper(
                    Helper::IteratorNext,
                    &[self.frame, iterator_value, done_reg, value_reg, self.out],
                );
                self.route_completion(pc, tag, None);
            }
            Instruction::IteratorStep { dst, iterator } => {
                let handles = self.load_handles();
                let iterator_value = self.load_register(handles, iterator);
                let tag = self.call_helper(
                    Helper::IteratorStep,
                    &[self.frame, iterator_value, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::IteratorResult {
                done,
                value,
                result,
            } => {
                let handles = self.load_handles();
                let result_value = self.load_register(handles, result);
                let done_reg = self.iconst32(i64::from(done.get()));
                let value_reg = self.iconst32(i64::from(value.get()));
                // Two-write, like IteratorNext: the helper writes both `done`
                // and `value` slots directly from the frame on Normal, so no
                // `dst` store here.
                let tag = self.call_helper(
                    Helper::IteratorResult,
                    &[self.frame, result_value, done_reg, value_reg, self.out],
                );
                self.route_completion(pc, tag, None);
            }
            Instruction::IteratorClose {
                result,
                called,
                iterator,
                mode,
            } => {
                let handles = self.load_handles();
                let iterator_value = self.load_register(handles, iterator);
                let selector = self.iconst32(iterator_close_mode_selector(mode));
                let called_reg = self.iconst32(i64::from(called.get()));
                let tag = self.call_helper(
                    Helper::IteratorClose,
                    &[self.frame, iterator_value, selector, called_reg, self.out],
                );
                self.route_completion(pc, tag, Some(result));
            }
            Instruction::RequireCloseResult { result, called } => {
                let handles = self.load_handles();
                let result_value = self.load_register(handles, result);
                let called_value = self.load_register(handles, called);
                let tag = self.call_helper(
                    Helper::RequireCloseResult,
                    &[self.frame, result_value, called_value, self.out],
                );
                self.route_completion(pc, tag, None);
            }
            Instruction::DisposeCapture {
                method,
                kind,
                src,
                hint,
            } => {
                let handles = self.load_handles();
                let src_value = self.load_register(handles, src);
                let selector = self.iconst32(dispose_hint_selector(hint));
                let kind_reg = self.iconst32(i64::from(kind.get()));
                let tag = self.call_helper(
                    Helper::DisposeCapture,
                    &[self.frame, src_value, selector, kind_reg, self.out],
                );
                self.route_completion(pc, tag, Some(method));
            }
            Instruction::SuppressError {
                dst,
                error,
                suppressed,
            } => {
                let handles = self.load_handles();
                let error_value = self.load_register(handles, error);
                let suppressed_value = self.load_register(handles, suppressed);
                let tag = self.call_helper(
                    Helper::SuppressError,
                    &[self.frame, error_value, suppressed_value, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::Import { dst, specifier } => {
                let specifier_id = self.iconst32(i64::from(specifier.get()));
                let tag = self.call_helper(Helper::Import, &[self.frame, specifier_id, self.out]);
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::ImportDynamic { dst, specifier } => {
                let handles = self.load_handles();
                let specifier = self.load_register(handles, specifier);
                let tag =
                    self.call_helper(Helper::ImportDynamic, &[self.frame, specifier, self.out]);
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::Export { name, src } => {
                let handles = self.load_handles();
                let src_value = self.load_register(handles, src);
                let name_id = self.iconst32(i64::from(name.get()));
                let tag =
                    self.call_helper(Helper::Export, &[self.frame, name_id, src_value, self.out]);
                self.route_completion(pc, tag, None);
            }
            Instruction::GetSuper {
                dst,
                home,
                receiver,
                key,
            } => {
                let handles = self.load_handles();
                let home_value = self.load_register(handles, home);
                let receiver_value = self.load_register(handles, receiver);
                let key_value = self.load_register(handles, key);
                let tag = self.call_helper(
                    Helper::GetSuper,
                    &[self.frame, home_value, receiver_value, key_value, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::SetSuper {
                home,
                receiver,
                key,
                value,
            } => {
                let handles = self.load_handles();
                let home_value = self.load_register(handles, home);
                let receiver_value = self.load_register(handles, receiver);
                let key_value = self.load_register(handles, key);
                let value_value = self.load_register(handles, value);
                let tag = self.call_helper(
                    Helper::SetSuper,
                    &[
                        self.frame,
                        home_value,
                        receiver_value,
                        key_value,
                        value_value,
                        self.out,
                    ],
                );
                self.route_completion(pc, tag, None);
            }
            Instruction::ImportAttributes {
                dst,
                specifier,
                attributes,
            } => {
                let handles = self.load_handles();
                let attributes_value = self.load_register(handles, attributes);
                let specifier_id = self.iconst32(i64::from(specifier.get()));
                let tag = self.call_helper(
                    Helper::ImportAttributes,
                    &[self.frame, specifier_id, attributes_value, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::ImportDynamicAttributes {
                dst,
                specifier,
                attributes,
            } => {
                let handles = self.load_handles();
                let specifier_value = self.load_register(handles, specifier);
                let attributes_value = self.load_register(handles, attributes);
                let tag = self.call_helper(
                    Helper::ImportDynamicAttributes,
                    &[self.frame, specifier_value, attributes_value, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::CopyDataProperties {
                target,
                source,
                excluded,
            } => {
                let handles = self.load_handles();
                let target_value = self.load_register(handles, target);
                let source_value = self.load_register(handles, source);
                let excluded_value = self.load_register(handles, excluded);
                let tag = self.call_helper(
                    Helper::CopyDataProperties,
                    &[
                        self.frame,
                        target_value,
                        source_value,
                        excluded_value,
                        self.out,
                    ],
                );
                self.route_completion(pc, tag, None);
            }
            Instruction::GetTemplateObject { dst, cooked, raw } => {
                let handles = self.load_handles();
                let cooked_value = self.load_register(handles, cooked);
                let raw_value = self.load_register(handles, raw);
                let tag = self.call_helper(
                    Helper::GetTemplateObject,
                    &[self.frame, cooked_value, raw_value, self.out],
                );
                self.route_completion(pc, tag, Some(dst));
            }
            Instruction::Jump { target } => {
                let target = self.pc_block(target);
                self.builder.ins().jump(target, &[]);
            }
            Instruction::JumpIfTrue { condition, target } => {
                self.emit_conditional(condition, target.get() as usize, pc + 1);
            }
            Instruction::JumpIfFalse { condition, target } => {
                self.emit_conditional(condition, pc + 1, target.get() as usize);
            }
            Instruction::Return { value } => self.emit_return(value),
            Instruction::Throw { value } => self.emit_throw(pc, value),
            Instruction::Suspend { src, .. } | Instruction::Await { src, .. } => {
                self.emit_suspend(pc, src);
            }
            Instruction::Halt => self.emit_halt(),
        }
    }

    /// Routes a value-helper completion: on `Normal`, store `out.value` into
    /// `dst` (when the opcode defines one) and continue; otherwise route the
    /// abnormal completion to a handler or the caller.
    fn route_completion(&mut self, pc: usize, tag: Value, dst: Option<Register>) {
        let normal = self.builder.create_block();
        let abnormal = self.builder.create_block();
        // Normal (tag == 0) takes `normal`; any nonzero tag is abnormal.
        self.builder.ins().brif(tag, abnormal, &[], normal, &[]);

        self.builder.switch_to_block(normal);
        if let Some(dst) = dst {
            let handles = self.load_handles();
            let result = self.load_completion_value();
            self.store_register(handles, dst, result);
        }
        self.jump_to_next(pc);

        self.builder.switch_to_block(abnormal);
        self.emit_abnormal_completion(pc, tag);
    }

    /// Routes a nonzero completion tag: to a covering handler on `Throw` (the
    /// thrown value is bound into the handler's `catch_register`), otherwise
    /// propagated to the caller. `FatalTrap` never enters a handler.
    ///
    /// If the covering handler's block was not emitted (only a total,
    /// non-throwing helper reaches it), the completion is propagated to the
    /// caller — this abnormal edge is provably unreachable for such helpers.
    fn emit_abnormal_completion(&mut self, pc: usize, tag: Value) {
        let covering = innermost_handler(self.handlers, pc).and_then(|handler| {
            self.emitted_handler_block(handler)
                .map(|block| (handler, block))
        });
        match covering {
            Some((handler, handler_block)) => {
                let bind = self.builder.create_block();
                let propagate = self.builder.create_block();
                let is_throw = self.builder.ins().icmp_imm_u(IntCC::Equal, tag, TAG_THROW);
                self.builder.ins().brif(is_throw, bind, &[], propagate, &[]);

                self.builder.switch_to_block(bind);
                let handles = self.load_handles();
                let thrown = self.load_completion_value();
                self.store_register(handles, handler.catch_register, thrown);
                self.builder.ins().jump(handler_block, &[]);

                self.builder.switch_to_block(propagate);
                self.builder.ins().return_(&[tag]);
            }
            None => {
                self.builder.ins().return_(&[tag]);
            }
        }
    }

    /// The emitted block for a handler's target pc, or `None` when that pc was
    /// not marked reachable (so no throwing opcode routes there).
    fn emitted_handler_block(&self, handler: ExceptionHandler) -> Option<Block> {
        self.pc_blocks[handler.handler.get() as usize]
    }

    /// Emits `JumpIfTrue`/`JumpIfFalse`: coerce `condition` to boolean via the
    /// total [`Helper::Truthy`], then branch to `true_target` on truthy and
    /// `false_target` otherwise.
    fn emit_conditional(&mut self, condition: Register, true_target: usize, false_target: usize) {
        let handles = self.load_handles();
        let condition_value = self.load_register(handles, condition);
        let truth = self.call_helper(Helper::Truthy, &[self.frame, condition_value]);
        let then_block = self.pc_blocks[true_target].expect("branch target is reachable");
        let else_block = self.pc_blocks[false_target].expect("branch target is reachable");
        self.builder
            .ins()
            .brif(truth, then_block, &[], else_block, &[]);
    }

    fn emit_return(&mut self, value: Register) {
        let handles = self.load_handles();
        let return_value = self.load_register(handles, value);
        self.store_completion_value(return_value);
        let tag = self.iconst32(TAG_NORMAL);
        self.builder.ins().return_(&[tag]);
    }

    /// Emits `Throw`: bind the thrown value into a covering handler's
    /// `catch_register` and branch there, or write it to `out.value` and return
    /// `Throw` to the caller.
    fn emit_throw(&mut self, pc: usize, value: Register) {
        let handles = self.load_handles();
        let thrown = self.load_register(handles, value);
        match innermost_handler(self.handlers, pc) {
            Some(handler) => {
                self.store_register(handles, handler.catch_register, thrown);
                let handler_block = self.pc_block(handler.handler);
                self.builder.ins().jump(handler_block, &[]);
            }
            None => {
                self.store_completion_value(thrown);
                let tag = self.iconst32(TAG_THROW);
                self.builder.ins().return_(&[tag]);
            }
        }
    }

    /// Emits the `Suspend`/`Await` suspension path: store this suspension's
    /// resume token into `frame.bytecode_pc`, yield `src` in `out.value`, and
    /// return `Suspend`. Both opcodes share this ABI; only the runtime driver
    /// interprets the yielded value differently (generator item vs awaited
    /// operand).
    fn emit_suspend(&mut self, pc: usize, src: Register) {
        let token = self.iconst32(i64::from(pc as u32 + 1));
        self.builder.ins().store(
            MemFlagsData::trusted(),
            token,
            self.frame,
            SHADOW_FRAME_PC_OFFSET,
        );
        let handles = self.load_handles();
        let yielded = self.load_register(handles, src);
        self.store_completion_value(yielded);
        let tag = self.iconst32(TAG_SUSPEND);
        self.builder.ins().return_(&[tag]);
    }

    /// Emits a `Suspend`/`Await` resume prologue: obtain the resumed value from
    /// the runtime via [`Helper::ResumeValue`], store it into `dst`, and continue
    /// at `resume`. For [`Instruction::Suspend`] only, also obtain the resume
    /// mode via [`Helper::ResumeMode`] and store it into `mode`. Each helper is
    /// called at most once, and `ResumeMode` is only reached after `ResumeValue`
    /// succeeds.
    fn emit_resume_prologue(
        &mut self,
        pc: usize,
        dst: Register,
        resume: Pc,
        mode: Option<Register>,
    ) {
        let block = self.resume_blocks[&pc];
        self.builder.switch_to_block(block);
        let current_pc = self.iconst32(i64::from(pc as u32));
        self.builder.ins().store(
            MemFlagsData::trusted(),
            current_pc,
            self.frame,
            SHADOW_FRAME_PC_OFFSET,
        );
        let value_tag = self.call_helper(Helper::ResumeValue, &[self.frame, self.out]);

        let value_normal = self.builder.create_block();
        let value_abnormal = self.builder.create_block();
        self.builder
            .ins()
            .brif(value_tag, value_abnormal, &[], value_normal, &[]);

        self.builder.switch_to_block(value_normal);
        let handles = self.load_handles();
        let resumed = self.load_completion_value();
        self.store_register(handles, dst, resumed);

        if let Some(mode) = mode {
            let mode_tag = self.call_helper(Helper::ResumeMode, &[self.frame, self.out]);
            let mode_normal = self.builder.create_block();
            let mode_abnormal = self.builder.create_block();
            self.builder
                .ins()
                .brif(mode_tag, mode_abnormal, &[], mode_normal, &[]);

            self.builder.switch_to_block(mode_normal);
            let handles = self.load_handles();
            let mode_value = self.load_completion_value();
            self.store_register(handles, mode, mode_value);
            let target = self.pc_block(resume);
            self.builder.ins().jump(target, &[]);

            self.builder.switch_to_block(mode_abnormal);
            self.emit_abnormal_completion(pc, mode_tag);
        } else {
            let target = self.pc_block(resume);
            self.builder.ins().jump(target, &[]);
        }

        self.builder.switch_to_block(value_abnormal);
        self.emit_abnormal_completion(pc, value_tag);
    }

    fn emit_halt(&mut self) {
        let undefined = self.builder.ins().iconst(types::I64, UNDEFINED_BITS);
        self.store_completion_value(undefined);
        let tag = self.iconst32(TAG_NORMAL);
        self.builder.ins().return_(&[tag]);
    }

    fn emit_trap(&mut self, trap_id: i64) {
        let value = self.builder.ins().iconst(types::I64, trap_id);
        self.store_completion_value(value);
        let tag = self.iconst32(TAG_FATAL_TRAP);
        self.builder.ins().return_(&[tag]);
    }

    fn jump_to_next(&mut self, pc: usize) {
        let next = self.pc_blocks[pc + 1].expect("fallthrough successor is reachable");
        self.builder.ins().jump(next, &[]);
    }

    /// The Cranelift block for a bytecode target pc.
    fn pc_block(&self, target: Pc) -> Block {
        self.pc_blocks[target.get() as usize].expect("control-flow target is reachable")
    }

    fn iconst32(&mut self, value: i64) -> Value {
        self.builder.ins().iconst(types::I32, value)
    }

    fn load_handles(&mut self) -> Value {
        // Re-read on each use: a helper call may relocate the register array.
        self.builder.ins().load(
            types::I64,
            MemFlagsData::trusted(),
            self.frame,
            SHADOW_FRAME_HANDLES_OFFSET,
        )
    }

    fn load_register(&mut self, handles: Value, register: Register) -> Value {
        self.builder.ins().load(
            types::I64,
            MemFlagsData::trusted(),
            handles,
            register_offset(register),
        )
    }

    fn store_register(&mut self, handles: Value, register: Register, value: Value) {
        self.builder.ins().store(
            MemFlagsData::trusted(),
            value,
            handles,
            register_offset(register),
        );
    }

    fn load_completion_value(&mut self) -> Value {
        self.builder.ins().load(
            types::I64,
            MemFlagsData::trusted(),
            self.out,
            COMPLETION_VALUE_OFFSET,
        )
    }

    fn store_completion_value(&mut self, value: Value) {
        self.builder.ins().store(
            MemFlagsData::trusted(),
            value,
            self.out,
            COMPLETION_VALUE_OFFSET,
        );
    }

    fn call_helper(&mut self, helper: Helper, args: &[Value]) -> Value {
        let func_ref = self.helper_ref(helper);
        let call = self.builder.ins().call(func_ref, args);
        self.builder.inst_results(call)[0]
    }

    fn helper_ref(&mut self, helper: Helper) -> cranelift_codegen::ir::FuncRef {
        if let Some(&func_ref) = self.helper_refs.get(&helper) {
            return func_ref;
        }
        let signature = helper.signature(self.call_conv);
        let sig_ref = self.builder.import_signature(signature);
        let name = self
            .builder
            .func
            .declare_imported_user_function(UserExternalName::new(
                HELPER_NAMESPACE,
                helper.external_index(),
            ));
        let func_ref = self.builder.import_function(ExtFuncData {
            name: ExternalName::user(name),
            signature: sig_ref,
            colocated: false,
            patchable: false,
        });
        self.helper_refs.insert(helper, func_ref);
        func_ref
    }

    fn emit_consume_fuel(&mut self) {
        let amount = self.iconst32(1);
        let tag = self.call_helper(Helper::ConsumeFuel, &[self.frame, amount, self.out]);
        let normal = self.builder.create_block();
        let abnormal = self.builder.create_block();
        self.builder.ins().brif(tag, abnormal, &[], normal, &[]);

        self.builder.switch_to_block(abnormal);
        self.builder.ins().return_(&[tag]);

        self.builder.switch_to_block(normal);
    }
}

/// The byte offset of a register slot within the handles array. [`validate_slots`]
/// proves `register_count * 8` fits `i32`, so this conversion never truncates.
/// A slot offset is a full 32-bit displacement, so register ids past 127 scale
/// linearly without any special path.
fn register_offset(register: Register) -> i32 {
    i32::try_from(i64::from(register.get()) * VALUE_BYTES).expect("register slot offset fits i32")
}

// -- CFG analysis ------------------------------------------------------------

/// The set of pcs reachable from a fresh call (pc 0) plus every resumable
/// `Suspend`/`Await` point, following fallthrough, jumps, conditional targets,
/// suspension resumes, and the handler edge of any instruction that can route
/// a `Throw` completion into a covering handler.
fn reachable_pcs(code: &[Instruction], handlers: &[ExceptionHandler]) -> BTreeSet<usize> {
    let mut reachable = BTreeSet::new();
    let mut worklist = Vec::new();
    if !code.is_empty() {
        worklist.push(0usize);
    }
    while let Some(pc) = worklist.pop() {
        if !reachable.insert(pc) {
            continue;
        }
        let instruction = code[pc];
        instruction.visit_normal_successors(pc, |target| worklist.push(target));
        if routes_to_handler(instruction)
            && let Some(handler) = innermost_handler(handlers, pc)
        {
            worklist.push(handler.handler.get() as usize);
        }
    }
    reachable
}

/// Whether an instruction can transfer control to a covering handler: the
/// explicit `Throw`, or any completion-helper opcode whose abnormal path may
/// return `Throw`. Keeping this exhaustive guarantees every handler block a
/// throwing opcode targets is marked reachable and thus emitted.
///
/// The `false` arm lists every opcode that provably cannot route a `Throw`:
/// pure control flow, `Move`, and the total helpers ([`Helper::TypeOfGlobal`],
/// [`Helper::LoadThis`], [`Helper::LoadArguments`], [`Helper::LoadNewTarget`],
/// [`Helper::CreatePrivateName`]). Using an exhaustive `match` — not
/// `matches!` — forces a compile error if a new opcode is left unclassified.
fn routes_to_handler(instruction: Instruction) -> bool {
    match instruction {
        Instruction::LoadConst { .. }
        | Instruction::Unary { .. }
        | Instruction::Binary { .. }
        | Instruction::CreateObject { .. }
        | Instruction::ToObject { .. }
        | Instruction::CreateArray { .. }
        | Instruction::CreateCell { .. }
        | Instruction::CreateClosure { .. }
        | Instruction::GetProperty { .. }
        | Instruction::SetProperty { .. }
        | Instruction::DefineDataProperty { .. }
        | Instruction::LoadOwnDescriptorSlot { .. }
        | Instruction::DefineOwnDescriptorSlot { .. }
        | Instruction::WithHasBinding { .. }
        | Instruction::DeleteProperty { .. }
        | Instruction::DefineAccessor { .. }
        | Instruction::Call { .. }
        | Instruction::Construct { .. }
        | Instruction::ConstructWithNewTarget { .. }
        | Instruction::LoadGlobal { .. }
        | Instruction::StoreGlobal { .. }
        | Instruction::ArrayPush { .. }
        | Instruction::ArrayExtend { .. }
        | Instruction::ObjectSpread { .. }
        | Instruction::SetPrototype { .. }
        | Instruction::CreateRegExp { .. }
        | Instruction::GetIterator { .. }
        | Instruction::IteratorNext { .. }
        | Instruction::IteratorStep { .. }
        | Instruction::IteratorResult { .. }
        | Instruction::IteratorClose { .. }
        | Instruction::RequireCloseResult { .. }
        | Instruction::LoadImportMeta { .. }
        | Instruction::DisposeCapture { .. }
        | Instruction::SuppressError { .. }
        | Instruction::Import { .. }
        | Instruction::ImportDynamic { .. }
        | Instruction::Export { .. }
        | Instruction::GetSuper { .. }
        | Instruction::SetSuper { .. }
        | Instruction::ImportAttributes { .. }
        | Instruction::ImportDynamicAttributes { .. }
        | Instruction::CopyDataProperties { .. }
        | Instruction::GetTemplateObject { .. }
        | Instruction::RequireGlobalBinding { .. }
        | Instruction::Suspend { .. }
        | Instruction::Await { .. }
        | Instruction::Throw { .. } => true,
        Instruction::Move { .. }
        | Instruction::TypeOfGlobal { .. }
        | Instruction::LoadThis { .. }
        | Instruction::LoadArguments { .. }
        | Instruction::LoadNewTarget { .. }
        | Instruction::CreatePrivateName { .. }
        | Instruction::Jump { .. }
        | Instruction::JumpIfTrue { .. }
        | Instruction::JumpIfFalse { .. }
        | Instruction::Return { .. }
        | Instruction::Halt => false,
    }
}

/// Whether the opcode is emitted directly by the compiler/reference driver and
/// therefore requires an explicit pre-effect fuel charge. This exhaustive match
/// keeps the one-charge ledger synchronized with the bytecode algebra.
fn is_inline_instruction(instruction: Instruction) -> bool {
    match instruction {
        Instruction::Move { .. }
        | Instruction::Jump { .. }
        | Instruction::JumpIfTrue { .. }
        | Instruction::JumpIfFalse { .. }
        | Instruction::Return { .. }
        | Instruction::Halt
        | Instruction::Throw { .. }
        | Instruction::Suspend { .. }
        | Instruction::Await { .. } => true,
        Instruction::LoadConst { .. }
        | Instruction::Unary { .. }
        | Instruction::Binary { .. }
        | Instruction::CreateObject { .. }
        | Instruction::ToObject { .. }
        | Instruction::CreateArray { .. }
        | Instruction::CreateCell { .. }
        | Instruction::CreateClosure { .. }
        | Instruction::GetProperty { .. }
        | Instruction::SetProperty { .. }
        | Instruction::DefineDataProperty { .. }
        | Instruction::LoadOwnDescriptorSlot { .. }
        | Instruction::DefineOwnDescriptorSlot { .. }
        | Instruction::WithHasBinding { .. }
        | Instruction::DeleteProperty { .. }
        | Instruction::DefineAccessor { .. }
        | Instruction::Call { .. }
        | Instruction::Construct { .. }
        | Instruction::ConstructWithNewTarget { .. }
        | Instruction::LoadGlobal { .. }
        | Instruction::StoreGlobal { .. }
        | Instruction::TypeOfGlobal { .. }
        | Instruction::LoadThis { .. }
        | Instruction::LoadArguments { .. }
        | Instruction::LoadNewTarget { .. }
        | Instruction::LoadImportMeta { .. }
        | Instruction::ArrayPush { .. }
        | Instruction::ArrayExtend { .. }
        | Instruction::ObjectSpread { .. }
        | Instruction::SetPrototype { .. }
        | Instruction::CreatePrivateName { .. }
        | Instruction::CreateRegExp { .. }
        | Instruction::GetIterator { .. }
        | Instruction::IteratorNext { .. }
        | Instruction::IteratorStep { .. }
        | Instruction::IteratorResult { .. }
        | Instruction::IteratorClose { .. }
        | Instruction::RequireCloseResult { .. }
        | Instruction::DisposeCapture { .. }
        | Instruction::SuppressError { .. }
        | Instruction::Import { .. }
        | Instruction::ImportDynamic { .. }
        | Instruction::Export { .. }
        | Instruction::GetSuper { .. }
        | Instruction::SetSuper { .. }
        | Instruction::ImportAttributes { .. }
        | Instruction::ImportDynamicAttributes { .. }
        | Instruction::CopyDataProperties { .. }
        | Instruction::GetTemplateObject { .. }
        | Instruction::RequireGlobalBinding { .. } => false,
    }
}

/// The resume-dispatch tokens the entry accepts: `0` (fresh call) plus `P + 1`
/// for each reachable `Suspend`/`Await` at bytecode pc `P`, sorted and
/// deduplicated. One pc holds one instruction, so tokens are unique across
/// both suspension opcodes by construction.
fn resume_tokens(code: &[Instruction], reachable: &BTreeSet<usize>) -> Vec<u32> {
    let mut tokens = BTreeSet::new();
    if !code.is_empty() {
        tokens.insert(0u32);
    }
    for &pc in reachable {
        if let Instruction::Suspend { .. } | Instruction::Await { .. } = code[pc] {
            tokens.insert(pc as u32 + 1);
        }
    }
    tokens.into_iter().collect()
}

/// The innermost handler whose half-open `[start, end)` interval covers `pc`.
///
/// The verifier proves handlers are pairwise nested or disjoint, so "innermost"
/// is the covering handler with the greatest start (ties broken by smallest end,
/// then latest index) — a total, deterministic order.
fn innermost_handler(handlers: &[ExceptionHandler], pc: usize) -> Option<ExceptionHandler> {
    let pc = pc as u32;
    let mut best: Option<(usize, ExceptionHandler)> = None;
    for (index, handler) in handlers.iter().copied().enumerate() {
        if handler.start.get() > pc || pc >= handler.end.get() {
            continue;
        }
        let is_better = match best {
            None => true,
            Some((best_index, current)) => {
                (handler.start.get(), current.end.get(), index)
                    > (current.start.get(), handler.end.get(), best_index)
            }
        };
        if is_better {
            best = Some((index, handler));
        }
    }
    best.map(|(_, handler)| handler)
}

trait NormalSuccessors {
    /// Visits each normal-control successor pc (excluding handler edges).
    fn visit_normal_successors(self, pc: usize, visit: impl FnMut(usize));
}

impl NormalSuccessors for Instruction {
    fn visit_normal_successors(self, pc: usize, mut visit: impl FnMut(usize)) {
        match self {
            Instruction::Jump { target } => visit(target.get() as usize),
            Instruction::JumpIfTrue { target, .. } | Instruction::JumpIfFalse { target, .. } => {
                visit(target.get() as usize);
                visit(pc + 1);
            }
            // A suspension returns now; its `resume` pc is entered by a later
            // call through the resume prologue.
            Instruction::Suspend { resume, .. } | Instruction::Await { resume, .. } => {
                visit(resume.get() as usize);
            }
            Instruction::Return { .. } | Instruction::Throw { .. } | Instruction::Halt => {}
            Instruction::LoadConst { .. }
            | Instruction::Move { .. }
            | Instruction::Unary { .. }
            | Instruction::Binary { .. }
            | Instruction::CreateObject { .. }
            | Instruction::ToObject { .. }
            | Instruction::CreateArray { .. }
            | Instruction::CreateCell { .. }
            | Instruction::CreateClosure { .. }
            | Instruction::GetProperty { .. }
            | Instruction::SetProperty { .. }
            | Instruction::DefineDataProperty { .. }
            | Instruction::LoadOwnDescriptorSlot { .. }
            | Instruction::DefineOwnDescriptorSlot { .. }
            | Instruction::WithHasBinding { .. }
            | Instruction::DeleteProperty { .. }
            | Instruction::DefineAccessor { .. }
            | Instruction::Call { .. }
            | Instruction::Construct { .. }
            | Instruction::ConstructWithNewTarget { .. }
            | Instruction::LoadGlobal { .. }
            | Instruction::StoreGlobal { .. }
            | Instruction::TypeOfGlobal { .. }
            | Instruction::LoadThis { .. }
            | Instruction::LoadArguments { .. }
            | Instruction::LoadNewTarget { .. }
            | Instruction::LoadImportMeta { .. }
            | Instruction::SuppressError { .. }
            | Instruction::ArrayPush { .. }
            | Instruction::ArrayExtend { .. }
            | Instruction::ObjectSpread { .. }
            | Instruction::SetPrototype { .. }
            | Instruction::CreatePrivateName { .. }
            | Instruction::CreateRegExp { .. }
            | Instruction::GetIterator { .. }
            | Instruction::IteratorNext { .. }
            | Instruction::IteratorStep { .. }
            | Instruction::IteratorResult { .. }
            | Instruction::IteratorClose { .. }
            | Instruction::RequireCloseResult { .. }
            | Instruction::DisposeCapture { .. }
            | Instruction::Import { .. }
            | Instruction::ImportDynamic { .. }
            | Instruction::Export { .. }
            | Instruction::GetSuper { .. }
            | Instruction::SetSuper { .. }
            | Instruction::ImportAttributes { .. }
            | Instruction::ImportDynamicAttributes { .. }
            | Instruction::CopyDataProperties { .. }
            | Instruction::GetTemplateObject { .. }
            | Instruction::RequireGlobalBinding { .. } => visit(pc + 1),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bamts_bytecode::{
        Constant, ConstantId, EcmaString, Function as BytecodeFunction, FunctionFlags, Instruction,
        Pc, Register,
    };
    use cranelift_codegen::isa;

    /// A frontend config for the host target, without naming `target_lexicon`.
    fn host_config() -> TargetFrontendConfig {
        let flags = Flags::new(settings::builder());
        for name in [
            "x86_64",
            "aarch64",
            "riscv64",
            "s390x",
            "x86_64-unknown-linux-gnu",
        ] {
            if let Ok(builder) = isa::lookup_by_name(name)
                && let Ok(target) = builder.finish(flags.clone())
            {
                return target.frontend_config();
            }
        }
        panic!("no native ISA available for tests");
    }

    fn reg(index: u32) -> Register {
        Register::new(index)
    }

    fn func(
        register_count: u32,
        code: Vec<Instruction>,
        handlers: Vec<ExceptionHandler>,
    ) -> BytecodeFunction {
        BytecodeFunction::new(
            None,
            0,
            0,
            register_count,
            FunctionFlags::default(),
            code,
            handlers,
        )
    }

    fn verified(constants: Vec<Constant>, functions: Vec<BytecodeFunction>) -> Module<Verified> {
        Module::new(constants, functions, FunctionId::new(0))
            .verify()
            .expect("test module verifies")
    }

    fn single(function: BytecodeFunction) -> Module<Verified> {
        verified(vec![Constant::Undefined], vec![function])
    }

    #[test]
    fn capture_count_metadata_is_surfaced() {
        // A function declaring leading capture cells surfaces that count as
        // lowering metadata so a backend/runtime need not re-derive it. Entry
        // init (capture cells then parameters) counts as definitely-initialized,
        // so the body may read its capture registers without a prior write.
        let function = BytecodeFunction::new(
            None,
            2, // capture_count
            1, // parameter_count
            4, // register_count (>= captures + params)
            FunctionFlags::default(),
            vec![
                Instruction::Move {
                    dst: reg(3),
                    src: reg(0), // a capture cell, initialized on entry
                },
                Instruction::Halt,
            ],
            Vec::new(),
        );
        let module = single(function);
        let lowered = lower_code_module(ModuleId::new(0), &module, host_config()).expect("lowers");
        assert_eq!(lowered.functions[0].capture_count, 2);
    }

    /// Load `Undefined` (constant 0) into `dst`; a cheap way to satisfy the
    /// definite-initialization verifier before a register is read.
    fn load_undef(dst: Register) -> Instruction {
        Instruction::LoadConst {
            dst,
            constant: ConstantId::new(0),
        }
    }

    fn clif_of(module: &Module<Verified>) -> String {
        let lowered = lower_code_module(ModuleId::new(0), module, host_config()).expect("lowers");
        lowered.functions[0].clif.display().to_string()
    }

    /// Lower a module and return the single function's helpers and CLIF text.
    fn lower_one(module: &Module<Verified>) -> (Vec<Helper>, String) {
        let lowered = lower_code_module(ModuleId::new(0), module, host_config()).expect("lowers");
        let function = &lowered.functions[0];
        (
            function.helpers.clone(),
            function.clif.display().to_string(),
        )
    }

    #[test]
    fn entry_signature_is_the_native_abi() {
        let module = single(func(1, vec![Instruction::Halt], Vec::new()));
        let lowered = lower_code_module(ModuleId::new(0), &module, host_config()).expect("lowers");
        let function = &lowered.functions[0];
        let signature = &function.signature;
        assert_eq!(signature.params.len(), 2);
        assert_eq!(signature.params[0].value_type, types::I64);
        assert_eq!(signature.params[1].value_type, types::I64);
        assert_eq!(signature.returns.len(), 1);
        assert_eq!(signature.returns[0].value_type, types::I32);
        assert_eq!(function.symbol, "bamts_m0_fn_0");
        assert_eq!(function.id.get(), 0);
        assert_eq!(lowered.entry.get(), 0);
    }

    #[test]
    fn halt_only_function_returns_normal_with_undefined() {
        let module = single(func(1, vec![Instruction::Halt], Vec::new()));
        let clif = clif_of(&module);
        // Single entry (token 0): no resume-token load.
        assert!(
            !clif.contains("load.i32"),
            "no dispatch load expected:\n{clif}"
        );
        assert!(
            clif.contains("0x7ffb_0000_0000_0000"),
            "undefined store missing:\n{clif}"
        );
        assert!(clif.contains("return"), "must return:\n{clif}");
        let lowered = lower_code_module(ModuleId::new(0), &module, host_config()).expect("lowers");
        assert_eq!(lowered.functions[0].helpers, vec![Helper::ConsumeFuel]);
        assert_eq!(lowered.functions[0].entry_points, vec![0]);
    }

    #[test]
    fn helper_index_table_is_a_stable_bijection() {
        // Every helper round-trips through its external index, and the table
        // covers a dense 0..=52 range with unique symbols.
        let helpers = [
            Helper::LoadConstant,
            Helper::Unary,
            Helper::Binary,
            Helper::CreateObject,
            Helper::CreateArray,
            Helper::CreateClosure,
            Helper::GetProperty,
            Helper::SetProperty,
            Helper::DeleteProperty,
            Helper::Call,
            Helper::Construct,
            Helper::Import,
            Helper::Truthy,
            Helper::ResumeValue,
            Helper::DefineAccessor,
            Helper::LoadGlobal,
            Helper::StoreGlobal,
            Helper::TypeOfGlobal,
            Helper::LoadThis,
            Helper::LoadArguments,
            Helper::LoadNewTarget,
            Helper::ArrayPush,
            Helper::ArrayExtend,
            Helper::ObjectSpread,
            Helper::SetPrototype,
            Helper::CreatePrivateName,
            Helper::CreateRegExp,
            Helper::GetIterator,
            Helper::IteratorNext,
            Helper::Export,
            Helper::ConsumeFuel,
            Helper::CreateCell,
            Helper::IteratorStep,
            Helper::IteratorResult,
            Helper::IteratorClose,
            Helper::RequireCloseResult,
            Helper::ToObject,
            Helper::ImportDynamic,
            Helper::LoadImportMeta,
            Helper::DisposeCapture,
            Helper::SuppressError,
            Helper::ConstructWithNewTarget,
            Helper::DefineDataProperty,
            Helper::LoadOwnDescriptorSlot,
            Helper::DefineOwnDescriptorSlot,
            Helper::WithHasBinding,
            Helper::ResumeMode,
            Helper::GetSuper,
            Helper::SetSuper,
            Helper::ImportAttributes,
            Helper::ImportDynamicAttributes,
            Helper::CopyDataProperties,
            Helper::GetTemplateObject,
            Helper::RequireGlobalBinding,
        ];
        let mut symbols = BTreeSet::new();
        for (expected_index, helper) in helpers.iter().copied().enumerate() {
            let index = helper.external_index();
            assert_eq!(index as usize, expected_index, "dense index for {helper:?}");
            assert_eq!(
                Helper::from_external_index(index),
                Some(helper),
                "round-trip for {helper:?}"
            );
            assert!(symbols.insert(helper.symbol()), "unique symbol {helper:?}");
        }
        assert_eq!(symbols.len(), 54);
        assert_eq!(Helper::from_external_index(54), None);
    }
    #[test]
    fn iterator_close_helpers_use_the_pinned_abis() {
        let module = single(func(
            3,
            vec![
                load_undef(reg(0)),
                Instruction::IteratorClose {
                    result: reg(1),
                    called: reg(2),
                    iterator: reg(0),
                    mode: IteratorCloseMode::Propagate,
                },
                Instruction::RequireCloseResult {
                    result: reg(1),
                    called: reg(2),
                },
                Instruction::DisposeCapture {
                    method: reg(1),
                    kind: reg(2),
                    src: reg(0),
                    hint: DisposeHint::Async,
                },
                Instruction::SuppressError {
                    dst: reg(1),
                    error: reg(0),
                    suppressed: reg(1),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        ));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::IteratorClose));
        assert!(helpers.contains(&Helper::RequireCloseResult));
        assert!(helpers.contains(&Helper::DisposeCapture));
        assert!(helpers.contains(&Helper::SuppressError));
        assert_eq!(Helper::IteratorClose.external_index(), 34);
        assert_eq!(Helper::RequireCloseResult.external_index(), 35);
        assert_eq!(Helper::DisposeCapture.external_index(), 39);
        assert_eq!(Helper::SuppressError.external_index(), 40);
        assert!(
            clif.contains("(i64, i64, i32, i32, i64) -> i32"),
            "iterator-close helper sig wrong:\n{clif}"
        );
        assert!(
            clif.contains("(i64, i64, i64, i64) -> i32"),
            "require-close-result helper sig wrong:\n{clif}"
        );
        assert!(
            clif.contains("u1:39"),
            "dispose-capture helper import missing:\n{clif}"
        );
    }

    #[test]
    fn load_const_routes_through_the_constant_helper() {
        let module = single(func(
            1,
            vec![load_undef(reg(0)), Instruction::Halt],
            Vec::new(),
        ));
        let (helpers, clif) = lower_one(&module);
        assert_eq!(helpers, vec![Helper::LoadConstant, Helper::ConsumeFuel]);
        assert_eq!(Helper::LoadConstant.symbol(), "bamts_load_constant");
        assert_eq!(Helper::LoadConstant.external_index(), 0);
        assert_eq!(Helper::from_external_index(0), Some(Helper::LoadConstant));
        assert!(
            clif.contains("u1:0"),
            "constant helper import missing:\n{clif}"
        );
        assert!(
            clif.contains("(i64, i32, i64) -> i32"),
            "constant helper sig wrong:\n{clif}"
        );
        assert!(clif.contains("call"), "helper call missing:\n{clif}");
    }

    #[test]
    fn binary_routes_through_the_binary_helper() {
        let code = vec![
            load_undef(reg(0)),
            load_undef(reg(1)),
            Instruction::Binary {
                dst: reg(2),
                op: BinaryOp::Add,
                left: reg(0),
                right: reg(1),
            },
            Instruction::Halt,
        ];
        let module = single(func(3, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::Binary));
        assert_eq!(Helper::Binary.external_index(), 2);
        assert!(
            clif.contains("u1:2"),
            "binary helper import missing:\n{clif}"
        );
        assert!(
            clif.contains("(i64, i32, i64, i64, i64) -> i32"),
            "binary helper sig wrong:\n{clif}"
        );
    }

    #[test]
    fn unary_routes_through_the_unary_helper() {
        let code = vec![
            load_undef(reg(0)),
            Instruction::Unary {
                dst: reg(1),
                op: UnaryOp::Negate,
                operand: reg(0),
            },
            Instruction::Halt,
        ];
        let module = single(func(2, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::Unary));
        assert!(
            clif.contains("u1:1"),
            "unary helper import missing:\n{clif}"
        );
        assert!(
            clif.contains("(i64, i32, i64, i64) -> i32"),
            "unary helper sig wrong:\n{clif}"
        );
    }

    #[test]
    fn move_copies_registers_without_a_helper() {
        let code = vec![
            load_undef(reg(0)),
            Instruction::Move {
                dst: reg(1),
                src: reg(0),
            },
            Instruction::Halt,
        ];
        let module = single(func(2, code, Vec::new()));
        let (helpers, _) = lower_one(&module);
        // Move introduces only its explicit instruction-budget helper.
        assert_eq!(helpers, vec![Helper::LoadConstant, Helper::ConsumeFuel]);
    }

    #[test]
    fn reachable_inline_pcs_each_emit_one_fuel_charge() {
        let code = vec![
            load_undef(reg(0)),
            Instruction::Move {
                dst: reg(1),
                src: reg(0),
            },
            Instruction::Jump { target: Pc::new(4) },
            Instruction::Binary {
                dst: reg(0),
                op: BinaryOp::Add,
                left: reg(0),
                right: reg(0),
            },
            Instruction::Halt,
        ];
        let module = single(func(2, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert_eq!(helpers, vec![Helper::LoadConstant, Helper::ConsumeFuel]);

        let declaration = clif
            .lines()
            .find(|line| line.contains("u1:30"))
            .expect("consume-fuel import");
        let function_ref = declaration
            .split_whitespace()
            .next()
            .expect("helper function reference");
        assert_eq!(
            clif.matches(&format!("call {function_ref}")).count(),
            3,
            "Move, Jump, and Halt each charge once; LoadConst and unreachable Binary do not:\n{clif}"
        );
    }

    #[test]
    fn conditional_branch_coerces_via_truthy() {
        // r0 = undef; if truthy(r0) goto 3 else fall to 2; both halt.
        let code = vec![
            load_undef(reg(0)),
            Instruction::JumpIfTrue {
                condition: reg(0),
                target: Pc::new(3),
            },
            Instruction::Halt,
            Instruction::Halt,
        ];
        let module = single(func(1, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::Truthy));
        assert_eq!(Helper::Truthy.external_index(), 12);
        assert!(
            clif.contains("u1:12"),
            "truthy helper import missing:\n{clif}"
        );
        // Truthy is total: two i64 params, one i32 result, no out-parameter.
        assert!(
            clif.contains("(i64, i64) -> i32"),
            "truthy helper sig wrong:\n{clif}"
        );
        assert!(clif.contains("brif"), "conditional branch missing:\n{clif}");
    }

    #[test]
    fn jump_if_false_branches_with_inverted_polarity() {
        // pc0: r0 = undef. pc1: if !truthy(r0) goto pc3 else fall to pc2.
        // The truthy edge must fall through to pc2; the falsy edge must reach
        // the jump target pc3 — the argument-swapped mirror of JumpIfTrue.
        let code = vec![
            load_undef(reg(0)),
            Instruction::JumpIfFalse {
                condition: reg(0),
                target: Pc::new(3),
            },
            Instruction::Halt,
            Instruction::Halt,
        ];
        let module = single(func(1, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::Truthy));
        let truthy_declaration = clif
            .lines()
            .find(|line| line.contains("u1:12"))
            .expect("truthy import");
        let truthy_ref = truthy_declaration
            .split_whitespace()
            .next()
            .expect("truthy function reference");
        let mut lines = clif.lines();
        lines
            .find(|line| line.contains(&format!("call {truthy_ref}")))
            .expect("truthy call");
        let brif = lines
            .find(|line| line.contains("brif"))
            .expect("conditional branch missing");
        let edges: Vec<u32> = brif
            .split(|c: char| !c.is_ascii_alphanumeric())
            .filter_map(|token| token.strip_prefix("block").and_then(|n| n.parse().ok()))
            .collect();
        assert_eq!(
            edges.len(),
            2,
            "conditional brif has two block edges:\n{clif}"
        );
        assert!(
            edges[0] < edges[1],
            "JumpIfFalse polarity: truthy edge must target the earlier fallthrough block:\n{clif}"
        );
    }

    #[test]
    fn create_closure_passes_the_captures_value_not_an_index() {
        // r0 = undef (captures array placeholder); r1 = closure(fn 0, captures r0).
        let code = vec![
            load_undef(reg(0)),
            Instruction::CreateClosure {
                dst: reg(1),
                function: FunctionId::new(0),
                captures: reg(0),
            },
            Instruction::Halt,
        ];
        let module = single(func(2, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::CreateClosure));
        assert_eq!(Helper::CreateClosure.external_index(), 5);
        assert!(
            clif.contains("u1:5"),
            "closure helper import missing:\n{clif}"
        );
        // (frame, function_id:i32, captures:i64, out) -> tag.
        assert!(
            clif.contains("(i64, i32, i64, i64) -> i32"),
            "closure helper sig wrong:\n{clif}"
        );
        // The captures register (r0) is loaded and passed as a value; the args
        // path performs no pointer arithmetic.
        assert!(
            !clif.contains("iadd"),
            "closure captures must be a value, not a computed pointer:\n{clif}"
        );
    }

    #[test]
    fn call_passes_arguments_as_a_value_without_pointer_math() {
        // r0..r2 = undef; r3 = call r0 with this=r1 and arguments array r2.
        let code = vec![
            load_undef(reg(0)),
            load_undef(reg(1)),
            load_undef(reg(2)),
            Instruction::Call {
                dst: reg(3),
                callee: reg(0),
                this_value: reg(1),
                arguments: reg(2),
            },
            Instruction::Halt,
        ];
        let module = single(func(4, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::Call));
        assert_eq!(Helper::Call.external_index(), 9);
        assert!(clif.contains("u1:9"), "call helper import missing:\n{clif}");
        // (frame, callee, this, arguments, out) -> tag; arguments is a value.
        assert!(
            clif.contains("(i64, i64, i64, i64, i64) -> i32"),
            "call helper sig wrong:\n{clif}"
        );
        // No fixed window: the arguments array is a register value, not a
        // computed base pointer.
        assert!(
            !clif.contains("iadd"),
            "arguments must be a value, not a window pointer:\n{clif}"
        );
    }

    #[test]
    fn construct_passes_arguments_as_a_value() {
        let code = vec![
            load_undef(reg(0)),
            load_undef(reg(1)),
            Instruction::Construct {
                dst: reg(2),
                callee: reg(0),
                arguments: reg(1),
            },
            Instruction::Halt,
        ];
        let module = single(func(3, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::Construct));
        assert_eq!(Helper::Construct.external_index(), 10);
        assert!(clif.contains("u1:10"), "construct import missing:\n{clif}");
        assert!(
            clif.contains("(i64, i64, i64, i64) -> i32"),
            "construct helper sig wrong:\n{clif}"
        );
    }

    #[test]
    fn construct_with_new_target_uses_call_shaped_five_i64_abi() {
        // r0 = callee; r1 = new_target; r2 = arguments array; r3 = dst.
        let code = vec![
            load_undef(reg(0)),
            load_undef(reg(1)),
            load_undef(reg(2)),
            Instruction::ConstructWithNewTarget {
                dst: reg(3),
                callee: reg(0),
                new_target: reg(1),
                arguments: reg(2),
            },
            Instruction::Halt,
        ];
        let module = single(func(4, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::ConstructWithNewTarget));
        assert_eq!(Helper::ConstructWithNewTarget.external_index(), 41);
        assert_eq!(
            Helper::ConstructWithNewTarget.symbol(),
            "bamts_construct_with_new_target"
        );
        assert_eq!(Helper::Construct.external_index(), 10);
        assert!(
            clif.contains("u1:41"),
            "construct-with-new-target import missing:\n{clif}"
        );
        assert!(
            clif.contains("(i64, i64, i64, i64, i64) -> i32"),
            "construct-with-new-target must share Call's five-I64 ABI:\n{clif}"
        );
        assert!(
            !clif.contains("iadd"),
            "arguments must be a value, not a window pointer:\n{clif}"
        );
    }

    #[test]
    fn define_data_property_uses_call_shaped_five_i64_abi() {
        // r0 = object; r1 = key; r2 = value. No destination register.
        let code = vec![
            Instruction::CreateObject { dst: reg(0) },
            load_undef(reg(1)),
            load_undef(reg(2)),
            Instruction::DefineDataProperty {
                object: reg(0),
                key: reg(1),
                value: reg(2),
            },
            Instruction::Halt,
        ];
        let module = single(func(3, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::DefineDataProperty));
        assert_eq!(Helper::DefineDataProperty.external_index(), 42);
        assert_eq!(
            Helper::DefineDataProperty.symbol(),
            "bamts_define_data_property"
        );
        assert_eq!(Helper::SetProperty.external_index(), 7);
        assert!(
            clif.contains("u1:42"),
            "define-data-property import missing:\n{clif}"
        );
        assert!(
            clif.contains("(i64, i64, i64, i64, i64) -> i32"),
            "define-data-property must share Call's five-I64 ABI:\n{clif}"
        );
    }

    #[test]
    fn load_own_descriptor_slot_uses_object_key_slot_abi() {
        let code = vec![
            Instruction::CreateObject { dst: reg(0) },
            load_undef(reg(1)),
            Instruction::LoadOwnDescriptorSlot {
                dst: reg(2),
                object: reg(0),
                key: reg(1),
                slot: DescriptorSlot::Getter,
            },
            Instruction::Halt,
        ];
        let module = single(func(3, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::LoadOwnDescriptorSlot));
        assert_eq!(Helper::LoadOwnDescriptorSlot.external_index(), 43);
        assert_eq!(
            Helper::LoadOwnDescriptorSlot.symbol(),
            "bamts_load_own_descriptor_slot"
        );
        assert!(
            clif.contains("u1:43"),
            "load-own-descriptor-slot import missing:\n{clif}"
        );
        assert!(
            clif.contains("(i64, i64, i64, i32, i64) -> i32"),
            "load-own-descriptor-slot ABI wrong:\n{clif}"
        );
    }

    #[test]
    fn define_own_descriptor_slot_uses_define_accessor_shaped_abi() {
        let code = vec![
            Instruction::CreateObject { dst: reg(0) },
            load_undef(reg(1)),
            load_undef(reg(2)),
            Instruction::DefineOwnDescriptorSlot {
                object: reg(0),
                key: reg(1),
                src: reg(2),
                slot: DescriptorSlot::Value,
            },
            Instruction::Halt,
        ];
        let module = single(func(3, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::DefineOwnDescriptorSlot));
        assert_eq!(Helper::DefineOwnDescriptorSlot.external_index(), 44);
        assert_eq!(
            Helper::DefineOwnDescriptorSlot.symbol(),
            "bamts_define_own_descriptor_slot"
        );
        assert_eq!(Helper::DefineAccessor.external_index(), 14);
        assert!(
            clif.contains("u1:44"),
            "define-own-descriptor-slot import missing:\n{clif}"
        );
        assert!(
            clif.contains("(i64, i64, i64, i64, i32, i64) -> i32"),
            "define-own-descriptor-slot must share DefineAccessor ABI:\n{clif}"
        );
    }

    #[test]
    fn with_has_binding_uses_get_property_shaped_abi() {
        let code = vec![
            Instruction::CreateObject { dst: reg(0) },
            load_undef(reg(1)),
            Instruction::WithHasBinding {
                dst: reg(2),
                object: reg(0),
                key: reg(1),
            },
            Instruction::Halt,
        ];
        let module = single(func(3, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::WithHasBinding));
        assert_eq!(Helper::WithHasBinding.external_index(), 45);
        assert_eq!(Helper::WithHasBinding.symbol(), "bamts_with_has_binding");
        assert!(
            clif.contains("u1:45"),
            "with-has-binding import missing:\n{clif}"
        );
        assert!(
            clif.contains("(i64, i64, i64, i64) -> i32"),
            "with-has-binding ABI wrong:\n{clif}"
        );
    }

    #[test]
    fn calls_scale_past_fixed_window_via_arguments_array() {
        // A single arguments-array register removes any fixed-window ceiling:
        // there is no arg_count operand and no per-argument addressing at all.
        let code = vec![
            load_undef(reg(0)),
            load_undef(reg(1)),
            load_undef(reg(2)),
            Instruction::Call {
                dst: reg(3),
                callee: reg(0),
                this_value: reg(1),
                arguments: reg(2),
            },
            Instruction::Halt,
        ];
        let module = single(func(4, code, Vec::new()));
        let (_, clif) = lower_one(&module);
        // The call carries exactly one arguments operand regardless of arity.
        assert!(
            !clif.contains("iadd"),
            "no window arithmetic for any arity:\n{clif}"
        );
    }

    #[test]
    fn property_access_uses_a_register_key() {
        // r0 = object; r1 = key value; r2 = r0[r1]; r0[r1] = r1; delete r0[r1].
        let code = vec![
            Instruction::CreateObject { dst: reg(0) },
            load_undef(reg(1)),
            Instruction::GetProperty {
                dst: reg(2),
                object: reg(0),
                key: reg(1),
            },
            Instruction::SetProperty {
                object: reg(0),
                key: reg(1),
                value: reg(1),
            },
            Instruction::DeleteProperty {
                dst: reg(3),
                object: reg(0),
                key: reg(1),
            },
            Instruction::Halt,
        ];
        let module = single(func(4, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::GetProperty));
        assert!(helpers.contains(&Helper::SetProperty));
        assert!(helpers.contains(&Helper::DeleteProperty));
        assert!(
            clif.contains("u1:6"),
            "get-property import missing:\n{clif}"
        );
        assert!(
            clif.contains("u1:7"),
            "set-property import missing:\n{clif}"
        );
        assert!(
            clif.contains("u1:8"),
            "delete-property import missing:\n{clif}"
        );
        assert!(
            clif.contains("(i64, i64, i64, i32, i64) -> i32"),
            "get property sig wrong (register key):\n{clif}"
        );
        assert!(
            clif.contains("(i64, i64, i64, i64) -> i32"),
            "delete property sig wrong (register key):\n{clif}"
        );
        assert!(
            clif.contains("(i64, i64, i64, i64, i32, i64) -> i32"),
            "set property sig wrong (register key):\n{clif}"
        );
    }

    #[test]
    fn define_accessor_carries_a_kind_selector() {
        let code = vec![
            Instruction::CreateObject { dst: reg(0) },
            load_undef(reg(1)),
            load_undef(reg(2)),
            Instruction::DefineAccessor {
                object: reg(0),
                key: reg(1),
                accessor: reg(2),
                kind: AccessorKind::Getter,
            },
            Instruction::Halt,
        ];
        let module = single(func(3, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::DefineAccessor));
        assert_eq!(Helper::DefineAccessor.external_index(), 14);
        assert!(clif.contains("u1:14"), "accessor import missing:\n{clif}");
        // (frame, object, key, accessor, kind:i32, out) -> tag.
        assert!(
            clif.contains("(i64, i64, i64, i64, i32, i64) -> i32"),
            "accessor helper sig wrong:\n{clif}"
        );
    }

    #[test]
    fn globals_lower_to_load_store_and_typeof_helpers() {
        let code = vec![
            Instruction::LoadGlobal {
                dst: reg(0),
                name: ConstantId::new(0),
            },
            Instruction::StoreGlobal {
                name: ConstantId::new(0),
                value: reg(0),
            },
            Instruction::TypeOfGlobal {
                dst: reg(1),
                name: ConstantId::new(0),
            },
            Instruction::Halt,
        ];
        let module = verified(
            vec![Constant::String(EcmaString::encode("g"))],
            vec![func(2, code, Vec::new())],
        );
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::LoadGlobal));
        assert!(helpers.contains(&Helper::StoreGlobal));
        assert!(helpers.contains(&Helper::TypeOfGlobal));
        assert!(
            clif.contains("u1:15"),
            "load-global import missing:\n{clif}"
        );
        assert!(
            clif.contains("u1:16"),
            "store-global import missing:\n{clif}"
        );
        assert!(
            clif.contains("u1:17"),
            "typeof-global import missing:\n{clif}"
        );
    }

    #[test]
    fn this_arguments_new_target_are_total_and_unhandled() {
        // Total helpers (no throw) still write out.value; even under a covering
        // handler they must not mark the handler reachable, so LoadThis under a
        // handler still lowers cleanly with no handler routing helper.
        let code = vec![
            Instruction::LoadThis { dst: reg(0) },
            Instruction::LoadArguments { dst: reg(1) },
            Instruction::LoadNewTarget { dst: reg(2) },
            Instruction::Halt,
        ];
        let module = single(func(3, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::LoadThis));
        assert!(helpers.contains(&Helper::LoadArguments));
        assert!(helpers.contains(&Helper::LoadNewTarget));
        assert!(clif.contains("u1:18"), "load-this import missing:\n{clif}");
        assert!(
            clif.contains("u1:19"),
            "load-arguments import missing:\n{clif}"
        );
        assert!(
            clif.contains("u1:20"),
            "load-new-target import missing:\n{clif}"
        );
    }

    #[test]
    fn total_helper_under_handler_does_not_emit_handler_edge() {
        // A handler covers a total (non-throwing) TypeOfGlobal. Because it can
        // never throw, the handler pc is unreachable and not emitted; lowering
        // must still succeed (the abnormal edge propagates rather than jumping
        // to a non-existent block).
        let code = vec![
            Instruction::TypeOfGlobal {
                dst: reg(0),
                name: ConstantId::new(0),
            },
            Instruction::Halt,
            // pc 2: would-be handler, unreachable via the total op.
            load_undef(reg(0)),
            Instruction::Halt,
        ];
        let handlers = vec![ExceptionHandler {
            start: Pc::new(0),
            end: Pc::new(1),
            handler: Pc::new(2),
            catch_register: reg(0),
        }];
        let module = verified(
            vec![Constant::String(EcmaString::encode("g"))],
            vec![func(1, code, handlers)],
        );
        // Must lower without panicking on a missing handler block.
        let lowered = lower_code_module(ModuleId::new(0), &module, host_config()).expect("lowers");
        assert!(lowered.functions[0].helpers.contains(&Helper::TypeOfGlobal));
    }

    #[test]
    fn arrays_and_spreads_lower_to_their_helpers() {
        let code = vec![
            Instruction::CreateArray { dst: reg(0) },
            load_undef(reg(1)),
            Instruction::ArrayPush {
                array: reg(0),
                value: reg(1),
            },
            Instruction::ArrayExtend {
                array: reg(0),
                iterable: reg(1),
            },
            Instruction::CreateObject { dst: reg(2) },
            Instruction::ObjectSpread {
                target: reg(2),
                source: reg(1),
            },
            Instruction::Halt,
        ];
        let module = single(func(3, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::ArrayPush));
        assert!(helpers.contains(&Helper::ArrayExtend));
        assert!(helpers.contains(&Helper::ObjectSpread));
        assert!(clif.contains("u1:21"), "array-push import missing:\n{clif}");
        assert!(
            clif.contains("u1:22"),
            "array-extend import missing:\n{clif}"
        );
        assert!(
            clif.contains("u1:23"),
            "object-spread import missing:\n{clif}"
        );
    }

    #[test]
    fn prototype_private_and_regexp_lower_to_their_helpers() {
        let code = vec![
            Instruction::CreateObject { dst: reg(0) },
            Instruction::CreateObject { dst: reg(1) },
            Instruction::SetPrototype {
                object: reg(0),
                prototype: reg(1),
            },
            Instruction::CreatePrivateName {
                dst: reg(2),
                description: ConstantId::new(0),
            },
            Instruction::CreateRegExp {
                dst: reg(3),
                pattern: ConstantId::new(0),
                flags: ConstantId::new(1),
            },
            Instruction::Halt,
        ];
        let module = verified(
            vec![
                Constant::String(EcmaString::encode("p")),
                Constant::String(EcmaString::encode("g")),
            ],
            vec![func(4, code, Vec::new())],
        );
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::SetPrototype));
        assert!(helpers.contains(&Helper::CreatePrivateName));
        assert!(helpers.contains(&Helper::CreateRegExp));
        assert!(
            clif.contains("u1:24"),
            "set-prototype import missing:\n{clif}"
        );
        assert!(
            clif.contains("u1:25"),
            "private-name import missing:\n{clif}"
        );
        assert!(clif.contains("u1:26"), "regexp import missing:\n{clif}");
        // RegExp carries two i32 constant selectors.
        assert!(
            clif.contains("(i64, i32, i32, i64) -> i32"),
            "regexp helper sig wrong:\n{clif}"
        );
    }

    #[test]
    fn get_iterator_carries_a_kind_selector() {
        let code = vec![
            load_undef(reg(0)),
            Instruction::GetIterator {
                dst: reg(1),
                src: reg(0),
                kind: IteratorKind::Sync,
            },
            Instruction::Halt,
        ];
        let module = single(func(2, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::GetIterator));
        assert_eq!(Helper::GetIterator.external_index(), 27);
        assert!(
            clif.contains("u1:27"),
            "get-iterator import missing:\n{clif}"
        );
        // (frame, src:i64, kind:i32, out) -> tag.
        assert!(
            clif.contains("(i64, i64, i32, i64) -> i32"),
            "get-iterator helper sig wrong:\n{clif}"
        );
    }

    #[test]
    fn iterator_next_writes_both_done_and_value_registers() {
        // r0 = iterator; IteratorNext done=r1 value=r2 iterator=r0.
        let code = vec![
            load_undef(reg(0)),
            Instruction::IteratorNext {
                done: reg(1),
                value: reg(2),
                iterator: reg(0),
            },
            Instruction::Halt,
        ];
        let module = single(func(3, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::IteratorNext));
        assert_eq!(Helper::IteratorNext.external_index(), 28);
        assert!(
            clif.contains("u1:28"),
            "iterator-next import missing:\n{clif}"
        );
        // (frame, iterator:i64, done_reg:i32, value_reg:i32, out) -> tag: the two
        // destination register indices are passed so the helper writes both.
        assert!(
            clif.contains("(i64, i64, i32, i32, i64) -> i32"),
            "iterator-next helper sig wrong:\n{clif}"
        );
        // Both destination register indices (r1 -> 1, r2 -> 2) are materialized
        // as i32 constants and handed to the helper.
        assert!(
            clif.contains("iconst.i32 1") && clif.contains("iconst.i32 2"),
            "both destination register indices must be passed:\n{clif}"
        );
    }

    #[test]
    fn iterator_next_under_handler_binds_catch_on_throw() {
        // A throwing IteratorNext under a handler routes its Throw to the catch.
        let code = vec![
            load_undef(reg(0)),
            Instruction::IteratorNext {
                done: reg(1),
                value: reg(2),
                iterator: reg(0),
            },
            Instruction::Halt,
            // pc 3: handler.
            Instruction::Halt,
        ];
        let handlers = vec![ExceptionHandler {
            start: Pc::new(0),
            end: Pc::new(3),
            handler: Pc::new(3),
            catch_register: reg(0),
        }];
        let module = single(func(3, code, handlers));
        let clif = clif_of(&module);
        // Normal-vs-abnormal then throw-vs-propagate around the throwing op.
        let brif_count = clif.matches("brif").count();
        assert!(
            brif_count >= 2,
            "expected handler routing brifs, got {brif_count}:\n{clif}"
        );
    }

    #[test]
    fn iterator_step_routes_its_raw_result_through_the_step_helper() {
        // r0 = iterator; IteratorStep dst=r1 iterator=r0.
        let code = vec![
            load_undef(reg(0)),
            Instruction::IteratorStep {
                dst: reg(1),
                iterator: reg(0),
            },
            Instruction::Halt,
        ];
        let module = single(func(2, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::IteratorStep));
        assert_eq!(Helper::IteratorStep.external_index(), 32);
        assert!(
            clif.contains("u1:32"),
            "iterator-step import missing:\n{clif}"
        );
        // (frame, iterator:i64, out) -> tag: one value operand, result via out.
        assert!(
            clif.contains("(i64, i64, i64) -> i32"),
            "iterator-step helper sig wrong:\n{clif}"
        );
    }

    #[test]
    fn iterator_result_writes_both_done_and_value_registers() {
        // r0 = raw result; IteratorResult done=r1 value=r2 result=r0.
        let code = vec![
            load_undef(reg(0)),
            Instruction::IteratorResult {
                done: reg(1),
                value: reg(2),
                result: reg(0),
            },
            Instruction::Halt,
        ];
        let module = single(func(3, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::IteratorResult));
        assert_eq!(Helper::IteratorResult.external_index(), 33);
        assert!(
            clif.contains("u1:33"),
            "iterator-result import missing:\n{clif}"
        );
        // (frame, result:i64, done_reg:i32, value_reg:i32, out) -> tag: the two
        // destination register indices are passed so the helper writes both.
        assert!(
            clif.contains("(i64, i64, i32, i32, i64) -> i32"),
            "iterator-result helper sig wrong:\n{clif}"
        );
        // Both destination register indices (r1 -> 1, r2 -> 2) are materialized
        // as i32 constants and handed to the helper.
        assert!(
            clif.contains("iconst.i32 1") && clif.contains("iconst.i32 2"),
            "both destination register indices must be passed:\n{clif}"
        );
    }

    #[test]
    fn export_lowers_to_the_export_helper() {
        let code = vec![
            load_undef(reg(0)),
            Instruction::Export {
                name: ConstantId::new(0),
                src: reg(0),
            },
            Instruction::Halt,
        ];
        let module = verified(
            vec![Constant::String(EcmaString::encode("x"))],
            vec![func(1, code, Vec::new())],
        );
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::Export));
        assert_eq!(Helper::Export.external_index(), 29);
        assert!(clif.contains("u1:29"), "export import missing:\n{clif}");
        assert!(
            clif.contains("(i64, i32, i64, i64) -> i32"),
            "export helper sig wrong:\n{clif}"
        );
    }

    #[test]
    fn suspend_uses_a_resume_token_and_resume_helper() {
        // r0 = undef; suspend (yield r0), resume at pc 2; pc 2 halts.
        let code = vec![
            load_undef(reg(0)),
            Instruction::Suspend {
                dst: reg(0),
                src: reg(0),
                resume: Pc::new(2),
                mode: reg(1),
            },
            Instruction::Halt,
        ];
        let module = single(func(2, code, Vec::new()));
        let lowered = lower_code_module(ModuleId::new(0), &module, host_config()).expect("lowers");
        let function = &lowered.functions[0];
        // Fresh token 0 plus the suspend at pc 1 -> token 2.
        assert_eq!(function.entry_points, vec![0, 2]);
        assert!(function.helpers.contains(&Helper::ResumeValue));
        assert_eq!(Helper::ResumeValue.external_index(), 13);
        assert!(function.helpers.contains(&Helper::ResumeMode));
        assert_eq!(Helper::ResumeMode.external_index(), 46);
        let clif = function.clif.display().to_string();
        // Multi-token dispatch loads and compares the resume token.
        assert!(
            clif.contains("load.i32"),
            "dispatch token load missing:\n{clif}"
        );
        assert!(clif.contains("icmp"), "dispatch compare missing:\n{clif}");
        // The suspend stores its resume token into the frame.
        assert!(
            clif.contains("store"),
            "resume token store missing:\n{clif}"
        );
        assert!(
            clif.contains("u1:13"),
            "resume helper import missing:\n{clif}"
        );
        assert!(
            clif.contains("u1:46"),
            "resume mode helper import missing:\n{clif}"
        );
    }

    #[test]
    fn await_shares_the_suspend_abi_with_a_distinct_resume_token() {
        // r0 = undef; suspend (yield r0) at pc 1 resuming at pc 2; await r0 at
        // pc 2 resuming at pc 3; pc 3 halts. Both suspensions are reachable,
        // each through the other's resume edge.
        let code = vec![
            load_undef(reg(0)),
            Instruction::Suspend {
                dst: reg(0),
                src: reg(0),
                resume: Pc::new(2),
                mode: reg(1),
            },
            Instruction::Await {
                dst: reg(0),
                src: reg(0),
                resume: Pc::new(3),
            },
            Instruction::Halt,
        ];
        let module = single(func(2, code, Vec::new()));
        let lowered = lower_code_module(ModuleId::new(0), &module, host_config()).expect("lowers");
        let function = &lowered.functions[0];
        // Fresh token 0, the suspend at pc 1 -> token 2, the await at pc 2 ->
        // token 3: distinct tokens across both suspension opcodes.
        assert_eq!(function.entry_points, vec![0, 2, 3]);
        assert!(function.helpers.contains(&Helper::ResumeValue));
        assert!(function.helpers.contains(&Helper::ResumeMode));
        assert_eq!(Helper::ResumeMode.external_index(), 46);
        let clif = function.clif.display().to_string();
        // Multi-token dispatch loads and compares the resume token.
        assert!(
            clif.contains("load.i32"),
            "dispatch token load missing:\n{clif}"
        );
        assert!(clif.contains("icmp"), "dispatch compare missing:\n{clif}");
        assert!(
            clif.contains("u1:13"),
            "resume helper import missing:\n{clif}"
        );
        assert!(
            clif.contains("u1:46"),
            "resume mode helper import missing:\n{clif}"
        );
    }
    #[test]
    fn suspend_resume_prologue_calls_resume_value_then_resume_mode() {
        // Load undefined into r0, then yield it via Suspend. r1 receives the
        // resume mode. The resume prologue must call ResumeValue before
        // ResumeMode and store both results into the destination registers.
        let code = vec![
            load_undef(reg(0)),
            Instruction::Suspend {
                dst: reg(0),
                src: reg(0),
                resume: Pc::new(2),
                mode: reg(1),
            },
            Instruction::Halt,
        ];
        let module = single(func(2, code, Vec::new()));
        let clif = lower_one(&module).1;
        let value_call = clif.find("u1:13").expect("ResumeValue call missing");
        let mode_call = clif.find("u1:46").expect("ResumeMode call missing");
        assert!(
            value_call < mode_call,
            "ResumeValue must be called before ResumeMode:\n{clif}"
        );
        assert!(clif.contains("store"), "resume stores missing:\n{clif}");
    }

    #[test]
    fn await_resume_prologue_uses_only_resume_value() {
        // Load undefined into r0, then await it. Await uses ResumeValue only.
        let code = vec![
            load_undef(reg(0)),
            Instruction::Await {
                dst: reg(0),
                src: reg(0),
                resume: Pc::new(2),
            },
            Instruction::Halt,
        ];
        let module = single(func(1, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::ResumeValue));
        assert!(!helpers.contains(&Helper::ResumeMode));
        assert!(
            clif.contains("u1:13"),
            "ResumeValue import missing:\n{clif}"
        );
        assert!(
            !clif.contains("u1:46"),
            "Await must not import ResumeMode:\n{clif}"
        );
    }

    #[test]
    fn throwing_op_under_a_handler_routes_and_binds_catch_register() {
        // handler covers [0,3), dispatches to pc 3 binding into r0.
        let code = vec![
            load_undef(reg(0)),
            load_undef(reg(1)),
            Instruction::Binary {
                dst: reg(2),
                op: BinaryOp::Add,
                left: reg(0),
                right: reg(1),
            },
            Instruction::Halt,
        ];
        let handlers = vec![ExceptionHandler {
            start: Pc::new(0),
            end: Pc::new(3),
            handler: Pc::new(3),
            catch_register: reg(0),
        }];
        let module = single(func(3, code, handlers));
        let clif = clif_of(&module);
        // Around the throwing Binary: normal-vs-abnormal, then throw-vs-propagate.
        let brif_count = clif.matches("brif").count();
        assert!(
            brif_count >= 2,
            "expected handler routing brifs, got {brif_count}:\n{clif}"
        );
        assert!(
            clif.contains("icmp"),
            "throw discriminator missing:\n{clif}"
        );
    }

    #[test]
    fn explicit_throw_binds_catch_register_and_jumps() {
        // r0 = undef; throw r0; handler at pc 2 binds into r0.
        let code = vec![
            load_undef(reg(0)),
            Instruction::Throw { value: reg(0) },
            Instruction::Halt,
        ];
        let handlers = vec![ExceptionHandler {
            start: Pc::new(0),
            end: Pc::new(2),
            handler: Pc::new(2),
            catch_register: reg(0),
        }];
        let module = single(func(1, code, handlers));
        let (helpers, clif) = lower_one(&module);
        // A locally-caught throw needs only its fuel helper and jumps to the handler.
        assert_eq!(helpers, vec![Helper::LoadConstant, Helper::ConsumeFuel]);
        assert!(clif.contains("jump"), "handler jump missing:\n{clif}");
        assert!(
            clif.contains("store"),
            "catch-register bind missing:\n{clif}"
        );
    }

    #[test]
    fn return_writes_completion_and_normal_tag() {
        let code = vec![load_undef(reg(0)), Instruction::Return { value: reg(0) }];
        let module = single(func(1, code, Vec::new()));
        let (helpers, clif) = lower_one(&module);
        assert_eq!(helpers, vec![Helper::LoadConstant, Helper::ConsumeFuel]);
        assert!(
            clif.contains("store"),
            "return value store missing:\n{clif}"
        );
        assert!(clif.contains("return"), "return missing:\n{clif}");
    }

    #[test]
    fn high_register_offsets_scale_past_127() {
        // A register id past 127 (r500) addresses at byte offset 500*8 = 4000,
        // a full 32-bit displacement, not a signed byte. LoadConst into r500
        // stores out.value at that offset.
        let code = vec![load_undef(reg(500)), Instruction::Halt];
        let module = single(func(501, code, Vec::new()));
        let (_, clif) = lower_one(&module);
        assert!(
            clif.contains("+4000"),
            "expected a +4000 byte offset for r500:\n{clif}"
        );
    }

    #[test]
    fn import_and_closure_are_lowered() {
        let code = vec![
            load_undef(reg(0)),
            Instruction::CreateClosure {
                dst: reg(1),
                function: FunctionId::new(0),
                captures: reg(0),
            },
            Instruction::Import {
                dst: reg(2),
                specifier: ConstantId::new(0),
            },
            Instruction::Halt,
        ];
        let module = verified(
            vec![Constant::String(EcmaString::encode("mod"))],
            vec![func(3, code, Vec::new())],
        );
        let (helpers, _) = lower_one(&module);
        assert!(helpers.contains(&Helper::CreateClosure));
        assert!(helpers.contains(&Helper::Import));
    }

    #[test]
    fn lowering_is_deterministic() {
        let code = vec![
            load_undef(reg(0)),
            Instruction::Binary {
                dst: reg(1),
                op: BinaryOp::Add,
                left: reg(0),
                right: reg(0),
            },
            Instruction::Jump { target: Pc::new(3) },
            Instruction::Halt,
        ];
        let make = || single(func(2, code.clone(), Vec::new()));
        let a = clif_of(&make());
        let b = clif_of(&make());
        assert_eq!(a, b);
    }

    #[test]
    fn unreachable_code_is_not_emitted() {
        // Jump over the Binary straight to Halt; the Binary is unreachable and
        // must not lower a helper.
        let code = vec![
            Instruction::Jump { target: Pc::new(2) },
            Instruction::Binary {
                dst: reg(0),
                op: BinaryOp::Add,
                left: reg(0),
                right: reg(0),
            },
            Instruction::Halt,
        ];
        let module = single(func(1, code, Vec::new()));
        let (helpers, _) = lower_one(&module);
        assert_eq!(
            helpers,
            vec![Helper::ConsumeFuel],
            "unreachable Binary must not lower its helper"
        );
    }

    #[test]
    fn multiple_functions_get_distinct_symbols() {
        let functions = vec![
            func(0, vec![Instruction::Halt], Vec::new()),
            func(0, vec![Instruction::Halt], Vec::new()),
        ];
        let module = verified(Vec::new(), functions);
        let lowered = lower_code_module(ModuleId::new(0), &module, host_config()).expect("lowers");
        assert_eq!(lowered.functions.len(), 2);
        assert_eq!(lowered.functions[0].symbol, "bamts_m0_fn_0");
        assert_eq!(lowered.functions[1].symbol, "bamts_m0_fn_1");
        let name0 = lowered.functions[0].clif.display().to_string();
        assert!(name0.contains("u0:0"), "function 0 name wrong:\n{name0}");
        let name1 = lowered.functions[1].clif.display().to_string();
        assert!(name1.contains("u0:1"), "function 1 name wrong:\n{name1}");
    }

    #[test]
    fn innermost_handler_prefers_the_tightest_interval() {
        let outer = ExceptionHandler {
            start: Pc::new(0),
            end: Pc::new(10),
            handler: Pc::new(20),
            catch_register: reg(0),
        };
        let inner = ExceptionHandler {
            start: Pc::new(2),
            end: Pc::new(6),
            handler: Pc::new(30),
            catch_register: reg(1),
        };
        let handlers = [outer, inner];
        assert_eq!(
            innermost_handler(&handlers, 4).map(|h| h.handler),
            Some(Pc::new(30))
        );
        assert_eq!(
            innermost_handler(&handlers, 8).map(|h| h.handler),
            Some(Pc::new(20))
        );
        assert_eq!(innermost_handler(&handlers, 10), None);
    }

    #[test]
    fn non_64_bit_targets_are_rejected() {
        let config = TargetFrontendConfig {
            default_call_conv: CallConv::SystemV,
            pointer_width: {
                let flags = Flags::new(settings::builder());
                match isa::lookup_by_name("i686")
                    .ok()
                    .and_then(|b| b.finish(flags).ok())
                {
                    Some(target) => target.frontend_config().pointer_width,
                    None => return, // no 32-bit ISA compiled in; nothing to test
                }
            },
            page_size_align_log2: 12,
        };
        let module = single(func(0, vec![Instruction::Halt], Vec::new()));
        let error =
            lower_code_module(ModuleId::new(0), &module, config).expect_err("32-bit rejected");
        assert!(matches!(
            error,
            LowerError::UnsupportedPointerWidth { bits: 32 }
        ));
    }

    #[test]
    fn error_display_is_stable() {
        let width = LowerError::UnsupportedPointerWidth { bits: 32 };
        assert!(width.to_string().contains("64-bit"));
        let many = LowerError::TooManyFunctions { count: 200 };
        assert!(many.to_string().contains("200"));
        let slots = LowerError::RegisterFileTooLarge {
            function: FunctionId::new(1),
            register_count: 9,
        };
        assert!(slots.to_string().contains("function 1"));
        let sig = LowerError::EntrySignatureMismatch {
            function: FunctionId::new(2),
        };
        assert!(sig.to_string().contains("function 2"));
        let ir = LowerError::IrVerification {
            function: FunctionId::new(3),
            message: "boom".to_string(),
        };
        let text = ir.to_string();
        assert!(text.contains("function 3"));
        assert!(text.contains("boom"));
    }

    #[test]
    fn constant_pool_does_not_perturb_lowering() {
        let functions = vec![BytecodeFunction::new(
            Some(ConstantId::new(0)),
            0,
            0,
            0,
            FunctionFlags::default(),
            vec![Instruction::Halt],
            Vec::new(),
        )];
        let module = Module::new(
            vec![Constant::String(EcmaString::encode("main"))],
            functions,
            FunctionId::new(0),
        )
        .verify()
        .expect("verifies");
        let lowered = lower_code_module(ModuleId::new(0), &module, host_config()).expect("lowers");
        assert_eq!(lowered.functions[0].symbol, "bamts_m0_fn_0");
    }
    #[test]
    fn program_lowering_retains_module_local_ids_and_entry_tuple() {
        let make_module = |name: &str| bamts_bytecode::ProgramModule {
            name: ConstantId::new(0),
            code: Module::new(
                vec![Constant::String(EcmaString::encode(name))],
                vec![func(0, vec![Instruction::Halt], Vec::new())],
                FunctionId::new(0),
            )
            .verify()
            .expect("module verifies"),
            edges: Vec::new(),
            bindings: Vec::new(),
            exports: Vec::new(),
        };
        let program = Program::link(
            vec![make_module("dependency"), make_module("entry")],
            ModuleId::new(1),
        )
        .expect("program verifies");

        let lowered = lower_program(&program, host_config()).expect("program lowers");
        assert_eq!(lowered.modules.len(), 2);
        assert_eq!(lowered.modules[0].id, ModuleId::new(0));
        assert_eq!(lowered.modules[1].id, ModuleId::new(1));
        assert_eq!(lowered.modules[0].functions[0].id, FunctionId::new(0));
        assert_eq!(lowered.modules[1].functions[0].id, FunctionId::new(0));
        assert_eq!(lowered.modules[0].functions[0].symbol, "bamts_m0_fn_0");
        assert_eq!(lowered.modules[1].functions[0].symbol, "bamts_m1_fn_0");
        assert_eq!(lowered.entry_module, ModuleId::new(1));
        assert_eq!(lowered.entry_function, FunctionId::new(0));
    }

    fn two_module_lowered() -> LoweredProgram {
        let make_module = |name: &str| bamts_bytecode::ProgramModule {
            name: ConstantId::new(0),
            code: Module::new(
                vec![Constant::String(EcmaString::encode(name))],
                vec![func(0, vec![Instruction::Halt], Vec::new())],
                FunctionId::new(0),
            )
            .verify()
            .expect("module verifies"),
            edges: Vec::new(),
            bindings: Vec::new(),
            exports: Vec::new(),
        };
        let program = Program::link(
            vec![make_module("dependency"), make_module("entry")],
            ModuleId::new(1),
        )
        .expect("program verifies");
        lower_program(&program, host_config()).expect("program lowers")
    }

    #[test]
    fn validate_lowered_program_accepts_canonical_order() {
        assert_eq!(
            validate_lowered_program(&two_module_lowered()).unwrap(),
            vec![(0, 0), (1, 0)]
        );
    }

    #[test]
    fn validate_lowered_program_rejects_module_identity_mismatch() {
        let mut lowered = two_module_lowered();
        lowered.modules[0].id = ModuleId::new(7);

        assert!(matches!(
            validate_lowered_program(&lowered),
            Err(LoweredProgramError::ModuleIndexMismatch { expected, found })
                if expected == 0 && found == 7
        ));
    }

    #[test]
    fn validate_lowered_program_rejects_function_identity_mismatch() {
        let mut lowered = two_module_lowered();
        lowered.modules[0].functions[0].id = FunctionId::new(3);

        assert!(matches!(
            validate_lowered_program(&lowered),
            Err(LoweredProgramError::FunctionIndexMismatch { module, expected, found })
                if module == 0 && expected == 0 && found == 3
        ));
    }

    #[test]
    fn load_import_meta_lowers_to_helper_38() {
        let module = single(func(
            1,
            vec![
                Instruction::LoadImportMeta { dst: reg(0) },
                Instruction::Halt,
            ],
            Vec::new(),
        ));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::LoadImportMeta));
        assert!(
            clif.contains("u1:38"),
            "load-import-meta import missing:\n{clif}"
        );
    }

    #[test]
    fn to_object_uses_the_pinned_throwing_helper_abi() {
        let module = single(func(
            2,
            vec![
                load_undef(reg(0)),
                Instruction::ToObject {
                    dst: reg(1),
                    src: reg(0),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        ));
        let (helpers, clif) = lower_one(&module);
        assert!(helpers.contains(&Helper::ToObject));
        assert_eq!(Helper::ToObject.external_index(), 36);
        assert!(clif.contains("u1:36"), "ToObject import missing:\n{clif}");
        assert!(
            clif.contains("(i64, i64, i64) -> i32"),
            "ToObject helper ABI wrong:\n{clif}"
        );
    }

    #[test]
    fn pre_cancelled_token_aborts_lower_program() {
        let module = verified(
            vec![Constant::String(EcmaString::encode("<test>"))],
            vec![func(1, vec![Instruction::Halt], Vec::new())],
        );
        let program = Program::link(
            vec![bamts_bytecode::ProgramModule {
                name: ConstantId::new(0),
                code: module,
                edges: Vec::new(),
                bindings: Vec::new(),
                exports: Vec::new(),
            }],
            ModuleId::new(0),
        )
        .expect("program verifies");
        let cancel = CancellationToken::new();
        cancel.cancel();
        let result = lower_program_with_cancel(&program, host_config(), &cancel);
        assert!(matches!(
            result,
            Err(ProgramLowerError {
                kind: LowerError::Cancelled,
                ..
            })
        ));
    }
}
