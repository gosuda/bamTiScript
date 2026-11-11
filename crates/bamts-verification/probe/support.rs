//! Freestanding support linked with the target-cell probe object.
//!
//! This is the whole runtime of a target-cell image: the two helpers the probe
//! calls, and an entry point that runs it and turns what it saw into an exit
//! status. `toolchain measure` compiles it for the target; cargo never sees it.
//! `@INT32_42@` is replaced with the boxed value of the measuring build.

#![no_std]

const INT32_42: u64 = @INT32_42@;

const NORMAL: u32 = 0;
const FATAL_TRAP: u32 = 3;

/// Layout of `bamts_native::ShadowFrame`.
#[repr(C)]
pub struct ShadowFrame {
    previous: *mut ShadowFrame,
    bytecode_pc: u32,
    module_id: u32,
    handles: *mut u64,
    handle_len: u16,
    padding: [u8; 6],
}

static mut FUEL: u64 = 0;

unsafe extern "C" {
    fn bamts_m0_fn_0(frame: *mut ShadowFrame, out: *mut u64) -> u32;
}

/// # Safety
///
/// `out` must be writable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bamts_load_constant(
    _frame: *mut ShadowFrame,
    constant: u32,
    out: *mut u64,
) -> u32 {
    if constant != 1 {
        return FATAL_TRAP;
    }
    unsafe { out.write(INT32_42) };
    NORMAL
}

/// # Safety
///
/// Called only from the single thread `bamts_probe_run` runs on.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bamts_consume_fuel(
    _frame: *mut ShadowFrame,
    amount: u32,
    _out: *mut u64,
) -> u32 {
    unsafe { FUEL = FUEL.wrapping_add(u64::from(amount)) };
    NORMAL
}

/// Runs the probe. Zero means it returned `int32:42` and charged fuel.
///
/// # Safety
///
/// Called once, on a single thread, from the image's entry point.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bamts_probe_run() -> i32 {
    let mut register = 0u64;
    let mut out = 0u64;
    let mut frame = ShadowFrame {
        previous: core::ptr::null_mut(),
        bytecode_pc: 0,
        module_id: 0,
        handles: &raw mut register,
        handle_len: 1,
        padding: [0; 6],
    };
    let tag = unsafe { bamts_m0_fn_0(&raw mut frame, &raw mut out) };
    if tag != NORMAL {
        10
    } else if out != INT32_42 {
        11
    } else if unsafe { FUEL } == 0 {
        12
    } else {
        0
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
core::arch::global_asm!(
    ".globl _start",
    "_start:",
    "xor ebp, ebp",
    "and rsp, -16",
    "call bamts_probe_run",
    "mov edi, eax",
    "mov eax, 231",
    "syscall",
);

#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
core::arch::global_asm!(
    ".globl _start",
    "_start:",
    "bl bamts_probe_run",
    "mov x8, #94",
    "svc #0",
);

#[cfg(all(target_os = "linux", target_arch = "riscv64"))]
core::arch::global_asm!(
    ".globl _start",
    "_start:",
    "call bamts_probe_run",
    "li a7, 94",
    "ecall",
);

#[cfg(all(target_os = "linux", target_arch = "s390x"))]
core::arch::global_asm!(
    ".globl _start",
    "_start:",
    "aghi %r15, -160",
    "brasl %r14, bamts_probe_run",
    "svc 248",
);

#[cfg(not(target_os = "linux"))]
#[unsafe(no_mangle)]
pub extern "C" fn main() -> i32 {
    unsafe { bamts_probe_run() }
}
