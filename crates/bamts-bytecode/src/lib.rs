//! Production BamTS bytecode: a verified instruction set, strict codec, and
//! definite-initialization verifier with an unforgeable `Verified` typestate.
//!
//! # Relation to the formal five-op core
//!
//! The proven structural core in `formal/lean/Bamti/Bytecode/Model.lean`
//! (`Load`, `Add`, `Jump`, `Suspend`, `Halt`) is preserved exactly as a
//! *subset* of this ISA:
//!
//! * `Load`    -> [`Instruction::LoadConst`] (now names the loaded constant).
//! * `Add`     -> [`Instruction::Binary`] with [`BinaryOp::Add`] (generalized
//!   to the full closed operator algebra).
//! * `Jump`    -> [`Instruction::Jump`] (identical control transfer).
//! * `Suspend` -> [`Instruction::Suspend`] (refined with an out register for
//!   the resumed value and an in register for the yielded value).
//! * `Halt`    -> [`Instruction::Halt`] (identical terminator).
//!
//! Every additional opcode *extends* that core. The verifier here mirrors the
//! *structure* proven in `Bytecode/Verify.lean` -- a real entry, valid CFG
//! targets, nested (non-partially-overlapping) handlers, and a syntactic
//! definite-initialization witness across CFG joins -- before the `Verified`
//! typestate can be constructed. Number constants use `Bamti.canonical_nan`,
//! and persisted constants carry no heap or runtime identity, matching
//! `no_serialized_runtime_identity`.
//!
//! # Dynamic-computation ISA
//!
//! Unlike a fixed-key/fixed-window shape, this ISA expresses the *dynamic*
//! runtime kernel of the corpus without special-casing syntax:
//!
//! * **Property access is register-keyed.** [`Instruction::GetProperty`],
//!   [`Instruction::SetProperty`], and [`Instruction::DeleteProperty`] take the
//!   key in a `Register`, so computed access (`obj[e]`), string/number keys,
//!   `Symbol` keys, and private names (via [`Instruction::CreatePrivateName`])
//!   are one uniform operation. [`Instruction::DefineAccessor`] installs a
//!   getter or setter descriptor under a register key.
//!   [`Instruction::LoadOwnDescriptorSlot`] /
//!   [`Instruction::DefineOwnDescriptorSlot`] address one own-descriptor slot
//!   (`value` / `get` / `set`) without invoking accessors or walking the
//!   prototype chain.
//! * **Calls are variadic.** [`Instruction::Call`],
//!   [`Instruction::Construct`], and [`Instruction::ConstructWithNewTarget`]
//!   receive one *arguments-array* `Register`, so
//!   spread (`f(...xs)`) and any arity -- far beyond 127 -- lower identically.
//!   The runtime validates that the register holds a dynamic array.
//! * **Closures capture explicitly.** [`Instruction::CreateClosure`] binds a
//!   function together with a *captures-array* `Register`. On entry, a callee's
//!   leading [`Function::capture_count`] registers are the captured cells,
//!   followed by its [`Function::parameter_count`] parameters; both count as
//!   definitely initialized on entry.
//! * **Aggregate building blocks.** [`Instruction::ArrayPush`],
//!   [`Instruction::ArrayExtend`] (iterable spread), [`Instruction::ObjectSpread`],
//!   and [`Instruction::SetPrototype`] build non-empty arrays, objects, and
//!   class prototype chains incrementally.
//! * **Iteration protocol.** [`Instruction::GetIterator`] (with a closed
//!   [`IteratorKind`]) and the two-write [`Instruction::IteratorNext`] model
//!   `for`/`of`, `for`/`in`, destructuring, and array/call spread against the
//!   ECMAScript iterator protocol. The two-write
//!   [`Instruction::IteratorClose`] performs the abrupt-completion close step.
//!   `for`/`await`/`of` splits each step across
//!   [`Instruction::IteratorStep`] (acquire the raw, possibly-promised iterator
//!   result), [`Instruction::Await`] (suspend until it settles), and the
//!   two-write [`Instruction::IteratorResult`] (validate the settled object and
//!   read `done`/`value`). [`Instruction::RequireCloseResult`] validates the
//!   result of a callable `iterator.return` on non-throw exits.
//! * **Environment access.** [`Instruction::LoadGlobal`],
//!   [`Instruction::StoreGlobal`], [`Instruction::TypeOfGlobal`] (the last
//!   models `typeof g` without throwing on an undeclared global),
//!   [`Instruction::LoadThis`], [`Instruction::LoadArguments`], and
//!   [`Instruction::LoadNewTarget`] name the ambient bindings a function body
//!   observes.
//! * **Modules.** [`Instruction::Import`] is dynamic and names a dependency by
//!   string constant; static bindings and exports live in [`Program`] linkage
//!   metadata so they identify live cells rather than activation registers.
//! * **Regular expressions.** [`Instruction::CreateRegExp`] materializes a
//!   `RegExp` from string-constant pattern and flags.
//!
//! ## Resume contract (async / generators)
//!
//! [`Instruction::Suspend`] carries `{ dst, src, resume, mode }` for generator
//! `yield`, while [`Instruction::Await`] retains `{ dst, src, resume }` for an
//! awaited operand. Both suspension primitives have the same single-successor
//! CFG shape, but only a generator suspension receives an engine-written resume
//! completion mode. [`FunctionFlags::is_async`] and
//! [`FunctionFlags::is_generator`] select *how* a suspension is driven:
//!
//! 1. The activation yields the value in `src` (a produced item for a
//!    generator `yield`; an awaited operand for `await`) to its driver.
//! 2. When the driver resumes the activation, control continues at `resume`
//!    with the resumed value written to `dst`. A generator suspension also
//!    receives [`RESUME_NEXT`], [`RESUME_THROW`], or [`RESUME_RETURN`] in
//!    `mode`; the compiler dispatches that completion inside the suspended
//!    body's protected ranges.
//! 3. `resume` is the only CFG successor of either suspension opcode, so the
//!    definite-initialization witness treats every register live across a
//!    suspension as it would across any join: `dst` (and `mode` for `Suspend`)
//!    is initialized on the resume edge, and registers not provably initialized
//!    before the suspension are not assumed initialized after it.
//!
//! A generator's completion is an ordinary [`Instruction::Return`]; an uncaught
//! throw during drive routes to an enclosing [`ExceptionHandler`] exactly as in
//! synchronous code.
//!
//! The wire format is a deliberate superset departure from the formal single
//! seven-bit-group encoding: integer fields are canonical unsigned LEB128 `u32`
//! (functions and modules may exceed 127 instructions, constants, registers,
//! captures, and arguments), bounded by explicit decode and structural resource
//! limits. Its round-trip guarantees -- totality over hostile bytes, canonical
//! re-encoding, and decode/encode identity -- are fresh properties of this
//! codec, proven by the tests in this module, not the Lean single-byte theorems
//! (`decode_total`, `decode_encode_canonical`, `encode_decode_identity`), which
//! remain scoped to the formal five-op wire.

#![forbid(unsafe_code)]

use std::error::Error;
use std::fmt;
use std::marker::PhantomData;

/// `BMTBC\0\0\1`, matching `Bamti.Bytecode.magicBytes`.
pub const MAGIC: [u8; 8] = [66, 77, 84, 66, 67, 0, 0, 1];
/// The sole supported wire version.
pub const FORMAT_VERSION: u8 = 5;

/// Structural verify-time ceiling on a function's register count. Generous
/// enough for real code yet bounds definite-initialization bitset allocation.
pub const MAX_REGISTERS: u32 = 1 << 16;
/// Structural verify-time ceiling on a function's instruction count.
pub const MAX_INSTRUCTIONS: u32 = 1 << 20;
/// Structural verify-time ceiling on a function's handler count.
pub const MAX_HANDLERS: u32 = 1 << 16;
/// Structural verify-time ceiling on a module's constant count.
pub const MAX_CONSTANTS: u32 = 1 << 20;
/// Structural verify-time ceiling on a module's function count.
pub const MAX_FUNCTIONS: u32 = 1 << 20;
/// Canonical decoder ceiling for one BigInt constant's decimal text.
pub const MAX_BIGINT_BYTES: u32 = 1 << 20;

/// Combined verify-time ceiling on the total definite-initialization fact
/// storage a module may force the verifier to allocate, in 64-bit words. Each
/// function needs `instructions * ceil(registers / 64)` words, so independent
/// per-function maxima (`MAX_INSTRUCTIONS * (MAX_REGISTERS / 64)` alone is
/// 2^30 words = 8 GiB, and modules hold many functions) would permit multi-GiB
/// allocations from untrusted input. This bound caps that transient storage at
/// `MAX_VERIFIER_FACTS_WORDS * 8` bytes (64 MiB) while remaining generous
/// enough for large real modules with far more than 127 functions.
pub const MAX_VERIFIER_FACTS_WORDS: u64 = 1 << 23;

const CANONICAL_NAN_BITS: u64 = 0x7ff8_0000_0000_0000;
const EXPONENT_MASK: u64 = 0x7ff0_0000_0000_0000;
const FRACTION_MASK: u64 = 0x000f_ffff_ffff_ffff;

macro_rules! index_type {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        #[repr(transparent)]
        pub struct $name(u32);

        impl $name {
            #[must_use]
            pub const fn new(raw: u32) -> Self {
                Self(raw)
            }

            #[must_use]
            pub const fn get(self) -> u32 {
                self.0
            }
        }
    };
}

index_type!(
    /// Index of a virtual register within a function's register file.
    Register
);
index_type!(
    /// Index into a module's constant pool.
    ConstantId
);
index_type!(
    /// Index into a module's function table.
    FunctionId
);
index_type!(
    /// A program counter: an instruction index within a function's code.
    Pc
);

mod string;

mod isa;
mod program;
mod verifier;

pub use string::{EcmaString, EcmaStringBuilder, IllFormedUtf16, InvalidCodePoint};

pub use program::{
    Binding, BindingId, BindingKind, Edge, EdgeId, EdgeKind, EdgeTarget, Export, ExportSource,
    ModuleId, PROGRAM_MAGIC, PROGRAM_VERSION, Program, ProgramDecodeError, ProgramDecodeErrorKind,
    ProgramDecodeLimits, ProgramLoadError, ProgramModule, ProgramVerifyError,
    ProgramVerifyErrorKind, ResolvedExport, decode_program, decode_verified_program,
};

/// Formats one IEEE-754 number with ECMAScript `Number::toString` semantics.
#[must_use]
pub fn format_number(number: f64) -> String {
    if number.is_nan() {
        return "NaN".to_owned();
    }
    if number == f64::INFINITY {
        return "Infinity".to_owned();
    }
    if number == f64::NEG_INFINITY {
        return "-Infinity".to_owned();
    }
    if number == 0.0 {
        return "0".to_owned();
    }

    let negative = number.is_sign_negative();
    let raw = number.abs().to_string();
    let (mantissa, explicit_exponent) = match raw.split_once(['e', 'E']) {
        Some((mantissa, exponent)) => (
            mantissa,
            exponent
                .parse::<i32>()
                .expect("Rust formats finite f64 exponents as i32"),
        ),
        None => (raw.as_str(), 0),
    };
    let decimal = mantissa.find('.').unwrap_or(mantissa.len());
    let untrimmed: String = mantissa.chars().filter(|ch| *ch != '.').collect();
    let first = untrimmed
        .find(|ch| ch != '0')
        .expect("a nonzero number has a nonzero decimal digit");
    let digits = untrimmed[first..].trim_end_matches('0');
    let exponent = explicit_exponent + decimal as i32 - first as i32 - 1;

    let mut result = String::new();
    if negative {
        result.push('-');
    }
    if !(-6..21).contains(&exponent) {
        result.push(digits.as_bytes()[0] as char);
        if digits.len() > 1 {
            result.push('.');
            result.push_str(&digits[1..]);
        }
        result.push('e');
        if exponent >= 0 {
            result.push('+');
        }
        result.push_str(&exponent.to_string());
    } else if exponent >= 0 {
        let integer_digits = exponent as usize + 1;
        if digits.len() <= integer_digits {
            result.push_str(digits);
            result.extend(std::iter::repeat_n('0', integer_digits - digits.len()));
        } else {
            result.push_str(&digits[..integer_digits]);
            result.push('.');
            result.push_str(&digits[integer_digits..]);
        }
    } else {
        result.push_str("0.");
        result.extend(std::iter::repeat_n('0', (-exponent - 1) as usize));
        result.push_str(digits);
    }
    result
}

/// Canonical IEEE-754 bits. Every positive or negative NaN payload collapses
/// to the unique arithmetic NaN from `Bamti.canonical_nan`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct NumberBits(u64);

impl NumberBits {
    #[must_use]
    pub const fn from_bits(bits: u64) -> Self {
        if is_nan(bits) {
            Self(CANONICAL_NAN_BITS)
        } else {
            Self(bits)
        }
    }

    #[must_use]
    pub const fn from_f64(value: f64) -> Self {
        Self::from_bits(value.to_bits())
    }

    #[must_use]
    pub const fn bits(self) -> u64 {
        self.0
    }

    #[must_use]
    pub const fn to_f64(self) -> f64 {
        f64::from_bits(self.0)
    }

    const fn from_wire(bits: u64) -> Option<Self> {
        if is_nan(bits) && bits != CANONICAL_NAN_BITS {
            None
        } else {
            Some(Self(bits))
        }
    }
}

const fn is_nan(bits: u64) -> bool {
    bits & EXPONENT_MASK == EXPONENT_MASK && bits & FRACTION_MASK != 0
}

/// A canonical BigInt literal in decimal text form. Constructed only through
/// [`BigIntLiteral::new`], so a `BigIntLiteral` value is *always* a canonical
/// decimal integer: optional leading `-`, no redundant leading zeros, no `-0`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct BigIntLiteral(String);

impl BigIntLiteral {
    /// Parses canonical decimal text, rejecting empty text, non-digits,
    /// redundant leading zeros, a bare sign, and negative zero.
    #[must_use]
    pub fn new(text: String) -> Option<Self> {
        if is_canonical_bigint(&text) {
            Some(Self(text))
        } else {
            None
        }
    }

    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

fn is_canonical_bigint(text: &str) -> bool {
    let bytes = text.as_bytes();
    if bytes.is_empty() {
        return false;
    }
    let negative = bytes[0] == b'-';
    let digits = if negative { &bytes[1..] } else { bytes };
    if digits.is_empty() || !digits.iter().all(u8::is_ascii_digit) {
        return false;
    }
    // No redundant leading zero (e.g. "007", "00").
    if digits.len() > 1 && digits[0] == b'0' {
        return false;
    }
    // No "-0".
    !(negative && digits == b"0")
}

/// Persistable values. Heap references, holes, and uninitialized sentinels are
/// intentionally absent because they are runtime identities/states. String
/// constants back property keys, global names, private-name descriptions,
/// regular-expression pattern/flags, module specifiers, and export names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Constant {
    Number(NumberBits),
    Int32(i32),
    String(EcmaString),
    Boolean(bool),
    Null,
    Undefined,
    BigInt(BigIntLiteral),
}

/// Closed set of unary operators.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum UnaryOp {
    Void,
    TypeOf,
    Plus,
    Negate,
    BitwiseNot,
    LogicalNot,
    /// ECMAScript `ToString`, which a template literal applies to a substitution.
    ToString,
    /// ECMAScript `ToPropertyKey`, applied once to a key that is both read and
    /// written. A primitive stays as it is, since it converts the same way each
    /// time; only an object runs user code.
    ToPropertyKey,
}

impl UnaryOp {
    const fn to_u8(self) -> u8 {
        match self {
            Self::Void => 0,
            Self::TypeOf => 1,
            Self::Plus => 2,
            Self::Negate => 3,
            Self::BitwiseNot => 4,
            Self::LogicalNot => 5,
            Self::ToString => 6,
            Self::ToPropertyKey => 7,
        }
    }

    const fn from_u8(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::Void),
            1 => Some(Self::TypeOf),
            2 => Some(Self::Plus),
            3 => Some(Self::Negate),
            4 => Some(Self::BitwiseNot),
            5 => Some(Self::LogicalNot),
            6 => Some(Self::ToString),
            7 => Some(Self::ToPropertyKey),
            _ => None,
        }
    }
}

/// Closed set of binary operators. [`BinaryOp::Add`] is the formal core's `Add`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    Exponent,
    BitAnd,
    BitOr,
    BitXor,
    ShiftLeft,
    ShiftRight,
    UnsignedShiftRight,
    Equal,
    NotEqual,
    StrictEqual,
    StrictNotEqual,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    InstanceOf,
    In,
}

impl BinaryOp {
    const fn to_u8(self) -> u8 {
        match self {
            Self::Add => 0,
            Self::Subtract => 1,
            Self::Multiply => 2,
            Self::Divide => 3,
            Self::Remainder => 4,
            Self::Exponent => 5,
            Self::BitAnd => 6,
            Self::BitOr => 7,
            Self::BitXor => 8,
            Self::ShiftLeft => 9,
            Self::ShiftRight => 10,
            Self::UnsignedShiftRight => 11,
            Self::Equal => 12,
            Self::NotEqual => 13,
            Self::StrictEqual => 14,
            Self::StrictNotEqual => 15,
            Self::LessThan => 16,
            Self::LessThanOrEqual => 17,
            Self::GreaterThan => 18,
            Self::GreaterThanOrEqual => 19,
            Self::InstanceOf => 20,
            Self::In => 21,
        }
    }

    const fn from_u8(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::Add),
            1 => Some(Self::Subtract),
            2 => Some(Self::Multiply),
            3 => Some(Self::Divide),
            4 => Some(Self::Remainder),
            5 => Some(Self::Exponent),
            6 => Some(Self::BitAnd),
            7 => Some(Self::BitOr),
            8 => Some(Self::BitXor),
            9 => Some(Self::ShiftLeft),
            10 => Some(Self::ShiftRight),
            11 => Some(Self::UnsignedShiftRight),
            12 => Some(Self::Equal),
            13 => Some(Self::NotEqual),
            14 => Some(Self::StrictEqual),
            15 => Some(Self::StrictNotEqual),
            16 => Some(Self::LessThan),
            17 => Some(Self::LessThanOrEqual),
            18 => Some(Self::GreaterThan),
            19 => Some(Self::GreaterThanOrEqual),
            20 => Some(Self::InstanceOf),
            21 => Some(Self::In),
            _ => None,
        }
    }
}

/// Closed set of iterator acquisition protocols for [`Instruction::GetIterator`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum IteratorKind {
    /// `Symbol.iterator` (`for`/`of`, array/call spread, destructuring).
    Sync,
    /// `Symbol.asyncIterator` (`for`/`await`/`of`).
    Async,
    /// Enumerable string keys (`for`/`in`).
    Keys,
}

impl IteratorKind {
    const fn to_u8(self) -> u8 {
        match self {
            Self::Sync => 0,
            Self::Async => 1,
            Self::Keys => 2,
        }
    }

    const fn from_u8(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::Sync),
            1 => Some(Self::Async),
            2 => Some(Self::Keys),
            _ => None,
        }
    }
}

/// Error handling policy for [`Instruction::IteratorClose`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum IteratorCloseMode {
    /// Surface a close failure as the current throw completion.
    Propagate,
    /// Preserve an existing abrupt completion over a user close failure.
    PreserveAbrupt,
}

impl IteratorCloseMode {
    const fn to_u8(self) -> u8 {
        match self {
            Self::Propagate => 0,
            Self::PreserveAbrupt => 1,
        }
    }

    const fn from_u8(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::Propagate),
            1 => Some(Self::PreserveAbrupt),
            _ => None,
        }
    }
}

/// Hint selecting the well-known disposal method [`Instruction::DisposeCapture`] records.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DisposeHint {
    /// Require a callable `Symbol.dispose` method.
    Sync,
    /// Prefer `Symbol.asyncDispose`, falling back to `Symbol.dispose`.
    Async,
}

impl DisposeHint {
    const fn to_u8(self) -> u8 {
        match self {
            Self::Sync => 0,
            Self::Async => 1,
        }
    }

    const fn from_u8(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::Sync),
            1 => Some(Self::Async),
            _ => None,
        }
    }
}

/// Which half of an accessor descriptor [`Instruction::DefineAccessor`] installs.
/// A property with both a getter and a setter is defined by two instructions on
/// the same key.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum AccessorKind {
    Getter,
    Setter,
    /// A [`Self::Getter`] on a class, whose accessors are not enumerable.
    ClassGetter,
    /// A [`Self::Setter`] on a class, whose accessors are not enumerable.
    ClassSetter,
}

impl AccessorKind {
    const fn to_u8(self) -> u8 {
        match self {
            Self::Getter => 0,
            Self::Setter => 1,
            Self::ClassGetter => 2,
            Self::ClassSetter => 3,
        }
    }

    const fn from_u8(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::Getter),
            1 => Some(Self::Setter),
            2 => Some(Self::ClassGetter),
            3 => Some(Self::ClassSetter),
            _ => None,
        }
    }

    /// Whether this installs the getter half of the descriptor.
    #[must_use]
    pub const fn is_getter(self) -> bool {
        matches!(self, Self::Getter | Self::ClassGetter)
    }

    /// Whether a property this creates is enumerable.
    #[must_use]
    pub const fn is_enumerable(self) -> bool {
        matches!(self, Self::Getter | Self::Setter)
    }
}

/// Which own-property descriptor slot
/// [`Instruction::LoadOwnDescriptorSlot`] /
/// [`Instruction::DefineOwnDescriptorSlot`] addresses.
///
/// Wire tags are `0` = value, `1` = getter, `2` = setter, `3` = entire. These
/// opcodes never invoke accessors and never walk the prototype chain.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DescriptorSlot {
    Value,
    Getter,
    Setter,
    /// The whole property, replaced by a writable, enumerable, configurable
    /// data property: ECMAScript `CreateDataProperty`. It reads as `undefined`.
    Entire,
}

impl DescriptorSlot {
    const fn to_u8(self) -> u8 {
        match self {
            Self::Value => 0,
            Self::Getter => 1,
            Self::Setter => 2,
            Self::Entire => 3,
        }
    }

    const fn from_u8(tag: u8) -> Option<Self> {
        match tag {
            0 => Some(Self::Value),
            1 => Some(Self::Getter),
            2 => Some(Self::Setter),
            3 => Some(Self::Entire),
            _ => None,
        }
    }
}

/// The realm intrinsic error constructor [`Instruction::ThrowIntrinsicError`]
/// throws. The thrown object takes the realm's own prototype, never the
/// value of the mutable global binding of the same name.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum IntrinsicErrorKind {
    TypeError,
    ReferenceError,
}

impl IntrinsicErrorKind {
    /// The intrinsic constructor's name.
    #[must_use]
    pub const fn constructor_name(self) -> &'static str {
        match self {
            Self::TypeError => "TypeError",
            Self::ReferenceError => "ReferenceError",
        }
    }

    /// The stable selector used on the wire and across the native helper ABI.
    #[must_use]
    pub const fn selector(self) -> u32 {
        match self {
            Self::TypeError => 0,
            Self::ReferenceError => 1,
        }
    }

    /// Inverts [`Self::selector`]; `None` for an unknown selector.
    #[must_use]
    pub const fn from_selector(selector: u32) -> Option<Self> {
        match selector {
            0 => Some(Self::TypeError),
            1 => Some(Self::ReferenceError),
            _ => None,
        }
    }
}

/// Normal generator resumption (`Generator.prototype.next`).
pub const RESUME_NEXT: i32 = 0;
/// Abrupt throw resumption (`Generator.prototype.throw`).
pub const RESUME_THROW: i32 = 1;
/// Abrupt return resumption (`Generator.prototype.return`).
pub const RESUME_RETURN: i32 = 2;

/// The production instruction algebra. Existing opcodes 0..=50 retain stable
/// wire tags; later instructions append new tags without reinterpreting them.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Instruction {
    /// Load a constant into `dst` (refines the formal `Load`).
    LoadConst { dst: Register, constant: ConstantId },
    /// Copy `src` into `dst`.
    Move { dst: Register, src: Register },
    /// Apply a unary operator to `operand`, writing `dst`.
    Unary {
        dst: Register,
        op: UnaryOp,
        operand: Register,
    },
    /// Apply a binary operator (generalizes the formal `Add`), writing `dst`.
    Binary {
        dst: Register,
        op: BinaryOp,
        left: Register,
        right: Register,
    },
    /// Create a fresh empty object in `dst`.
    CreateObject { dst: Register },
    /// Apply ECMAScript `ToObject` to `src`, writing the object to `dst`.
    ///
    /// Null and undefined throw; objects preserve identity; primitives receive
    /// their corresponding wrapper object. This is append-only wire tag 42.
    ToObject { dst: Register, src: Register },
    /// Load the current module's stable host-provided `import.meta` object.
    ///
    /// This is append-only wire tag 44 and has no static-edge operand.
    LoadImportMeta { dst: Register },
    /// Create a fresh empty array in `dst`.
    CreateArray { dst: Register },
    /// Create a compiler-private one-element array cell seeded with the
    /// runtime-only uninitialized sentinel.
    CreateCell { dst: Register },
    /// Materialize a closure over `function`, binding the captured cells held in
    /// the array register `captures`, into `dst`. The captured cells initialize
    /// the callee's leading `capture_count` registers.
    CreateClosure {
        dst: Register,
        function: FunctionId,
        captures: Register,
    },
    /// `dst = object[key]`, with the property key taken from a register.
    GetProperty {
        dst: Register,
        object: Register,
        key: Register,
    },
    /// `object[key] = value`, with the property key taken from a register.
    SetProperty {
        object: Register,
        key: Register,
        value: Register,
    },
    /// `dst = delete object[key]`, with the property key taken from a register.
    DeleteProperty {
        dst: Register,
        object: Register,
        key: Register,
    },
    /// Install a getter or setter `accessor` under `key` on `object`.
    DefineAccessor {
        object: Register,
        key: Register,
        accessor: Register,
        kind: AccessorKind,
    },
    /// Define `object[key]` as a data property with value from a register.
    DefineDataProperty {
        object: Register,
        key: Register,
        value: Register,
    },
    /// Read one own-descriptor slot of `object[key]` into `dst`.
    ///
    /// Own-only and non-invoking: never runs a getter and never walks the
    /// prototype chain. Absent properties and mismatched descriptor shapes
    /// yield `undefined` in `dst`. Append-only wire tag 49.
    LoadOwnDescriptorSlot {
        dst: Register,
        object: Register,
        key: Register,
        slot: DescriptorSlot,
    },
    /// Write `src` into one own-descriptor slot of `object[key]`.
    ///
    /// Mutates the addressed slot in place, preserving the sibling accessor
    /// half and the writable/enumerable/configurable bits. A descriptor-shape
    /// mismatch is a runtime `TypeError`. Append-only wire tag 50.
    DefineOwnDescriptorSlot {
        object: Register,
        key: Register,
        src: Register,
        slot: DescriptorSlot,
    },
    /// `dst = HasBinding(object, key)` for a `with` object environment record.
    ///
    /// Converts `key` to a property key, tests `HasProperty`, then consults
    /// `object[@@unscopables]` via the realm intrinsic. Append-only wire tag 51.
    WithHasBinding {
        dst: Register,
        object: Register,
        key: Register,
    },
    /// Call `callee` with receiver `this_value` and the dynamic argument array
    /// in `arguments`, writing the result to `dst`. Spread and any arity lower
    /// through the single arguments array.
    Call {
        dst: Register,
        callee: Register,
        this_value: Register,
        arguments: Register,
    },
    /// Construct with `callee` and the dynamic argument array in `arguments`,
    /// writing the instance to `dst`.
    Construct {
        dst: Register,
        callee: Register,
        arguments: Register,
    },
    /// Construct with `callee`, an explicit `new.target` in `new_target`, and
    /// the dynamic argument array in `arguments`, writing the instance to `dst`.
    ///
    /// Operand order on the wire is `dst`, `callee`, `new_target`, `arguments`.
    /// This is append-only wire tag 47.
    ConstructWithNewTarget {
        dst: Register,
        callee: Register,
        new_target: Register,
        arguments: Register,
    },
    /// `dst = globalThis[name]`, where `name` is a string constant. Throws a
    /// `ReferenceError` at runtime for an undeclared global.
    LoadGlobal { dst: Register, name: ConstantId },
    /// `globalThis[name] = value`, where `name` is a string constant.
    StoreGlobal { name: ConstantId, value: Register },
    /// `dst = typeof globalThis[name]`, where `name` is a string constant.
    /// Yields `"undefined"` for an undeclared global rather than throwing.
    TypeOfGlobal { dst: Register, name: ConstantId },
    /// Load the receiver binding `this` into `dst`.
    LoadThis { dst: Register },
    /// Load the `arguments` exotic object into `dst`.
    LoadArguments { dst: Register },
    /// Load `new.target` into `dst`.
    LoadNewTarget { dst: Register },
    /// Append `value` to the array in `array`.
    ArrayPush { array: Register, value: Register },
    /// Spread every element of `iterable` onto the end of the array in `array`.
    ArrayExtend { array: Register, iterable: Register },
    /// Copy the own enumerable properties of `source` onto `target`
    /// (`{ ...source }`).
    ObjectSpread { target: Register, source: Register },
    /// Set the `[[Prototype]]` of `object` to `prototype`.
    SetPrototype {
        object: Register,
        prototype: Register,
    },
    /// Create a fresh private name described by the string constant
    /// `description`, writing it to `dst`. The result is used as a register key
    /// for private-field access via the property instructions.
    CreatePrivateName {
        dst: Register,
        description: ConstantId,
    },
    /// Create a `RegExp` from the string-constant `pattern` and `flags`.
    CreateRegExp {
        dst: Register,
        pattern: ConstantId,
        flags: ConstantId,
    },
    /// Acquire an iterator over `src` using protocol `kind`, writing it to `dst`.
    GetIterator {
        dst: Register,
        src: Register,
        kind: IteratorKind,
    },
    /// Advance `iterator` one step: write whether iteration is done to `done`
    /// and the produced value to `value` (two writes).
    IteratorNext {
        done: Register,
        value: Register,
        iterator: Register,
    },
    /// Advance `iterator` one step, writing the raw iterator result -- the
    /// object its `next` method returns, possibly a promise for an async
    /// iterator -- to `dst`. `for await` splits the step this way so it can
    /// suspend on the raw result with [`Instruction::Await`] before reading
    /// `done`/`value` via [`Instruction::IteratorResult`].
    IteratorStep { dst: Register, iterator: Register },
    /// Validate the iterator result object in `result`: write whether
    /// iteration is done to `done` and the produced value to `value` (two
    /// writes), exactly as [`Instruction::IteratorNext`] reports them.
    IteratorResult {
        done: Register,
        value: Register,
        result: Register,
    },
    /// Call `iterator.return`, writing its raw result to `result` and a boolean
    /// to `called` that is true exactly when a callable return method was invoked.
    ///
    /// [`IteratorCloseMode::Propagate`] surfaces a close failure as a throw.
    /// [`IteratorCloseMode::PreserveAbrupt`] swallows a user close throw and
    /// writes `undefined`; engine failures remain fatal.
    IteratorClose {
        result: Register,
        called: Register,
        iterator: Register,
        mode: IteratorCloseMode,
    },
    /// Require a callable `iterator.return` result to be an object.
    ///
    /// Falls through when the return method was absent or non-callable
    /// (`called` is false), otherwise throws a `TypeError` with message
    /// `iterator.return() returned a non-object` unless `result` is an object.
    RequireCloseResult { result: Register, called: Register },
    /// Capture a disposable resource's method and disposal kind.
    ///
    /// `method` and `kind` are distinct outputs. `kind` is `0` for a nullish
    /// resource, `1` for a direct `@@dispose` or `@@asyncDispose` method, and
    /// `2` when async disposal falls back to `@@dispose`.
    DisposeCapture {
        method: Register,
        kind: Register,
        src: Register,
        hint: DisposeHint,
    },
    /// Construct an intrinsic `SuppressedError` with the disposal failure in
    /// `error` and the prior body or disposal failure in `suppressed`.
    /// Both fields are preserved as non-enumerable own data properties.
    SuppressError {
        dst: Register,
        error: Register,
        suppressed: Register,
    },
    /// Unconditional control transfer (identical to the formal `Jump`).
    Jump { target: Pc },
    /// Branch to `target` when `condition` is truthy, else fall through.
    JumpIfTrue { condition: Register, target: Pc },
    /// Branch to `target` when `condition` is falsy, else fall through.
    JumpIfFalse { condition: Register, target: Pc },
    /// Return `value` to the caller (terminator).
    Return { value: Register },
    /// Throw `value` (terminator; caught by an enclosing handler if any).
    Throw { value: Register },
    /// Yield `src` (the `yield` form, including delegated `yield*`) and resume
    /// at `resume`, receiving the resumed value in `dst` and the engine-defined
    /// completion mode in `mode`. See the module-level resume contract.
    Suspend {
        dst: Register,
        src: Register,
        resume: Pc,
        mode: Register,
    },
    /// Await the operand in `src` and resume at `resume`, receiving the
    /// settled value in `dst`. It shares [`Instruction::Suspend`]'s CFG shape
    /// but has no completion-mode destination; keeping the
    /// opcodes distinct lets an async-generator body tell `await` from
    /// `yield`. See the module-level resume contract.
    Await {
        dst: Register,
        src: Register,
        resume: Pc,
    },
    /// Import the module named by the string constant `specifier` into `dst`.
    Import {
        dst: Register,
        specifier: ConstantId,
    },
    /// Evaluate `import(specifier)` using the runtime module resolver, writing
    /// its Promise result to `dst`. Unlike [`Self::Import`], this has no
    /// static-edge operand and is legal in a classic script.
    ///
    /// This is append-only wire tag 43.
    ImportDynamic { dst: Register, specifier: Register },
    /// Export the local value in `src` under the string constant `name`.
    Export { name: ConstantId, src: Register },
    /// `dst = home.[[Prototype]][key]`, invoked with `receiver` as `this`.
    GetSuper {
        dst: Register,
        home: Register,
        receiver: Register,
        key: Register,
    },
    /// Set `home.[[Prototype]][key]` using `receiver` as the receiver.
    SetSuper {
        home: Register,
        receiver: Register,
        key: Register,
        value: Register,
    },
    /// Static import carrying an attributes object.
    ImportAttributes {
        dst: Register,
        specifier: ConstantId,
        attributes: Register,
    },
    /// Dynamic import carrying an attributes/options object.
    ImportDynamicAttributes {
        dst: Register,
        specifier: Register,
        attributes: Register,
    },
    /// Copy enumerable own properties while excluding the listed keys.
    CopyDataProperties {
        target: Register,
        source: Register,
        excluded: Register,
    },
    /// Load the interned template object for one tagged-template site.
    GetTemplateObject {
        dst: Register,
        cooked: Register,
        raw: Register,
    },
    /// Throw a `ReferenceError` when the global `name` is unbound, without
    /// reading its value or invoking any accessor.
    RequireGlobalBinding { name: ConstantId },
    /// Throw a new error built from the realm's intrinsic `kind` constructor
    /// with the string constant `message`.
    ThrowIntrinsicError {
        kind: IntrinsicErrorKind,
        message: ConstantId,
    },
    /// Terminate the current activation (identical to the formal `Halt`).
    Halt,
}

impl From<isa::Instruction> for Instruction {
    fn from(instruction: isa::Instruction) -> Self {
        match instruction {
            isa::Instruction::GetSuper {
                dst,
                home,
                receiver,
                key,
            } => Self::GetSuper {
                dst,
                home,
                receiver,
                key,
            },
            isa::Instruction::SetSuper {
                home,
                receiver,
                key,
                value,
            } => Self::SetSuper {
                home,
                receiver,
                key,
                value,
            },
            isa::Instruction::ImportAttributes {
                dst,
                specifier,
                attributes,
            } => Self::ImportAttributes {
                dst,
                specifier,
                attributes,
            },
            isa::Instruction::ImportDynamicAttributes {
                dst,
                specifier,
                attributes,
            } => Self::ImportDynamicAttributes {
                dst,
                specifier,
                attributes,
            },
            isa::Instruction::CopyDataProperties {
                target,
                source,
                excluded,
            } => Self::CopyDataProperties {
                target,
                source,
                excluded,
            },
            isa::Instruction::GetTemplateObject { dst, cooked, raw } => {
                Self::GetTemplateObject { dst, cooked, raw }
            }
            isa::Instruction::RequireGlobalBinding { name } => Self::RequireGlobalBinding { name },
            isa::Instruction::ThrowIntrinsicError { kind, message } => {
                Self::ThrowIntrinsicError { kind, message }
            }
        }
    }
}

impl Instruction {
    fn extension(self) -> Option<isa::Instruction> {
        Some(match self {
            Self::GetSuper {
                dst,
                home,
                receiver,
                key,
            } => isa::Instruction::GetSuper {
                dst,
                home,
                receiver,
                key,
            },
            Self::SetSuper {
                home,
                receiver,
                key,
                value,
            } => isa::Instruction::SetSuper {
                home,
                receiver,
                key,
                value,
            },
            Self::ImportAttributes {
                dst,
                specifier,
                attributes,
            } => isa::Instruction::ImportAttributes {
                dst,
                specifier,
                attributes,
            },
            Self::ImportDynamicAttributes {
                dst,
                specifier,
                attributes,
            } => isa::Instruction::ImportDynamicAttributes {
                dst,
                specifier,
                attributes,
            },
            Self::CopyDataProperties {
                target,
                source,
                excluded,
            } => isa::Instruction::CopyDataProperties {
                target,
                source,
                excluded,
            },
            Self::GetTemplateObject { dst, cooked, raw } => {
                isa::Instruction::GetTemplateObject { dst, cooked, raw }
            }
            Self::RequireGlobalBinding { name } => isa::Instruction::RequireGlobalBinding { name },
            Self::ThrowIntrinsicError { kind, message } => {
                isa::Instruction::ThrowIntrinsicError { kind, message }
            }
            _ => return None,
        })
    }

    /// Visits every register this instruction reads before executing.
    fn visit_reads(self, mut visit: impl FnMut(Register)) {
        match self {
            Self::Move { src, .. } => visit(src),
            Self::ToObject { src, .. } => visit(src),
            Self::Unary { operand, .. } => visit(operand),
            Self::Binary { left, right, .. } => {
                visit(left);
                visit(right);
            }
            Self::CreateClosure { captures, .. } => visit(captures),
            Self::GetProperty { object, key, .. }
            | Self::DeleteProperty { object, key, .. }
            | Self::WithHasBinding { object, key, .. } => {
                visit(object);
                visit(key);
            }
            Self::SetProperty { object, key, value }
            | Self::DefineDataProperty { object, key, value } => {
                visit(object);
                visit(key);
                visit(value);
            }
            Self::LoadOwnDescriptorSlot { object, key, .. } => {
                visit(object);
                visit(key);
            }
            Self::DefineOwnDescriptorSlot {
                object, key, src, ..
            } => {
                visit(object);
                visit(key);
                visit(src);
            }
            Self::DefineAccessor {
                object,
                key,
                accessor,
                ..
            } => {
                visit(object);
                visit(key);
                visit(accessor);
            }
            Self::Call {
                callee,
                this_value,
                arguments,
                ..
            } => {
                visit(callee);
                visit(this_value);
                visit(arguments);
            }
            Self::Construct {
                callee, arguments, ..
            } => {
                visit(callee);
                visit(arguments);
            }
            Self::ConstructWithNewTarget {
                callee,
                new_target,
                arguments,
                ..
            } => {
                visit(callee);
                visit(new_target);
                visit(arguments);
            }
            Self::StoreGlobal { value, .. } => visit(value),
            Self::ArrayPush { array, value } => {
                visit(array);
                visit(value);
            }
            Self::ArrayExtend { array, iterable } => {
                visit(array);
                visit(iterable);
            }
            Self::ObjectSpread { target, source } => {
                visit(target);
                visit(source);
            }
            Self::SetPrototype { object, prototype } => {
                visit(object);
                visit(prototype);
            }
            Self::GetIterator { src, .. } => visit(src),
            Self::IteratorNext { iterator, .. }
            | Self::IteratorStep { iterator, .. }
            | Self::IteratorClose { iterator, .. } => visit(iterator),
            Self::IteratorResult { result, .. } => visit(result),
            Self::RequireCloseResult { result, called } => {
                visit(result);
                visit(called);
            }
            Self::DisposeCapture { src, .. } => visit(src),
            Self::SuppressError {
                error, suppressed, ..
            } => {
                visit(error);
                visit(suppressed);
            }
            Self::JumpIfTrue { condition, .. } | Self::JumpIfFalse { condition, .. } => {
                visit(condition);
            }
            Self::Return { value } | Self::Throw { value } | Self::Export { src: value, .. } => {
                visit(value);
            }
            Self::Suspend { src, .. } | Self::Await { src, .. } => visit(src),
            Self::ImportDynamic { specifier, .. } => visit(specifier),
            Self::GetSuper {
                home,
                receiver,
                key,
                ..
            } => {
                visit(home);
                visit(receiver);
                visit(key);
            }
            Self::SetSuper {
                home,
                receiver,
                key,
                value,
            } => {
                visit(home);
                visit(receiver);
                visit(key);
                visit(value);
            }
            Self::ImportAttributes { attributes, .. } => visit(attributes),
            Self::ImportDynamicAttributes {
                specifier,
                attributes,
                ..
            } => {
                visit(specifier);
                visit(attributes);
            }
            Self::CopyDataProperties {
                target,
                source,
                excluded,
            } => {
                visit(target);
                visit(source);
                visit(excluded);
            }
            Self::GetTemplateObject { cooked, raw, .. } => {
                visit(cooked);
                visit(raw);
            }
            Self::LoadConst { .. }
            | Self::CreateObject { .. }
            | Self::CreateArray { .. }
            | Self::CreateCell { .. }
            | Self::LoadGlobal { .. }
            | Self::TypeOfGlobal { .. }
            | Self::LoadThis { .. }
            | Self::LoadArguments { .. }
            | Self::LoadNewTarget { .. }
            | Self::LoadImportMeta { .. }
            | Self::CreatePrivateName { .. }
            | Self::CreateRegExp { .. }
            | Self::Jump { .. }
            | Self::Import { .. }
            | Self::RequireGlobalBinding { .. }
            | Self::ThrowIntrinsicError { .. }
            | Self::Halt => {}
        }
    }

    /// Visits each register this instruction defines: zero, one, or two.
    /// [`Instruction::IteratorNext`], [`Instruction::IteratorResult`],
    /// [`Instruction::IteratorClose`], and [`Instruction::Suspend`] are the
    /// two-write opcodes.
    pub fn visit_writes(self, mut visit: impl FnMut(Register)) {
        match self {
            Self::LoadConst { dst, .. }
            | Self::Move { dst, .. }
            | Self::Unary { dst, .. }
            | Self::Binary { dst, .. }
            | Self::CreateObject { dst }
            | Self::ToObject { dst, .. }
            | Self::CreateArray { dst }
            | Self::CreateCell { dst }
            | Self::CreateClosure { dst, .. }
            | Self::GetProperty { dst, .. }
            | Self::DeleteProperty { dst, .. }
            | Self::WithHasBinding { dst, .. }
            | Self::LoadOwnDescriptorSlot { dst, .. }
            | Self::Call { dst, .. }
            | Self::Construct { dst, .. }
            | Self::ConstructWithNewTarget { dst, .. }
            | Self::LoadGlobal { dst, .. }
            | Self::TypeOfGlobal { dst, .. }
            | Self::LoadThis { dst }
            | Self::LoadArguments { dst }
            | Self::LoadNewTarget { dst }
            | Self::LoadImportMeta { dst }
            | Self::CreatePrivateName { dst, .. }
            | Self::CreateRegExp { dst, .. }
            | Self::GetIterator { dst, .. }
            | Self::IteratorStep { dst, .. }
            | Self::Await { dst, .. }
            | Self::Import { dst, .. }
            | Self::ImportDynamic { dst, .. }
            | Self::GetSuper { dst, .. }
            | Self::ImportAttributes { dst, .. }
            | Self::ImportDynamicAttributes { dst, .. }
            | Self::GetTemplateObject { dst, .. }
            | Self::SuppressError { dst, .. } => visit(dst),
            Self::Suspend { dst, mode, .. } => {
                visit(dst);
                visit(mode);
            }
            Self::IteratorNext { done, value, .. } | Self::IteratorResult { done, value, .. } => {
                visit(done);
                visit(value);
            }
            Self::IteratorClose { result, called, .. } => {
                visit(result);
                visit(called);
            }
            Self::DisposeCapture { method, kind, .. } => {
                visit(method);
                visit(kind);
            }
            Self::SetProperty { .. }
            | Self::DefineDataProperty { .. }
            | Self::DefineOwnDescriptorSlot { .. }
            | Self::DefineAccessor { .. }
            | Self::StoreGlobal { .. }
            | Self::ArrayPush { .. }
            | Self::ArrayExtend { .. }
            | Self::SetSuper { .. }
            | Self::CopyDataProperties { .. }
            | Self::ObjectSpread { .. }
            | Self::SetPrototype { .. }
            | Self::Export { .. }
            | Self::Jump { .. }
            | Self::JumpIfTrue { .. }
            | Self::JumpIfFalse { .. }
            | Self::Return { .. }
            | Self::Throw { .. }
            | Self::RequireCloseResult { .. }
            | Self::RequireGlobalBinding { .. }
            | Self::ThrowIntrinsicError { .. }
            | Self::Halt => {}
        }
    }

    /// Visits each normal-control successor. Terminators visit nothing, which
    /// is exactly how reachable fall-off is forbidden: any non-terminator whose
    /// fall-through `pc + 1` equals the code length fails target verification.
    fn visit_successors(self, pc: u32, mut visit: impl FnMut(Pc)) {
        match self {
            Self::Jump { target } => visit(target),
            Self::JumpIfTrue { target, .. } | Self::JumpIfFalse { target, .. } => {
                visit(target);
                visit(Pc::new(pc + 1));
            }
            Self::Suspend { resume, .. } | Self::Await { resume, .. } => visit(resume),
            Self::Return { .. } | Self::Throw { .. } | Self::Halt => {}
            Self::LoadConst { .. }
            | Self::Move { .. }
            | Self::Unary { .. }
            | Self::Binary { .. }
            | Self::CreateObject { .. }
            | Self::ToObject { .. }
            | Self::CreateArray { .. }
            | Self::CreateCell { .. }
            | Self::CreateClosure { .. }
            | Self::GetProperty { .. }
            | Self::SetProperty { .. }
            | Self::DefineDataProperty { .. }
            | Self::LoadOwnDescriptorSlot { .. }
            | Self::DefineOwnDescriptorSlot { .. }
            | Self::WithHasBinding { .. }
            | Self::DeleteProperty { .. }
            | Self::DefineAccessor { .. }
            | Self::Call { .. }
            | Self::Construct { .. }
            | Self::ConstructWithNewTarget { .. }
            | Self::LoadGlobal { .. }
            | Self::StoreGlobal { .. }
            | Self::TypeOfGlobal { .. }
            | Self::LoadThis { .. }
            | Self::LoadArguments { .. }
            | Self::LoadNewTarget { .. }
            | Self::LoadImportMeta { .. }
            | Self::ArrayPush { .. }
            | Self::ArrayExtend { .. }
            | Self::ObjectSpread { .. }
            | Self::SetPrototype { .. }
            | Self::CreatePrivateName { .. }
            | Self::CreateRegExp { .. }
            | Self::GetIterator { .. }
            | Self::IteratorNext { .. }
            | Self::IteratorStep { .. }
            | Self::IteratorResult { .. }
            | Self::IteratorClose { .. }
            | Self::RequireCloseResult { .. }
            | Self::DisposeCapture { .. }
            | Self::SuppressError { .. }
            | Self::Import { .. }
            | Self::ImportDynamic { .. }
            | Self::GetSuper { .. }
            | Self::SetSuper { .. }
            | Self::ImportAttributes { .. }
            | Self::ImportDynamicAttributes { .. }
            | Self::CopyDataProperties { .. }
            | Self::GetTemplateObject { .. }
            | Self::RequireGlobalBinding { .. }
            | Self::ThrowIntrinsicError { .. }
            | Self::Export { .. } => visit(Pc::new(pc + 1)),
        }
    }
}

/// A half-open protected range `[start, end)`, its handler entry PC, and the
/// register that receives the thrown value on dispatch.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExceptionHandler {
    pub start: Pc,
    pub end: Pc,
    pub handler: Pc,
    pub catch_register: Register,
}

/// Compact function flags record.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct FunctionFlags {
    pub is_async: bool,
    pub is_generator: bool,
    pub is_constructable: bool,
    /// Non-strict ECMAScript code, which only a JavaScript script can contain.
    pub is_sloppy: bool,
    /// A generator whose parameters can run code. A call runs it to its first
    /// `Suspend`, which ends the prologue, so a throw reaches the caller.
    pub binds_at_call: bool,
}

impl FunctionFlags {
    const ASYNC: u8 = 0b001;
    const GENERATOR: u8 = 0b010;
    const CONSTRUCTABLE: u8 = 0b100;
    const SLOPPY: u8 = 0b1000;
    const BINDS_AT_CALL: u8 = 0b1_0000;
    const KNOWN: u8 =
        Self::ASYNC | Self::GENERATOR | Self::CONSTRUCTABLE | Self::SLOPPY | Self::BINDS_AT_CALL;

    const fn to_bits(self) -> u8 {
        let mut bits = 0;
        if self.is_async {
            bits |= Self::ASYNC;
        }
        if self.is_generator {
            bits |= Self::GENERATOR;
        }
        if self.is_constructable {
            bits |= Self::CONSTRUCTABLE;
        }
        if self.is_sloppy {
            bits |= Self::SLOPPY;
        }
        if self.binds_at_call {
            bits |= Self::BINDS_AT_CALL;
        }
        bits
    }

    const fn from_bits(bits: u8) -> Option<Self> {
        if bits & !Self::KNOWN != 0 {
            return None;
        }
        Some(Self {
            is_async: bits & Self::ASYNC != 0,
            is_generator: bits & Self::GENERATOR != 0,
            is_constructable: bits & Self::CONSTRUCTABLE != 0,
            is_sloppy: bits & Self::SLOPPY != 0,
            binds_at_call: bits & Self::BINDS_AT_CALL != 0,
        })
    }
}

/// An explicit function record: metadata, code, and handlers. On entry the
/// leading `capture_count` registers hold the closure's captured cells and the
/// next `parameter_count` registers hold the parameters; all `capture_count +
/// parameter_count` are initialized on entry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Function {
    name: Option<ConstantId>,
    capture_count: u32,
    parameter_count: u32,
    register_count: u32,
    flags: FunctionFlags,
    code: Vec<Instruction>,
    handlers: Vec<ExceptionHandler>,
}

impl Function {
    #[must_use]
    pub fn new(
        name: Option<ConstantId>,
        capture_count: u32,
        parameter_count: u32,
        register_count: u32,
        flags: FunctionFlags,
        code: Vec<Instruction>,
        handlers: Vec<ExceptionHandler>,
    ) -> Self {
        Self {
            name,
            capture_count,
            parameter_count,
            register_count,
            flags,
            code,
            handlers,
        }
    }

    #[must_use]
    pub const fn name(&self) -> Option<ConstantId> {
        self.name
    }

    #[must_use]
    pub const fn capture_count(&self) -> u32 {
        self.capture_count
    }

    #[must_use]
    pub const fn parameter_count(&self) -> u32 {
        self.parameter_count
    }

    #[must_use]
    pub const fn register_count(&self) -> u32 {
        self.register_count
    }

    #[must_use]
    pub const fn flags(&self) -> FunctionFlags {
        self.flags
    }

    #[must_use]
    pub fn code(&self) -> &[Instruction] {
        &self.code
    }

    #[must_use]
    pub fn handlers(&self) -> &[ExceptionHandler] {
        &self.handlers
    }

    /// The count of registers initialized on entry: captures followed by
    /// parameters. Saturating, so it never wraps for hostile metadata (the
    /// verifier separately rejects a sum exceeding `register_count`).
    const fn entry_initialized(&self) -> u32 {
        self.capture_count.saturating_add(self.parameter_count)
    }
}

/// Marker for decoded or newly assembled, untrusted bytecode.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Unverified {
    _private: (),
}

/// Unforgeable marker proving verification completed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Verified {
    _private: (),
}

/// Explicit constant pool, function table, and entry function, with typestate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Module<State = Unverified> {
    constants: Vec<Constant>,
    functions: Vec<Function>,
    entry: FunctionId,
    certificates: Vec<Certificate>,
    state: PhantomData<State>,
}

impl<State> Module<State> {
    #[must_use]
    pub fn constants(&self) -> &[Constant] {
        &self.constants
    }

    #[must_use]
    pub fn functions(&self) -> &[Function] {
        &self.functions
    }

    #[must_use]
    pub const fn entry(&self) -> FunctionId {
        self.entry
    }
}

impl Module<Unverified> {
    #[must_use]
    pub fn new(constants: Vec<Constant>, functions: Vec<Function>, entry: FunctionId) -> Self {
        Self {
            constants,
            functions,
            entry,
            certificates: Vec::new(),
            state: PhantomData,
        }
    }

    /// Consumes untrusted structure and is the only route to `Module<Verified>`.
    ///
    /// # Errors
    /// Returns the first structural violation found (bounds, references, CFG,
    /// handlers, or definite initialization).
    pub fn verify(self) -> Result<Module<Verified>, VerifyError> {
        verify_module(self)
    }
}

impl Module<Verified> {
    #[must_use]
    pub fn certificate(&self, function: FunctionId) -> Option<&Certificate> {
        self.certificates.get(function.get() as usize)
    }

    /// Heap bytes retained by this module's verification certificates.
    #[must_use]
    pub fn verification_bytes(&self) -> usize {
        self.certificates.iter().fold(0usize, |bytes, certificate| {
            bytes.saturating_add(certificate.retained_bytes())
        })
    }

    /// Emits one deterministic canonical representation.
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut output = Vec::new();
        output.extend_from_slice(&MAGIC);
        output.push(FORMAT_VERSION);
        write_u32(self.constants.len() as u32, &mut output);
        for constant in &self.constants {
            encode_constant(constant, &mut output);
        }
        write_u32(self.functions.len() as u32, &mut output);
        write_u32(self.entry.get(), &mut output);
        for function in &self.functions {
            encode_function(function, &mut output);
        }
        output
    }
}

/// Forward-dataflow definite-initialization facts, mirroring Lean's
/// `Certificate.facts`. Construction is private, so certificates are unforgeable.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Certificate {
    register_count: u32,
    facts: Vec<RegisterSet>,
}

impl Certificate {
    fn retained_bytes(&self) -> usize {
        self.facts.iter().fold(
            std::mem::size_of::<Self>().saturating_add(
                self.facts
                    .len()
                    .saturating_mul(std::mem::size_of::<RegisterSet>()),
            ),
            |bytes, facts| {
                bytes.saturating_add(facts.words.len().saturating_mul(std::mem::size_of::<u64>()))
            },
        )
    }

    #[must_use]
    pub fn instruction_count(&self) -> usize {
        self.facts.len()
    }

    /// Whether `register` is definitely initialized before executing `pc`.
    /// Total for every wrapper value: out-of-range registers or PCs yield
    /// `None` rather than panicking.
    #[must_use]
    pub fn initialized_before(&self, pc: Pc, register: Register) -> Option<bool> {
        if register.get() >= self.register_count {
            return None;
        }
        self.facts
            .get(pc.get() as usize)
            .map(|facts| facts.contains(register))
    }
}

/// A dynamically sized register bitset covering a function's register file.
#[derive(Clone, Debug, Eq, PartialEq)]
struct RegisterSet {
    words: Box<[u64]>,
}

impl RegisterSet {
    fn words_for(register_count: u32) -> usize {
        (register_count as usize).div_ceil(64)
    }

    fn empty(register_count: u32) -> Self {
        Self {
            words: vec![0; Self::words_for(register_count)].into_boxed_slice(),
        }
    }

    fn full(register_count: u32) -> Self {
        let words_len = Self::words_for(register_count);
        let mut words = vec![u64::MAX; words_len];
        let remainder = register_count % 64;
        if remainder != 0 && words_len != 0 {
            words[words_len - 1] = (1_u64 << remainder) - 1;
        }
        Self {
            words: words.into_boxed_slice(),
        }
    }

    fn contains(&self, register: Register) -> bool {
        let index = register.get() as usize;
        self.words
            .get(index / 64)
            .is_some_and(|word| word & (1_u64 << (index % 64)) != 0)
    }

    fn insert(&mut self, register: Register) {
        let index = register.get() as usize;
        if let Some(word) = self.words.get_mut(index / 64) {
            *word |= 1_u64 << (index % 64);
        }
    }

    fn insert_prefix(&mut self, count: u32) {
        for register in 0..count {
            self.insert(Register::new(register));
        }
    }

    fn intersect(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (slot, mask) in self.words.iter_mut().zip(other.words.iter()) {
            let next = *slot & *mask;
            if next != *slot {
                changed = true;
                *slot = next;
            }
        }
        changed
    }
}

/// A structural verification failure, located at a function and/or instruction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifyError {
    pub function: Option<FunctionId>,
    pub instruction: Option<Pc>,
    pub kind: VerifyErrorKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VerifyErrorKind {
    EmptyModule,
    VerifierWorkLimitExceeded {
        work: u64,
        limit: u64,
    },
    TooManyConstants {
        count: usize,
    },
    TooManyFunctions {
        count: usize,
    },
    EntryFunctionOutOfBounds {
        entry: u32,
        function_count: usize,
    },
    EmptyFunction,
    TooManyInstructions {
        count: usize,
    },
    TooManyHandlers {
        count: usize,
    },
    RegisterCountOutOfBounds {
        count: u32,
    },
    ParameterCountExceedsRegisters {
        parameter_count: u32,
        register_count: u32,
    },
    EntryRegistersExceedRegisterCount {
        capture_count: u32,
        parameter_count: u32,
        register_count: u32,
    },
    FunctionNameOutOfBounds {
        constant: u32,
    },
    FunctionNameNotString {
        constant: ConstantId,
    },
    RegisterOutOfBounds {
        register: Register,
        register_count: u32,
    },
    AliasedIteratorCloseOutputs {
        register: Register,
    },
    AliasedIteratorNextOutputs {
        register: Register,
    },
    AliasedIteratorResultOutputs {
        register: Register,
    },
    AliasedDisposeCaptureOutputs {
        register: Register,
    },
    AliasedCopyDataProperties {
        register: Register,
    },
    ConstantOutOfBounds {
        constant: ConstantId,
        constant_count: usize,
    },
    StringConstantExpected {
        constant: ConstantId,
    },
    FunctionReferenceOutOfBounds {
        function: FunctionId,
        function_count: usize,
    },
    JumpOutOfBounds {
        target: u32,
        instruction_count: usize,
    },
    InvalidHandlerBounds {
        handler: usize,
        start: u32,
        end: u32,
        target: u32,
    },
    HandlerCatchRegisterOutOfBounds {
        handler: usize,
        register: Register,
        register_count: u32,
    },
    HandlersPartiallyOverlap {
        left: usize,
        right: usize,
    },
    ReadBeforeWrite {
        register: Register,
    },
}

impl fmt::Display for VerifyError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(function) = self.function {
            write!(formatter, "function {}", function.get())?;
            if let Some(instruction) = self.instruction {
                write!(formatter, " instruction {}", instruction.get())?;
            }
            formatter.write_str(": ")?;
        }
        match &self.kind {
            VerifyErrorKind::EmptyModule => formatter.write_str("module has no functions"),
            VerifyErrorKind::VerifierWorkLimitExceeded { work, limit } => write!(
                formatter,
                "verifier fact allocation {work} words exceeds the {limit}-word limit"
            ),
            VerifyErrorKind::TooManyConstants { count } => {
                write!(formatter, "{count} constants exceed the structural limit")
            }
            VerifyErrorKind::TooManyFunctions { count } => {
                write!(formatter, "{count} functions exceed the structural limit")
            }
            VerifyErrorKind::EntryFunctionOutOfBounds {
                entry,
                function_count,
            } => write!(
                formatter,
                "entry function {entry} is outside {function_count} functions"
            ),
            VerifyErrorKind::EmptyFunction => {
                formatter.write_str("function has no entry instruction")
            }
            VerifyErrorKind::TooManyInstructions { count } => {
                write!(
                    formatter,
                    "{count} instructions exceed the structural limit"
                )
            }
            VerifyErrorKind::TooManyHandlers { count } => {
                write!(formatter, "{count} handlers exceed the structural limit")
            }
            VerifyErrorKind::RegisterCountOutOfBounds { count } => {
                write!(
                    formatter,
                    "register count {count} exceeds the structural limit"
                )
            }
            VerifyErrorKind::ParameterCountExceedsRegisters {
                parameter_count,
                register_count,
            } => write!(
                formatter,
                "parameter count {parameter_count} exceeds register count {register_count}"
            ),
            VerifyErrorKind::EntryRegistersExceedRegisterCount {
                capture_count,
                parameter_count,
                register_count,
            } => write!(
                formatter,
                "capture count {capture_count} plus parameter count {parameter_count} exceeds \
                 register count {register_count}"
            ),
            VerifyErrorKind::FunctionNameOutOfBounds { constant } => {
                write!(
                    formatter,
                    "function name constant {constant} is out of bounds"
                )
            }
            VerifyErrorKind::FunctionNameNotString { constant } => write!(
                formatter,
                "function name constant {} is not a string",
                constant.get()
            ),
            VerifyErrorKind::RegisterOutOfBounds {
                register,
                register_count,
            } => write!(
                formatter,
                "register {} is outside register count {register_count}",
                register.get()
            ),
            VerifyErrorKind::AliasedIteratorCloseOutputs { register } => write!(
                formatter,
                "iterator close result and called outputs alias register {}",
                register.get()
            ),
            VerifyErrorKind::AliasedIteratorNextOutputs { register } => write!(
                formatter,
                "iterator next done and value outputs alias register {}",
                register.get()
            ),
            VerifyErrorKind::AliasedIteratorResultOutputs { register } => write!(
                formatter,
                "iterator result done and value outputs alias register {}",
                register.get()
            ),
            VerifyErrorKind::AliasedDisposeCaptureOutputs { register } => write!(
                formatter,
                "dispose capture method and kind outputs alias register {}",
                register.get()
            ),
            VerifyErrorKind::AliasedCopyDataProperties { register } => write!(
                formatter,
                "copy-data-properties target aliases input register {}",
                register.get()
            ),
            VerifyErrorKind::ConstantOutOfBounds {
                constant,
                constant_count,
            } => write!(
                formatter,
                "constant {} is outside {constant_count} constants",
                constant.get()
            ),
            VerifyErrorKind::StringConstantExpected { constant } => {
                write!(formatter, "constant {} must be a string", constant.get())
            }
            VerifyErrorKind::FunctionReferenceOutOfBounds {
                function,
                function_count,
            } => write!(
                formatter,
                "function reference {} is outside {function_count} functions",
                function.get()
            ),
            VerifyErrorKind::JumpOutOfBounds {
                target,
                instruction_count,
            } => write!(
                formatter,
                "target {target} is not one of {instruction_count} instruction boundaries"
            ),
            VerifyErrorKind::InvalidHandlerBounds {
                handler,
                start,
                end,
                target,
            } => write!(
                formatter,
                "handler {handler} has invalid range {start}..{end} or target {target}"
            ),
            VerifyErrorKind::HandlerCatchRegisterOutOfBounds {
                handler,
                register,
                register_count,
            } => write!(
                formatter,
                "handler {handler} catch register {} is outside register count {register_count}",
                register.get()
            ),
            VerifyErrorKind::HandlersPartiallyOverlap { left, right } => write!(
                formatter,
                "handlers {left} and {right} partially overlap instead of nesting"
            ),
            VerifyErrorKind::ReadBeforeWrite { register } => write!(
                formatter,
                "register {} may be read before initialization",
                register.get()
            ),
        }
    }
}

impl Error for VerifyError {}

fn module_error(kind: VerifyErrorKind) -> VerifyError {
    VerifyError {
        function: None,
        instruction: None,
        kind,
    }
}

fn function_error(function: usize, kind: VerifyErrorKind) -> VerifyError {
    VerifyError {
        function: Some(FunctionId::new(function as u32)),
        instruction: None,
        kind,
    }
}

fn instruction_error(function: usize, pc: usize, kind: VerifyErrorKind) -> VerifyError {
    VerifyError {
        function: Some(FunctionId::new(function as u32)),
        instruction: Some(Pc::new(pc as u32)),
        kind,
    }
}

fn verify_module(module: Module<Unverified>) -> Result<Module<Verified>, VerifyError> {
    if module.functions.is_empty() {
        return Err(module_error(VerifyErrorKind::EmptyModule));
    }
    if module.constants.len() as u64 > u64::from(MAX_CONSTANTS) {
        return Err(module_error(VerifyErrorKind::TooManyConstants {
            count: module.constants.len(),
        }));
    }
    if module.functions.len() as u64 > u64::from(MAX_FUNCTIONS) {
        return Err(module_error(VerifyErrorKind::TooManyFunctions {
            count: module.functions.len(),
        }));
    }
    if module.entry.get() as usize >= module.functions.len() {
        return Err(module_error(VerifyErrorKind::EntryFunctionOutOfBounds {
            entry: module.entry.get(),
            function_count: module.functions.len(),
        }));
    }

    // Combined, overflow-safe cap on the definite-initialization fact storage
    // this module can force the verifier to allocate, checked before any
    // per-function allocation. Saturating arithmetic can only tighten the
    // bound, so it never masks an over-limit module. The comparison is
    // strict `>`: facts-work equal to the cap is the largest permitted
    // allocation. Acceptance at exactly the cap is intentionally untested
    // because it forces the full 64 MiB `facts` allocation; the boundary is
    // pinned from the rejection side only (see `verifier_rejects_facts_work_
    // above_cap`).
    let mut total_facts_words: u64 = 0;
    for function in &module.functions {
        let words = RegisterSet::words_for(function.register_count) as u64;
        let function_words = (function.code.len() as u64).saturating_mul(words);
        total_facts_words = total_facts_words.saturating_add(function_words);
        if total_facts_words > MAX_VERIFIER_FACTS_WORDS {
            return Err(module_error(VerifyErrorKind::VerifierWorkLimitExceeded {
                work: total_facts_words,
                limit: MAX_VERIFIER_FACTS_WORDS,
            }));
        }
    }

    let mut certificates = Vec::with_capacity(module.functions.len());
    for (index, function) in module.functions.iter().enumerate() {
        certificates.push(verify_function(&module, index, function)?);
    }

    Ok(Module {
        constants: module.constants,
        functions: module.functions,
        entry: module.entry,
        certificates,
        state: PhantomData,
    })
}

fn verify_function(
    module: &Module<Unverified>,
    function_index: usize,
    function: &Function,
) -> Result<Certificate, VerifyError> {
    if function.code.is_empty() {
        return Err(function_error(
            function_index,
            VerifyErrorKind::EmptyFunction,
        ));
    }
    if function.code.len() as u64 > u64::from(MAX_INSTRUCTIONS) {
        return Err(function_error(
            function_index,
            VerifyErrorKind::TooManyInstructions {
                count: function.code.len(),
            },
        ));
    }
    if function.handlers.len() as u64 > u64::from(MAX_HANDLERS) {
        return Err(function_error(
            function_index,
            VerifyErrorKind::TooManyHandlers {
                count: function.handlers.len(),
            },
        ));
    }
    if function.register_count > MAX_REGISTERS {
        return Err(function_error(
            function_index,
            VerifyErrorKind::RegisterCountOutOfBounds {
                count: function.register_count,
            },
        ));
    }
    if function.parameter_count > function.register_count {
        return Err(function_error(
            function_index,
            VerifyErrorKind::ParameterCountExceedsRegisters {
                parameter_count: function.parameter_count,
                register_count: function.register_count,
            },
        ));
    }
    // Captures and parameters share the leading register file; their sum must
    // fit. Checked with u64 so hostile counts near u32::MAX cannot wrap.
    if u64::from(function.capture_count) + u64::from(function.parameter_count)
        > u64::from(function.register_count)
    {
        return Err(function_error(
            function_index,
            VerifyErrorKind::EntryRegistersExceedRegisterCount {
                capture_count: function.capture_count,
                parameter_count: function.parameter_count,
                register_count: function.register_count,
            },
        ));
    }
    verify_function_name(module, function_index, function)?;
    verify_handlers(function_index, function)?;
    for (pc, instruction) in function.code.iter().copied().enumerate() {
        verify_instruction(module, function_index, function, pc, instruction)?;
    }
    definite_initialization(function_index, function)
}

fn verify_function_name(
    module: &Module<Unverified>,
    function_index: usize,
    function: &Function,
) -> Result<(), VerifyError> {
    let Some(name) = function.name else {
        return Ok(());
    };
    let Some(constant) = module.constants.get(name.get() as usize) else {
        return Err(function_error(
            function_index,
            VerifyErrorKind::FunctionNameOutOfBounds {
                constant: name.get(),
            },
        ));
    };
    if !matches!(constant, Constant::String(_)) {
        return Err(function_error(
            function_index,
            VerifyErrorKind::FunctionNameNotString { constant: name },
        ));
    }
    Ok(())
}

fn verify_handlers(function_index: usize, function: &Function) -> Result<(), VerifyError> {
    let code_len = function.code.len();
    for (index, handler) in function.handlers.iter().copied().enumerate() {
        if handler.start.get() >= handler.end.get()
            || handler.end.get() as usize > code_len
            || handler.handler.get() as usize >= code_len
        {
            return Err(function_error(
                function_index,
                VerifyErrorKind::InvalidHandlerBounds {
                    handler: index,
                    start: handler.start.get(),
                    end: handler.end.get(),
                    target: handler.handler.get(),
                },
            ));
        }
        if handler.catch_register.get() >= function.register_count {
            return Err(function_error(
                function_index,
                VerifyErrorKind::HandlerCatchRegisterOutOfBounds {
                    handler: index,
                    register: handler.catch_register,
                    register_count: function.register_count,
                },
            ));
        }
    }
    // Deterministic O(n log n) laminar-family check over half-open ranges.
    // Sort handler indices by (start ascending, end descending) so an
    // enclosing range is always visited before any range it contains, then
    // sweep with a stack of open ancestor ends. `function.handlers` is never
    // mutated, so its original order (and the reported indices) is preserved.
    let mut order: Vec<usize> = (0..function.handlers.len()).collect();
    order.sort_by(|&left, &right| {
        let a = function.handlers[left];
        let b = function.handlers[right];
        a.start
            .get()
            .cmp(&b.start.get())
            .then_with(|| b.end.get().cmp(&a.end.get()))
    });
    let mut open: Vec<(u32, usize)> = Vec::new();
    for &index in &order {
        let range = function.handlers[index];
        let start = range.start.get();
        let end = range.end.get();
        // Disjoint and sibling ranges (including adjacency `[a, b) + [b, c)`)
        // close once the sweep passes their end.
        while open.last().is_some_and(|&(open_end, _)| open_end <= start) {
            open.pop();
        }
        if let Some(&(parent_end, parent_index)) = open.last() {
            // The current range shares an open ancestor. It must nest fully
            // inside it; extending past the ancestor's end is a partial overlap
            // (or a crossing), never proper nesting.
            if end > parent_end {
                let (left, right) = if parent_index < index {
                    (parent_index, index)
                } else {
                    (index, parent_index)
                };
                return Err(function_error(
                    function_index,
                    VerifyErrorKind::HandlersPartiallyOverlap { left, right },
                ));
            }
        }
        open.push((end, index));
    }
    Ok(())
}

fn verify_instruction(
    module: &Module<Unverified>,
    function_index: usize,
    function: &Function,
    pc: usize,
    instruction: Instruction,
) -> Result<(), VerifyError> {
    let register_count = function.register_count;
    let constant_count = module.constants.len();
    let function_count = module.functions.len();
    let code_len = function.code.len();
    if let Some(extension) = instruction.extension() {
        verifier::verify_extension(
            function_index,
            pc,
            extension,
            register_count,
            &module.constants,
            code_len,
        )
        .map_err(|error| VerifyError {
            function: error.function,
            instruction: error.instruction,
            kind: match error.kind {
                verifier::Kind::RegisterOutOfBounds {
                    register,
                    register_count,
                } => VerifyErrorKind::RegisterOutOfBounds {
                    register,
                    register_count,
                },
                verifier::Kind::JumpOutOfBounds {
                    target,
                    instruction_count,
                } => VerifyErrorKind::JumpOutOfBounds {
                    target,
                    instruction_count,
                },
                verifier::Kind::ConstantOutOfBounds {
                    constant,
                    constant_count,
                } => VerifyErrorKind::ConstantOutOfBounds {
                    constant,
                    constant_count,
                },
                verifier::Kind::StringConstantExpected { constant } => {
                    VerifyErrorKind::StringConstantExpected { constant }
                }
                verifier::Kind::AliasedCopyDataProperties { register } => {
                    VerifyErrorKind::AliasedCopyDataProperties { register }
                }
            },
        })?;
    }

    let check_register = |register: Register| -> Result<(), VerifyError> {
        if register.get() >= register_count {
            Err(instruction_error(
                function_index,
                pc,
                VerifyErrorKind::RegisterOutOfBounds {
                    register,
                    register_count,
                },
            ))
        } else {
            Ok(())
        }
    };
    let check_constant = |constant: ConstantId| -> Result<(), VerifyError> {
        if constant.get() as usize >= constant_count {
            Err(instruction_error(
                function_index,
                pc,
                VerifyErrorKind::ConstantOutOfBounds {
                    constant,
                    constant_count,
                },
            ))
        } else {
            Ok(())
        }
    };
    // A string constant reference: property/global/private/regexp/export/import
    // names must all resolve to a `Constant::String`.
    let check_string_constant = |constant: ConstantId| -> Result<(), VerifyError> {
        check_constant(constant)?;
        if matches!(
            module.constants[constant.get() as usize],
            Constant::String(_)
        ) {
            Ok(())
        } else {
            Err(instruction_error(
                function_index,
                pc,
                VerifyErrorKind::StringConstantExpected { constant },
            ))
        }
    };

    match instruction {
        Instruction::LoadConst { dst, constant } => {
            check_register(dst)?;
            check_constant(constant)?;
        }
        Instruction::Move { dst, src } => {
            check_register(dst)?;
            check_register(src)?;
        }
        Instruction::ToObject { dst, src } => {
            check_register(dst)?;
            check_register(src)?;
        }
        Instruction::Unary { dst, operand, .. } => {
            check_register(dst)?;
            check_register(operand)?;
        }
        Instruction::Binary {
            dst, left, right, ..
        } => {
            check_register(dst)?;
            check_register(left)?;
            check_register(right)?;
        }
        Instruction::CreateObject { dst }
        | Instruction::CreateArray { dst }
        | Instruction::CreateCell { dst } => {
            check_register(dst)?;
        }
        Instruction::CreateClosure {
            dst,
            function: reference,
            captures,
        } => {
            check_register(dst)?;
            check_register(captures)?;
            if reference.get() as usize >= function_count {
                return Err(instruction_error(
                    function_index,
                    pc,
                    VerifyErrorKind::FunctionReferenceOutOfBounds {
                        function: reference,
                        function_count,
                    },
                ));
            }
        }
        Instruction::GetProperty { dst, object, key }
        | Instruction::DeleteProperty { dst, object, key }
        | Instruction::WithHasBinding { dst, object, key } => {
            check_register(dst)?;
            check_register(object)?;
            check_register(key)?;
        }
        Instruction::SetProperty { object, key, value }
        | Instruction::DefineDataProperty { object, key, value } => {
            check_register(object)?;
            check_register(key)?;
            check_register(value)?;
        }
        Instruction::LoadOwnDescriptorSlot {
            dst, object, key, ..
        } => {
            check_register(dst)?;
            check_register(object)?;
            check_register(key)?;
        }
        Instruction::DefineOwnDescriptorSlot {
            object, key, src, ..
        } => {
            check_register(object)?;
            check_register(key)?;
            check_register(src)?;
        }
        Instruction::DefineAccessor {
            object,
            key,
            accessor,
            ..
        } => {
            check_register(object)?;
            check_register(key)?;
            check_register(accessor)?;
        }
        Instruction::Call {
            dst,
            callee,
            this_value,
            arguments,
        } => {
            check_register(dst)?;
            check_register(callee)?;
            check_register(this_value)?;
            check_register(arguments)?;
        }
        Instruction::Construct {
            dst,
            callee,
            arguments,
        } => {
            check_register(dst)?;
            check_register(callee)?;
            check_register(arguments)?;
        }
        Instruction::ConstructWithNewTarget {
            dst,
            callee,
            new_target,
            arguments,
        } => {
            check_register(dst)?;
            check_register(callee)?;
            check_register(new_target)?;
            check_register(arguments)?;
        }
        Instruction::LoadGlobal { dst, name } | Instruction::TypeOfGlobal { dst, name } => {
            check_register(dst)?;
            check_string_constant(name)?;
        }
        Instruction::StoreGlobal { name, value } => {
            check_string_constant(name)?;
            check_register(value)?;
        }
        Instruction::LoadThis { dst }
        | Instruction::LoadArguments { dst }
        | Instruction::LoadNewTarget { dst }
        | Instruction::LoadImportMeta { dst } => {
            check_register(dst)?;
        }
        Instruction::ArrayPush { array, value } => {
            check_register(array)?;
            check_register(value)?;
        }
        Instruction::ArrayExtend { array, iterable } => {
            check_register(array)?;
            check_register(iterable)?;
        }
        Instruction::ObjectSpread { target, source } => {
            check_register(target)?;
            check_register(source)?;
        }
        Instruction::SetPrototype { object, prototype } => {
            check_register(object)?;
            check_register(prototype)?;
        }
        Instruction::CreatePrivateName { dst, description } => {
            check_register(dst)?;
            check_string_constant(description)?;
        }
        Instruction::CreateRegExp {
            dst,
            pattern,
            flags,
        } => {
            check_register(dst)?;
            check_string_constant(pattern)?;
            check_string_constant(flags)?;
        }
        Instruction::GetIterator { dst, src, .. } => {
            check_register(dst)?;
            check_register(src)?;
        }
        Instruction::IteratorNext {
            done,
            value,
            iterator,
        } => {
            check_register(done)?;
            check_register(value)?;
            check_register(iterator)?;
            if done == value {
                return Err(instruction_error(
                    function_index,
                    pc,
                    VerifyErrorKind::AliasedIteratorNextOutputs { register: done },
                ));
            }
        }
        Instruction::IteratorStep { dst, iterator } => {
            check_register(dst)?;
            check_register(iterator)?;
        }
        Instruction::IteratorResult {
            done,
            value,
            result,
        } => {
            check_register(done)?;
            check_register(value)?;
            check_register(result)?;
            if done == value {
                return Err(instruction_error(
                    function_index,
                    pc,
                    VerifyErrorKind::AliasedIteratorResultOutputs { register: done },
                ));
            }
        }
        Instruction::IteratorClose {
            result,
            called,
            iterator,
            ..
        } => {
            check_register(result)?;
            check_register(called)?;
            check_register(iterator)?;
            if result == called {
                return Err(instruction_error(
                    function_index,
                    pc,
                    VerifyErrorKind::AliasedIteratorCloseOutputs { register: result },
                ));
            }
        }
        Instruction::RequireCloseResult { result, called } => {
            check_register(result)?;
            check_register(called)?;
        }
        Instruction::DisposeCapture {
            method, kind, src, ..
        } => {
            check_register(method)?;
            check_register(kind)?;
            check_register(src)?;
            if method == kind {
                return Err(instruction_error(
                    function_index,
                    pc,
                    VerifyErrorKind::AliasedDisposeCaptureOutputs { register: method },
                ));
            }
        }
        Instruction::SuppressError {
            dst,
            error,
            suppressed,
        } => {
            check_register(dst)?;
            check_register(error)?;
            check_register(suppressed)?;
        }
        Instruction::Jump { target } => verify_target(function_index, pc, target, code_len)?,
        Instruction::JumpIfTrue { condition, target }
        | Instruction::JumpIfFalse { condition, target } => {
            check_register(condition)?;
            verify_target(function_index, pc, target, code_len)?;
        }
        Instruction::Return { value } | Instruction::Throw { value } => check_register(value)?,
        Instruction::Suspend {
            dst,
            src,
            resume,
            mode,
        } => {
            check_register(dst)?;
            check_register(src)?;
            check_register(mode)?;
            verify_target(function_index, pc, resume, code_len)?;
        }
        Instruction::Await { dst, src, resume } => {
            check_register(dst)?;
            check_register(src)?;
            verify_target(function_index, pc, resume, code_len)?;
        }
        Instruction::Import { dst, specifier } => {
            check_register(dst)?;
            check_string_constant(specifier)?;
        }
        Instruction::ImportDynamic { dst, specifier } => {
            check_register(dst)?;
            check_register(specifier)?;
        }
        Instruction::Export { name, src } => {
            check_string_constant(name)?;
            check_register(src)?;
        }
        Instruction::GetSuper { .. }
        | Instruction::SetSuper { .. }
        | Instruction::ImportAttributes { .. }
        | Instruction::ImportDynamicAttributes { .. }
        | Instruction::CopyDataProperties { .. }
        | Instruction::GetTemplateObject { .. }
        | Instruction::RequireGlobalBinding { .. }
        | Instruction::ThrowIntrinsicError { .. } => {}
        Instruction::Halt => {}
    }

    // Every normal successor (including fall-through) must be a real
    // instruction boundary: this forbids reachable fall-off past the end.
    let mut successor_error = None;
    instruction.visit_successors(pc as u32, |successor| {
        if successor_error.is_none() {
            successor_error = verify_target(function_index, pc, successor, code_len).err();
        }
    });
    if let Some(error) = successor_error {
        return Err(error);
    }
    Ok(())
}

fn verify_target(
    function_index: usize,
    pc: usize,
    target: Pc,
    instruction_count: usize,
) -> Result<(), VerifyError> {
    if target.get() as usize >= instruction_count {
        Err(instruction_error(
            function_index,
            pc,
            VerifyErrorKind::JumpOutOfBounds {
                target: target.get(),
                instruction_count,
            },
        ))
    } else {
        Ok(())
    }
}

/// Builds the greatest syntactic forward witness satisfying every transfer,
/// with the entry fact fixed to the capture and parameter registers. Handler
/// entries are reached conservatively: an exception may occur at the first
/// protected instruction, so a handler's fact is the intersection of the
/// pre-facts across its protected range plus its catch register. This does not
/// use semantic reachability, matching Lean's `Certificate` and
/// `verifier_never_skips_invariant`.
fn definite_initialization(
    function_index: usize,
    function: &Function,
) -> Result<Certificate, VerifyError> {
    let register_count = function.register_count;
    let mut facts = vec![RegisterSet::full(register_count); function.code.len()];
    let mut entry = RegisterSet::empty(register_count);
    entry.insert_prefix(function.entry_initialized());
    facts[0] = entry;

    loop {
        let mut changed = false;
        for (pc, instruction) in function.code.iter().copied().enumerate() {
            let mut after = facts[pc].clone();
            instruction.visit_writes(|write| after.insert(write));
            instruction.visit_successors(pc as u32, |successor| {
                changed |= facts[successor.get() as usize].intersect(&after);
            });
        }
        for handler in function.handlers.iter().copied() {
            let start = handler.start.get() as usize;
            let end = handler.end.get() as usize;
            let mut contribution = RegisterSet::full(register_count);
            for protected in &facts[start..end] {
                contribution.intersect(protected);
            }
            contribution.insert(handler.catch_register);
            changed |= facts[handler.handler.get() as usize].intersect(&contribution);
        }
        if !changed {
            break;
        }
    }

    for (pc, instruction) in function.code.iter().copied().enumerate() {
        let mut missing = None;
        instruction.visit_reads(|register| {
            if missing.is_none() && !facts[pc].contains(register) {
                missing = Some(register);
            }
        });
        if let Some(register) = missing {
            return Err(instruction_error(
                function_index,
                pc,
                VerifyErrorKind::ReadBeforeWrite { register },
            ));
        }
    }
    Ok(Certificate {
        register_count,
        facts,
    })
}

/// Decoder allocation/input ceilings, enforced before any allocation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DecodeLimits {
    pub max_bytes: usize,
    pub max_constants: u32,
    pub max_functions: u32,
    pub max_capture_count: u32,
    pub max_parameter_count: u32,
    pub max_register_count: u32,
    pub max_instructions_per_function: u32,
    pub max_total_instructions: u64,
    pub max_handlers_per_function: u32,
    pub max_string_units: u32,
    pub max_bigint_bytes: u32,
}

impl Default for DecodeLimits {
    fn default() -> Self {
        Self {
            max_bytes: 16 * 1024 * 1024,
            max_constants: MAX_CONSTANTS,
            max_functions: MAX_FUNCTIONS,
            max_capture_count: MAX_REGISTERS,
            max_parameter_count: MAX_REGISTERS,
            max_register_count: MAX_REGISTERS,
            max_instructions_per_function: MAX_INSTRUCTIONS,
            max_total_instructions: 1 << 24,
            max_handlers_per_function: MAX_HANDLERS,
            max_string_units: 1 << 20,
            max_bigint_bytes: MAX_BIGINT_BYTES,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DecodeError {
    pub offset: usize,
    pub kind: DecodeErrorKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DecodeErrorKind {
    InputLimitExceeded {
        limit: usize,
        actual: usize,
    },
    UnexpectedEof,
    BadMagic {
        expected: u8,
        actual: u8,
    },
    UnsupportedVersion {
        version: u8,
    },
    NonCanonicalInteger,
    IntegerOverflow,
    InvalidConstantTag {
        tag: u8,
    },
    NonCanonicalNumber {
        bits: u64,
    },
    InvalidUtf8,
    InvalidBigInt,
    InvalidFunctionFlags {
        bits: u8,
    },
    InvalidUnaryOp {
        tag: u8,
    },
    InvalidBinaryOp {
        tag: u8,
    },
    InvalidIteratorKind {
        tag: u8,
    },
    InvalidIteratorCloseMode {
        tag: u8,
    },
    InvalidDisposeHint {
        tag: u8,
    },
    InvalidAccessorKind {
        tag: u8,
    },
    InvalidDescriptorSlot {
        tag: u8,
    },
    InvalidOpcode {
        opcode: u8,
    },
    LimitExceeded {
        field: &'static str,
        limit: u64,
        actual: u64,
    },
    TrailingBytes {
        count: usize,
    },
    InvalidIntrinsicErrorKind {
        selector: u32,
    },
}

impl fmt::Display for DecodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "byte {}: ", self.offset)?;
        match self.kind {
            DecodeErrorKind::InputLimitExceeded { limit, actual } => {
                write!(formatter, "input has {actual} bytes, limit is {limit}")
            }
            DecodeErrorKind::UnexpectedEof => formatter.write_str("unexpected end of input"),
            DecodeErrorKind::BadMagic { expected, actual } => write!(
                formatter,
                "bad magic byte {actual:#04x}, expected {expected:#04x}"
            ),
            DecodeErrorKind::UnsupportedVersion { version } => {
                write!(formatter, "unsupported format version {version}")
            }
            DecodeErrorKind::NonCanonicalInteger => {
                formatter.write_str("noncanonical (overlong) LEB128 integer")
            }
            DecodeErrorKind::IntegerOverflow => {
                formatter.write_str("LEB128 integer exceeds 32 bits")
            }
            DecodeErrorKind::InvalidConstantTag { tag } => {
                write!(formatter, "invalid constant tag {tag}")
            }
            DecodeErrorKind::NonCanonicalNumber { bits } => {
                write!(formatter, "noncanonical NaN bits {bits:#018x}")
            }
            DecodeErrorKind::InvalidUtf8 => formatter.write_str("bigint text is not UTF-8"),
            DecodeErrorKind::InvalidBigInt => {
                formatter.write_str("bigint constant is not canonical decimal text")
            }
            DecodeErrorKind::InvalidFunctionFlags { bits } => {
                write!(formatter, "invalid function flags {bits:#04x}")
            }
            DecodeErrorKind::InvalidUnaryOp { tag } => {
                write!(formatter, "invalid unary operator {tag}")
            }
            DecodeErrorKind::InvalidBinaryOp { tag } => {
                write!(formatter, "invalid binary operator {tag}")
            }
            DecodeErrorKind::InvalidIteratorKind { tag } => {
                write!(formatter, "invalid iterator kind {tag}")
            }
            DecodeErrorKind::InvalidIteratorCloseMode { tag } => {
                write!(formatter, "invalid iterator close mode {tag}")
            }
            DecodeErrorKind::InvalidDisposeHint { tag } => {
                write!(formatter, "invalid dispose hint {tag}")
            }
            DecodeErrorKind::InvalidAccessorKind { tag } => {
                write!(formatter, "invalid accessor kind {tag}")
            }
            DecodeErrorKind::InvalidDescriptorSlot { tag } => {
                write!(formatter, "invalid descriptor slot {tag}")
            }
            DecodeErrorKind::InvalidOpcode { opcode } => {
                write!(formatter, "invalid opcode {opcode}")
            }
            DecodeErrorKind::LimitExceeded {
                field,
                limit,
                actual,
            } => write!(formatter, "{field} value {actual} exceeds limit {limit}"),
            DecodeErrorKind::TrailingBytes { count } => write!(formatter, "{count} trailing bytes"),
            DecodeErrorKind::InvalidIntrinsicErrorKind { selector } => {
                write!(formatter, "invalid intrinsic error kind {selector}")
            }
        }
    }
}

impl Error for DecodeError {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LoadError {
    Decode(DecodeError),
    Verify(VerifyError),
}

impl fmt::Display for LoadError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Decode(error) => error.fmt(formatter),
            Self::Verify(error) => error.fmt(formatter),
        }
    }
}

impl Error for LoadError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Decode(error) => Some(error),
            Self::Verify(error) => Some(error),
        }
    }
}

/// Strictly decodes untrusted bytes. Every length is checked before allocation;
/// semantic validity remains represented by the `Unverified` typestate.
///
/// # Errors
/// Returns the first malformed, noncanonical, or over-limit byte encountered,
/// or trailing bytes after a complete module.
pub fn decode(bytes: &[u8], limits: &DecodeLimits) -> Result<Module<Unverified>, DecodeError> {
    if bytes.len() > limits.max_bytes {
        return Err(DecodeError {
            offset: 0,
            kind: DecodeErrorKind::InputLimitExceeded {
                limit: limits.max_bytes,
                actual: bytes.len(),
            },
        });
    }
    let mut decoder = Decoder {
        bytes,
        offset: 0,
        limits,
        total_instructions: 0,
    };
    let module = decoder.module()?;
    if decoder.offset != bytes.len() {
        return Err(DecodeError {
            offset: decoder.offset,
            kind: DecodeErrorKind::TrailingBytes {
                count: bytes.len() - decoder.offset,
            },
        });
    }
    Ok(module)
}

/// Decodes and verifies in one boundary operation.
///
/// # Errors
/// Returns [`LoadError::Decode`] for malformed bytes or [`LoadError::Verify`]
/// for a structurally invalid module.
pub fn decode_verified(bytes: &[u8], limits: &DecodeLimits) -> Result<Module<Verified>, LoadError> {
    decode(bytes, limits)
        .map_err(LoadError::Decode)?
        .verify()
        .map_err(LoadError::Verify)
}

struct Decoder<'a> {
    bytes: &'a [u8],
    offset: usize,
    limits: &'a DecodeLimits,
    total_instructions: u64,
}

impl<'a> Decoder<'a> {
    fn module(&mut self) -> Result<Module<Unverified>, DecodeError> {
        for expected in MAGIC {
            let at = self.offset;
            let actual = self.byte()?;
            if actual != expected {
                return Err(self.error(at, DecodeErrorKind::BadMagic { expected, actual }));
            }
        }
        let version_at = self.offset;
        let version = self.byte()?;
        if version != FORMAT_VERSION {
            return Err(self.error(version_at, DecodeErrorKind::UnsupportedVersion { version }));
        }

        let constant_count = self.bounded("constant count", self.limits.max_constants)?;
        let mut constants = Vec::with_capacity(self.cap(constant_count));
        for _ in 0..constant_count {
            constants.push(self.constant()?);
        }

        let function_count = self.bounded("function count", self.limits.max_functions)?;
        let entry = FunctionId::new(self.leb128()?);
        let mut functions = Vec::with_capacity(self.cap(function_count));
        for _ in 0..function_count {
            functions.push(self.function()?);
        }
        Ok(Module::new(constants, functions, entry))
    }

    fn constant(&mut self) -> Result<Constant, DecodeError> {
        let tag_at = self.offset;
        match self.byte()? {
            0 => {
                let number_at = self.offset;
                let bits = u64::from_le_bytes(self.exact::<8>()?);
                NumberBits::from_wire(bits)
                    .map(Constant::Number)
                    .ok_or_else(|| {
                        self.error(number_at, DecodeErrorKind::NonCanonicalNumber { bits })
                    })
            }
            1 => Ok(Constant::Int32(i32::from_le_bytes(self.exact::<4>()?))),
            2 => Ok(Constant::String(self.string()?)),
            3 => Ok(Constant::Boolean(false)),
            4 => Ok(Constant::Boolean(true)),
            5 => Ok(Constant::Null),
            6 => Ok(Constant::Undefined),
            7 => {
                let start = self.offset;
                let text = self.text()?;
                BigIntLiteral::new(text)
                    .map(Constant::BigInt)
                    .ok_or_else(|| self.error(start, DecodeErrorKind::InvalidBigInt))
            }
            tag => Err(self.error(tag_at, DecodeErrorKind::InvalidConstantTag { tag })),
        }
    }

    fn string(&mut self) -> Result<EcmaString, DecodeError> {
        let unit_count = self.bounded("string unit count", self.limits.max_string_units)?;
        let byte_count = usize::try_from(unit_count)
            .ok()
            .and_then(|units| units.checked_mul(2))
            .ok_or_else(|| self.error(self.offset, DecodeErrorKind::UnexpectedEof))?;
        let bytes = self.slice(byte_count)?;
        Ok(EcmaString::from_le_bytes(bytes))
    }

    fn text(&mut self) -> Result<String, DecodeError> {
        let length = self.bounded("bigint byte length", self.limits.max_bigint_bytes)?;
        let start = self.offset;
        let bytes = self.slice(length as usize)?;
        let value = std::str::from_utf8(bytes)
            .map_err(|_| self.error(start, DecodeErrorKind::InvalidUtf8))?;
        Ok(value.to_owned())
    }

    fn function(&mut self) -> Result<Function, DecodeError> {
        let name = match self.leb128()? {
            0 => None,
            encoded => Some(ConstantId::new(encoded - 1)),
        };
        let capture_count = self.bounded("capture count", self.limits.max_capture_count)?;
        let parameter_count = self.bounded("parameter count", self.limits.max_parameter_count)?;
        let register_count = self.bounded("register count", self.limits.max_register_count)?;
        let flags_at = self.offset;
        let flags_bits = self.byte()?;
        let flags = FunctionFlags::from_bits(flags_bits).ok_or_else(|| {
            self.error(
                flags_at,
                DecodeErrorKind::InvalidFunctionFlags { bits: flags_bits },
            )
        })?;
        let instruction_at = self.offset;
        let instruction_count = self.bounded(
            "instruction count",
            self.limits.max_instructions_per_function,
        )?;
        self.total_instructions += u64::from(instruction_count);
        if self.total_instructions > self.limits.max_total_instructions {
            return Err(self.error(
                instruction_at,
                DecodeErrorKind::LimitExceeded {
                    field: "total instruction count",
                    limit: self.limits.max_total_instructions,
                    actual: self.total_instructions,
                },
            ));
        }
        let mut code = Vec::with_capacity(self.cap(instruction_count));
        for _ in 0..instruction_count {
            code.push(self.instruction()?);
        }

        let handler_count = self.bounded("handler count", self.limits.max_handlers_per_function)?;
        let mut handlers = Vec::with_capacity(self.cap(handler_count));
        for _ in 0..handler_count {
            handlers.push(ExceptionHandler {
                start: Pc::new(self.leb128()?),
                end: Pc::new(self.leb128()?),
                handler: Pc::new(self.leb128()?),
                catch_register: Register::new(self.leb128()?),
            });
        }
        Ok(Function::new(
            name,
            capture_count,
            parameter_count,
            register_count,
            flags,
            code,
            handlers,
        ))
    }

    fn instruction(&mut self) -> Result<Instruction, DecodeError> {
        let opcode_at = self.offset;
        match self.byte()? {
            0 => Ok(Instruction::LoadConst {
                dst: Register::new(self.leb128()?),
                constant: ConstantId::new(self.leb128()?),
            }),
            1 => Ok(Instruction::Move {
                dst: Register::new(self.leb128()?),
                src: Register::new(self.leb128()?),
            }),
            2 => Ok(Instruction::Unary {
                dst: Register::new(self.leb128()?),
                op: self.unary_op()?,
                operand: Register::new(self.leb128()?),
            }),
            3 => Ok(Instruction::Binary {
                dst: Register::new(self.leb128()?),
                op: self.binary_op()?,
                left: Register::new(self.leb128()?),
                right: Register::new(self.leb128()?),
            }),
            4 => Ok(Instruction::CreateObject {
                dst: Register::new(self.leb128()?),
            }),
            5 => Ok(Instruction::CreateArray {
                dst: Register::new(self.leb128()?),
            }),
            6 => Ok(Instruction::CreateClosure {
                dst: Register::new(self.leb128()?),
                function: FunctionId::new(self.leb128()?),
                captures: Register::new(self.leb128()?),
            }),
            7 => Ok(Instruction::GetProperty {
                dst: Register::new(self.leb128()?),
                object: Register::new(self.leb128()?),
                key: Register::new(self.leb128()?),
            }),
            8 => Ok(Instruction::SetProperty {
                object: Register::new(self.leb128()?),
                key: Register::new(self.leb128()?),
                value: Register::new(self.leb128()?),
            }),
            9 => Ok(Instruction::DeleteProperty {
                dst: Register::new(self.leb128()?),
                object: Register::new(self.leb128()?),
                key: Register::new(self.leb128()?),
            }),
            10 => Ok(Instruction::DefineAccessor {
                object: Register::new(self.leb128()?),
                key: Register::new(self.leb128()?),
                accessor: Register::new(self.leb128()?),
                kind: self.accessor_kind()?,
            }),
            11 => Ok(Instruction::Call {
                dst: Register::new(self.leb128()?),
                callee: Register::new(self.leb128()?),
                this_value: Register::new(self.leb128()?),
                arguments: Register::new(self.leb128()?),
            }),
            12 => Ok(Instruction::Construct {
                dst: Register::new(self.leb128()?),
                callee: Register::new(self.leb128()?),
                arguments: Register::new(self.leb128()?),
            }),
            13 => Ok(Instruction::LoadGlobal {
                dst: Register::new(self.leb128()?),
                name: ConstantId::new(self.leb128()?),
            }),
            14 => Ok(Instruction::StoreGlobal {
                name: ConstantId::new(self.leb128()?),
                value: Register::new(self.leb128()?),
            }),
            15 => Ok(Instruction::TypeOfGlobal {
                dst: Register::new(self.leb128()?),
                name: ConstantId::new(self.leb128()?),
            }),
            16 => Ok(Instruction::LoadThis {
                dst: Register::new(self.leb128()?),
            }),
            17 => Ok(Instruction::LoadArguments {
                dst: Register::new(self.leb128()?),
            }),
            18 => Ok(Instruction::LoadNewTarget {
                dst: Register::new(self.leb128()?),
            }),
            19 => Ok(Instruction::ArrayPush {
                array: Register::new(self.leb128()?),
                value: Register::new(self.leb128()?),
            }),
            20 => Ok(Instruction::ArrayExtend {
                array: Register::new(self.leb128()?),
                iterable: Register::new(self.leb128()?),
            }),
            21 => Ok(Instruction::ObjectSpread {
                target: Register::new(self.leb128()?),
                source: Register::new(self.leb128()?),
            }),
            22 => Ok(Instruction::SetPrototype {
                object: Register::new(self.leb128()?),
                prototype: Register::new(self.leb128()?),
            }),
            23 => Ok(Instruction::CreatePrivateName {
                dst: Register::new(self.leb128()?),
                description: ConstantId::new(self.leb128()?),
            }),
            24 => Ok(Instruction::CreateRegExp {
                dst: Register::new(self.leb128()?),
                pattern: ConstantId::new(self.leb128()?),
                flags: ConstantId::new(self.leb128()?),
            }),
            25 => Ok(Instruction::GetIterator {
                dst: Register::new(self.leb128()?),
                src: Register::new(self.leb128()?),
                kind: self.iterator_kind()?,
            }),
            26 => Ok(Instruction::IteratorNext {
                done: Register::new(self.leb128()?),
                value: Register::new(self.leb128()?),
                iterator: Register::new(self.leb128()?),
            }),
            27 => Ok(Instruction::Jump {
                target: Pc::new(self.leb128()?),
            }),
            28 => Ok(Instruction::JumpIfTrue {
                condition: Register::new(self.leb128()?),
                target: Pc::new(self.leb128()?),
            }),
            29 => Ok(Instruction::JumpIfFalse {
                condition: Register::new(self.leb128()?),
                target: Pc::new(self.leb128()?),
            }),
            30 => Ok(Instruction::Return {
                value: Register::new(self.leb128()?),
            }),
            31 => Ok(Instruction::Throw {
                value: Register::new(self.leb128()?),
            }),
            32 => Ok(Instruction::Suspend {
                dst: Register::new(self.leb128()?),
                src: Register::new(self.leb128()?),
                resume: Pc::new(self.leb128()?),
                mode: Register::new(self.leb128()?),
            }),
            33 => Ok(Instruction::Import {
                dst: Register::new(self.leb128()?),
                specifier: ConstantId::new(self.leb128()?),
            }),
            34 => Ok(Instruction::Export {
                name: ConstantId::new(self.leb128()?),
                src: Register::new(self.leb128()?),
            }),
            35 => Ok(Instruction::Halt),
            36 => Ok(Instruction::CreateCell {
                dst: Register::new(self.leb128()?),
            }),
            37 => Ok(Instruction::Await {
                dst: Register::new(self.leb128()?),
                src: Register::new(self.leb128()?),
                resume: Pc::new(self.leb128()?),
            }),
            38 => Ok(Instruction::IteratorStep {
                dst: Register::new(self.leb128()?),
                iterator: Register::new(self.leb128()?),
            }),
            39 => Ok(Instruction::IteratorResult {
                done: Register::new(self.leb128()?),
                value: Register::new(self.leb128()?),
                result: Register::new(self.leb128()?),
            }),
            40 => Ok(Instruction::IteratorClose {
                result: Register::new(self.leb128()?),
                called: Register::new(self.leb128()?),
                iterator: Register::new(self.leb128()?),
                mode: self.iterator_close_mode()?,
            }),
            41 => Ok(Instruction::RequireCloseResult {
                result: Register::new(self.leb128()?),
                called: Register::new(self.leb128()?),
            }),
            42 => Ok(Instruction::ToObject {
                dst: Register::new(self.leb128()?),
                src: Register::new(self.leb128()?),
            }),
            43 => Ok(Instruction::ImportDynamic {
                dst: Register::new(self.leb128()?),
                specifier: Register::new(self.leb128()?),
            }),
            44 => Ok(Instruction::LoadImportMeta {
                dst: Register::new(self.leb128()?),
            }),
            45 => Ok(Instruction::DisposeCapture {
                method: Register::new(self.leb128()?),
                kind: Register::new(self.leb128()?),
                src: Register::new(self.leb128()?),
                hint: self.dispose_hint()?,
            }),
            46 => Ok(Instruction::SuppressError {
                dst: Register::new(self.leb128()?),
                error: Register::new(self.leb128()?),
                suppressed: Register::new(self.leb128()?),
            }),
            47 => Ok(Instruction::ConstructWithNewTarget {
                dst: Register::new(self.leb128()?),
                callee: Register::new(self.leb128()?),
                new_target: Register::new(self.leb128()?),
                arguments: Register::new(self.leb128()?),
            }),
            48 => Ok(Instruction::DefineDataProperty {
                object: Register::new(self.leb128()?),
                key: Register::new(self.leb128()?),
                value: Register::new(self.leb128()?),
            }),
            49 => Ok(Instruction::LoadOwnDescriptorSlot {
                dst: Register::new(self.leb128()?),
                object: Register::new(self.leb128()?),
                key: Register::new(self.leb128()?),
                slot: self.descriptor_slot()?,
            }),
            50 => Ok(Instruction::DefineOwnDescriptorSlot {
                object: Register::new(self.leb128()?),
                key: Register::new(self.leb128()?),
                src: Register::new(self.leb128()?),
                slot: self.descriptor_slot()?,
            }),
            51 => Ok(Instruction::WithHasBinding {
                dst: Register::new(self.leb128()?),
                object: Register::new(self.leb128()?),
                key: Register::new(self.leb128()?),
            }),
            opcode if (isa::FIRST_EXTENSION_TAG..isa::EXTENSION_TAG_END).contains(&opcode) => {
                let (instruction, next) = isa::decode_from_tag(opcode, self.bytes, self.offset)?;
                self.offset = next;
                Ok(instruction.into())
            }
            opcode => Err(self.error(opcode_at, DecodeErrorKind::InvalidOpcode { opcode })),
        }
    }

    fn unary_op(&mut self) -> Result<UnaryOp, DecodeError> {
        let at = self.offset;
        let tag = self.byte()?;
        UnaryOp::from_u8(tag).ok_or_else(|| self.error(at, DecodeErrorKind::InvalidUnaryOp { tag }))
    }

    fn binary_op(&mut self) -> Result<BinaryOp, DecodeError> {
        let at = self.offset;
        let tag = self.byte()?;
        BinaryOp::from_u8(tag)
            .ok_or_else(|| self.error(at, DecodeErrorKind::InvalidBinaryOp { tag }))
    }

    fn iterator_kind(&mut self) -> Result<IteratorKind, DecodeError> {
        let at = self.offset;
        let tag = self.byte()?;
        IteratorKind::from_u8(tag)
            .ok_or_else(|| self.error(at, DecodeErrorKind::InvalidIteratorKind { tag }))
    }

    fn iterator_close_mode(&mut self) -> Result<IteratorCloseMode, DecodeError> {
        let at = self.offset;
        let tag = self.byte()?;
        IteratorCloseMode::from_u8(tag)
            .ok_or_else(|| self.error(at, DecodeErrorKind::InvalidIteratorCloseMode { tag }))
    }

    fn dispose_hint(&mut self) -> Result<DisposeHint, DecodeError> {
        let at = self.offset;
        let tag = self.byte()?;
        DisposeHint::from_u8(tag)
            .ok_or_else(|| self.error(at, DecodeErrorKind::InvalidDisposeHint { tag }))
    }

    fn accessor_kind(&mut self) -> Result<AccessorKind, DecodeError> {
        let at = self.offset;
        let tag = self.byte()?;
        AccessorKind::from_u8(tag)
            .ok_or_else(|| self.error(at, DecodeErrorKind::InvalidAccessorKind { tag }))
    }

    fn descriptor_slot(&mut self) -> Result<DescriptorSlot, DecodeError> {
        let at = self.offset;
        let tag = self.byte()?;
        DescriptorSlot::from_u8(tag)
            .ok_or_else(|| self.error(at, DecodeErrorKind::InvalidDescriptorSlot { tag }))
    }

    fn bounded(&mut self, field: &'static str, limit: u32) -> Result<u32, DecodeError> {
        let at = self.offset;
        let actual = self.leb128()?;
        if actual > limit {
            Err(self.error(
                at,
                DecodeErrorKind::LimitExceeded {
                    field,
                    limit: u64::from(limit),
                    actual: u64::from(actual),
                },
            ))
        } else {
            Ok(actual)
        }
    }

    /// Reads one canonical unsigned LEB128 `u32`. Rejects EOF mid-integer,
    /// overlong (trailing-zero) encodings, and values exceeding 32 bits.
    fn leb128(&mut self) -> Result<u32, DecodeError> {
        let start = self.offset;
        crate::program::read_leb128(self.bytes, &mut self.offset).map_err(|error| {
            // EOF is reported where the missing byte belongs (current offset);
            // overflow and noncanonical encoding are reported at the integer's
            // start, matching the original decoder's diagnostics.
            let offset = match error {
                crate::program::Leb128Error::UnexpectedEof => self.offset,
                crate::program::Leb128Error::IntegerOverflow
                | crate::program::Leb128Error::NonCanonicalInteger => start,
            };
            let kind = match error {
                crate::program::Leb128Error::UnexpectedEof => DecodeErrorKind::UnexpectedEof,
                crate::program::Leb128Error::IntegerOverflow => DecodeErrorKind::IntegerOverflow,
                crate::program::Leb128Error::NonCanonicalInteger => {
                    DecodeErrorKind::NonCanonicalInteger
                }
            };
            self.error(offset, kind)
        })
    }

    fn cap(&self, count: u32) -> usize {
        // Each element consumes at least one wire byte, so the remaining input
        // caps how many can actually be present; never pre-allocate beyond it.
        (count as usize).min(self.bytes.len().saturating_sub(self.offset))
    }

    fn byte(&mut self) -> Result<u8, DecodeError> {
        let Some(byte) = self.bytes.get(self.offset).copied() else {
            return Err(self.error(self.offset, DecodeErrorKind::UnexpectedEof));
        };
        self.offset += 1;
        Ok(byte)
    }

    fn exact<const N: usize>(&mut self) -> Result<[u8; N], DecodeError> {
        let bytes = self.slice(N)?;
        let mut result = [0; N];
        result.copy_from_slice(bytes);
        Ok(result)
    }

    fn slice(&mut self, length: usize) -> Result<&'a [u8], DecodeError> {
        let source: &'a [u8] = self.bytes;
        let Some(end) = self.offset.checked_add(length) else {
            return Err(self.error(self.offset, DecodeErrorKind::UnexpectedEof));
        };
        let Some(bytes) = source.get(self.offset..end) else {
            return Err(self.error(self.offset, DecodeErrorKind::UnexpectedEof));
        };
        self.offset = end;
        Ok(bytes)
    }

    const fn error(&self, offset: usize, kind: DecodeErrorKind) -> DecodeError {
        DecodeError { offset, kind }
    }
}

fn write_u32(value: u32, output: &mut Vec<u8>) {
    let mut remaining = value;
    loop {
        let byte = (remaining & 0x7f) as u8;
        remaining >>= 7;
        if remaining == 0 {
            output.push(byte);
            return;
        }
        output.push(byte | 0x80);
    }
}

fn encode_constant(constant: &Constant, output: &mut Vec<u8>) {
    match constant {
        Constant::Number(bits) => {
            output.push(0);
            output.extend_from_slice(&bits.bits().to_le_bytes());
        }
        Constant::Int32(value) => {
            output.push(1);
            output.extend_from_slice(&value.to_le_bytes());
        }
        Constant::String(value) => {
            output.push(2);
            write_string(value, output);
        }
        Constant::Boolean(false) => output.push(3),
        Constant::Boolean(true) => output.push(4),
        Constant::Null => output.push(5),
        Constant::Undefined => output.push(6),
        Constant::BigInt(value) => {
            output.push(7);
            write_text(value.as_str(), output);
        }
    }
}

fn write_string(value: &EcmaString, output: &mut Vec<u8>) {
    write_u32(value.len_units() as u32, output);
    for unit in value.as_units() {
        output.extend_from_slice(&unit.to_le_bytes());
    }
}

fn write_text(value: &str, output: &mut Vec<u8>) {
    write_u32(value.len() as u32, output);
    output.extend_from_slice(value.as_bytes());
}

fn encode_function(function: &Function, output: &mut Vec<u8>) {
    write_u32(function.name.map_or(0, |name| name.get() + 1), output);
    write_u32(function.capture_count, output);
    write_u32(function.parameter_count, output);
    write_u32(function.register_count, output);
    output.push(function.flags.to_bits());
    write_u32(function.code.len() as u32, output);
    for instruction in &function.code {
        encode_instruction(*instruction, output);
    }
    write_u32(function.handlers.len() as u32, output);
    for handler in &function.handlers {
        write_u32(handler.start.get(), output);
        write_u32(handler.end.get(), output);
        write_u32(handler.handler.get(), output);
        write_u32(handler.catch_register.get(), output);
    }
}

fn encode_instruction(instruction: Instruction, output: &mut Vec<u8>) {
    if let Some(extension) = instruction.extension() {
        extension.encode(output);
        return;
    }
    match instruction {
        Instruction::LoadConst { dst, constant } => {
            output.push(0);
            write_u32(dst.get(), output);
            write_u32(constant.get(), output);
        }
        Instruction::Move { dst, src } => {
            output.push(1);
            write_u32(dst.get(), output);
            write_u32(src.get(), output);
        }
        Instruction::Unary { dst, op, operand } => {
            output.push(2);
            write_u32(dst.get(), output);
            output.push(op.to_u8());
            write_u32(operand.get(), output);
        }
        Instruction::Binary {
            dst,
            op,
            left,
            right,
        } => {
            output.push(3);
            write_u32(dst.get(), output);
            output.push(op.to_u8());
            write_u32(left.get(), output);
            write_u32(right.get(), output);
        }
        Instruction::CreateObject { dst } => {
            output.push(4);
            write_u32(dst.get(), output);
        }
        Instruction::CreateArray { dst } => {
            output.push(5);
            write_u32(dst.get(), output);
        }
        Instruction::CreateClosure {
            dst,
            function,
            captures,
        } => {
            output.push(6);
            write_u32(dst.get(), output);
            write_u32(function.get(), output);
            write_u32(captures.get(), output);
        }
        Instruction::GetProperty { dst, object, key } => {
            output.push(7);
            write_u32(dst.get(), output);
            write_u32(object.get(), output);
            write_u32(key.get(), output);
        }
        Instruction::SetProperty { object, key, value } => {
            output.push(8);
            write_u32(object.get(), output);
            write_u32(key.get(), output);
            write_u32(value.get(), output);
        }
        Instruction::DeleteProperty { dst, object, key } => {
            output.push(9);
            write_u32(dst.get(), output);
            write_u32(object.get(), output);
            write_u32(key.get(), output);
        }
        Instruction::DefineAccessor {
            object,
            key,
            accessor,
            kind,
        } => {
            output.push(10);
            write_u32(object.get(), output);
            write_u32(key.get(), output);
            write_u32(accessor.get(), output);
            output.push(kind.to_u8());
        }
        Instruction::Call {
            dst,
            callee,
            this_value,
            arguments,
        } => {
            output.push(11);
            write_u32(dst.get(), output);
            write_u32(callee.get(), output);
            write_u32(this_value.get(), output);
            write_u32(arguments.get(), output);
        }
        Instruction::Construct {
            dst,
            callee,
            arguments,
        } => {
            output.push(12);
            write_u32(dst.get(), output);
            write_u32(callee.get(), output);
            write_u32(arguments.get(), output);
        }
        Instruction::LoadGlobal { dst, name } => {
            output.push(13);
            write_u32(dst.get(), output);
            write_u32(name.get(), output);
        }
        Instruction::StoreGlobal { name, value } => {
            output.push(14);
            write_u32(name.get(), output);
            write_u32(value.get(), output);
        }
        Instruction::TypeOfGlobal { dst, name } => {
            output.push(15);
            write_u32(dst.get(), output);
            write_u32(name.get(), output);
        }
        Instruction::LoadThis { dst } => {
            output.push(16);
            write_u32(dst.get(), output);
        }
        Instruction::LoadArguments { dst } => {
            output.push(17);
            write_u32(dst.get(), output);
        }
        Instruction::LoadNewTarget { dst } => {
            output.push(18);
            write_u32(dst.get(), output);
        }
        Instruction::ArrayPush { array, value } => {
            output.push(19);
            write_u32(array.get(), output);
            write_u32(value.get(), output);
        }
        Instruction::ArrayExtend { array, iterable } => {
            output.push(20);
            write_u32(array.get(), output);
            write_u32(iterable.get(), output);
        }
        Instruction::ObjectSpread { target, source } => {
            output.push(21);
            write_u32(target.get(), output);
            write_u32(source.get(), output);
        }
        Instruction::SetPrototype { object, prototype } => {
            output.push(22);
            write_u32(object.get(), output);
            write_u32(prototype.get(), output);
        }
        Instruction::CreatePrivateName { dst, description } => {
            output.push(23);
            write_u32(dst.get(), output);
            write_u32(description.get(), output);
        }
        Instruction::CreateRegExp {
            dst,
            pattern,
            flags,
        } => {
            output.push(24);
            write_u32(dst.get(), output);
            write_u32(pattern.get(), output);
            write_u32(flags.get(), output);
        }
        Instruction::GetIterator { dst, src, kind } => {
            output.push(25);
            write_u32(dst.get(), output);
            write_u32(src.get(), output);
            output.push(kind.to_u8());
        }
        Instruction::IteratorNext {
            done,
            value,
            iterator,
        } => {
            output.push(26);
            write_u32(done.get(), output);
            write_u32(value.get(), output);
            write_u32(iterator.get(), output);
        }
        Instruction::Jump { target } => {
            output.push(27);
            write_u32(target.get(), output);
        }
        Instruction::JumpIfTrue { condition, target } => {
            output.push(28);
            write_u32(condition.get(), output);
            write_u32(target.get(), output);
        }
        Instruction::JumpIfFalse { condition, target } => {
            output.push(29);
            write_u32(condition.get(), output);
            write_u32(target.get(), output);
        }
        Instruction::Return { value } => {
            output.push(30);
            write_u32(value.get(), output);
        }
        Instruction::Throw { value } => {
            output.push(31);
            write_u32(value.get(), output);
        }
        Instruction::Suspend {
            dst,
            src,
            resume,
            mode,
        } => {
            output.push(32);
            write_u32(dst.get(), output);
            write_u32(src.get(), output);
            write_u32(resume.get(), output);
            write_u32(mode.get(), output);
        }
        Instruction::Import { dst, specifier } => {
            output.push(33);
            write_u32(dst.get(), output);
            write_u32(specifier.get(), output);
        }
        Instruction::ImportDynamic { dst, specifier } => {
            output.push(43);
            write_u32(dst.get(), output);
            write_u32(specifier.get(), output);
        }
        Instruction::Export { name, src } => {
            output.push(34);
            write_u32(name.get(), output);
            write_u32(src.get(), output);
        }
        Instruction::Halt => output.push(35),
        Instruction::CreateCell { dst } => {
            output.push(36);
            write_u32(dst.get(), output);
        }
        Instruction::Await { dst, src, resume } => {
            output.push(37);
            write_u32(dst.get(), output);
            write_u32(src.get(), output);
            write_u32(resume.get(), output);
        }
        Instruction::IteratorStep { dst, iterator } => {
            output.push(38);
            write_u32(dst.get(), output);
            write_u32(iterator.get(), output);
        }
        Instruction::IteratorResult {
            done,
            value,
            result,
        } => {
            output.push(39);
            write_u32(done.get(), output);
            write_u32(value.get(), output);
            write_u32(result.get(), output);
        }
        Instruction::IteratorClose {
            result,
            called,
            iterator,
            mode,
        } => {
            output.push(40);
            write_u32(result.get(), output);
            write_u32(called.get(), output);
            write_u32(iterator.get(), output);
            output.push(mode.to_u8());
        }
        Instruction::RequireCloseResult { result, called } => {
            output.push(41);
            write_u32(result.get(), output);
            write_u32(called.get(), output);
        }
        Instruction::DisposeCapture {
            method,
            kind,
            src,
            hint,
        } => {
            output.push(45);
            write_u32(method.get(), output);
            write_u32(kind.get(), output);
            write_u32(src.get(), output);
            output.push(hint.to_u8());
        }
        Instruction::SuppressError {
            dst,
            error,
            suppressed,
        } => {
            output.push(46);
            write_u32(dst.get(), output);
            write_u32(error.get(), output);
            write_u32(suppressed.get(), output);
        }
        Instruction::ToObject { dst, src } => {
            output.push(42);
            write_u32(dst.get(), output);
            write_u32(src.get(), output);
        }
        Instruction::LoadImportMeta { dst } => {
            output.push(44);
            write_u32(dst.get(), output);
        }
        Instruction::ConstructWithNewTarget {
            dst,
            callee,
            new_target,
            arguments,
        } => {
            output.push(47);
            write_u32(dst.get(), output);
            write_u32(callee.get(), output);
            write_u32(new_target.get(), output);
            write_u32(arguments.get(), output);
        }
        Instruction::DefineDataProperty { object, key, value } => {
            output.push(48);
            write_u32(object.get(), output);
            write_u32(key.get(), output);
            write_u32(value.get(), output);
        }
        Instruction::LoadOwnDescriptorSlot {
            dst,
            object,
            key,
            slot,
        } => {
            output.push(49);
            write_u32(dst.get(), output);
            write_u32(object.get(), output);
            write_u32(key.get(), output);
            output.push(slot.to_u8());
        }
        Instruction::DefineOwnDescriptorSlot {
            object,
            key,
            src,
            slot,
        } => {
            output.push(50);
            write_u32(object.get(), output);
            write_u32(key.get(), output);
            write_u32(src.get(), output);
            output.push(slot.to_u8());
        }
        Instruction::WithHasBinding { dst, object, key } => {
            output.push(51);
            write_u32(dst.get(), output);
            write_u32(object.get(), output);
            write_u32(key.get(), output);
        }
        Instruction::GetSuper { .. }
        | Instruction::SetSuper { .. }
        | Instruction::ImportAttributes { .. }
        | Instruction::ImportDynamicAttributes { .. }
        | Instruction::CopyDataProperties { .. }
        | Instruction::GetTemplateObject { .. }
        | Instruction::RequireGlobalBinding { .. }
        | Instruction::ThrowIntrinsicError { .. } => unreachable!("handled above"),
    }
}

#[cfg(test)]
mod tests;
