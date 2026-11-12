//! Canonical typed-array kinds, length slots, and numeric conversions.
//!
//! A typed array is a view over an ArrayBuffer or SharedArrayBuffer backing
//! store. This module never owns a second byte vector.
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::sync::Arc;

use super::arraybuffer::{ArrayBufferHandle, SharedBlock};
use super::{
    allocate_string, builtin_property, define_data, define_frozen_data, heap_index,
    install_constructor_function, install_function, range_error, type_error,
};
use crate::intrinsics::builtins::bigint::{self, BigIntValue};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{
    EvalFailure, HeapEntry, Host, IterationKind, Machine, Property, PropertyKey, PropertyMap,
};
use bamts_bytecode::{EcmaString, EcmaStringBuilder};
use bamts_native::{Decoded, Value};

/// Number of typed-array element kinds in the ES2025 surface.
pub(crate) const KIND_COUNT: usize = 12;

/// A typed-array element representation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub(crate) enum ElementKind {
    Int8,
    Uint8,
    Uint8Clamped,
    Int16,
    Uint16,
    Int32,
    Uint32,
    Float16,
    Float32,
    Float64,
    BigInt64,
    BigUint64,
}

/// Static properties of one [`ElementKind`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ElementKindInfo {
    pub(crate) name: &'static str,
    pub(crate) element_size: usize,
    pub(crate) is_bigint: bool,
}

impl ElementKind {
    pub(crate) const ALL: [Self; KIND_COUNT] = [
        Self::Int8,
        Self::Uint8,
        Self::Uint8Clamped,
        Self::Int16,
        Self::Uint16,
        Self::Int32,
        Self::Uint32,
        Self::Float16,
        Self::Float32,
        Self::Float64,
        Self::BigInt64,
        Self::BigUint64,
    ];

    pub(crate) const fn info(self) -> ElementKindInfo {
        match self {
            Self::Int8 => ElementKindInfo::new("Int8Array", 1, false),
            Self::Uint8 => ElementKindInfo::new("Uint8Array", 1, false),
            Self::Uint8Clamped => ElementKindInfo::new("Uint8ClampedArray", 1, false),
            Self::Int16 => ElementKindInfo::new("Int16Array", 2, false),
            Self::Uint16 => ElementKindInfo::new("Uint16Array", 2, false),
            Self::Int32 => ElementKindInfo::new("Int32Array", 4, false),
            Self::Uint32 => ElementKindInfo::new("Uint32Array", 4, false),
            Self::Float16 => ElementKindInfo::new("Float16Array", 2, false),
            Self::Float32 => ElementKindInfo::new("Float32Array", 4, false),
            Self::Float64 => ElementKindInfo::new("Float64Array", 8, false),
            Self::BigInt64 => ElementKindInfo::new("BigInt64Array", 8, true),
            Self::BigUint64 => ElementKindInfo::new("BigUint64Array", 8, true),
        }
    }

    pub(crate) const fn name(self) -> &'static str {
        self.info().name
    }

    pub(crate) const fn element_size(self) -> usize {
        self.info().element_size
    }

    pub(crate) const fn is_bigint(self) -> bool {
        self.info().is_bigint
    }
}

impl ElementKindInfo {
    const fn new(name: &'static str, element_size: usize, is_bigint: bool) -> Self {
        Self {
            name,
            element_size,
            is_bigint,
        }
    }
}

/// A fixed view length or the ES2025 auto-length marker.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum LengthSlot {
    Fixed(usize),
    Auto,
}

/// ES `ToUint8Clamp`, including ties-to-even.
pub(crate) fn to_uint8_clamp(number: f64) -> u8 {
    if number.is_nan() || number <= 0.0 {
        return 0;
    }
    if number >= 255.0 {
        return 255;
    }
    let floor = number.floor();
    let fraction = number - floor;
    if fraction > 0.5 || (fraction == 0.5 && (floor as u64) & 1 == 1) {
        floor as u8 + 1
    } else {
        floor as u8
    }
}

/// ES modulo conversion for unsigned integer element kinds.
pub(crate) fn to_uint_mod(number: f64, bits: u32) -> u64 {
    debug_assert!(matches!(bits, 8 | 16 | 32));
    if !number.is_finite() || number == 0.0 {
        return 0;
    }
    let modulus = (1_u64 << bits) as f64;
    number.trunc().rem_euclid(modulus) as u64
}

/// ES modulo conversion for signed integer element kinds.
pub(crate) fn to_int_mod(number: f64, bits: u32) -> i64 {
    let unsigned = to_uint_mod(number, bits);
    let sign = 1_u64 << (bits - 1);
    if unsigned >= sign {
        (unsigned as i64) - (1_i64 << bits)
    } else {
        unsigned as i64
    }
}

/// Converts a Number to IEEE-754 binary16 with round-to-nearest, ties-to-even.
pub(crate) fn f64_to_f16_bits(number: f64) -> u16 {
    let bits = number.to_bits();
    let sign = ((bits >> 48) & 0x8000) as u16;
    let exponent = ((bits >> 52) & 0x7ff) as i32;
    let fraction = bits & ((1_u64 << 52) - 1);

    if exponent == 0x7ff {
        return if fraction == 0 {
            sign | 0x7c00
        } else {
            sign | 0x7e00
        };
    }
    if exponent == 0 {
        return sign;
    }

    let unbiased = exponent - 1023;
    if unbiased > 15 {
        return sign | 0x7c00;
    }
    if unbiased < -25 {
        return sign;
    }

    let significand = (1_u64 << 52) | fraction;
    if unbiased >= -14 {
        let rounded = round_shift_ties_even(significand, 42);
        if rounded == 0x800 {
            let next_exponent = unbiased + 16;
            return if next_exponent >= 31 {
                sign | 0x7c00
            } else {
                sign | ((next_exponent as u16) << 10)
            };
        }
        return sign | (((unbiased + 15) as u16) << 10) | ((rounded as u16) & 0x03ff);
    }

    let rounded = round_shift_ties_even(significand, (28 - unbiased) as u32);
    sign | rounded as u16
}

/// Converts IEEE-754 binary16 bits to Number without changing signed zero.
pub(crate) fn f16_bits_to_f64(bits: u16) -> f64 {
    let negative = bits & 0x8000 != 0;
    let exponent = (bits >> 10) & 0x1f;
    let fraction = bits & 0x03ff;
    let magnitude = match (exponent, fraction) {
        (0, 0) => 0.0,
        (0, fraction) => f64::from(fraction) * 2_f64.powi(-24),
        (0x1f, 0) => f64::INFINITY,
        (0x1f, _) => f64::NAN,
        (exponent, fraction) => {
            (1.0 + f64::from(fraction) / 1024.0) * 2_f64.powi(i32::from(exponent) - 15)
        }
    };
    if negative { -magnitude } else { magnitude }
}

fn round_shift_ties_even(value: u64, shift: u32) -> u64 {
    if shift == 0 {
        return value;
    }
    if shift > 64 {
        return 0;
    }
    let quotient = if shift == 64 { 0 } else { value >> shift };
    let remainder_mask = if shift == 64 {
        u64::MAX
    } else {
        (1_u64 << shift) - 1
    };
    let remainder = value & remainder_mask;
    let halfway = 1_u64 << (shift - 1);
    quotient + u64::from(remainder > halfway || (remainder == halfway && quotient & 1 == 1))
}
/// The live bounds of a typed-array view.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ViewBounds {
    pub(crate) element_length: usize,
    pub(crate) byte_length: usize,
    pub(crate) detached: bool,
    pub(crate) out_of_bounds: bool,
}

impl ViewBounds {
    const fn inaccessible(detached: bool) -> Self {
        Self {
            element_length: 0,
            byte_length: 0,
            detached,
            out_of_bounds: true,
        }
    }
}

/// A typed-array backing store. Both brands expose the same byte operations.
#[derive(Clone, Debug)]
pub(crate) enum ViewBuffer {
    Array(ArrayBufferHandle),
    Shared(Arc<SharedBlock>),
}

impl ViewBuffer {
    pub(crate) fn from_value<H: Host>(
        machine: &Machine<'_, H>,
        value: Value,
    ) -> Result<Self, EvalFailure> {
        let Some(index) = machine.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
            return Err(type_error("TypedArray buffer is not an ArrayBuffer"));
        };
        match &machine.heap[index] {
            HeapEntry::ArrayBuffer { .. } => {
                Ok(Self::Array(ArrayBufferHandle::from_value(machine, value)?))
            }
            HeapEntry::SharedArrayBuffer { data, .. } => Ok(Self::Shared(Arc::clone(data))),
            _ => Err(type_error("TypedArray buffer is not an ArrayBuffer")),
        }
    }

    pub(crate) fn value_is_buffer<H: Host>(machine: &Machine<'_, H>, value: Value) -> bool {
        machine
            .runtime_slot(value)
            .ok()
            .flatten()
            .is_some_and(|index| {
                matches!(
                    machine.heap[index],
                    HeapEntry::ArrayBuffer { .. } | HeapEntry::SharedArrayBuffer { .. }
                )
            })
    }

    pub(crate) fn byte_length<H: Host>(
        &self,
        machine: &Machine<'_, H>,
    ) -> Result<usize, EvalFailure> {
        match self {
            Self::Array(buffer) => buffer.byte_length(machine),
            Self::Shared(buffer) => Ok(buffer.byte_length()),
        }
    }

    pub(crate) fn is_detached<H: Host>(&self, machine: &Machine<'_, H>) -> bool {
        match self {
            Self::Array(buffer) => buffer.is_detached(machine),
            Self::Shared(buffer) => buffer.is_detached(),
        }
    }

    pub(crate) fn is_resizable<H: Host>(
        &self,
        machine: &Machine<'_, H>,
    ) -> Result<bool, EvalFailure> {
        match self {
            Self::Array(buffer) => buffer.is_resizable(machine),
            Self::Shared(buffer) => Ok(buffer.is_growable()),
        }
    }

    pub(crate) fn with_bytes<H: Host, R>(
        &self,
        machine: &Machine<'_, H>,
        operation: impl FnOnce(&[u8]) -> R,
    ) -> Result<R, EvalFailure> {
        match self {
            Self::Array(buffer) => buffer.with_bytes(machine, operation),
            Self::Shared(buffer) => Ok(buffer.with_bytes(operation)),
        }
    }

    pub(crate) fn with_bytes_mut<H: Host, R>(
        &self,
        machine: &mut Machine<'_, H>,
        operation: impl FnOnce(&mut [u8]) -> R,
    ) -> Result<R, EvalFailure> {
        match self {
            Self::Array(buffer) => buffer.with_bytes_mut(machine, operation),
            Self::Shared(buffer) => Ok(buffer.with_bytes_mut(operation)),
        }
    }

    fn same_storage(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Array(left), Self::Array(right)) => left == right,
            (Self::Shared(left), Self::Shared(right)) => Arc::ptr_eq(left, right),
            _ => false,
        }
    }
}

#[derive(Clone, Copy)]
struct ViewFields {
    kind: ElementKind,
    buffer: Value,
    byte_offset: usize,
    byte_length: LengthSlot,
    array_length: LengthSlot,
}

fn view_fields<H: Host>(machine: &Machine<'_, H>, view: Value) -> Result<ViewFields, EvalFailure> {
    let Some(index) = machine.runtime_slot(view).map_err(EvalFailure::Runtime)? else {
        return Err(type_error(
            "TypedArray method called on incompatible receiver",
        ));
    };
    let HeapEntry::TypedArray {
        kind,
        buffer,
        byte_offset,
        byte_length,
        array_length,
        ..
    } = &machine.heap[index]
    else {
        return Err(type_error(
            "TypedArray method called on incompatible receiver",
        ));
    };
    Ok(ViewFields {
        kind: *kind,
        buffer: *buffer,
        byte_offset: *byte_offset,
        byte_length: *byte_length,
        array_length: *array_length,
    })
}
#[derive(Clone, Debug)]
pub(crate) struct TypedArraySnapshot {
    pub(crate) kind: ElementKind,
    pub(crate) buffer: ViewBuffer,
    pub(crate) byte_offset: usize,
    pub(crate) bounds: ViewBounds,
}

pub(crate) fn typed_array_snapshot<H: Host>(
    machine: &Machine<'_, H>,
    view: Value,
) -> Result<TypedArraySnapshot, EvalFailure> {
    let fields = view_fields(machine, view)?;
    Ok(TypedArraySnapshot {
        kind: fields.kind,
        buffer: ViewBuffer::from_value(machine, fields.buffer)?,
        byte_offset: fields.byte_offset,
        bounds: typed_array_bounds_for(machine, fields)?,
    })
}

pub(crate) fn typed_array_bounds<H: Host>(
    machine: &Machine<'_, H>,
    view: Value,
) -> Result<ViewBounds, EvalFailure> {
    let fields = view_fields(machine, view)?;
    typed_array_bounds_for(machine, fields)
}

fn typed_array_bounds_for<H: Host>(
    machine: &Machine<'_, H>,
    fields: ViewFields,
) -> Result<ViewBounds, EvalFailure> {
    let buffer = ViewBuffer::from_value(machine, fields.buffer)?;
    if buffer.is_detached(machine) {
        return Ok(ViewBounds::inaccessible(true));
    }
    let buffer_length = buffer.byte_length(machine)?;
    if fields.byte_offset > buffer_length {
        return Ok(ViewBounds::inaccessible(false));
    }
    let remaining = buffer_length - fields.byte_offset;
    let byte_length = match fields.byte_length {
        LengthSlot::Auto => remaining / fields.kind.element_size() * fields.kind.element_size(),
        LengthSlot::Fixed(length) if length <= remaining => length,
        LengthSlot::Fixed(_) => return Ok(ViewBounds::inaccessible(false)),
    };
    let element_length = match fields.array_length {
        LengthSlot::Auto => byte_length / fields.kind.element_size(),
        LengthSlot::Fixed(length)
            if length
                .checked_mul(fields.kind.element_size())
                .is_some_and(|required| required <= byte_length) =>
        {
            length
        }
        LengthSlot::Fixed(_) => return Ok(ViewBounds::inaccessible(false)),
    };
    Ok(ViewBounds {
        element_length,
        byte_length,
        detached: false,
        out_of_bounds: false,
    })
}

pub(crate) fn read_element<H: Host>(
    machine: &mut Machine<'_, H>,
    view: Value,
    element_index: usize,
) -> Result<Value, EvalFailure> {
    let fields = view_fields(machine, view)?;
    let bounds = typed_array_bounds_for(machine, fields)?;
    if bounds.out_of_bounds || element_index >= bounds.element_length {
        return Ok(Value::UNDEFINED);
    }
    let start = fields
        .byte_offset
        .checked_add(
            element_index
                .checked_mul(fields.kind.element_size())
                .ok_or_else(|| range_error("Invalid typed array index"))?,
        )
        .ok_or_else(|| range_error("Invalid typed array index"))?;
    let buffer = ViewBuffer::from_value(machine, fields.buffer)?;
    let mut storage = [0_u8; 8];
    buffer.with_bytes(machine, |bytes| {
        storage[..fields.kind.element_size()]
            .copy_from_slice(&bytes[start..start + fields.kind.element_size()]);
    })?;
    value_from_storage(machine, fields.kind, storage)
}
pub(crate) fn debug_elements<H: Host>(
    machine: &Machine<'_, H>,
    view: Value,
    limit: usize,
) -> Result<(ElementKind, usize, Vec<String>), EvalFailure> {
    let fields = view_fields(machine, view)?;
    let bounds = typed_array_bounds_for(machine, fields)?;
    let buffer = ViewBuffer::from_value(machine, fields.buffer)?;
    let take = bounds.element_length.min(limit);
    let mut values = Vec::with_capacity(take);
    buffer.with_bytes(machine, |bytes| {
        for index in 0..take {
            let start = fields.byte_offset + index * fields.kind.element_size();
            let mut storage = [0_u8; 8];
            storage[..fields.kind.element_size()]
                .copy_from_slice(&bytes[start..start + fields.kind.element_size()]);
            values.push(storage_to_string(fields.kind, storage));
        }
    })?;
    Ok((fields.kind, bounds.element_length, values))
}

fn storage_to_string(kind: ElementKind, storage: [u8; 8]) -> String {
    match kind {
        ElementKind::Int8 => i8::from_le_bytes([storage[0]]).to_string(),
        ElementKind::Uint8 | ElementKind::Uint8Clamped => storage[0].to_string(),
        ElementKind::Int16 => i16::from_le_bytes(storage[..2].try_into().unwrap()).to_string(),
        ElementKind::Uint16 => u16::from_le_bytes(storage[..2].try_into().unwrap()).to_string(),
        ElementKind::Int32 => i32::from_le_bytes(storage[..4].try_into().unwrap()).to_string(),
        ElementKind::Uint32 => u32::from_le_bytes(storage[..4].try_into().unwrap()).to_string(),
        ElementKind::Float16 => crate::format_number(f16_bits_to_f64(u16::from_le_bytes(
            storage[..2].try_into().unwrap(),
        ))),
        ElementKind::Float32 => crate::format_number(f64::from(f32::from_le_bytes(
            storage[..4].try_into().unwrap(),
        ))),
        ElementKind::Float64 => crate::format_number(f64::from_le_bytes(storage)),
        ElementKind::BigInt64 => i64::from_le_bytes(storage).to_string(),
        ElementKind::BigUint64 => u64::from_le_bytes(storage).to_string(),
    }
}

pub(crate) fn write_element<H: Host>(
    machine: &mut Machine<'_, H>,
    view: Value,
    element_index: usize,
    value: Value,
) -> Result<bool, EvalFailure> {
    let fields = view_fields(machine, view)?;
    // IntegerIndexedElementSet converts before checking detached/OOB state.
    let storage = storage_from_value(machine, fields.kind, value)?;
    let bounds = typed_array_bounds_for(machine, fields)?;
    if bounds.out_of_bounds || element_index >= bounds.element_length {
        return Ok(false);
    }
    let start = fields
        .byte_offset
        .checked_add(
            element_index
                .checked_mul(fields.kind.element_size())
                .ok_or_else(|| range_error("Invalid typed array index"))?,
        )
        .ok_or_else(|| range_error("Invalid typed array index"))?;
    let buffer = ViewBuffer::from_value(machine, fields.buffer)?;
    buffer.with_bytes_mut(machine, |bytes| {
        bytes[start..start + fields.kind.element_size()]
            .copy_from_slice(&storage[..fields.kind.element_size()]);
    })?;
    Ok(true)
}

fn numeric_value<H: Host>(machine: &mut Machine<'_, H>, value: Value) -> Result<f64, EvalFailure> {
    match machine.coerce_number_observable(value)?.decode() {
        Some(Decoded::Int32(value)) => Ok(f64::from(value as i32)),
        Some(Decoded::Number(value)) => Ok(value),
        _ => unreachable!("ToNumber produces a numeric value"),
    }
}

/// ToIntegerOrInfinity. Adding `+0` turns the `-0` that truncating a small
/// negative fraction yields into the `+0` the operation is defined to return.
pub(crate) fn integer_or_infinity<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<f64, EvalFailure> {
    let number = numeric_value(machine, value)?;
    Ok(if number.is_nan() {
        0.0
    } else {
        number.trunc() + 0.0
    })
}

fn length_of_array_like<H: Host>(
    machine: &mut Machine<'_, H>,
    source: Value,
) -> Result<usize, EvalFailure> {
    const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;
    let length = machine.get_named_property(source, "length")?;
    let number = numeric_value(machine, length)?;
    if number.is_nan() || number <= 0.0 {
        return Ok(0);
    }
    if number == f64::INFINITY {
        return Ok(MAX_SAFE_INTEGER as usize);
    }
    Ok(number.trunc().min(MAX_SAFE_INTEGER) as usize)
}

pub(crate) fn storage_from_value<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: ElementKind,
    value: Value,
) -> Result<[u8; 8], EvalFailure> {
    let mut storage = [0_u8; 8];
    if kind.is_bigint() {
        let primitive = bigint::to_bigint(machine, value)?;
        let bigint = bigint::bigint_from_value(machine, primitive)?
            .expect("ToBigInt returns a BigInt")
            .as_uint_n(64)
            .to_u64()
            .expect("64-bit unsigned BigInt fits");
        storage.copy_from_slice(&bigint.to_le_bytes());
        return Ok(storage);
    }
    let number = numeric_value(machine, value)?;
    match kind {
        ElementKind::Int8 => storage[0] = to_int_mod(number, 8) as i8 as u8,
        ElementKind::Uint8 => storage[0] = to_uint_mod(number, 8) as u8,
        ElementKind::Uint8Clamped => storage[0] = to_uint8_clamp(number),
        ElementKind::Int16 => {
            storage[..2].copy_from_slice(&(to_int_mod(number, 16) as i16).to_le_bytes())
        }
        ElementKind::Uint16 => {
            storage[..2].copy_from_slice(&(to_uint_mod(number, 16) as u16).to_le_bytes())
        }
        ElementKind::Int32 => {
            storage[..4].copy_from_slice(&(to_int_mod(number, 32) as i32).to_le_bytes())
        }
        ElementKind::Uint32 => {
            storage[..4].copy_from_slice(&(to_uint_mod(number, 32) as u32).to_le_bytes())
        }
        ElementKind::Float16 => {
            storage[..2].copy_from_slice(&f64_to_f16_bits(number).to_le_bytes())
        }
        ElementKind::Float32 => storage[..4].copy_from_slice(&(number as f32).to_le_bytes()),
        ElementKind::Float64 => storage.copy_from_slice(&number.to_le_bytes()),
        ElementKind::BigInt64 | ElementKind::BigUint64 => unreachable!(),
    }
    Ok(storage)
}

pub(crate) fn value_from_storage<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: ElementKind,
    storage: [u8; 8],
) -> Result<Value, EvalFailure> {
    let number = match kind {
        ElementKind::Int8 => {
            return Ok(Value::int32(i8::from_le_bytes([storage[0]]) as i32 as u32));
        }
        ElementKind::Uint8 | ElementKind::Uint8Clamped => {
            return Ok(Value::int32(u32::from(storage[0])));
        }
        ElementKind::Int16 => {
            return Ok(Value::int32(
                i16::from_le_bytes([storage[0], storage[1]]) as i32 as u32,
            ));
        }
        ElementKind::Uint16 => {
            return Ok(Value::int32(u32::from(u16::from_le_bytes([
                storage[0], storage[1],
            ]))));
        }
        ElementKind::Int32 => {
            return Ok(Value::int32(
                i32::from_le_bytes(storage[..4].try_into().unwrap()) as u32,
            ));
        }
        ElementKind::Uint32 => {
            return Ok(crate::number_value(f64::from(u32::from_le_bytes(
                storage[..4].try_into().unwrap(),
            ))));
        }
        ElementKind::Float16 => {
            f16_bits_to_f64(u16::from_le_bytes(storage[..2].try_into().unwrap()))
        }
        ElementKind::Float32 => f64::from(f32::from_le_bytes(storage[..4].try_into().unwrap())),
        ElementKind::Float64 => f64::from_le_bytes(storage),
        ElementKind::BigInt64 => {
            let signed = i64::from_le_bytes(storage);
            let value = if signed < 0 {
                BigIntValue::from_u64(signed.unsigned_abs()).neg()
            } else {
                BigIntValue::from_u64(signed as u64)
            };
            return bigint::allocate_bigint(machine, &value);
        }
        ElementKind::BigUint64 => {
            return bigint::allocate_bigint(
                machine,
                &BigIntValue::from_u64(u64::from_le_bytes(storage)),
            );
        }
    };
    Ok(Value::number(number))
}

pub(crate) fn typed_array_index(name: &EcmaString) -> Option<Option<usize>> {
    let text = name.to_utf8_lossy();
    canonical_index(&text)
}

fn canonical_index(text: &str) -> Option<Option<usize>> {
    if text == "-0" {
        return Some(None);
    }
    let number = match text {
        "NaN" => f64::NAN,
        "Infinity" => f64::INFINITY,
        "-Infinity" => f64::NEG_INFINITY,
        _ => text.parse::<f64>().ok()?,
    };
    if crate::format_number(number) != text {
        return None;
    }
    if !number.is_finite() || number < 0.0 || number.fract() != 0.0 || number >= usize::MAX as f64 {
        Some(None)
    } else {
        Some(Some(number as usize))
    }
}

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let shared_prototype = super::super::ordinary_prototype(heap, builtins.object_prototype());
    let shared_constructor = install_constructor_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "%TypedArray%",
            length: 0,
            handler: abstract_constructor::<H>,
        },
    );
    builtins.set_constructor_prototype(heap, atoms, shapes, shared_constructor, shared_prototype);
    builtins.set_typedarray_constructor(shared_constructor);
    builtins.set_typedarray_prototype(shared_prototype);
    for (name, length, handler) in [
        ("from", 1, from::<H> as BuiltinHandler<H>),
        ("of", 0, of::<H>),
    ] {
        let function = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name,
                length,
                handler,
            },
        );
        define_data(heap, atoms, shapes, shared_constructor, name, function);
    }

    for (property_name, function_name, getter) in [
        ("buffer", "get buffer", get_buffer::<H> as BuiltinHandler<H>),
        (
            "byteLength",
            "get byteLength",
            get_byte_length::<H> as BuiltinHandler<H>,
        ),
        (
            "byteOffset",
            "get byteOffset",
            get_byte_offset::<H> as BuiltinHandler<H>,
        ),
        ("length", "get length", get_length::<H> as BuiltinHandler<H>),
    ] {
        let getter = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name: function_name,
                length: 0,
                handler: getter,
            },
        );
        let HeapEntry::Object { properties, .. } = &mut heap[heap_index(shared_prototype)] else {
            unreachable!("%TypedArray%.prototype is ordinary")
        };
        properties.insert(
            shapes,
            PropertyKey::Named(atoms.intern_str(property_name)),
            Property::Accessor {
                getter: Some(getter),
                setter: None,
                enumerable: false,
                configurable: true,
            },
        );
    }
    let array_to_string = {
        let properties = match &heap[heap_index(builtins.array_prototype())] {
            HeapEntry::Object { properties, .. } | HeapEntry::Array { properties, .. } => {
                properties
            }
            _ => unreachable!("Array.prototype is ordinary"),
        };
        let Some(Property::Data { value, .. }) =
            properties.get(shapes, &PropertyKey::Named(atoms.intern_str("toString")))
        else {
            unreachable!("Array.prototype.toString is installed first")
        };
        *value
    };
    define_data(
        heap,
        atoms,
        shapes,
        shared_prototype,
        "toString",
        array_to_string,
    );

    let tag_getter = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "get [Symbol.toStringTag]",
            length: 0,
            handler: get_to_string_tag::<H>,
        },
    );
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(shared_prototype)] else {
        unreachable!("%TypedArray%.prototype is ordinary")
    };
    properties.insert(
        shapes,
        PropertyKey::Symbol(heap_index(builtins.symbol_to_string_tag()) as u32),
        Property::Accessor {
            getter: Some(tag_getter),
            setter: None,
            enumerable: false,
            configurable: true,
        },
    );

    for (name, length, handler) in [
        ("at", 1, at::<H> as BuiltinHandler<H>),
        ("copyWithin", 2, copy_within::<H>),
        ("entries", 0, entries::<H>),
        ("every", 1, every::<H>),
        ("fill", 1, fill::<H>),
        ("filter", 1, filter::<H>),
        ("find", 1, find::<H>),
        ("findIndex", 1, find_index::<H>),
        ("findLast", 1, find_last::<H>),
        ("findLastIndex", 1, find_last_index::<H>),
        ("forEach", 1, for_each::<H>),
        ("includes", 1, includes::<H>),
        ("indexOf", 1, index_of::<H>),
        ("join", 1, join::<H>),
        ("keys", 0, keys::<H>),
        ("lastIndexOf", 1, last_index_of::<H>),
        ("map", 1, map::<H>),
        ("reduce", 1, reduce::<H>),
        ("reduceRight", 1, reduce_right::<H>),
        ("set", 1, set::<H>),
        ("slice", 2, slice::<H>),
        ("reverse", 0, reverse::<H>),
        ("sort", 1, sort::<H>),
        ("subarray", 2, subarray::<H>),
        ("some", 1, some::<H>),
        ("values", 0, values::<H>),
        ("toLocaleString", 0, to_locale_string::<H>),
        ("toReversed", 0, to_reversed::<H>),
        ("toSorted", 1, to_sorted::<H>),
        ("with", 2, with::<H>),
    ] {
        let function = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name,
                length,
                handler,
            },
        );
        define_data(heap, atoms, shapes, shared_prototype, name, function);
        if name == "values" {
            let HeapEntry::Object { properties, .. } = &mut heap[heap_index(shared_prototype)]
            else {
                unreachable!("%TypedArray%.prototype is ordinary")
            };
            properties.insert(
                shapes,
                PropertyKey::Symbol(heap_index(builtins.symbol_iterator()) as u32),
                builtin_property(function),
            );
        }
    }

    for kind in ElementKind::ALL {
        let prototype = super::super::ordinary_prototype(heap, shared_prototype);
        let constructor = install_constructor_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name: kind.name(),
                length: 3,
                handler: constructor::<H>,
            },
        );
        builtins.set_constructor_prototype(heap, atoms, shapes, constructor, prototype);
        let HeapEntry::NativeFunction {
            prototype: parent, ..
        } = &mut heap[heap_index(constructor)]
        else {
            unreachable!("TypedArray constructors are native functions")
        };
        *parent = Some(shared_constructor);
        builtins.set_typed_array_constructor(kind, constructor);
        builtins.set_typed_array_prototype(kind, prototype);
        define_frozen_data(
            heap,
            atoms,
            shapes,
            constructor,
            "BYTES_PER_ELEMENT",
            crate::number_value(kind.element_size() as f64),
        );
        define_frozen_data(
            heap,
            atoms,
            shapes,
            prototype,
            "BYTES_PER_ELEMENT",
            crate::number_value(kind.element_size() as f64),
        );
        define_data(heap, atoms, shapes, prototype, "constructor", constructor);
        if kind == ElementKind::Uint8 {
            for (name, length, handler) in [
                ("fromBase64", 1, from_base64::<H> as BuiltinHandler<H>),
                ("fromHex", 1, from_hex::<H>),
            ] {
                let function = install_function(
                    heap,
                    atoms,
                    shapes,
                    builtins,
                    crate::intrinsics::BuiltinDef {
                        name,
                        length,
                        handler,
                    },
                );
                define_data(heap, atoms, shapes, constructor, name, function);
            }
            for (name, length, handler) in [
                (
                    "setFromBase64",
                    1,
                    set_from_base64::<H> as BuiltinHandler<H>,
                ),
                ("setFromHex", 1, set_from_hex::<H>),
                ("toBase64", 0, to_base64::<H>),
                ("toHex", 0, to_hex::<H>),
            ] {
                let function = install_function(
                    heap,
                    atoms,
                    shapes,
                    builtins,
                    crate::intrinsics::BuiltinDef {
                        name,
                        length,
                        handler,
                    },
                );
                define_data(heap, atoms, shapes, prototype, name, function);
            }
        }
        globals.insert(EcmaString::encode(kind.name()), constructor);
    }
}

#[derive(Clone, Copy)]
enum Base64Alphabet {
    Base64,
    Base64Url,
}

#[derive(Clone, Copy)]
enum LastChunkHandling {
    Loose,
    Strict,
    StopBeforePartial,
}

struct DecodedBytes {
    bytes: Vec<u8>,
    read: usize,
    error: Option<&'static str>,
}

fn encoding_syntax_error<H: Host>(
    machine: &mut Machine<'_, H>,
    message: impl Into<String>,
) -> EvalFailure {
    let id = machine
        .intrinsics
        .builtins
        .id_named("SyntaxError")
        .expect("SyntaxError installed");
    machine.throw_error(id, EcmaString::encode(&Into::<String>::into(message)))
}

fn options_object<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Option<Value>,
) -> Result<Option<Value>, EvalFailure> {
    match value {
        None | Some(Value::UNDEFINED) => Ok(None),
        Some(value) if machine.is_object(value) => Ok(Some(value)),
        Some(_) => Err(type_error("Uint8Array encoding options must be an object")),
    }
}

fn option_text<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Option<Value>,
    name: &str,
) -> Result<Option<String>, EvalFailure> {
    let Some(options) = options else {
        return Ok(None);
    };
    let value = machine.get_named_property(options, name)?;
    if value == Value::UNDEFINED {
        return Ok(None);
    }
    machine
        .string_value(value)
        .map(|text| Some(text.to_utf8_lossy()))
        .ok_or_else(|| type_error("Uint8Array encoding option must be a string"))
}

fn base64_alphabet<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Option<Value>,
) -> Result<Base64Alphabet, EvalFailure> {
    match option_text(machine, options, "alphabet")?.as_deref() {
        None | Some("base64") => Ok(Base64Alphabet::Base64),
        Some("base64url") => Ok(Base64Alphabet::Base64Url),
        Some(_) => Err(type_error(
            "Uint8Array base64 alphabet must be \"base64\" or \"base64url\"",
        )),
    }
}

fn last_chunk_handling<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Option<Value>,
) -> Result<LastChunkHandling, EvalFailure> {
    match option_text(machine, options, "lastChunkHandling")?.as_deref() {
        None | Some("loose") => Ok(LastChunkHandling::Loose),
        Some("strict") => Ok(LastChunkHandling::Strict),
        Some("stop-before-partial") => Ok(LastChunkHandling::StopBeforePartial),
        Some(_) => Err(type_error(
            "lastChunkHandling must be \"loose\", \"strict\", or \"stop-before-partial\"",
        )),
    }
}

fn string_argument<H: Host>(machine: &Machine<'_, H>, value: Value) -> Result<String, EvalFailure> {
    machine
        .string_value(value)
        .map(|text| text.to_utf8_lossy())
        .ok_or_else(|| type_error("Uint8Array encoding input must be a string"))
}

fn skip_ascii_whitespace(text: &[u8], mut index: usize) -> usize {
    while index < text.len() && matches!(text[index], b'\t' | b'\n' | 0x0c | b'\r' | b' ') {
        index += 1;
    }
    index
}

fn base64_digit(byte: u8, alphabet: Base64Alphabet) -> Option<u8> {
    match byte {
        b'A'..=b'Z' => Some(byte - b'A'),
        b'a'..=b'z' => Some(byte - b'a' + 26),
        b'0'..=b'9' => Some(byte - b'0' + 52),
        b'+' if matches!(alphabet, Base64Alphabet::Base64) => Some(62),
        b'/' if matches!(alphabet, Base64Alphabet::Base64) => Some(63),
        b'-' if matches!(alphabet, Base64Alphabet::Base64Url) => Some(62),
        b'_' if matches!(alphabet, Base64Alphabet::Base64Url) => Some(63),
        _ => None,
    }
}

fn decode_base64_chunk(
    chunk: &[u8; 4],
    chunk_length: usize,
    reject_extra_bits: bool,
) -> Result<([u8; 3], usize), ()> {
    if chunk_length == 2 && reject_extra_bits && chunk[1] & 0x0f != 0 {
        return Err(());
    }
    if chunk_length == 3 && reject_extra_bits && chunk[2] & 0x03 != 0 {
        return Err(());
    }
    let decoded = [
        (chunk[0] << 2) | (chunk[1] >> 4),
        (chunk[1] << 4) | (chunk[2] >> 2),
        (chunk[2] << 6) | chunk[3],
    ];
    Ok((decoded, chunk_length - 1))
}

fn decode_base64(
    text: &str,
    alphabet: Base64Alphabet,
    handling: LastChunkHandling,
    max_length: usize,
) -> DecodedBytes {
    if max_length == 0 {
        return DecodedBytes {
            bytes: Vec::new(),
            read: 0,
            error: None,
        };
    }
    let text = text.as_bytes();
    let mut read = 0;
    let mut bytes = Vec::new();
    let mut chunk = [0_u8; 4];
    let mut chunk_length = 0;
    let mut index = 0;
    loop {
        index = skip_ascii_whitespace(text, index);
        if index == text.len() {
            if chunk_length > 0 {
                match handling {
                    LastChunkHandling::StopBeforePartial => {
                        return DecodedBytes {
                            bytes,
                            read,
                            error: None,
                        };
                    }
                    LastChunkHandling::Loose if chunk_length > 1 => {
                        let (decoded, count) = decode_base64_chunk(&chunk, chunk_length, false)
                            .expect("loose partial chunks accept overflow bits");
                        bytes.extend_from_slice(&decoded[..count]);
                    }
                    LastChunkHandling::Loose | LastChunkHandling::Strict => {
                        return DecodedBytes {
                            bytes,
                            read,
                            error: Some("invalid base64 final chunk"),
                        };
                    }
                }
            }
            return DecodedBytes {
                bytes,
                read: text.len(),
                error: None,
            };
        }

        let byte = text[index];
        index += 1;
        if byte == b'=' {
            if chunk_length < 2 {
                return DecodedBytes {
                    bytes,
                    read,
                    error: Some("invalid base64 padding"),
                };
            }
            index = skip_ascii_whitespace(text, index);
            if chunk_length == 2 {
                if index == text.len() {
                    if matches!(handling, LastChunkHandling::StopBeforePartial) {
                        return DecodedBytes {
                            bytes,
                            read,
                            error: None,
                        };
                    }
                    return DecodedBytes {
                        bytes,
                        read,
                        error: Some("invalid base64 padding"),
                    };
                }
                if text[index] == b'=' {
                    index = skip_ascii_whitespace(text, index + 1);
                }
            }
            if index < text.len() {
                return DecodedBytes {
                    bytes,
                    read,
                    error: Some("invalid base64 padding"),
                };
            }
            match decode_base64_chunk(
                &chunk,
                chunk_length,
                matches!(handling, LastChunkHandling::Strict),
            ) {
                Ok((decoded, count)) => bytes.extend_from_slice(&decoded[..count]),
                Err(()) => {
                    return DecodedBytes {
                        bytes,
                        read,
                        error: Some("base64 padding has non-zero overflow bits"),
                    };
                }
            }
            return DecodedBytes {
                bytes,
                read: text.len(),
                error: None,
            };
        }

        let Some(digit) = base64_digit(byte, alphabet) else {
            return DecodedBytes {
                bytes,
                read,
                error: Some("invalid base64 character"),
            };
        };
        let remaining = max_length - bytes.len();
        if (remaining == 1 && chunk_length == 2) || (remaining == 2 && chunk_length == 3) {
            return DecodedBytes {
                bytes,
                read,
                error: None,
            };
        }
        chunk[chunk_length] = digit;
        chunk_length += 1;
        if chunk_length == 4 {
            let (decoded, count) = decode_base64_chunk(&chunk, chunk_length, false)
                .expect("complete chunks are always decodable");
            bytes.extend_from_slice(&decoded[..count]);
            chunk = [0; 4];
            chunk_length = 0;
            read = index;
            if bytes.len() == max_length {
                return DecodedBytes {
                    bytes,
                    read,
                    error: None,
                };
            }
        }
    }
}

fn decode_hex(text: &str, max_length: usize) -> DecodedBytes {
    let text = text.as_bytes();
    if !text.len().is_multiple_of(2) {
        return DecodedBytes {
            bytes: Vec::new(),
            read: 0,
            error: Some("hex input must contain a whole number of bytes"),
        };
    }
    let nibble = |byte: u8| match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    };
    let mut bytes = Vec::with_capacity((text.len() / 2).min(max_length));
    let mut read = 0;
    while read < text.len() && bytes.len() < max_length {
        let Some(high) = nibble(text[read]) else {
            return DecodedBytes {
                bytes,
                read,
                error: Some("invalid hexadecimal digit"),
            };
        };
        let Some(low) = nibble(text[read + 1]) else {
            return DecodedBytes {
                bytes,
                read,
                error: Some("invalid hexadecimal digit"),
            };
        };
        bytes.push((high << 4) | low);
        read += 2;
    }
    DecodedBytes {
        bytes,
        read,
        error: None,
    }
}

fn validate_uint8<H: Host>(
    machine: &Machine<'_, H>,
    view: Value,
) -> Result<ViewFields, EvalFailure> {
    let fields = view_fields(machine, view)?;
    if fields.kind != ElementKind::Uint8 {
        return Err(type_error(
            "Uint8Array method called on an incompatible receiver",
        ));
    }
    Ok(fields)
}

fn uint8_bytes<H: Host>(machine: &Machine<'_, H>, view: Value) -> Result<Vec<u8>, EvalFailure> {
    let fields = validate_uint8(machine, view)?;
    let bounds = typed_array_bounds_for(machine, fields)?;
    if bounds.detached || bounds.out_of_bounds {
        return Err(type_error("Uint8Array view is detached or out of bounds"));
    }
    ViewBuffer::from_value(machine, fields.buffer)?.with_bytes(machine, |bytes| {
        bytes[fields.byte_offset..fields.byte_offset + bounds.byte_length].to_vec()
    })
}

fn write_uint8_bytes<H: Host>(
    machine: &mut Machine<'_, H>,
    fields: ViewFields,
    bytes: &[u8],
) -> Result<(), EvalFailure> {
    ViewBuffer::from_value(machine, fields.buffer)?.with_bytes_mut(machine, |target| {
        target[fields.byte_offset..fields.byte_offset + bytes.len()].copy_from_slice(bytes);
    })
}

fn construct_uint8<H: Host>(
    machine: &mut Machine<'_, H>,
    bytes: &[u8],
) -> Result<Value, EvalFailure> {
    let constructor = machine
        .intrinsics
        .builtins
        .typed_array_constructor(ElementKind::Uint8);
    let target = construct_typed_array(machine, constructor, bytes.len())?;
    let fields = validate_uint8(machine, target)?;
    write_uint8_bytes(machine, fields, bytes)?;
    Ok(target)
}

fn encoding_result<H: Host>(
    machine: &mut Machine<'_, H>,
    read: usize,
    written: usize,
) -> Result<BuiltinOutcome, EvalFailure> {
    let result = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.builtins.object_prototype()),
            boxed_primitive: None,
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)?;
    let read_key = PropertyKey::Named(machine.intern_str("read"));
    let written_key = PropertyKey::Named(machine.intern_str("written"));
    machine.create_data_property_key(result, read_key, crate::number_value(read as f64))?;
    machine.create_data_property_key(result, written_key, crate::number_value(written as f64))?;
    Ok(BuiltinOutcome::Value(result))
}

fn from_base64<H: Host>(
    machine: &mut Machine<'_, H>,
    _constructor: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let text = string_argument(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let options = options_object(machine, args.get(1).copied())?;
    let alphabet = base64_alphabet(machine, options)?;
    let handling = last_chunk_handling(machine, options)?;
    let decoded = decode_base64(&text, alphabet, handling, usize::MAX);
    if let Some(error) = decoded.error {
        return Err(encoding_syntax_error(machine, error));
    }
    Ok(BuiltinOutcome::Value(construct_uint8(
        machine,
        &decoded.bytes,
    )?))
}

fn from_hex<H: Host>(
    machine: &mut Machine<'_, H>,
    _constructor: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let text = string_argument(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let decoded = decode_hex(&text, usize::MAX);
    if let Some(error) = decoded.error {
        return Err(encoding_syntax_error(machine, error));
    }
    Ok(BuiltinOutcome::Value(construct_uint8(
        machine,
        &decoded.bytes,
    )?))
}

fn encode_base64(bytes: &[u8], alphabet: Base64Alphabet, omit_padding: bool) -> String {
    let table = match alphabet {
        Base64Alphabet::Base64 => {
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
        }
        Base64Alphabet::Base64Url => {
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
        }
    };
    let mut encoded = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for chunk in bytes.chunks(3) {
        encoded.push(char::from(table[usize::from(chunk[0] >> 2)]));
        encoded.push(char::from(
            table
                [usize::from(((chunk[0] & 0x03) << 4) | (chunk.get(1).copied().unwrap_or(0) >> 4))],
        ));
        if let Some(second) = chunk.get(1).copied() {
            encoded.push(char::from(
                table[usize::from(
                    ((second & 0x0f) << 2) | (chunk.get(2).copied().unwrap_or(0) >> 6),
                )],
            ));
        } else if !omit_padding {
            encoded.push('=');
        }
        if let Some(third) = chunk.get(2).copied() {
            encoded.push(char::from(table[usize::from(third & 0x3f)]));
        } else if !omit_padding {
            encoded.push('=');
        }
    }
    encoded
}

fn to_base64<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    validate_uint8(machine, this)?;
    let options = options_object(machine, args.first().copied())?;
    let alphabet = base64_alphabet(machine, options)?;
    let omit_padding = if let Some(options) = options {
        let value = machine.get_named_property(options, "omitPadding")?;
        machine.to_boolean(value)
    } else {
        false
    };
    let bytes = uint8_bytes(machine, this)?;
    let encoded = encode_base64(&bytes, alphabet, omit_padding);
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        EcmaString::encode(&encoded),
    )?))
}

fn to_hex<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let bytes = uint8_bytes(machine, this)?;
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        EcmaString::encode(&encoded),
    )?))
}

fn set_from_base64<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let fields = validate_uint8(machine, this)?;
    let text = string_argument(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let options = options_object(machine, args.get(1).copied())?;
    let alphabet = base64_alphabet(machine, options)?;
    let handling = last_chunk_handling(machine, options)?;
    let bounds = typed_array_bounds_for(machine, fields)?;
    if bounds.detached || bounds.out_of_bounds {
        return Err(type_error("Uint8Array view is detached or out of bounds"));
    }
    let decoded = decode_base64(&text, alphabet, handling, bounds.element_length);
    write_uint8_bytes(machine, fields, &decoded.bytes)?;
    if let Some(error) = decoded.error {
        return Err(encoding_syntax_error(machine, error));
    }
    encoding_result(machine, decoded.read, decoded.bytes.len())
}

fn set_from_hex<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let fields = validate_uint8(machine, this)?;
    let text = string_argument(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let bounds = typed_array_bounds_for(machine, fields)?;
    if bounds.detached || bounds.out_of_bounds {
        return Err(type_error("Uint8Array view is detached or out of bounds"));
    }
    let decoded = decode_hex(&text, bounds.element_length);
    write_uint8_bytes(machine, fields, &decoded.bytes)?;
    if let Some(error) = decoded.error {
        return Err(encoding_syntax_error(machine, error));
    }
    encoding_result(machine, decoded.read, decoded.bytes.len())
}

fn abstract_constructor<H: Host>(
    _machine: &mut Machine<'_, H>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Err(type_error("%TypedArray% is not directly constructable"))
}

fn constructor_prototype<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: ElementKind,
) -> Result<Value, EvalFailure> {
    let intrinsic = machine.intrinsics.builtins.typed_array_prototype(kind);
    let new_target = machine.current_new_target();
    if new_target == Value::UNDEFINED {
        return Ok(intrinsic);
    }
    let candidate = machine.get_named_property(new_target, "prototype")?;
    Ok(if machine.is_object(candidate) {
        candidate
    } else {
        intrinsic
    })
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _callee: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !constructing {
        return Err(type_error("TypedArray constructor requires 'new'"));
    }
    let builtin = machine
        .current_builtin_id()
        .ok_or_else(|| type_error("invalid TypedArray constructor"))?;
    let kind = machine
        .intrinsics
        .builtins
        .typed_array_kind_for_builtin(builtin)
        .ok_or_else(|| type_error("invalid TypedArray constructor"))?;
    let source = args.first().copied().unwrap_or(Value::UNDEFINED);
    let object_prototype = if machine.is_object(source) {
        Some(constructor_prototype(machine, kind)?)
    } else {
        None
    };
    let (buffer, byte_offset, byte_length, array_length, values) =
        if ViewBuffer::value_is_buffer(machine, source) {
            view_over_buffer(machine, kind, source, &args[1..])?
        } else if let Ok(source_fields) = view_fields(machine, source) {
            let source_bounds = typed_array_bounds_for(machine, source_fields)?;
            if source_bounds.detached || source_bounds.out_of_bounds {
                return Err(type_error(
                    "Cannot copy a detached or out-of-bounds TypedArray",
                ));
            }
            if source_fields.kind == kind {
                let bytes = view_bytes(machine, source_fields, source_bounds)?;
                fresh_bytes_view(machine, kind, &bytes)?
            } else {
                if source_fields.kind.is_bigint() != kind.is_bigint() {
                    return Err(type_error("Cannot mix BigInt and Number TypedArrays"));
                }
                let mut values = Vec::with_capacity(source_bounds.element_length);
                for index in 0..source_bounds.element_length {
                    values.push(read_element(machine, source, index)?);
                }
                fresh_view(machine, kind, values)?
            }
        } else if source == Value::UNDEFINED || !machine.is_object(source) {
            let length = if source == Value::UNDEFINED {
                0
            } else {
                super::arraybuffer::to_index(machine, source)?
            };
            fresh_zeroed_view(machine, kind, length)?
        } else {
            let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
            let iterator_key = PropertyKey::Symbol(heap_index(iterator_symbol) as u32);
            let iterator_method = machine.get_property_key(source, &iterator_key)?;
            let values = match iterator_method.decode() {
                Some(Decoded::Undefined | Decoded::Null) => array_like_values(machine, source)?,
                _ if machine.is_callable(iterator_method)? => machine.iterable_values(source)?,
                _ => return Err(type_error("value is not iterable")),
            };
            fresh_view(machine, kind, values)?
        };
    let prototype = match object_prototype {
        Some(prototype) => prototype,
        None => constructor_prototype(machine, kind)?,
    };
    let view = machine
        .allocate(HeapEntry::TypedArray {
            kind,
            buffer,
            byte_offset,
            byte_length,
            array_length,
            properties: PropertyMap::default(),
            prototype: Some(prototype),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)?;
    if let Some(values) = values {
        for (index, value) in values.into_iter().enumerate() {
            let _ = write_element(machine, view, index, value)?;
        }
    }
    Ok(BuiltinOutcome::Value(view))
}

type PreparedView = (Value, usize, LengthSlot, LengthSlot, Option<Vec<Value>>);

fn fresh_zeroed_view<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: ElementKind,
    length: usize,
) -> Result<PreparedView, EvalFailure> {
    let byte_length = length
        .checked_mul(kind.element_size())
        .ok_or_else(|| range_error("Invalid typed array length"))?;
    let buffer = ArrayBufferHandle::allocate(machine, byte_length, None)?.value();
    Ok((
        buffer,
        0,
        LengthSlot::Fixed(byte_length),
        LengthSlot::Fixed(length),
        None,
    ))
}

fn fresh_view<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: ElementKind,
    values: Vec<Value>,
) -> Result<PreparedView, EvalFailure> {
    let mut prepared = fresh_zeroed_view(machine, kind, values.len())?;
    prepared.4 = Some(values);
    Ok(prepared)
}

fn view_bytes<H: Host>(
    machine: &Machine<'_, H>,
    fields: ViewFields,
    bounds: ViewBounds,
) -> Result<Vec<u8>, EvalFailure> {
    let buffer = ViewBuffer::from_value(machine, fields.buffer)?;
    buffer.with_bytes(machine, |bytes| {
        bytes[fields.byte_offset..fields.byte_offset + bounds.byte_length].to_vec()
    })
}

fn fresh_bytes_view<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: ElementKind,
    bytes: &[u8],
) -> Result<PreparedView, EvalFailure> {
    debug_assert!(bytes.len().is_multiple_of(kind.element_size()));
    let prepared = fresh_zeroed_view(machine, kind, bytes.len() / kind.element_size())?;
    ArrayBufferHandle::from_value(machine, prepared.0)?
        .with_bytes_mut(machine, |target| target.copy_from_slice(bytes))?;
    Ok(prepared)
}

fn view_over_buffer<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: ElementKind,
    buffer: Value,
    args: &[Value],
) -> Result<PreparedView, EvalFailure> {
    let backing = ViewBuffer::from_value(machine, buffer)?;
    let offset =
        super::arraybuffer::to_index(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    if !offset.is_multiple_of(kind.element_size()) {
        return Err(range_error("TypedArray byteOffset is not aligned"));
    }
    let requested_length = match args.get(1).copied() {
        None | Some(Value::UNDEFINED) => None,
        Some(length) => Some(super::arraybuffer::to_index(machine, length)?),
    };
    if backing.is_detached(machine) {
        return Err(type_error(
            "Cannot construct a TypedArray over a detached buffer",
        ));
    }
    let available = backing.byte_length(machine)?;
    if offset > available {
        return Err(range_error("TypedArray byteOffset is outside the buffer"));
    }
    match requested_length {
        None if backing.is_resizable(machine)? => {
            Ok((buffer, offset, LengthSlot::Auto, LengthSlot::Auto, None))
        }
        None => {
            let remaining = available - offset;
            if !remaining.is_multiple_of(kind.element_size()) {
                return Err(range_error("TypedArray byte length is not aligned"));
            }
            Ok((
                buffer,
                offset,
                LengthSlot::Fixed(remaining),
                LengthSlot::Fixed(remaining / kind.element_size()),
                None,
            ))
        }
        Some(length) => {
            let bytes = length
                .checked_mul(kind.element_size())
                .ok_or_else(|| range_error("Invalid typed array length"))?;
            if offset.checked_add(bytes).is_none_or(|end| end > available) {
                return Err(range_error("TypedArray view exceeds its buffer"));
            }
            Ok((
                buffer,
                offset,
                LengthSlot::Fixed(bytes),
                LengthSlot::Fixed(length),
                None,
            ))
        }
    }
}

fn array_like_values<H: Host>(
    machine: &mut Machine<'_, H>,
    source: Value,
) -> Result<Vec<Value>, EvalFailure> {
    let source = machine.value_to_object(source)?;
    let length = length_of_array_like(machine, source)?;
    machine
        .ensure_object_property_capacity(length)
        .map_err(|_| range_error("Invalid typed array length"))?;
    let mut values = Vec::with_capacity(length);
    for index in 0..length {
        values.push(machine.get_named_property(source, &index.to_string())?);
    }
    Ok(values)
}

fn get_to_string_tag<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let Ok(fields) = view_fields(machine, this) else {
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    };
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        EcmaString::encode(fields.kind.name()),
    )?))
}

fn get_buffer<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(view_fields(machine, this)?.buffer))
}

fn get_byte_length<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(crate::number_value(
        typed_array_bounds(machine, this)?.byte_length as f64,
    )))
}

fn get_byte_offset<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let fields = view_fields(machine, this)?;
    let bounds = typed_array_bounds_for(machine, fields)?;
    Ok(BuiltinOutcome::Value(crate::number_value(
        if bounds.out_of_bounds {
            0
        } else {
            fields.byte_offset
        } as f64,
    )))
}

fn get_length<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(crate::number_value(
        typed_array_bounds(machine, this)?.element_length as f64,
    )))
}

fn validated<H: Host>(
    machine: &Machine<'_, H>,
    view: Value,
) -> Result<(ElementKind, usize), EvalFailure> {
    let fields = view_fields(machine, view)?;
    let bounds = typed_array_bounds_for(machine, fields)?;
    if bounds.detached || bounds.out_of_bounds {
        return Err(type_error(
            "TypedArray method called on a detached or out-of-bounds view",
        ));
    }
    Ok((fields.kind, bounds.element_length))
}

fn construct_typed_array<H: Host>(
    machine: &mut Machine<'_, H>,
    constructor: Value,
    length: usize,
) -> Result<Value, EvalFailure> {
    if !machine.is_callable(constructor)? {
        return Err(type_error("TypedArray constructor is not callable"));
    }
    let target = machine.construct_value(constructor, &[crate::number_value(length as f64)])?;
    let (_, actual) = validated(machine, target)
        .map_err(|_| type_error("TypedArray constructor did not return a valid TypedArray"))?;
    if actual < length {
        return Err(type_error(
            "TypedArray constructor returned an array that is too small",
        ));
    }
    Ok(target)
}

fn species_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    source: Value,
) -> Result<Value, EvalFailure> {
    let kind = view_fields(machine, source)?.kind;
    let default = machine.intrinsics.builtins.typed_array_constructor(kind);
    let constructor = machine.get_named_property(source, "constructor")?;
    match constructor.decode() {
        Some(Decoded::Undefined) => Ok(default),
        _ if !machine.is_object(constructor) => Err(type_error(
            "TypedArray constructor property is not an object",
        )),
        _ => {
            let key = PropertyKey::Symbol(
                heap_index(machine.intrinsics.builtins.symbol_species()) as u32
            );
            let species = machine.get_property_key(constructor, &key)?;
            Ok(match species.decode() {
                Some(Decoded::Undefined | Decoded::Null) => default,
                _ => species,
            })
        }
    }
}

fn species_create<H: Host>(
    machine: &mut Machine<'_, H>,
    source: Value,
    length: usize,
) -> Result<Value, EvalFailure> {
    let source_kind = view_fields(machine, source)?.kind;
    let constructor = species_constructor(machine, source)?;
    let target = construct_typed_array(machine, constructor, length)?;
    let target_kind = view_fields(machine, target)?.kind;
    if source_kind.is_bigint() != target_kind.is_bigint() {
        return Err(type_error("Cannot mix BigInt and Number TypedArrays"));
    }
    Ok(target)
}

fn same_type_create<H: Host>(
    machine: &mut Machine<'_, H>,
    source: Value,
    length: usize,
) -> Result<Value, EvalFailure> {
    let kind = view_fields(machine, source)?.kind;
    let constructor = machine.intrinsics.builtins.typed_array_constructor(kind);
    construct_typed_array(machine, constructor, length)
}

fn callback<H: Host>(machine: &Machine<'_, H>, args: &[Value]) -> Result<Value, EvalFailure> {
    let callback = args.first().copied().unwrap_or(Value::UNDEFINED);
    if !machine.is_callable(callback)? {
        return Err(type_error("callback is not a function"));
    }
    Ok(callback)
}

fn relative_index<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    length: usize,
) -> Result<usize, EvalFailure> {
    let index = integer_or_infinity(machine, value)?;
    Ok(if index == f64::NEG_INFINITY {
        0
    } else if index < 0.0 {
        (length as f64 + index).max(0.0) as usize
    } else {
        index.min(length as f64) as usize
    })
}

fn typed_values<H: Host>(
    machine: &mut Machine<'_, H>,
    view: Value,
) -> Result<Vec<Value>, EvalFailure> {
    let (_, length) = validated(machine, view)?;
    let mut values = Vec::with_capacity(length);
    for index in 0..length {
        values.push(read_element(machine, view, index)?);
    }
    Ok(values)
}

fn every<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let callback = callback(machine, args)?;
    let this_arg = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    for index in 0..length {
        let value = read_element(machine, this, index)?;
        if !machine.call_truthy(
            callback,
            this_arg,
            &[value, crate::number_value(index as f64), this],
        )? {
            return Ok(BuiltinOutcome::Value(Value::FALSE));
        }
    }
    Ok(BuiltinOutcome::Value(Value::TRUE))
}

fn fill<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (kind, length) = validated(machine, this)?;
    let value = args.first().copied().unwrap_or(Value::UNDEFINED);
    let value = if kind.is_bigint() {
        bigint::to_bigint(machine, value)?
    } else {
        machine.coerce_number_observable(value)?
    };
    let start = relative_index(
        machine,
        args.get(1).copied().unwrap_or(Value::UNDEFINED),
        length,
    )?;
    let end = relative_index(
        machine,
        args.get(2)
            .copied()
            .unwrap_or(crate::number_value(length as f64)),
        length,
    )?;
    let (_, live_length) = validated(machine, this)?;
    for index in start..end.min(live_length) {
        write_element(machine, this, index, value)?;
    }
    Ok(BuiltinOutcome::Value(this))
}

fn filter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let callback = callback(machine, args)?;
    let this_arg = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let mut selected = Vec::new();
    for index in 0..length {
        let value = read_element(machine, this, index)?;
        if machine.call_truthy(
            callback,
            this_arg,
            &[value, crate::number_value(index as f64), this],
        )? {
            selected.push(value);
        }
    }
    let target = species_create(machine, this, selected.len())?;
    for (index, value) in selected.into_iter().enumerate() {
        write_element(machine, target, index, value)?;
    }
    Ok(BuiltinOutcome::Value(target))
}

fn find_match<H: Host, I: Iterator<Item = usize>>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    indices: I,
) -> Result<Option<(usize, Value)>, EvalFailure> {
    let callback = callback(machine, args)?;
    let this_arg = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    for index in indices {
        let value = read_element(machine, this, index)?;
        if machine.call_truthy(
            callback,
            this_arg,
            &[value, crate::number_value(index as f64), this],
        )? {
            return Ok(Some((index, value)));
        }
    }
    Ok(None)
}

fn find<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let found =
        find_match(machine, this, args, 0..length)?.map_or(Value::UNDEFINED, |(_, value)| value);
    Ok(BuiltinOutcome::Value(found))
}

fn find_index<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let found = find_match(machine, this, args, 0..length)?.map_or(-1.0, |(index, _)| index as f64);
    Ok(BuiltinOutcome::Value(crate::number_value(found)))
}

fn find_last<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let found = find_match(machine, this, args, (0..length).rev())?
        .map_or(Value::UNDEFINED, |(_, value)| value);
    Ok(BuiltinOutcome::Value(found))
}

fn find_last_index<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let found =
        find_match(machine, this, args, (0..length).rev())?.map_or(-1.0, |(index, _)| index as f64);
    Ok(BuiltinOutcome::Value(crate::number_value(found)))
}

fn for_each<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let callback = callback(machine, args)?;
    let this_arg = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    for index in 0..length {
        let value = read_element(machine, this, index)?;
        machine.call_callback(
            callback,
            this_arg,
            &[value, crate::number_value(index as f64), this],
        )?;
    }
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn forward_start<H: Host>(
    machine: &mut Machine<'_, H>,
    argument: Option<Value>,
    length: usize,
) -> Result<Option<usize>, EvalFailure> {
    if length == 0 {
        return Ok(None);
    }
    let Some(argument) = argument else {
        return Ok(Some(0));
    };
    let index = integer_or_infinity(machine, argument)?;
    if index == f64::INFINITY || index >= length as f64 {
        return Ok(None);
    }
    if index == f64::NEG_INFINITY || index < -(length as f64) {
        return Ok(Some(0));
    }
    Ok(Some(if index < 0.0 {
        (length as f64 + index) as usize
    } else {
        index as usize
    }))
}

fn backward_start<H: Host>(
    machine: &mut Machine<'_, H>,
    argument: Option<Value>,
    length: usize,
) -> Result<Option<usize>, EvalFailure> {
    if length == 0 {
        return Ok(None);
    }
    let Some(argument) = argument else {
        return Ok(Some(length - 1));
    };
    let index = integer_or_infinity(machine, argument)?;
    if index == f64::NEG_INFINITY || index < -(length as f64) {
        return Ok(None);
    }
    Ok(Some(if index < 0.0 {
        (length as f64 + index) as usize
    } else {
        index.min((length - 1) as f64) as usize
    }))
}

fn includes<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let needle = args.first().copied().unwrap_or(Value::UNDEFINED);
    let found = if let Some(start) = forward_start(machine, args.get(1).copied(), length)? {
        let mut found = false;
        for index in start..length {
            let value = read_element(machine, this, index)?;
            if machine.same_value_zero(value, needle) {
                found = true;
                break;
            }
        }
        found
    } else {
        false
    };
    Ok(BuiltinOutcome::Value(Value::boolean(found)))
}

fn index_of<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let needle = args.first().copied().unwrap_or(Value::UNDEFINED);
    let mut found = -1.0;
    if let Some(start) = forward_start(machine, args.get(1).copied(), length)? {
        for index in start..length {
            let value = read_element(machine, this, index)?;
            if machine.strict_equal(value, needle) {
                found = index as f64;
                break;
            }
        }
    }
    Ok(BuiltinOutcome::Value(crate::number_value(found)))
}

fn keys<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    validated(machine, this)?;
    Ok(BuiltinOutcome::Value(super::collections::iterator(
        machine,
        this,
        IterationKind::Key,
    )?))
}

fn last_index_of<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let needle = args.first().copied().unwrap_or(Value::UNDEFINED);
    let mut found = -1.0;
    if let Some(start) = backward_start(machine, args.get(1).copied(), length)? {
        for index in (0..=start).rev() {
            let value = read_element(machine, this, index)?;
            if machine.strict_equal(value, needle) {
                found = index as f64;
                break;
            }
        }
    }
    Ok(BuiltinOutcome::Value(crate::number_value(found)))
}

fn map<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let callback = callback(machine, args)?;
    let target = species_create(machine, this, length)?;
    let this_arg = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    for index in 0..length {
        let value = read_element(machine, this, index)?;
        let mapped = machine.call_value(
            callback,
            this_arg,
            &[value, crate::number_value(index as f64), this],
        )?;
        write_element(machine, target, index, mapped)?;
    }
    Ok(BuiltinOutcome::Value(target))
}

fn reduce_impl<H: Host, I: Iterator<Item = usize>>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    mut indices: I,
) -> Result<Value, EvalFailure> {
    let callback = callback(machine, args)?;
    let mut accumulator = if let Some(initial) = args.get(1).copied() {
        initial
    } else {
        let index = indices
            .next()
            .ok_or_else(|| type_error("Reduce of empty TypedArray with no initial value"))?;
        read_element(machine, this, index)?
    };
    for index in indices {
        let value = read_element(machine, this, index)?;
        accumulator = machine.call_callback(
            callback,
            Value::UNDEFINED,
            &[accumulator, value, crate::number_value(index as f64), this],
        )?;
    }
    Ok(accumulator)
}

fn reduce<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    Ok(BuiltinOutcome::Value(reduce_impl(
        machine,
        this,
        args,
        0..length,
    )?))
}

fn reduce_right<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    Ok(BuiltinOutcome::Value(reduce_impl(
        machine,
        this,
        args,
        (0..length).rev(),
    )?))
}

fn compare_function<H: Host>(
    machine: &Machine<'_, H>,
    args: &[Value],
) -> Result<Option<Value>, EvalFailure> {
    match args.first().copied().unwrap_or(Value::UNDEFINED).decode() {
        Some(Decoded::Undefined) => Ok(None),
        _ => {
            let compare = args[0];
            if !machine.is_callable(compare)? {
                return Err(type_error("TypedArray comparator is not callable"));
            }
            Ok(Some(compare))
        }
    }
}

fn default_typed_array_order<H: Host>(
    machine: &Machine<'_, H>,
    kind: ElementKind,
    left: Value,
    right: Value,
) -> Result<Ordering, EvalFailure> {
    if kind.is_bigint() {
        let left = bigint::bigint_from_value(machine, left)?
            .expect("BigInt TypedArray elements are BigInts");
        let right = bigint::bigint_from_value(machine, right)?
            .expect("BigInt TypedArray elements are BigInts");
        return Ok(left.cmp(&right));
    }

    let number = |value: Value| match value.decode() {
        Some(Decoded::Int32(value)) => f64::from(value as i32),
        Some(Decoded::Number(value)) => value,
        _ => unreachable!("Number TypedArray elements are Numbers"),
    };
    let left = number(left);
    let right = number(right);
    Ok(match (left.is_nan(), right.is_nan()) {
        (true, true) => Ordering::Equal,
        (true, false) => Ordering::Greater,
        (false, true) => Ordering::Less,
        (false, false) if left == 0.0 && right == 0.0 => {
            match (left.is_sign_negative(), right.is_sign_negative()) {
                (true, false) => Ordering::Less,
                (false, true) => Ordering::Greater,
                _ => Ordering::Equal,
            }
        }
        (false, false) => left.total_cmp(&right),
    })
}

fn compare_typed_array_elements<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: ElementKind,
    left: Value,
    right: Value,
    compare: Option<Value>,
) -> Result<Ordering, EvalFailure> {
    let Some(compare) = compare else {
        return default_typed_array_order(machine, kind, left, right);
    };
    let result = machine.call_value(compare, Value::UNDEFINED, &[left, right])?;
    let result = numeric_value(machine, result)?;
    Ok(if result.is_nan() || result == 0.0 {
        Ordering::Equal
    } else if result < 0.0 {
        Ordering::Less
    } else {
        Ordering::Greater
    })
}

fn stable_sort_typed_values<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: ElementKind,
    mut source: Vec<Value>,
    compare: Option<Value>,
) -> Result<Vec<Value>, EvalFailure> {
    if source.len() < 2 {
        return Ok(source);
    }
    let mut target = source.clone();
    let mut width = 1_usize;
    while width < source.len() {
        let mut start = 0_usize;
        while start < source.len() {
            let middle = start.saturating_add(width).min(source.len());
            let end = middle.saturating_add(width).min(source.len());
            let (mut left, mut right, mut output) = (start, middle, start);
            while left < middle && right < end {
                if compare_typed_array_elements(
                    machine,
                    kind,
                    source[left],
                    source[right],
                    compare,
                )? != Ordering::Greater
                {
                    target[output] = source[left];
                    left += 1;
                } else {
                    target[output] = source[right];
                    right += 1;
                }
                output += 1;
            }
            while left < middle {
                target[output] = source[left];
                left += 1;
                output += 1;
            }
            while right < end {
                target[output] = source[right];
                right += 1;
                output += 1;
            }
            start = end;
        }
        std::mem::swap(&mut source, &mut target);
        width = width.saturating_mul(2);
    }
    Ok(source)
}

fn sort<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let compare = compare_function(machine, args)?;
    let (kind, _) = validated(machine, this)?;
    let values = typed_values(machine, this)?;
    let values = stable_sort_typed_values(machine, kind, values, compare)?;
    for (index, value) in values.into_iter().enumerate() {
        write_element(machine, this, index, value)?;
    }
    Ok(BuiltinOutcome::Value(this))
}

fn to_reversed<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let target = same_type_create(machine, this, length)?;
    for index in 0..length {
        let value = read_element(machine, this, length - index - 1)?;
        write_element(machine, target, index, value)?;
    }
    Ok(BuiltinOutcome::Value(target))
}

fn to_sorted<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let compare = compare_function(machine, args)?;
    let (kind, length) = validated(machine, this)?;
    let target = same_type_create(machine, this, length)?;
    let values = typed_values(machine, this)?;
    let values = stable_sort_typed_values(machine, kind, values, compare)?;
    for (index, value) in values.into_iter().enumerate() {
        write_element(machine, target, index, value)?;
    }
    Ok(BuiltinOutcome::Value(target))
}

fn with<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (kind, length) = validated(machine, this)?;
    let relative = integer_or_infinity(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let actual = if relative >= 0.0 {
        relative
    } else {
        length as f64 + relative
    };
    let replacement = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let replacement = if kind.is_bigint() {
        bigint::to_bigint(machine, replacement)?
    } else {
        machine.coerce_number_observable(replacement)?
    };
    let live = typed_array_bounds(machine, this)?;
    if !actual.is_finite()
        || actual < 0.0
        || actual >= live.element_length as f64
        || live.detached
        || live.out_of_bounds
    {
        return Err(range_error("TypedArray index is out of range"));
    }
    let target = same_type_create(machine, this, length)?;
    let actual = actual as usize;
    for index in 0..length {
        let value = if index == actual {
            replacement
        } else {
            read_element(machine, this, index)?
        };
        write_element(machine, target, index, value)?;
    }
    Ok(BuiltinOutcome::Value(target))
}

fn reverse<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let values = typed_values(machine, this)?;
    for (index, value) in values.into_iter().rev().enumerate() {
        write_element(machine, this, index, value)?;
    }
    Ok(BuiltinOutcome::Value(this))
}

fn some<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let callback = callback(machine, args)?;
    let this_arg = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    for index in 0..length {
        let value = read_element(machine, this, index)?;
        if machine.call_truthy(
            callback,
            this_arg,
            &[value, crate::number_value(index as f64), this],
        )? {
            return Ok(BuiltinOutcome::Value(Value::TRUE));
        }
    }
    Ok(BuiltinOutcome::Value(Value::FALSE))
}

fn values<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    validated(machine, this)?;
    Ok(BuiltinOutcome::Value(super::collections::iterator(
        machine,
        this,
        IterationKind::Value,
    )?))
}

fn from<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !machine.is_callable(this)? {
        return Err(type_error("TypedArray.from receiver is not a constructor"));
    }
    let source = args.first().copied().unwrap_or(Value::UNDEFINED);
    let mapper = match args.get(1).copied() {
        Some(value) if value != Value::UNDEFINED => {
            if !machine.is_callable(value)? {
                return Err(type_error("TypedArray.from mapper is not callable"));
            }
            Some(value)
        }
        _ => None,
    };
    let iterator_key =
        PropertyKey::Symbol(heap_index(machine.intrinsics.builtins.symbol_iterator()) as u32);
    let iterator_method = machine.get_property_key(source, &iterator_key)?;
    let values = match iterator_method.decode() {
        Some(Decoded::Undefined | Decoded::Null) => array_like_values(machine, source)?,
        _ if machine.is_callable(iterator_method)? => machine.iterable_values(source)?,
        _ => return Err(type_error("value is not iterable")),
    };
    let target = construct_typed_array(machine, this, values.len())?;
    let this_arg = args.get(2).copied().unwrap_or(Value::UNDEFINED);
    for (index, value) in values.into_iter().enumerate() {
        let value = if let Some(mapper) = mapper {
            machine.call_value(
                mapper,
                this_arg,
                &[value, crate::number_value(index as f64)],
            )?
        } else {
            value
        };
        write_element(machine, target, index, value)?;
    }
    Ok(BuiltinOutcome::Value(target))
}

fn of<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let target = construct_typed_array(machine, this, args.len())?;
    for (index, value) in args.iter().copied().enumerate() {
        write_element(machine, target, index, value)?;
    }
    Ok(BuiltinOutcome::Value(target))
}

fn at<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let index = integer_or_infinity(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let index = if index < 0.0 {
        length as f64 + index
    } else {
        index
    };
    let value = if index < 0.0 || index >= length as f64 {
        Value::UNDEFINED
    } else {
        read_element(machine, this, index as usize)?
    };
    Ok(BuiltinOutcome::Value(value))
}

fn copy_within<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let fields = view_fields(machine, this)?;
    let (_, length) = validated(machine, this)?;
    let target = relative_index(
        machine,
        args.first().copied().unwrap_or(Value::UNDEFINED),
        length,
    )?;
    let start = relative_index(
        machine,
        args.get(1).copied().unwrap_or(Value::UNDEFINED),
        length,
    )?;
    let end = relative_index(
        machine,
        args.get(2)
            .copied()
            .unwrap_or(crate::number_value(length as f64)),
        length,
    )?;
    let requested = end.saturating_sub(start).min(length.saturating_sub(target));
    if requested == 0 {
        return Ok(BuiltinOutcome::Value(this));
    }
    let live = typed_array_bounds_for(machine, fields)?;
    if live.detached || live.out_of_bounds {
        return Err(type_error(
            "TypedArray method called on a detached or out-of-bounds view",
        ));
    }
    let count = requested
        .min(live.element_length.saturating_sub(start))
        .min(live.element_length.saturating_sub(target));
    if count == 0 {
        return Ok(BuiltinOutcome::Value(this));
    }
    let element_size = fields.kind.element_size();
    let source_start = fields.byte_offset + start * element_size;
    let target_start = fields.byte_offset + target * element_size;
    let byte_count = count * element_size;
    ViewBuffer::from_value(machine, fields.buffer)?.with_bytes_mut(machine, |bytes| {
        bytes.copy_within(source_start..source_start + byte_count, target_start);
    })?;
    Ok(BuiltinOutcome::Value(this))
}
fn set<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let target_fields = view_fields(machine, this)?;
    let target_offset =
        integer_or_infinity(machine, args.get(1).copied().unwrap_or(Value::UNDEFINED))?;
    if target_offset < 0.0 {
        return Err(range_error("TypedArray set offset is outside the target"));
    }
    let target_bounds = typed_array_bounds_for(machine, target_fields)?;
    if target_bounds.detached || target_bounds.out_of_bounds {
        return Err(type_error(
            "Cannot write a detached or out-of-bounds TypedArray",
        ));
    }
    if target_offset == f64::INFINITY {
        return Err(range_error("TypedArray set offset is outside the target"));
    }
    let target_offset = target_offset as usize;
    let source = args.first().copied().unwrap_or(Value::UNDEFINED);

    if let Ok(source_fields) = view_fields(machine, source) {
        let source_bounds = typed_array_bounds_for(machine, source_fields)?;
        if source_bounds.detached || source_bounds.out_of_bounds {
            return Err(type_error(
                "Cannot copy a detached or out-of-bounds TypedArray",
            ));
        }
        if target_offset
            .checked_add(source_bounds.element_length)
            .is_none_or(|end| end > target_bounds.element_length)
        {
            return Err(range_error("TypedArray source does not fit in the target"));
        }
        if target_fields.kind.is_bigint() != source_fields.kind.is_bigint() {
            return Err(type_error("Cannot mix BigInt and Number TypedArrays"));
        }

        if target_fields.kind == source_fields.kind {
            let bytes = view_bytes(machine, source_fields, source_bounds)?;
            let target_start =
                target_fields.byte_offset + target_offset * target_fields.kind.element_size();
            ViewBuffer::from_value(machine, target_fields.buffer)?.with_bytes_mut(
                machine,
                |target| {
                    target[target_start..target_start + bytes.len()].copy_from_slice(&bytes);
                },
            )?;
        } else if ViewBuffer::from_value(machine, target_fields.buffer)?
            .same_storage(&ViewBuffer::from_value(machine, source_fields.buffer)?)
        {
            let values = typed_values(machine, source)?;
            for (index, value) in values.into_iter().enumerate() {
                write_element(machine, this, target_offset + index, value)?;
            }
        } else {
            for index in 0..source_bounds.element_length {
                let value = read_element(machine, source, index)?;
                write_element(machine, this, target_offset + index, value)?;
            }
        }
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    }

    let source = machine.value_to_object(source)?;
    let source_length = length_of_array_like(machine, source)?;
    if target_offset
        .checked_add(source_length)
        .is_none_or(|end| end > target_bounds.element_length)
    {
        return Err(range_error(
            "Array-like source does not fit in the TypedArray",
        ));
    }
    for index in 0..source_length {
        let value = machine.get_named_property(source, &index.to_string())?;
        write_element(machine, this, target_offset + index, value)?;
    }
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn slice<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source_fields = view_fields(machine, this)?;
    let (_, length) = validated(machine, this)?;
    let start = relative_index(
        machine,
        args.first().copied().unwrap_or(Value::UNDEFINED),
        length,
    )?;
    let end = relative_index(
        machine,
        args.get(1)
            .copied()
            .unwrap_or(crate::number_value(length as f64)),
        length,
    )?;
    let requested = end.saturating_sub(start);
    let target = species_create(machine, this, requested)?;
    if requested == 0 {
        return Ok(BuiltinOutcome::Value(target));
    }
    let live = typed_array_bounds_for(machine, source_fields)?;
    if live.detached || live.out_of_bounds {
        return Err(type_error(
            "TypedArray method called on a detached or out-of-bounds view",
        ));
    }
    let count = end.min(live.element_length).saturating_sub(start);
    if count == 0 {
        return Ok(BuiltinOutcome::Value(target));
    }
    let target_fields = view_fields(machine, target)?;
    if source_fields.kind == target_fields.kind {
        let element_size = source_fields.kind.element_size();
        let source_start = source_fields.byte_offset + start * element_size;
        let byte_count = count * element_size;
        let source_buffer = ViewBuffer::from_value(machine, source_fields.buffer)?;
        let bytes = source_buffer.with_bytes(machine, |bytes| {
            bytes[source_start..source_start + byte_count].to_vec()
        })?;
        let target_start = target_fields.byte_offset;
        ViewBuffer::from_value(machine, target_fields.buffer)?.with_bytes_mut(
            machine,
            |target| {
                target[target_start..target_start + byte_count].copy_from_slice(&bytes);
            },
        )?;
    } else {
        for index in 0..count {
            let value = read_element(machine, this, start + index)?;
            write_element(machine, target, index, value)?;
        }
    }
    Ok(BuiltinOutcome::Value(target))
}

fn subarray<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let fields = view_fields(machine, this)?;
    let bounds = typed_array_bounds_for(machine, fields)?;
    let length = if bounds.out_of_bounds {
        0
    } else {
        bounds.element_length
    };
    let begin = relative_index(
        machine,
        args.first().copied().unwrap_or(Value::UNDEFINED),
        length,
    )?;
    let end_is_omitted = args.get(1).is_none_or(|value| *value == Value::UNDEFINED);
    let end = if end_is_omitted {
        length
    } else {
        relative_index(machine, args[1], length)?
    };
    let new_length = end.saturating_sub(begin);
    let begin_byte_offset = fields
        .byte_offset
        .checked_add(
            begin
                .checked_mul(fields.kind.element_size())
                .ok_or_else(|| range_error("Invalid TypedArray subarray offset"))?,
        )
        .ok_or_else(|| range_error("Invalid TypedArray subarray offset"))?;
    let constructor = species_constructor(machine, this)?;
    if !machine.is_callable(constructor)? {
        return Err(type_error("TypedArray constructor is not callable"));
    }
    let buffer = fields.buffer;
    let offset = crate::number_value(begin_byte_offset as f64);
    let target = if fields.array_length == LengthSlot::Auto && end_is_omitted {
        machine.construct_value(constructor, &[buffer, offset])?
    } else {
        machine.construct_value(
            constructor,
            &[buffer, offset, crate::number_value(new_length as f64)],
        )?
    };
    let (target_kind, target_length) = validated(machine, target)
        .map_err(|_| type_error("TypedArray constructor did not return a valid TypedArray"))?;
    if target_kind.is_bigint() != fields.kind.is_bigint() {
        return Err(type_error("Cannot mix BigInt and Number TypedArrays"));
    }
    if target_length < new_length {
        return Err(type_error(
            "TypedArray constructor returned an array that is too small",
        ));
    }
    Ok(BuiltinOutcome::Value(target))
}

fn to_locale_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let mut output = EcmaStringBuilder::new();
    for index in 0..length {
        if index != 0 {
            output.push_unit(b',' as u16);
        }
        let value = read_element(machine, this, index)?;
        if matches!(value.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            continue;
        }
        let method = machine.get_named_property(value, "toLocaleString")?;
        if !machine.is_callable(method)? {
            return Err(type_error("toLocaleString is not callable"));
        }
        let localized = machine.call_value(method, value, args)?;
        let text = machine.coerce_string_observable(localized)?;
        for &unit in text.as_units() {
            output.push_unit(unit);
        }
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}

fn entries<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    validated(machine, this)?;
    Ok(BuiltinOutcome::Value(super::collections::iterator(
        machine,
        this,
        IterationKind::Entry,
    )?))
}
fn join<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, length) = validated(machine, this)?;
    let separator = match args.first().copied() {
        None | Some(Value::UNDEFINED) => EcmaString::encode(","),
        Some(value) => machine.coerce_string_observable(value)?,
    };
    let mut output = EcmaStringBuilder::new();
    for index in 0..length {
        if index != 0 {
            for &unit in separator.as_units() {
                output.push_unit(unit);
            }
        }
        let value = read_element(machine, this, index)?;
        if !matches!(value.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            let text = machine.coerce_string_observable(value)?;
            for &unit in text.as_units() {
                output.push_unit(unit);
            }
        }
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intrinsics::builtins::test_support::{TestHost, blank_program, ordinary_object};
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, ThrowOrigin};

    fn with_machine(test: impl FnOnce(&mut Machine<'_, TestHost>)) {
        let program = blank_program("typed-array methods");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        test(&mut machine);
    }

    fn value(outcome: BuiltinOutcome) -> Value {
        let BuiltinOutcome::Value(value) = outcome else {
            panic!("TypedArray builtin did not complete with a value")
        };
        value
    }

    fn typed_array(machine: &mut Machine<'_, TestHost>, name: &str, values: &[Value]) -> Value {
        let constructor = machine
            .intrinsics
            .global(name)
            .expect("constructor is installed");
        let view = machine
            .construct_value(constructor, &[crate::number_value(values.len() as f64)])
            .expect("TypedArray construction succeeds");
        for (index, value) in values.iter().copied().enumerate() {
            assert!(write_element(machine, view, index, value).unwrap());
        }
        view
    }

    fn native(
        machine: &mut Machine<'_, TestHost>,
        name: &'static str,
        handler: BuiltinHandler<TestHost>,
    ) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name,
            length: 2,
            handler,
        });
        native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            name,
            2,
        )
    }

    fn decoded_numbers(machine: &mut Machine<'_, TestHost>, view: Value) -> Vec<f64> {
        typed_values(machine, view)
            .unwrap()
            .into_iter()
            .map(|value| match value.decode() {
                Some(Decoded::Int32(value)) => f64::from(value as i32),
                Some(Decoded::Number(value)) => value,
                _ => panic!("expected Number element"),
            })
            .collect()
    }

    fn compare_tens<H: Host>(
        machine: &mut Machine<'_, H>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let left = numeric_value(machine, args[0])?;
        let right = numeric_value(machine, args[1])?;
        Ok(BuiltinOutcome::Value(crate::number_value(
            (left / 10.0).trunc() - (right / 10.0).trunc(),
        )))
    }

    fn detach_sort_source<H: Host>(
        machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let global = machine
            .intrinsics
            .global("globalThis")
            .expect("globalThis is installed");
        let source = machine.get_named_property(global, "typedArraySortSource")?;
        let buffer = view_fields(machine, source)?.buffer;
        ArrayBufferHandle::from_value(machine, buffer)?.detach(machine, Value::UNDEFINED)?;
        Ok(BuiltinOutcome::Value(Value::int32(0)))
    }

    fn mark_offset_coercion<H: Host>(
        machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let global = machine
            .intrinsics
            .global("globalThis")
            .expect("globalThis is installed");
        machine.set_data_property(global, "typedArrayOffsetCoerced", Value::TRUE)?;
        Ok(BuiltinOutcome::Value(Value::int32(0)))
    }

    fn detach_fill_source<H: Host>(
        machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let global = machine
            .intrinsics
            .global("globalThis")
            .expect("globalThis is installed");
        let source = machine.get_named_property(global, "typedArrayFillSource")?;
        let buffer = view_fields(machine, source)?.buffer;
        ArrayBufferHandle::from_value(machine, buffer)?.detach(machine, Value::UNDEFINED)?;
        Ok(BuiltinOutcome::Value(Value::int32(9)))
    }

    #[test]
    fn sort_mutates_with_numeric_and_custom_stable_ordering() {
        with_machine(|machine| {
            let source = typed_array(
                machine,
                "Float64Array",
                &[
                    crate::number_value(f64::NAN),
                    crate::number_value(0.0),
                    Value::number(-0.0),
                    crate::number_value(2.0),
                    crate::number_value(1.0),
                ],
            );
            assert_eq!(value(sort(machine, source, &[], false).unwrap()), source);
            let numbers = decoded_numbers(machine, source);
            assert!(numbers[0] == 0.0 && numbers[0].is_sign_negative());
            assert!(numbers[1] == 0.0 && numbers[1].is_sign_positive());
            assert_eq!(&numbers[2..4], &[1.0, 2.0]);
            assert!(numbers[4].is_nan());

            let source = typed_array(
                machine,
                "Int16Array",
                &[
                    Value::int32(21),
                    Value::int32(10),
                    Value::int32(20),
                    Value::int32(11),
                    Value::int32(12),
                ],
            );
            let compare = native(machine, "compare tens", compare_tens::<TestHost>);
            sort(machine, source, &[compare], false).unwrap();
            assert_eq!(
                decoded_numbers(machine, source),
                vec![10.0, 11.0, 12.0, 21.0, 20.0]
            );
        });
    }

    #[test]
    fn to_reversed_ignores_species_and_does_not_mutate_source() {
        with_machine(|machine| {
            let source = typed_array(
                machine,
                "Uint8Array",
                &[Value::int32(1), Value::int32(2), Value::int32(3)],
            );
            let species_holder = ordinary_object(machine);
            let species = machine.intrinsics.global("Int16Array").unwrap();
            let species_key = PropertyKey::Symbol(heap_index(
                machine.intrinsics.builtins.symbol_species(),
            ) as u32);
            machine
                .set_data_property_key(species_holder, species_key, species)
                .unwrap();
            machine
                .set_data_property(source, "constructor", species_holder)
                .unwrap();
            let reversed = value(to_reversed(machine, source, &[], false).unwrap());
            assert_ne!(reversed, source);
            assert_eq!(
                view_fields(machine, reversed).unwrap().kind,
                ElementKind::Uint8
            );
            assert_eq!(decoded_numbers(machine, reversed), vec![3.0, 2.0, 1.0]);
            assert_eq!(decoded_numbers(machine, source), vec![1.0, 2.0, 3.0]);
        });
    }

    #[test]
    fn to_sorted_orders_bigints_and_uses_captured_values_after_detach() {
        with_machine(|machine| {
            let values = ["10", "-1", "2"].map(|text| {
                machine
                    .allocate(HeapEntry::BigInt(text.to_owned()))
                    .expect("BigInt allocation succeeds")
            });
            let source = typed_array(machine, "BigInt64Array", &values);
            let sorted = value(to_sorted(machine, source, &[], false).unwrap());
            assert_ne!(sorted, source);
            assert_eq!(
                debug_elements(machine, sorted, usize::MAX).unwrap().2,
                vec!["-1", "2", "10"]
            );
            assert_eq!(
                debug_elements(machine, source, usize::MAX).unwrap().2,
                vec!["10", "-1", "2"]
            );

            let source = typed_array(machine, "Uint8Array", &[Value::int32(2), Value::int32(1)]);
            let global = machine.intrinsics.global("globalThis").unwrap();
            machine
                .set_data_property(global, "typedArraySortSource", source)
                .unwrap();
            let compare = native(
                machine,
                "detach sort source",
                detach_sort_source::<TestHost>,
            );
            let copied = value(to_sorted(machine, source, &[compare], false).unwrap());
            assert_eq!(decoded_numbers(machine, copied), vec![2.0, 1.0]);
            let source_buffer = view_fields(machine, source).unwrap().buffer;
            assert!(
                ArrayBufferHandle::from_value(machine, source_buffer)
                    .unwrap()
                    .is_detached(machine)
            );
        });
    }

    #[test]
    fn with_converts_before_range_check_and_ignores_species() {
        with_machine(|machine| {
            let one = machine
                .allocate(HeapEntry::BigInt("1".to_owned()))
                .expect("BigInt allocation succeeds");
            let two = machine
                .allocate(HeapEntry::BigInt("2".to_owned()))
                .expect("BigInt allocation succeeds");
            let source = typed_array(machine, "BigInt64Array", &[one, two]);
            assert!(matches!(
                with(machine, source, &[Value::int32(4), Value::int32(9)], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));

            let species_holder = ordinary_object(machine);
            let species = machine.intrinsics.global("Uint8Array").unwrap();
            let species_key = PropertyKey::Symbol(heap_index(
                machine.intrinsics.builtins.symbol_species(),
            ) as u32);
            machine
                .set_data_property_key(species_holder, species_key, species)
                .unwrap();
            machine
                .set_data_property(source, "constructor", species_holder)
                .unwrap();
            let nine = machine
                .allocate(HeapEntry::BigInt("9".to_owned()))
                .expect("BigInt allocation succeeds");
            let copied =
                value(with(machine, source, &[Value::int32(u32::MAX), nine], false).unwrap());
            assert_ne!(copied, source);
            assert_eq!(
                view_fields(machine, copied).unwrap().kind,
                ElementKind::BigInt64
            );
            assert_eq!(
                debug_elements(machine, copied, usize::MAX).unwrap().2,
                vec!["1", "9"]
            );
            assert_eq!(
                debug_elements(machine, source, usize::MAX).unwrap().2,
                vec!["1", "2"]
            );
        });
    }

    #[test]
    fn debug_elements_returns_bounded_prefix_and_total_length() {
        with_machine(|machine| {
            let elements = vec![Value::int32(7); 150];
            let view = typed_array(machine, "Uint8Array", &elements);
            let (kind, total, prefix) = debug_elements(machine, view, 100).unwrap();
            assert_eq!(kind, ElementKind::Uint8);
            assert_eq!(total, 150);
            assert_eq!(prefix.len(), 100);
            assert!(prefix.iter().all(|value| value == "7"));
        });
    }

    #[test]
    fn to_string_delegates_to_array_prototype_join() {
        with_machine(|machine| {
            let view = typed_array(machine, "Uint8Array", &[Value::int32(1), Value::int32(2)]);
            let to_string = machine.get_named_property(view, "toString").unwrap();
            let result = machine.call_value(to_string, view, &[]).unwrap();
            assert!(
                machine
                    .string_value(result)
                    .is_some_and(|text| text.eq_ascii("1,2"))
            );
        });
    }

    #[test]
    fn base64_and_hex_methods_round_trip_uint8_data() {
        with_machine(|machine| {
            let constructor = machine.intrinsics.global("Uint8Array").unwrap();
            let source = allocate_string(machine, EcmaString::encode("SGVsbG8=")).unwrap();
            let decoded = value(from_base64(machine, constructor, &[source], false).unwrap());
            assert_eq!(
                decoded_numbers(machine, decoded),
                vec![72.0, 101.0, 108.0, 108.0, 111.0]
            );
            let encoded = value(to_base64(machine, decoded, &[], false).unwrap());
            assert!(
                machine
                    .string_value(encoded)
                    .is_some_and(|text| text.eq_ascii("SGVsbG8="))
            );

            let hex = value(to_hex(machine, decoded, &[], false).unwrap());
            assert!(
                machine
                    .string_value(hex)
                    .is_some_and(|text| text.eq_ascii("48656c6c6f"))
            );
            let decoded =
                value(from_hex(machine, constructor, &[hex], false).expect("valid hex decodes"));
            assert_eq!(
                decoded_numbers(machine, decoded),
                vec![72.0, 101.0, 108.0, 108.0, 111.0]
            );
        });
    }

    #[test]
    fn encoding_methods_validate_strings_capacity_partial_errors_and_options() {
        with_machine(|machine| {
            let target = typed_array(machine, "Uint8Array", &[Value::int32(0), Value::int32(0)]);
            let source = allocate_string(machine, EcmaString::encode("AQI=")).unwrap();
            let result = value(set_from_base64(machine, target, &[source], false).unwrap());
            assert_eq!(
                machine.get_named_property(result, "read").unwrap(),
                crate::number_value(4.0)
            );
            assert_eq!(
                machine.get_named_property(result, "written").unwrap(),
                crate::number_value(2.0)
            );
            assert_eq!(decoded_numbers(machine, target), vec![1.0, 2.0]);

            let short = typed_array(machine, "Uint8Array", &[Value::int32(9)]);
            let full_chunk = allocate_string(machine, EcmaString::encode("TWFu")).unwrap();
            let result = value(set_from_base64(machine, short, &[full_chunk], false).unwrap());
            assert_eq!(
                machine.get_named_property(result, "read").unwrap(),
                crate::number_value(0.0)
            );
            assert_eq!(
                machine.get_named_property(result, "written").unwrap(),
                crate::number_value(0.0)
            );
            assert_eq!(decoded_numbers(machine, short), vec![9.0]);

            let padded = allocate_string(machine, EcmaString::encode("TQ==")).unwrap();
            let result = value(set_from_base64(machine, short, &[padded], false).unwrap());
            assert_eq!(
                machine.get_named_property(result, "read").unwrap(),
                crate::number_value(4.0)
            );
            assert_eq!(decoded_numbers(machine, short), vec![77.0]);

            let partial_target = typed_array(
                machine,
                "Uint8Array",
                &[
                    Value::int32(0),
                    Value::int32(0),
                    Value::int32(0),
                    Value::int32(0),
                ],
            );
            let invalid = allocate_string(machine, EcmaString::encode("TWFu$")).unwrap();
            let Err(EvalFailure::ThrowValue(error)) =
                set_from_base64(machine, partial_target, &[invalid], false)
            else {
                panic!("invalid base64 input throws SyntaxError after its valid prefix")
            };
            assert_eq!(
                decoded_numbers(machine, partial_target),
                vec![77.0, 97.0, 110.0, 0.0]
            );
            let syntax_error = machine
                .intrinsics
                .builtins
                .id_named("SyntaxError")
                .expect("SyntaxError is installed");
            assert_eq!(
                machine.internal_get_prototype_of(error).unwrap(),
                Some(machine.intrinsics.error_prototype(syntax_error))
            );

            let options = ordinary_object(machine);
            let strict = allocate_string(machine, EcmaString::encode("strict")).unwrap();
            machine
                .set_data_property(options, "lastChunkHandling", strict)
                .unwrap();
            let overflow = allocate_string(machine, EcmaString::encode("TR==")).unwrap();
            assert!(matches!(
                set_from_base64(machine, short, &[overflow, options], false),
                Err(EvalFailure::ThrowValue(_))
            ));

            let invalid_options = ordinary_object(machine);
            machine
                .set_data_property(invalid_options, "alphabet", Value::int32(1))
                .unwrap();
            let uint8_constructor = machine.intrinsics.global("Uint8Array").unwrap();
            assert!(matches!(
                from_base64(
                    machine,
                    uint8_constructor,
                    &[padded, invalid_options],
                    false,
                ),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert!(matches!(
                from_hex(machine, uint8_constructor, &[Value::int32(255)], false,),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));

            let hex_target =
                typed_array(machine, "Uint8Array", &[Value::int32(0), Value::int32(0)]);
            let invalid_hex = allocate_string(machine, EcmaString::encode("ffgg")).unwrap();
            assert!(matches!(
                set_from_hex(machine, hex_target, &[invalid_hex], false),
                Err(EvalFailure::ThrowValue(_))
            ));
            assert_eq!(decoded_numbers(machine, hex_target), vec![255.0, 0.0]);

            let int16 = machine.intrinsics.global("Int16Array").unwrap();
            let decoded = value(from_base64(machine, int16, &[padded], false).unwrap());
            assert_eq!(
                view_fields(machine, decoded).unwrap().kind,
                ElementKind::Uint8
            );
        });
    }

    #[test]
    fn all_families_round_trip_their_content_type_and_signed_values() {
        with_machine(|machine| {
            let minus_one_bigint = machine
                .allocate(HeapEntry::BigInt("-1".to_owned()))
                .expect("BigInt allocation succeeds");
            for kind in ElementKind::ALL {
                let input = if kind.is_bigint() {
                    minus_one_bigint
                } else {
                    crate::number_value(-1.0)
                };
                let view = typed_array(machine, kind.name(), &[input]);
                let fields = view_fields(machine, view).unwrap();
                assert_eq!(
                    fields.kind,
                    kind,
                    "{} stores its own element kind",
                    kind.name()
                );
                assert_eq!(validated(machine, view).unwrap().1, 1);
                let value = read_element(machine, view, 0).unwrap();
                if kind.is_bigint() {
                    assert!(bigint::bigint_from_value(machine, value).unwrap().is_some());
                } else {
                    assert!(matches!(
                        value.decode(),
                        Some(Decoded::Int32(_) | Decoded::Number(_))
                    ));
                }
            }
            let int8 = typed_array(machine, "Int8Array", &[crate::number_value(-1.0)]);
            assert_eq!(decoded_numbers(machine, int8), vec![-1.0]);
            let clamped = typed_array(
                machine,
                "Uint8ClampedArray",
                &[
                    crate::number_value(2.5),
                    crate::number_value(3.5),
                    crate::number_value(254.5),
                ],
            );
            assert_eq!(decoded_numbers(machine, clamped), vec![2.0, 4.0, 254.0]);
            for name in ["Float16Array", "Float32Array", "Float64Array"] {
                let view = typed_array(machine, name, &[Value::number(-0.0)]);
                let value = decoded_numbers(machine, view)[0];
                assert!(
                    value == 0.0 && value.is_sign_negative(),
                    "{name} preserves -0"
                );
            }
        });
    }

    #[test]
    fn resizable_views_track_whole_elements_and_fixed_views_recover() {
        with_machine(|machine| {
            let handle = ArrayBufferHandle::allocate(machine, 8, Some(16)).unwrap();
            let constructor = machine.intrinsics.global("Uint16Array").unwrap();
            let tracking = machine
                .construct_value(constructor, &[handle.value(), Value::int32(2)])
                .unwrap();
            let fixed = machine
                .construct_value(
                    constructor,
                    &[handle.value(), Value::int32(2), Value::int32(3)],
                )
                .unwrap();
            assert_eq!(
                typed_array_bounds(machine, tracking)
                    .unwrap()
                    .element_length,
                3
            );
            assert_eq!(
                typed_array_bounds(machine, tracking).unwrap().byte_length,
                6
            );

            handle.resize(machine, 7).unwrap();
            let tracking_bounds = typed_array_bounds(machine, tracking).unwrap();
            assert_eq!(tracking_bounds.element_length, 2);
            assert_eq!(tracking_bounds.byte_length, 4);
            assert_eq!(
                typed_array_bounds(machine, fixed).unwrap().element_length,
                0
            );
            assert!(matches!(
                fill(machine, fixed, &[Value::int32(1)], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));

            handle.resize(machine, 8).unwrap();
            assert_eq!(validated(machine, fixed).unwrap().1, 3);
            handle.resize(machine, 1).unwrap();
            let tracking_bounds = typed_array_bounds(machine, tracking).unwrap();
            assert!(tracking_bounds.out_of_bounds);
            assert_eq!(
                value(get_byte_offset(machine, tracking, &[], false).unwrap()),
                crate::number_value(0.0)
            );
        });
    }

    #[test]
    fn constructors_enforce_alignment_content_type_and_raw_bit_copying() {
        with_machine(|machine| {
            let odd = ArrayBufferHandle::allocate(machine, 3, None).unwrap();
            let uint16 = machine.intrinsics.global("Uint16Array").unwrap();
            assert!(matches!(
                machine.construct_value(uint16, &[odd.value()]),
                Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
            ));
            let aligned = ArrayBufferHandle::allocate(machine, 8, None).unwrap();
            assert!(matches!(
                machine.construct_value(uint16, &[aligned.value(), Value::int32(1)]),
                Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
            ));

            let negative_length = ordinary_object(machine);
            machine
                .set_data_property(negative_length, "length", crate::number_value(-3.0))
                .unwrap();
            let empty = machine.construct_value(uint16, &[negative_length]).unwrap();
            assert_eq!(validated(machine, empty).unwrap().1, 0);

            let number_source = typed_array(machine, "Uint8Array", &[Value::int32(1)]);
            let bigint64 = machine.intrinsics.global("BigInt64Array").unwrap();
            assert!(matches!(
                machine.construct_value(bigint64, &[number_source]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));

            let source = typed_array(machine, "Float64Array", &[Value::number(f64::NAN)]);
            let source_fields = view_fields(machine, source).unwrap();
            let payload = 0x7ff8_0000_0000_1234_u64.to_le_bytes();
            ViewBuffer::from_value(machine, source_fields.buffer)
                .unwrap()
                .with_bytes_mut(machine, |bytes| bytes.copy_from_slice(&payload))
                .unwrap();
            let float64 = machine.intrinsics.global("Float64Array").unwrap();
            let copied = machine.construct_value(float64, &[source]).unwrap();
            let copied_fields = view_fields(machine, copied).unwrap();
            let copied_bytes = ViewBuffer::from_value(machine, copied_fields.buffer)
                .unwrap()
                .with_bytes(machine, |bytes| bytes.to_vec())
                .unwrap();
            assert_eq!(copied_bytes, payload);
            let sliced = value(slice(machine, source, &[], false).unwrap());
            let sliced_fields = view_fields(machine, sliced).unwrap();
            let sliced_bytes = ViewBuffer::from_value(machine, sliced_fields.buffer)
                .unwrap()
                .with_bytes(machine, |bytes| bytes.to_vec())
                .unwrap();
            assert_eq!(sliced_bytes, payload);
            let set_target = typed_array(machine, "Float64Array", &[Value::number(0.0)]);
            set(machine, set_target, &[source], false).unwrap();
            let set_fields = view_fields(machine, set_target).unwrap();
            let set_bytes = ViewBuffer::from_value(machine, set_fields.buffer)
                .unwrap()
                .with_bytes(machine, |bytes| bytes.to_vec())
                .unwrap();
            assert_eq!(set_bytes, payload);

            let species_source = typed_array(machine, "Uint8Array", &[Value::int32(1)]);
            let species_holder = ordinary_object(machine);
            let species_key = PropertyKey::Symbol(heap_index(
                machine.intrinsics.builtins.symbol_species(),
            ) as u32);
            machine
                .set_data_property_key(species_holder, species_key, bigint64)
                .unwrap();
            machine
                .set_data_property(species_source, "constructor", species_holder)
                .unwrap();
            assert!(matches!(
                slice(machine, species_source, &[], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        });
    }

    #[test]
    fn copy_within_and_set_snapshot_overlap_and_preserve_raw_bits() {
        with_machine(|machine| {
            let target = typed_array(
                machine,
                "Uint8Array",
                &[
                    Value::int32(1),
                    Value::int32(2),
                    Value::int32(3),
                    Value::int32(4),
                ],
            );
            copy_within(
                machine,
                target,
                &[Value::int32(1), Value::int32(0), Value::int32(3)],
                false,
            )
            .unwrap();
            assert_eq!(decoded_numbers(machine, target), vec![1.0, 1.0, 2.0, 3.0]);

            let source = value(
                subarray(machine, target, &[Value::int32(0), Value::int32(3)], false).unwrap(),
            );
            set(machine, target, &[source, Value::int32(1)], false).unwrap();
            assert_eq!(decoded_numbers(machine, target), vec![1.0, 1.0, 1.0, 2.0]);

            let big = machine
                .allocate(HeapEntry::BigInt("7".to_owned()))
                .expect("BigInt allocation succeeds");
            let bigint_target = typed_array(machine, "BigInt64Array", &[big]);
            let number_source = typed_array(machine, "Uint8Array", &[Value::int32(1)]);
            assert!(matches!(
                set(machine, bigint_target, &[number_source], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert_eq!(
                debug_elements(machine, bigint_target, usize::MAX)
                    .unwrap()
                    .2,
                vec!["7"]
            );
        });
    }

    #[test]
    fn coercions_run_before_late_buffer_validation_without_mutation() {
        with_machine(|machine| {
            let target = typed_array(machine, "Uint8Array", &[Value::int32(1)]);
            let target_buffer = view_fields(machine, target).unwrap().buffer;
            ArrayBufferHandle::from_value(machine, target_buffer)
                .unwrap()
                .detach(machine, Value::UNDEFINED)
                .unwrap();
            let offset = ordinary_object(machine);
            let value_of = native(
                machine,
                "mark offset coercion",
                mark_offset_coercion::<TestHost>,
            );
            machine
                .set_data_property(offset, "valueOf", value_of)
                .unwrap();
            let source = ordinary_object(machine);
            machine
                .set_data_property(source, "length", Value::int32(0))
                .unwrap();
            assert!(matches!(
                set(machine, target, &[source, offset], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            let global = machine.intrinsics.global("globalThis").unwrap();
            assert_eq!(
                machine
                    .get_named_property(global, "typedArrayOffsetCoerced")
                    .unwrap(),
                Value::TRUE
            );

            let fill_target = typed_array(machine, "Uint8Array", &[Value::int32(1)]);
            machine
                .set_data_property(global, "typedArrayFillSource", fill_target)
                .unwrap();
            let replacement = ordinary_object(machine);
            let replacement_value_of = native(
                machine,
                "detach fill source",
                detach_fill_source::<TestHost>,
            );
            machine
                .set_data_property(replacement, "valueOf", replacement_value_of)
                .unwrap();
            assert!(matches!(
                fill(machine, fill_target, &[replacement], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        });
    }

    #[test]
    fn accessors_and_methods_reject_wrong_receivers_and_detached_views() {
        with_machine(|machine| {
            let ordinary = ordinary_object(machine);
            assert!(matches!(
                get_buffer(machine, ordinary, &[], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert!(matches!(
                includes(machine, ordinary, &[Value::int32(0)], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert_eq!(
                value(get_to_string_tag(machine, ordinary, &[], false).unwrap()),
                Value::UNDEFINED
            );

            let view = typed_array(machine, "Uint8Array", &[Value::int32(1)]);
            let tag = value(get_to_string_tag(machine, view, &[], false).unwrap());
            assert!(
                machine
                    .string_value(tag)
                    .is_some_and(|text| text.eq_ascii("Uint8Array"))
            );
            let buffer = view_fields(machine, view).unwrap().buffer;
            ArrayBufferHandle::from_value(machine, buffer)
                .unwrap()
                .detach(machine, Value::UNDEFINED)
                .unwrap();
            assert_eq!(
                value(get_length(machine, view, &[], false).unwrap()),
                crate::number_value(0.0)
            );
            assert_eq!(
                value(get_byte_length(machine, view, &[], false).unwrap()),
                crate::number_value(0.0)
            );
            assert!(matches!(
                includes(machine, view, &[Value::int32(1)], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        });
    }

    #[test]
    fn searches_distinguish_nan_signed_zero_and_extreme_starts() {
        with_machine(|machine| {
            let source = typed_array(
                machine,
                "Float64Array",
                &[
                    Value::number(f64::NAN),
                    Value::number(-0.0),
                    Value::number(0.0),
                    Value::number(3.0),
                ],
            );
            assert_eq!(
                value(includes(machine, source, &[Value::number(f64::NAN)], false).unwrap()),
                Value::TRUE
            );
            assert_eq!(
                value(index_of(machine, source, &[Value::number(f64::NAN)], false).unwrap()),
                crate::number_value(-1.0)
            );
            assert_eq!(
                value(
                    index_of(
                        machine,
                        source,
                        &[Value::number(0.0), Value::number(-3.0)],
                        false,
                    )
                    .unwrap()
                ),
                crate::number_value(1.0)
            );
            assert_eq!(
                value(last_index_of(machine, source, &[Value::number(-0.0)], false).unwrap()),
                crate::number_value(2.0)
            );
            assert_eq!(
                value(
                    includes(
                        machine,
                        source,
                        &[Value::number(3.0), Value::number(f64::INFINITY)],
                        false,
                    )
                    .unwrap()
                ),
                Value::FALSE
            );
        });
    }

    #[test]
    fn kind_table_is_complete_and_unique() {
        assert_eq!(ElementKind::ALL.len(), KIND_COUNT);
        let mut names = ElementKind::ALL.map(ElementKind::name).to_vec();
        names.sort_unstable();
        names.dedup();
        assert_eq!(names.len(), KIND_COUNT);
        assert_eq!(ElementKind::Float16.element_size(), 2);
        assert!(ElementKind::BigInt64.is_bigint());
    }

    #[test]
    fn integer_conversions_follow_ecmascript_modulo_and_clamp_rules() {
        assert_eq!(to_uint_mod(-1.0, 8), 255);
        assert_eq!(to_int_mod(255.0, 8), -1);
        assert_eq!(to_uint_mod(f64::NAN, 32), 0);
        assert_eq!(to_uint8_clamp(2.5), 2);
        assert_eq!(to_uint8_clamp(3.5), 4);
        assert_eq!(to_uint8_clamp(300.0), 255);
    }

    #[test]
    fn float16_round_trips_boundaries_and_special_values() {
        for value in [
            0.0,
            -0.0,
            1.0,
            -2.0,
            65_504.0,
            2_f64.powi(-14),
            2_f64.powi(-24),
        ] {
            let round_trip = f16_bits_to_f64(f64_to_f16_bits(value));
            assert_eq!(round_trip.to_bits(), value.to_bits(), "{value}");
        }
        assert_eq!(f64_to_f16_bits(65_520.0), 0x7c00);
        assert_eq!(f64_to_f16_bits(f64::INFINITY), 0x7c00);
        assert_eq!(f64_to_f16_bits(f64::NEG_INFINITY), 0xfc00);
        assert!(f16_bits_to_f64(f64_to_f16_bits(f64::NAN)).is_nan());
    }

    #[test]
    fn float16_rounding_is_ties_to_even() {
        let one = 1.0;
        let half_ulp = 2_f64.powi(-11);
        assert_eq!(f64_to_f16_bits(one + half_ulp), f64_to_f16_bits(one));
        let odd = f16_bits_to_f64(0x3c01);
        assert_eq!(f64_to_f16_bits(odd + half_ulp), 0x3c02);
        assert_eq!(f64_to_f16_bits(2_f64.powi(-25)), 0x0000);
        assert_eq!(f64_to_f16_bits(3.0 * 2_f64.powi(-25)), 0x0002);
    }
}
