//! BigInt built-in: constructor, static width converters, prototype methods,
//! and the arbitrary-precision numeric core ECMA-262 §6.1.6.2 / §21.2 requires.
//!
//! The runtime heap stores a BigInt as `HeapEntry::BigInt(String)` in canonical
//! decimal form. All arithmetic runs over the sign-magnitude `BigIntValue`
//! core below; the existing i128-bounded operator paths in `Machine` are
//! superseded by the `pub(crate)` helpers at the bottom of this module, which
//! the VM opcode and coercion paths rewire to (see the wiring report).
//!
//! Typed abrupt completion contract:
//! - division/remainder by zero and negative exponents are `RangeError`;
//! - mixed BigInt/Number arithmetic is a `TypeError`;
//! - non-integral `Number -> BigInt` conversion is a `RangeError`;
//! - `StringToBigInt` failures are real `SyntaxError` objects built through
//!   the installed `SyntaxError` constructor (mirrors `json_edge.rs`); a zero-length
//!   or whitespace-only string is `0n`, never an error.

use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, Value};

use super::{allocate_string, define_data, heap_index, install_function, range_error, type_error};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::{
    EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, ThrowOrigin, numeric_f64,
};

// ---- BIGINT CORE START ----
// Self-contained arbitrary-precision integer core. Everything between the
// markers avoids crate-internal imports so this section can be extracted and
// executed standalone (`rustc --test`) without the runtime wiring being live.
mod bigint_core {
    use std::cmp::Ordering;

    /// Maximum bit length of a produced BigInt value. Engines bound BigInt
    /// allocation similarly; exceeding this host capability is a typed
    /// `RangeError`, never a silent fallback.
    const MAX_VALUE_BITS: usize = 1 << 22;

    /// Sign-magnitude arbitrary-precision integer. `limbs` is little-endian
    /// base 2^32, normalized: zero is `limbs.is_empty()` and never negative.
    #[derive(Clone, Debug, Default, Eq, PartialEq)]
    pub(crate) struct BigIntValue {
        negative: bool,
        limbs: Vec<u32>,
    }

    /// Errors arising inside BigInt evaluation. The kind encodes the exact
    /// ECMA-262 error class; the Machine boundary picks the carrier.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub(crate) enum BigIntError {
        /// Division or remainder by zero; negative exponent; oversized value.
        Range(&'static str),
        /// Input is not a valid BigInt string per `StringToBigInt`.
        Syntax(&'static str),
    }

    // -- magnitude primitives -------------------------------------------------

    fn mag_trim(limbs: &mut Vec<u32>) {
        while limbs.last() == Some(&0) {
            limbs.pop();
        }
    }

    fn mag_cmp(a: &[u32], b: &[u32]) -> Ordering {
        if a.len() != b.len() {
            return a.len().cmp(&b.len());
        }
        for i in (0..a.len()).rev() {
            match a[i].cmp(&b[i]) {
                Ordering::Equal => {}
                order => return order,
            }
        }
        Ordering::Equal
    }

    fn mag_add(a: &[u32], b: &[u32]) -> Vec<u32> {
        let (long, short) = if a.len() >= b.len() { (a, b) } else { (b, a) };
        let mut out = Vec::with_capacity(long.len() + 1);
        let mut carry = 0u64;
        for (i, &limb) in long.iter().enumerate() {
            let sum = u64::from(limb) + u64::from(short.get(i).copied().unwrap_or(0)) + carry;
            out.push(sum as u32);
            carry = sum >> 32;
        }
        if carry != 0 {
            out.push(carry as u32);
        }
        out
    }

    /// Requires `a >= b`.
    fn mag_sub(a: &[u32], b: &[u32]) -> Vec<u32> {
        debug_assert!(mag_cmp(a, b) != Ordering::Less);
        let mut out = Vec::with_capacity(a.len());
        let mut borrow = false;
        for (i, &limb) in a.iter().enumerate() {
            let (d1, under1) = limb.overflowing_sub(b.get(i).copied().unwrap_or(0));
            let (d2, under2) = d1.overflowing_sub(u32::from(borrow));
            out.push(d2);
            borrow = under1 || under2;
        }
        debug_assert!(!borrow);
        mag_trim(&mut out);
        out
    }

    fn mag_mul(a: &[u32], b: &[u32]) -> Vec<u32> {
        if a.is_empty() || b.is_empty() {
            return Vec::new();
        }
        let mut out = vec![0u32; a.len() + b.len()];
        for (i, &ai) in a.iter().enumerate() {
            let mut carry = 0u64;
            for (j, &bj) in b.iter().enumerate() {
                let acc = u64::from(out[i + j]) + u64::from(ai) * u64::from(bj) + carry;
                out[i + j] = acc as u32;
                carry = acc >> 32;
            }
            let mut k = i + b.len();
            while carry != 0 {
                let acc = u64::from(out[k]) + carry;
                out[k] = acc as u32;
                carry = acc >> 32;
                k += 1;
            }
        }
        mag_trim(&mut out);
        out
    }

    fn mag_shl_bits(a: &[u32], bits: usize) -> Vec<u32> {
        if a.is_empty() {
            return Vec::new();
        }
        let limb_shift = bits / 32;
        let bit_shift = (bits % 32) as u32;
        let mut out = vec![0u32; limb_shift];
        if bit_shift == 0 {
            out.extend_from_slice(a);
        } else {
            let mut carry = 0u32;
            for &limb in a {
                out.push((limb << bit_shift) | carry);
                carry = limb >> (32 - bit_shift);
            }
            if carry != 0 {
                out.push(carry);
            }
        }
        out
    }

    fn mag_shr_bits(a: &[u32], bits: usize) -> Vec<u32> {
        let limb_shift = bits / 32;
        if limb_shift >= a.len() {
            return Vec::new();
        }
        let a = &a[limb_shift..];
        let bit_shift = (bits % 32) as u32;
        let mut out = Vec::with_capacity(a.len());
        if bit_shift == 0 {
            out.extend_from_slice(a);
        } else {
            for (i, &limb) in a.iter().enumerate() {
                let high = a.get(i + 1).copied().unwrap_or(0);
                out.push((limb >> bit_shift) | (high << (32 - bit_shift)));
            }
        }
        mag_trim(&mut out);
        out
    }

    fn bit_length_limbs(a: &[u32]) -> usize {
        match a.last() {
            None => 0,
            Some(&top) => {
                debug_assert!(top != 0);
                (a.len() - 1) * 32 + (32 - top.leading_zeros() as usize)
            }
        }
    }

    fn test_bit_limbs(a: &[u32], bit: usize) -> bool {
        a.get(bit / 32)
            .is_some_and(|limb| (limb >> (bit % 32)) & 1 == 1)
    }

    fn any_bit_below_limbs(a: &[u32], bit: usize) -> bool {
        let full = bit / 32;
        if a.iter().take(full).any(|&limb| limb != 0) {
            return true;
        }
        let rem = bit % 32;
        rem != 0
            && a.get(full)
                .is_some_and(|limb| limb & ((1u32 << rem) - 1) != 0)
    }

    fn mag_mul_add_small(a: &[u32], factor: u32, add: u32) -> Vec<u32> {
        let mut out = Vec::with_capacity(a.len() + 1);
        let mut carry = u64::from(add);
        for &limb in a {
            let acc = u64::from(limb) * u64::from(factor) + carry;
            out.push(acc as u32);
            carry = acc >> 32;
        }
        while carry != 0 {
            out.push(carry as u32);
            carry >>= 32;
        }
        mag_trim(&mut out);
        out
    }

    /// Knuth TAOCP 4.3.1 algorithm D over u32 limbs with u64 intermediates.
    /// `v` must be nonzero with a set top limb. Returns `(quotient, remainder)`
    /// magnitudes with `u = q * v + r` and `0 <= r < v`.
    fn mag_divmod(u: &[u32], v: &[u32]) -> (Vec<u32>, Vec<u32>) {
        debug_assert!(!v.is_empty() && v.last() != Some(&0));
        if mag_cmp(u, v) == Ordering::Less {
            return (Vec::new(), u.to_vec());
        }
        if v.len() == 1 {
            let d = u64::from(v[0]);
            let mut q = Vec::with_capacity(u.len());
            let mut rem = 0u64;
            for &limb in u.iter().rev() {
                let cur = (rem << 32) | u64::from(limb);
                q.push((cur / d) as u32);
                rem = cur % d;
            }
            q.reverse();
            mag_trim(&mut q);
            let mut r = vec![rem as u32];
            mag_trim(&mut r);
            return (q, r);
        }
        let n = v.len();
        let m = u.len() - n;
        let shift = v[n - 1].leading_zeros();
        let mut vn = vec![0u32; n];
        if shift == 0 {
            vn.copy_from_slice(v);
        } else {
            for i in (1..n).rev() {
                vn[i] = (v[i] << shift) | (v[i - 1] >> (32 - shift));
            }
            vn[0] = v[0] << shift;
        }
        let mut un = vec![0u32; u.len() + 1];
        if shift == 0 {
            un[..u.len()].copy_from_slice(u);
        } else {
            let mut carry = 0u32;
            for (i, &limb) in u.iter().enumerate() {
                un[i] = (limb << shift) | carry;
                carry = limb >> (32 - shift);
            }
            un[u.len()] = carry;
        }
        let mut q = vec![0u32; m + 1];
        for j in (0..=m).rev() {
            let high = (u64::from(un[j + n]) << 32) | u64::from(un[j + n - 1]);
            let d0 = u64::from(vn[n - 1]);
            let mut qhat = high / d0;
            let mut rhat = high % d0;
            while qhat == (1u64 << 32)
                || qhat * u64::from(vn[n - 2]) > ((rhat << 32) | u64::from(un[j + n - 2]))
            {
                qhat -= 1;
                rhat += d0;
                if rhat >= (1u64 << 32) {
                    break;
                }
            }
            let mut borrow: i64 = 0;
            let mut carry: u64 = 0;
            for i in 0..n {
                let product = qhat * u64::from(vn[i]) + carry;
                carry = product >> 32;
                let sub = i64::from(un[j + i]) - borrow - (product & 0xFFFF_FFFF) as i64;
                if sub < 0 {
                    un[j + i] = (sub + (1i64 << 32)) as u32;
                    borrow = 1;
                } else {
                    un[j + i] = sub as u32;
                    borrow = 0;
                }
            }
            let final_sub = i64::from(un[j + n]) - borrow - carry as i64;
            if final_sub < 0 {
                qhat -= 1;
                un[j + n] = (final_sub + (1i64 << 32)) as u32;
                let mut carry = 0u64;
                for i in 0..n {
                    let sum = u64::from(un[j + i]) + u64::from(vn[i]) + carry;
                    un[j + i] = sum as u32;
                    carry = sum >> 32;
                }
                un[j + n] = un[j + n].wrapping_add(carry as u32);
            } else {
                un[j + n] = final_sub as u32;
            }
            q[j] = qhat as u32;
        }
        mag_trim(&mut q);
        let mut r = un[..n].to_vec();
        if shift != 0 {
            let mut shifted = Vec::with_capacity(n);
            for (i, &limb) in r.iter().enumerate() {
                let high = r.get(i + 1).copied().unwrap_or(0);
                shifted.push((limb >> shift) | (high << (32 - shift)));
            }
            r = shifted;
        }
        mag_trim(&mut r);
        (q, r)
    }

    // -- construction -----------------------------------------------------------

    fn from_parts(negative: bool, mut limbs: Vec<u32>) -> BigIntValue {
        mag_trim(&mut limbs);
        BigIntValue {
            negative: negative && !limbs.is_empty(),
            limbs,
        }
    }

    impl BigIntValue {
        pub(crate) fn zero() -> Self {
            Self::default()
        }

        pub(crate) fn one() -> Self {
            from_parts(false, vec![1])
        }

        pub(crate) fn from_u64(value: u64) -> Self {
            let mut limbs = vec![value as u32, (value >> 32) as u32];
            mag_trim(&mut limbs);
            from_parts(false, limbs)
        }

        /// Exact BigInt corresponding to a finite, integral f64. Fractional
        /// inputs truncate like `f64::trunc`; callers implement
        /// `NumberToBigInt` by rejecting non-integral inputs before calling.
        pub(crate) fn from_f64_bits(value: f64) -> Self {
            debug_assert!(value.is_finite());
            if value == 0.0 {
                return Self::zero();
            }
            let negative = value.is_sign_negative();
            let raw = value.abs().to_bits();
            let exponent_bits = ((raw >> 52) & 0x7FF) as i64;
            let mantissa =
                (raw & 0x000F_FFFF_FFFF_FFFF) | if exponent_bits == 0 { 0 } else { 1u64 << 52 };
            // |value| = mantissa * 2^(exponent_bits - 1075)
            let shift = exponent_bits - 1075;
            let mut base = vec![mantissa as u32, (mantissa >> 32) as u32];
            mag_trim(&mut base);
            let limbs = if shift >= 0 {
                mag_shl_bits(&base, shift as usize)
            } else {
                mag_shr_bits(&base, (-shift) as usize)
            };
            from_parts(negative, limbs)
        }

        pub(crate) fn is_zero(&self) -> bool {
            self.limbs.is_empty()
        }

        pub(crate) fn bit_length(&self) -> usize {
            bit_length_limbs(&self.limbs)
        }

        pub(crate) fn neg(&self) -> Self {
            from_parts(!self.negative, self.limbs.clone())
        }

        /// Extract `floor(|self| / 2^from) mod 2^64`.
        fn extract_bits_u64(&self, from: usize) -> u64 {
            let limb_index = from / 32;
            let offset = (from % 32) as u32;
            let lo = self.limbs.get(limb_index).copied().unwrap_or(0);
            let next1 = self.limbs.get(limb_index + 1).copied().unwrap_or(0);
            let next2 = self.limbs.get(limb_index + 2).copied().unwrap_or(0);
            let mut out = u64::from(lo) >> offset;
            if offset > 0 {
                out |= u64::from(next1) << (32 - offset);
                out |= u64::from(next2) << (64 - offset);
            } else {
                out |= u64::from(next1) << 32;
            }
            out
        }

        pub(crate) fn to_u64(&self) -> Option<u64> {
            if self.negative || self.limbs.len() > 2 {
                return None;
            }
            Some(self.extract_bits_u64(0))
        }

        /// Rounded f64 per `Number(x)` semantics on BigInt: significand
        /// rounds to nearest, ties to even; magnitude overflows to infinity.
        pub(crate) fn to_f64(&self) -> f64 {
            let bit_length = self.bit_length();
            if bit_length == 0 {
                return 0.0;
            }
            let magnitude = if bit_length <= 53 {
                self.extract_bits_u64(0) as f64
            } else {
                let drop = bit_length - 53;
                let mut high = self.extract_bits_u64(drop);
                let mut drop = drop;
                let round_bit = test_bit_limbs(&self.limbs, drop - 1);
                let sticky = any_bit_below_limbs(&self.limbs, drop - 1);
                if round_bit && (sticky || high & 1 == 1) {
                    high += 1;
                    if high == 1u64 << 53 {
                        high >>= 1;
                        drop += 1;
                    }
                }
                (high as f64) * 2f64.powi(drop as i32)
            };
            if self.negative { -magnitude } else { magnitude }
        }

        /// Numeric comparison against a finite (or infinite) f64 without
        /// losing precision, per the BigInt/Number branch of IsLessThan.
        /// Returns `None` when `value` is NaN.
        pub(crate) fn compare_with_f64(&self, value: f64) -> Option<Ordering> {
            if value.is_nan() {
                return None;
            }
            if value == f64::INFINITY {
                return Some(Ordering::Less);
            }
            if value == f64::NEG_INFINITY {
                return Some(Ordering::Greater);
            }
            let truncated = value.trunc();
            let order = self.cmp(&Self::from_f64_bits(truncated));
            if order != Ordering::Equal {
                return Some(order);
            }
            let fraction = value - truncated;
            Some(if fraction > 0.0 {
                Ordering::Less
            } else if fraction < 0.0 {
                Ordering::Greater
            } else {
                Ordering::Equal
            })
        }

        pub(crate) fn cmp(&self, other: &Self) -> Ordering {
            match (self.negative, other.negative) {
                (false, true) => Ordering::Greater,
                (true, false) => Ordering::Less,
                (false, false) => mag_cmp(&self.limbs, &other.limbs),
                (true, true) => mag_cmp(&other.limbs, &self.limbs),
            }
        }

        pub(crate) fn add(&self, other: &Self) -> Self {
            if self.negative == other.negative {
                return from_parts(self.negative, mag_add(&self.limbs, &other.limbs));
            }
            match mag_cmp(&self.limbs, &other.limbs) {
                Ordering::Equal => Self::zero(),
                Ordering::Greater => from_parts(self.negative, mag_sub(&self.limbs, &other.limbs)),
                Ordering::Less => from_parts(other.negative, mag_sub(&other.limbs, &self.limbs)),
            }
        }

        pub(crate) fn sub(&self, other: &Self) -> Self {
            self.add(&other.neg())
        }

        pub(crate) fn mul(&self, other: &Self) -> Self {
            from_parts(
                self.negative != other.negative,
                mag_mul(&self.limbs, &other.limbs),
            )
        }

        /// Truncating division and remainder: quotient truncates toward zero,
        /// remainder takes the dividend's sign, per `BigInt::divide` /
        /// `BigInt::remainder` in ECMA-262.
        pub(crate) fn div_rem(&self, other: &Self) -> Result<(Self, Self), BigIntError> {
            if other.is_zero() {
                return Err(BigIntError::Range("BigInt division by zero"));
            }
            let (q, r) = mag_divmod(&self.limbs, &other.limbs);
            Ok((
                from_parts(self.negative != other.negative, q),
                from_parts(self.negative, r),
            ))
        }

        pub(crate) fn exponentiate(&self, exponent: &Self) -> Result<Self, BigIntError> {
            if exponent.negative {
                return Err(BigIntError::Range("BigInt exponent must be non-negative"));
            }
            let base_bits = self.bit_length();
            match (base_bits == 0, exponent.is_zero()) {
                (true, true) => return Ok(Self::one()),
                (true, false) => return Ok(Self::zero()),
                (false, true) => return Ok(Self::one()),
                (false, false) => {}
            }
            // ±1 never grows, so even an exponent too large to fit u64 has
            // an exact bounded result.
            if self.limbs == [1] {
                return Ok(if self.negative && test_bit_limbs(&exponent.limbs, 0) {
                    self.clone()
                } else {
                    Self::one()
                });
            }
            let exponent_value = exponent
                .to_u64()
                .ok_or(BigIntError::Range("BigInt value is too large"))?;
            let worst_case_bits = base_bits
                .checked_mul(exponent_value as usize)
                .ok_or(BigIntError::Range("BigInt value is too large"))?;
            if worst_case_bits > MAX_VALUE_BITS {
                return Err(BigIntError::Range("BigInt value is too large"));
            }
            let mut result = Self::one();
            let bits = exponent.bit_length();
            for i in (0..bits).rev() {
                result = result.mul(&result);
                if test_bit_limbs(&exponent.limbs, i) {
                    result = result.mul(self);
                }
            }
            Ok(result)
        }

        fn shift_amount(count: &Self) -> Result<usize, BigIntError> {
            let amount = count
                .to_u64()
                .ok_or(BigIntError::Range("BigInt shift count is too large"))?;
            let amount = usize::try_from(amount)
                .map_err(|_| BigIntError::Range("BigInt value is too large"))?;
            if amount > MAX_VALUE_BITS {
                return Err(BigIntError::Range("BigInt value is too large"));
            }
            Ok(amount)
        }

        pub(crate) fn shl(&self, count: &Self) -> Result<Self, BigIntError> {
            if count.negative {
                return self.shr(&count.neg());
            }
            Ok(from_parts(
                self.negative,
                mag_shl_bits(&self.limbs, Self::shift_amount(count)?),
            ))
        }

        /// Arithmetic right shift: rounds toward negative infinity (floor),
        /// so `-5n >> 1n === -3n`.
        pub(crate) fn shr(&self, count: &Self) -> Result<Self, BigIntError> {
            if count.negative {
                return self.shl(&count.neg());
            }
            if self.is_zero() {
                return Ok(Self::zero());
            }
            // A right shift at least as wide as the magnitude cannot retain a
            // data bit. Decide that directly so an arbitrarily large BigInt
            // shift count does not become a host-size conversion failure.
            let magnitude_bits = Self::from_u64(self.bit_length() as u64);
            if count.cmp(&magnitude_bits) != Ordering::Less {
                return Ok(if self.negative {
                    from_parts(true, vec![1])
                } else {
                    Self::zero()
                });
            }
            let amount = Self::shift_amount(count)?;
            if !self.negative {
                return Ok(from_parts(false, mag_shr_bits(&self.limbs, amount)));
            }
            // floor(-m / 2^k) = -ceil(m / 2^k) = -((m - 1 >> k) + 1)
            let decremented = mag_sub(&self.limbs, &[1]);
            let shifted = mag_add(&mag_shr_bits(&decremented, amount), &[1]);
            Ok(from_parts(true, shifted))
        }

        pub(crate) fn bit_not(&self) -> Self {
            // ~x = -x - 1
            self.neg().sub(&Self::one())
        }

        pub(crate) fn bit_and(&self, other: &Self) -> Self {
            self.bitwise(other, Bitwise::And)
        }

        pub(crate) fn bit_or(&self, other: &Self) -> Self {
            self.bitwise(other, Bitwise::Or)
        }

        pub(crate) fn bit_xor(&self, other: &Self) -> Self {
            self.bitwise(other, Bitwise::Xor)
        }

        fn bitwise(&self, other: &Self, op: Bitwise) -> Self {
            let width = self.limbs.len().max(other.limbs.len()) + 1;
            let left = two_complement_expand(self, width);
            let right = two_complement_expand(other, width);
            let mut out = vec![0u32; width];
            for i in 0..width {
                out[i] = match op {
                    Bitwise::And => left[i] & right[i],
                    Bitwise::Or => left[i] | right[i],
                    Bitwise::Xor => left[i] ^ right[i],
                };
            }
            let negative = match op {
                Bitwise::And => self.negative && other.negative,
                Bitwise::Or => self.negative || other.negative,
                Bitwise::Xor => self.negative != other.negative,
            };
            if negative {
                from_parts(true, negate_two_complement(&out))
            } else {
                from_parts(false, out)
            }
        }

        // -- width truncations --------------------------------------------------

        /// `BigInt.asUintN(Bits, X)`: residue of X modulo 2^bits.
        pub(crate) fn as_uint_n(&self, bits: usize) -> Self {
            if bits == 0 {
                return Self::zero();
            }
            let truncated = truncate_to_bits(&self.limbs, bits);
            if truncated.is_empty() {
                return Self::zero();
            }
            if self.negative {
                from_parts(false, complement_within_bits(&truncated, bits))
            } else {
                from_parts(false, truncated)
            }
        }

        /// `BigInt.asIntN(Bits, X)`: residue reinterpreted as signed width.
        pub(crate) fn as_int_n(&self, bits: usize) -> Self {
            if self.negative && bits > self.bit_length() {
                return self.clone();
            }
            let residue = self.as_uint_n(bits);
            if bits == 0 || residue.is_zero() {
                return Self::zero();
            }
            if test_bit_limbs(&residue.limbs, bits - 1) {
                from_parts(true, complement_within_bits(&residue.limbs, bits))
            } else {
                residue
            }
        }

        // -- text conversion -----------------------------------------------------

        /// `StringToBigInt` per ECMA-262: JS whitespace trimming, empty string
        /// is 0n, `0x`/`0b`/`0o` prefixes without signs, optional sign only for
        /// decimal digits, and no numeric separators anywhere.
        pub(crate) fn parse_string(text: &str) -> Result<Self, BigIntError> {
            let syntax = || BigIntError::Syntax("invalid BigInt literal");
            let trimmed = text.trim_matches(is_js_whitespace);
            if trimmed.is_empty() {
                return Ok(Self::zero());
            }
            let bytes = trimmed.as_bytes();
            if bytes.len() >= 2 && bytes[0] == b'0' {
                let radix = match bytes[1] {
                    b'x' | b'X' => Some(16u32),
                    b'b' | b'B' => Some(2u32),
                    b'o' | b'O' => Some(8u32),
                    _ => None,
                };
                if let Some(radix) = radix {
                    return parse_digits(&trimmed[2..], radix)
                        .map(|limbs| from_parts(false, limbs))
                        .ok_or_else(syntax);
                }
            }
            let (negative, digits) = match bytes[0] {
                b'-' => (true, &trimmed[1..]),
                b'+' => (false, &trimmed[1..]),
                _ => (false, trimmed),
            };
            parse_digits(digits, 10)
                .map(|limbs| from_parts(negative, limbs))
                .ok_or_else(syntax)
        }

        pub(crate) fn to_string_radix(&self, radix: u32) -> String {
            debug_assert!((2..=36).contains(&radix));
            if self.limbs.is_empty() {
                return "0".to_owned();
            }
            let (chunk, chunk_digits) = radix_chunk(radix);
            let mut work = self.limbs.clone();
            let mut digits: Vec<u8> = Vec::new();
            while !work.is_empty() {
                let mut remainder = 0u64;
                for i in (0..work.len()).rev() {
                    let cur = (remainder << 32) | u64::from(work[i]);
                    work[i] = (cur / u64::from(chunk)) as u32;
                    remainder = cur % u64::from(chunk);
                }
                mag_trim(&mut work);
                let mut rem = remainder as u32;
                if work.is_empty() {
                    while rem != 0 {
                        digits.push((rem % radix) as u8);
                        rem /= radix;
                    }
                } else {
                    for _ in 0..chunk_digits {
                        digits.push((rem % radix) as u8);
                        rem /= radix;
                    }
                }
            }
            let mut text = String::with_capacity(digits.len() + 1);
            if self.negative {
                text.push('-');
            }
            for &digit in digits.iter().rev() {
                let ch = if digit < 10 {
                    b'0' + digit
                } else {
                    b'a' + (digit - 10)
                };
                text.push(ch as char);
            }
            text
        }
    }

    #[derive(Clone, Copy)]
    enum Bitwise {
        And,
        Or,
        Xor,
    }

    fn is_js_whitespace(c: char) -> bool {
        matches!(
            c as u32,
            0x09 | 0x0A | 0x0B | 0x0C | 0x0D | 0x20 | 0xA0 | 0x1680 | 0x2000
                ..=0x200A | 0x2028 | 0x2029 | 0x202F | 0x205F | 0x3000 | 0xFEFF
        )
    }

    fn parse_digits(text: &str, radix: u32) -> Option<Vec<u32>> {
        if text.is_empty() {
            return None;
        }
        let mut limbs: Vec<u32> = Vec::new();
        for byte in text.bytes() {
            let digit = match byte {
                b'0'..=b'9' => u32::from(byte - b'0'),
                b'a'..=b'z' => u32::from(byte - b'a') + 10,
                b'A'..=b'Z' => u32::from(byte - b'A') + 10,
                _ => return None,
            };
            if digit >= radix {
                return None;
            }
            limbs = mag_mul_add_small(&limbs, radix, digit);
        }
        Some(limbs)
    }

    fn radix_chunk(radix: u32) -> (u32, usize) {
        let mut chunk = 1u64;
        let mut digits = 0usize;
        while chunk * u64::from(radix) <= u64::from(u32::MAX) {
            chunk *= u64::from(radix);
            digits += 1;
        }
        (chunk as u32, digits)
    }

    fn truncate_to_bits(limbs: &[u32], bits: usize) -> Vec<u32> {
        let full = bits / 32;
        let rem = bits % 32;
        let width = full + usize::from(rem != 0);
        let mut out = vec![0u32; width];
        for (i, slot) in out.iter_mut().enumerate() {
            *slot = limbs.get(i).copied().unwrap_or(0);
        }
        if rem != 0 {
            out[full] &= (1u32 << rem) - 1;
        }
        mag_trim(&mut out);
        out
    }

    /// Computes `2^bits - limbs` for nonzero `limbs < 2^bits`.
    fn complement_within_bits(limbs: &[u32], bits: usize) -> Vec<u32> {
        debug_assert!(!limbs.is_empty());
        let full = bits / 32;
        let rem = bits % 32;
        let width = full + usize::from(rem != 0);
        let mut out = vec![0u32; width];
        for (i, slot) in out.iter_mut().enumerate() {
            *slot = !limbs.get(i).copied().unwrap_or(0);
        }
        let mut carry = 1u32;
        for slot in out.iter_mut() {
            if carry == 0 {
                break;
            }
            let (value, overflowed) = slot.overflowing_add(1);
            *slot = value;
            carry = u32::from(overflowed);
        }
        if rem != 0 {
            out[full] &= (1u32 << rem) - 1;
        }
        mag_trim(&mut out);
        out
    }

    /// Two's-complement expansion of `value` over `width` u32 limbs, with
    /// infinite sign extension folded into the leading positions.
    fn two_complement_expand(value: &BigIntValue, width: usize) -> Vec<u32> {
        let mut out = vec![0u32; width];
        if !value.negative {
            for (slot, &limb) in out.iter_mut().zip(value.limbs.iter()) {
                *slot = limb;
            }
            return out;
        }
        // Negative: limbs of -(m) in two's complement are !(m - 1).
        let mut borrow = 1u32;
        for (i, slot) in out.iter_mut().enumerate() {
            let m = value.limbs.get(i).copied().unwrap_or(0);
            let (decremented, underflowed) = m.overflowing_sub(borrow);
            borrow = u32::from(underflowed);
            *slot = !decremented;
        }
        out
    }

    /// Inverse of `two_complement_expand` for negative results:
    /// magnitude is `!limbs + 1` computed in place.
    fn negate_two_complement(limbs: &[u32]) -> Vec<u32> {
        let mut out = Vec::with_capacity(limbs.len());
        let mut carry = true;
        for &limb in limbs {
            let inverted = !limb;
            let (value, overflowed) = if carry {
                inverted.overflowing_add(1)
            } else {
                (inverted, false)
            };
            out.push(value);
            carry = overflowed;
        }
        mag_trim(&mut out);
        out
    }

    #[cfg(test)]
    mod core_tests {
        use super::*;

        fn from_i128(value: i128) -> BigIntValue {
            let magnitude = value.unsigned_abs();
            let mut limbs = Vec::new();
            let mut rest = magnitude;
            while rest > 0 {
                limbs.push(rest as u32);
                rest >>= 32;
            }
            from_parts(value < 0, limbs)
        }

        fn to_i128(value: &BigIntValue) -> i128 {
            let mut magnitude = 0i128;
            for &limb in value.limbs.iter().rev() {
                magnitude = (magnitude << 32) | i128::from(limb);
            }
            if value.negative {
                -magnitude
            } else {
                magnitude
            }
        }

        fn xorshift(state: &mut u64) -> u64 {
            let mut x = *state;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            *state = x;
            x
        }

        fn random_i128(state: &mut u64, bits: u32) -> i128 {
            let mut value = 0i128;
            for _ in 0..bits.div_ceil(32) {
                value = (value << 32) | i128::from(xorshift(state) as u32);
            }
            if bits < 128 {
                value &= (1i128 << bits) - 1;
            }
            if xorshift(state) & 1 == 1 {
                -value
            } else {
                value
            }
        }

        #[test]
        fn add_sub_mul_cross_check_i128_space() {
            let mut state = 0x9E37_79B9_7F4A_7C15u64;
            for _ in 0..512 {
                let a = random_i128(&mut state, 60);
                let b = random_i128(&mut state, 60);
                let (x, y) = (from_i128(a), from_i128(b));
                assert_eq!(to_i128(&x.add(&y)), a + b, "add");
                assert_eq!(to_i128(&x.sub(&y)), a - b, "sub");
                assert_eq!(to_i128(&x.mul(&y)), a * b, "mul");
            }
        }

        #[test]
        fn div_rem_cross_check_i128_space() {
            let mut state = 0xDEAD_BEEF_CAFE_F00Du64;
            for _ in 0..512 {
                let a = random_i128(&mut state, 96);
                let b = random_i128(&mut state, 64);
                if b == 0 {
                    continue;
                }
                let (x, y) = (from_i128(a), from_i128(b));
                let (q, r) = x.div_rem(&y).expect("nonzero divisor");
                assert_eq!(to_i128(&q), a / b, "quotient");
                assert_eq!(to_i128(&r), a % b, "remainder");
            }
        }

        #[test]
        fn division_roundtrip_knuth_path() {
            let mut state = 0x1234_5678_9ABC_DEF0u64;
            for _ in 0..128 {
                // u: 4..12 limbs, v: 2..6 limbs — exercises Knuth D fully.
                let u_len = 4 + (xorshift(&mut state) % 9) as usize;
                let v_len = 2 + (xorshift(&mut state) % 5) as usize;
                let mut u = vec![0u32; u_len];
                let mut v = vec![0u32; v_len];
                for limb in u.iter_mut() {
                    *limb = xorshift(&mut state) as u32;
                }
                for limb in v.iter_mut() {
                    *limb = xorshift(&mut state) as u32;
                }
                *u.last_mut().unwrap() |= 1 << 31;
                *v.last_mut().unwrap() |= 1 << 31;
                let uv = BigIntValue {
                    negative: false,
                    limbs: u,
                };
                let vv = BigIntValue {
                    negative: false,
                    limbs: v,
                };
                let (q, r) = uv.div_rem(&vv).expect("nonzero divisor");
                let reconstructed = q.mul(&vv).add(&r);
                assert_eq!(reconstructed, uv, "u = q * v + r");
                assert_eq!(
                    r.cmp(&BigIntValue {
                        negative: false,
                        limbs: vv.limbs.clone()
                    }),
                    Ordering::Less
                );
                assert!(!r.negative);
            }
        }

        #[test]
        fn division_by_zero_is_range_error() {
            let one = BigIntValue::one();
            let zero = BigIntValue::zero();
            assert!(matches!(one.div_rem(&zero), Err(BigIntError::Range(_))));
        }

        #[test]
        fn power_of_two_format_and_parse() {
            let two = from_i128(2);
            let mut thousand = BigIntValue::one();
            for _ in 0..999 {
                thousand = thousand.mul(&two);
            }
            thousand = thousand.mul(&two);
            assert_eq!(thousand.bit_length(), 1001);
            let text = thousand.to_string_radix(10);
            assert_eq!(text.len(), 302, "2^1000 has 302 digits");
            assert!(text.starts_with("10715086071862673209"), "{text}");
            let parsed = BigIntValue::parse_string(&text).expect("valid decimal");
            assert_eq!(parsed, thousand, "decimal round trip");
            assert_eq!(
                thousand.to_string_radix(16),
                format!("1{}", "0".repeat(250)),
                "2^1000 in hex"
            );
        }

        #[test]
        fn parse_accepts_prefixes_signs_and_whitespace_only() {
            assert_eq!(BigIntValue::parse_string("  0x1F ").unwrap(), from_i128(31));
            assert_eq!(BigIntValue::parse_string("0B101").unwrap(), from_i128(5));
            assert_eq!(BigIntValue::parse_string("0o17").unwrap(), from_i128(15));
            assert_eq!(BigIntValue::parse_string("-42").unwrap(), from_i128(-42));
            assert_eq!(BigIntValue::parse_string("+42").unwrap(), from_i128(42));
            assert_eq!(BigIntValue::parse_string("").unwrap(), BigIntValue::zero());
            assert_eq!(
                BigIntValue::parse_string(" \u{3000}\u{00A0}").unwrap(),
                BigIntValue::zero()
            );
            assert_eq!(BigIntValue::parse_string("-0001").unwrap(), from_i128(-1));
        }

        #[test]
        fn parse_rejects_invalid_forms() {
            for bad in [
                "0x", "-0x1F", "+0b1", "1_000", "12 3", "1e5", "1.0", "0xG", "12a", "-",
            ] {
                let result = BigIntValue::parse_string(bad);
                assert!(
                    matches!(result, Err(BigIntError::Syntax(_))),
                    "{bad} must be a Syntax error, got {result:?}"
                );
            }
        }

        #[test]
        fn radix_round_trips_across_bases() {
            let mut state = 0x0F0F_0F0Fu64;
            for _ in 0..64 {
                let value = random_i128(&mut state, 100);
                let bigint = from_i128(value);
                for radix in 2u32..=36 {
                    let text = bigint.to_string_radix(radix);
                    let parsed = if radix == 10 {
                        BigIntValue::parse_string(&text).expect("radix-10 text parses")
                    } else {
                        let digits = text.trim_start_matches('-');
                        let limbs = parse_digits(digits, radix).expect("valid digits");
                        from_parts(text.starts_with('-'), limbs)
                    };
                    assert_eq!(parsed, bigint, "radix {radix} round trip for {value}");
                }
            }
        }

        #[test]
        fn shifts_floor_for_negative_and_inverse_positive() {
            let five = from_i128(5);
            let minus_five = from_i128(-5);
            let one = BigIntValue::one();
            assert_eq!(
                to_i128(&minus_five.shr(&one).unwrap()),
                -3,
                "-5 >> 1 floors"
            );
            assert_eq!(to_i128(&five.shr(&one).unwrap()), 2);
            assert_eq!(to_i128(&minus_five.shr(&from_i128(200)).unwrap()), -1);
            let shift = from_i128(100);
            let shifted = one.shl(&shift).unwrap();
            assert_eq!(shifted.bit_length(), 101);
            assert_eq!(shifted.shr(&shift).unwrap(), BigIntValue::one());
            assert_eq!(to_i128(&from_i128(-16).shr(&from_i128(4)).unwrap()), -1);
            assert_eq!(to_i128(&from_i128(255).shl(&from_i128(-3)).unwrap()), 31);
        }

        #[test]
        fn bitwise_cross_check_i128_space() {
            let mut state = 0xACA3_11A5u64;
            for _ in 0..512 {
                let a = random_i128(&mut state, 120);
                let b = random_i128(&mut state, 120);
                let (x, y) = (from_i128(a), from_i128(b));
                assert_eq!(to_i128(&x.bit_and(&y)), a & b, "and");
                assert_eq!(to_i128(&x.bit_or(&y)), a | b, "or");
                assert_eq!(to_i128(&x.bit_xor(&y)), a ^ b, "xor");
                assert_eq!(to_i128(&x.bit_not()), !a, "not");
            }
        }

        #[test]
        fn bitwise_across_word_boundaries() {
            let one = BigIntValue::one();
            let hundred = from_i128(100);
            let bit100 = one.shl(&hundred).unwrap();
            assert_eq!(bit100.bit_and(&bit100), bit100);
            assert_eq!(bit100.bit_and(&from_i128(1)), BigIntValue::zero());
            assert_eq!(from_i128(-1).bit_and(&bit100), bit100, "-1 & m == m");
            assert_eq!(from_i128(-1).bit_or(&bit100), from_i128(-1));
        }

        #[test]
        fn width_truncation_boundaries() {
            let one = BigIntValue::one();
            let p64 = from_i128(4).mul(&from_i128(4));
            let two_pow_63 = one.shl(&from_i128(63)).unwrap();
            assert_eq!(
                to_i128(&two_pow_63.as_int_n(64)),
                i64::MIN as i128,
                "asIntN(64, 2^63) is -2^63"
            );
            let minus_one = from_i128(-1);
            let max_u64 = from_parts(false, vec![u32::MAX, u32::MAX]);
            assert_eq!(minus_one.as_uint_n(64), max_u64);
            assert_eq!(from_i128(255).as_uint_n(8), from_i128(255));
            assert_eq!(from_i128(256).as_uint_n(8), BigIntValue::zero());
            assert_eq!(to_i128(&from_i128(255).as_int_n(8)), -1);
            assert_eq!(from_i128(0xFFFF).as_uint_n(0), BigIntValue::zero());
            assert_eq!(p64.as_int_n(32), from_i128(16), "low-width truncation");
            let two_pow_200 = one.shl(&from_i128(200)).unwrap();
            assert_eq!(two_pow_200.as_uint_n(8), BigIntValue::zero());
            assert_eq!(two_pow_200.as_int_n(201), two_pow_200.neg());
        }

        #[test]
        fn exponentiation_edges() {
            let two = from_i128(2);
            assert_eq!(
                two.exponentiate(&BigIntValue::zero()).unwrap(),
                BigIntValue::one()
            );
            assert_eq!(
                BigIntValue::zero()
                    .exponentiate(&BigIntValue::zero())
                    .unwrap(),
                BigIntValue::one()
            );
            assert_eq!(
                BigIntValue::zero().exponentiate(&two).unwrap(),
                BigIntValue::zero()
            );
            assert_eq!(
                to_i128(&two.exponentiate(&from_i128(64)).unwrap()),
                1i128 << 64
            );
            assert_eq!(
                to_i128(&from_i128(-3).exponentiate(&from_i128(3)).unwrap()),
                -27
            );
            let huge_even =
                BigIntValue::parse_string("340282366920938463463374607431768211456").unwrap();
            let huge_odd =
                BigIntValue::parse_string("340282366920938463463374607431768211457").unwrap();
            assert_eq!(
                BigIntValue::one().exponentiate(&huge_even).unwrap(),
                BigIntValue::one()
            );
            assert_eq!(
                from_i128(-1).exponentiate(&huge_even).unwrap(),
                BigIntValue::one()
            );
            assert_eq!(
                from_i128(-1).exponentiate(&huge_odd).unwrap(),
                from_i128(-1)
            );
            assert!(matches!(
                two.exponentiate(&from_i128(-1)),
                Err(BigIntError::Range(_))
            ));
        }

        #[test]
        fn f64_bridge_is_exact_under_53_bits_and_rounds_above() {
            let exact = from_i128((1i128 << 53) - 1);
            assert_eq!(exact.to_f64(), 9_007_199_254_740_991.0);
            assert_eq!(from_i128(-42).to_f64(), -42.0);
            // 2^53 + 1 rounds down to 2^53 (tie to even).
            let two_53 = from_i128(1i128 << 53);
            let above = from_i128((1i128 << 53) + 1);
            assert_eq!(above.to_f64(), two_53.to_f64());
            assert_eq!(two_53.to_f64(), 9_007_199_254_740_992.0);
            // 2^53 + 3 rounds to 2^53 + 4.
            let plus_three = from_i128((1i128 << 53) + 3);
            assert_eq!(plus_three.to_f64(), 9_007_199_254_740_996.0);
            // compare-with-f64 keeps full precision.
            assert_eq!(
                above.compare_with_f64(9_007_199_254_740_992.0),
                Some(Ordering::Greater)
            );
            assert_eq!(
                two_53.compare_with_f64(9_007_199_254_740_992.0),
                Some(Ordering::Equal)
            );
            assert_eq!(from_i128(1).compare_with_f64(1.5), Some(Ordering::Less));
            assert_eq!(
                from_i128(-2).compare_with_f64(-2.5),
                Some(Ordering::Greater)
            );
            assert_eq!(from_i128(1).compare_with_f64(f64::NAN), None);
            assert_eq!(
                from_i128(i64::MAX as i128).compare_with_f64(f64::INFINITY),
                Some(Ordering::Less)
            );
        }

        #[test]
        fn from_f64_bits_matches_small_integers() {
            let mut state = 7u64;
            for _ in 0..512 {
                let value = random_i128(&mut state, 60);
                let as_f64 = i64::try_from(value).unwrap_or_default() as f64;
                let rebuilt = BigIntValue::from_f64_bits(as_f64);
                assert_eq!(to_i128(&rebuilt), to_i128(&from_f64_integral_check(as_f64)));
            }
            assert_eq!(BigIntValue::from_f64_bits(0.0), BigIntValue::zero());
            assert_eq!(BigIntValue::from_f64_bits(-0.0), BigIntValue::zero());
        }

        fn from_f64_integral_check(value: f64) -> BigIntValue {
            // Reference conversion through i64 for values that fit exactly.
            let negative = value < 0.0;
            let magnitude = value.abs() as u64;
            let mut limbs = vec![magnitude as u32, (magnitude >> 32) as u32];
            mag_trim(&mut limbs);
            from_parts(negative, limbs)
        }
    }
}
use bigint_core::BigIntError;
pub(crate) use bigint_core::BigIntValue;
// ---- BIGINT CORE END ----

/// Binary operators that take BigInt operands once operands are primitive.
/// Mirrors `BinaryOp` so the VM can dispatch without a second state model.
#[derive(Clone, Copy, Debug)]
pub(crate) enum BigIntBinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    Exponentiate,
    BitAnd,
    BitOr,
    BitXor,
    LeftShift,
    RightShift,
    UnsignedRightShift,
}

/// Maps a core `BigIntError` to an abrupt completion. Type and range stays in
/// the typed `ThrowOrigin` channel; syntax failures build a real `SyntaxError`
/// instance through the installed error constructor, exactly as `json_edge.rs` does.
fn bigint_failure<H: Host>(machine: &mut Machine<'_, H>, error: BigIntError) -> EvalFailure {
    match error {
        BigIntError::Range(operation) => range_error(operation),
        BigIntError::Syntax(message) => {
            let id = machine
                .intrinsics
                .builtins
                .id_named("SyntaxError")
                .expect("SyntaxError intrinsic is installed");
            machine.throw_error(id, message.to_owned())
        }
    }
}

fn bigint_index<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<Option<usize>, EvalFailure> {
    let Some(index) = machine.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
        return Ok(None);
    };
    Ok(matches!(machine.heap[index], HeapEntry::BigInt(_)).then_some(index))
}

/// True only for a primitive `HeapEntry::BigInt`. JSON's `GetV(toJSON)` and
/// other parent algorithms use this without exposing the transient numeric
/// representation.
pub(crate) fn is_bigint<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<bool, EvalFailure> {
    Ok(bigint_index(machine, value)?.is_some())
}

/// Reads a heap BigInt value, if `value` is one, as a `BigIntValue`.
/// Stored payloads must be parseable; corrupt payloads are a typed range
/// failure identifying the broken invariant rather than a parse panic.
pub(crate) fn bigint_from_value<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<Option<BigIntValue>, EvalFailure> {
    let Some(index) = bigint_index(machine, value)? else {
        return Ok(None);
    };
    let HeapEntry::BigInt(text) = &machine.heap[index] else {
        unreachable!("bigint index matched");
    };
    BigIntValue::parse_string(text)
        .map(Some)
        .map_err(|_| range_error_or(text))
}

fn range_error_or(_text: &str) -> EvalFailure {
    EvalFailure::Throw(ThrowOrigin::RangeError {
        operation: "corrupt BigInt payload on the heap",
    })
}

/// Allocates a heap BigInt in canonical decimal form.
pub(crate) fn allocate_bigint<H: Host>(
    machine: &mut Machine<'_, H>,
    value: &BigIntValue,
) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::BigInt(value.to_string_radix(10)))
        .map_err(EvalFailure::Runtime)
}

/// Explicit `Number(bigint)` conversion. `Ok(None)` means the input is not a
/// BigInt and Number's ordinary `ToNumber` branch applies.
pub(crate) fn bigint_to_number<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<Option<Value>, EvalFailure> {
    Ok(bigint_from_value(machine, value)?.map(|bigint| crate::number_value(bigint.to_f64())))
}

/// `ToBigInt` per ECMA-262 §7.1.13 over a value the caller already reduced
/// with `ToPrimitive` (default hint); objects convert through that path.
pub(crate) fn to_bigint<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<Value, EvalFailure> {
    let primitive = machine.coerce_primitive_default(value)?;
    to_bigint_primitive(machine, primitive)
}

fn to_bigint_primitive<H: Host>(
    machine: &mut Machine<'_, H>,
    primitive: Value,
) -> Result<Value, EvalFailure> {
    match primitive.decode() {
        Some(Decoded::Undefined) => Err(type_error("Cannot convert undefined to a BigInt")),
        Some(Decoded::Null) => Err(type_error("Cannot convert null to a BigInt")),
        Some(Decoded::Boolean(flag)) => {
            allocate_bigint(machine, &BigIntValue::from_u64(u64::from(flag)))
        }
        Some(Decoded::Number(_)) | Some(Decoded::Int32(_)) => Err(type_error(
            "Cannot convert a Number value to a BigInt without an explicit conversion",
        )),
        Some(Decoded::HeapRef(_)) => {
            let index = machine
                .runtime_slot(primitive)
                .map_err(EvalFailure::Runtime)?
                .expect("heap reference decodes to a slot");
            match &machine.heap[index] {
                HeapEntry::BigInt(_) => Ok(primitive),
                HeapEntry::String(text) => {
                    let text = text.clone();
                    let utf8 = match text.to_utf8_strict() {
                        Ok(text) => text,
                        Err(_) => {
                            return Err(bigint_failure(
                                machine,
                                BigIntError::Syntax("invalid BigInt string"),
                            ));
                        }
                    };
                    match BigIntValue::parse_string(&utf8) {
                        Ok(bigint) => allocate_bigint(machine, &bigint),
                        Err(error) => Err(bigint_failure(machine, error)),
                    }
                }
                HeapEntry::Symbol { .. } | HeapEntry::PrivateName { .. } => {
                    Err(type_error("Cannot convert a Symbol value to a BigInt"))
                }
                _ => Err(type_error("Cannot convert object to a BigInt")),
            }
        }
        _ => Err(type_error("Cannot convert value to a BigInt")),
    }
}

/// `NumberToBigInt`: integral Numbers only; anything else is a RangeError.
fn number_to_bigint<H: Host>(
    machine: &mut Machine<'_, H>,
    number: f64,
) -> Result<Value, EvalFailure> {
    if !number.is_finite() || number.trunc() != number {
        return Err(range_error(
            "Cannot convert a non-integral number to a BigInt",
        ));
    }
    allocate_bigint(machine, &BigIntValue::from_f64_bits(number))
}

/// `thisBigIntValue` for prototype methods: accepts a BigInt primitive or an
/// object with a BigInt `[[BigIntData]]` (boxed primitive).
fn this_bigint_value<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<BigIntValue, EvalFailure> {
    if let Some(bigint) = bigint_from_value(machine, value)? {
        return Ok(bigint);
    }
    if let Some(index) = machine.runtime_slot(value).map_err(EvalFailure::Runtime)?
        && let HeapEntry::Object {
            boxed_primitive: Some(primitive),
            ..
        } = &machine.heap[index]
    {
        let primitive = *primitive;
        if let Some(bigint) = bigint_from_value(machine, primitive)? {
            return Ok(bigint);
        }
    }
    Err(type_error("BigInt method called on incompatible receiver"))
}

// -- operator helpers for the VM ------------------------------------------------

/// Binary operator over possibly-BigInt operands. `Ok(None)` means neither
/// operand is a BigInt and the caller's Number path applies. Mixed
/// BigInt/Number input is a `TypeError`. Division and remainder by zero and
/// negative exponents are `RangeError`s.
pub(crate) fn binary_op<H: Host>(
    machine: &mut Machine<'_, H>,
    op: BigIntBinaryOp,
    left: Value,
    right: Value,
) -> Result<Option<Value>, EvalFailure> {
    let left_is_bigint = bigint_index(machine, left)?.is_some();
    let right_is_bigint = bigint_index(machine, right)?.is_some();
    if !left_is_bigint && !right_is_bigint {
        return Ok(None);
    }
    if left_is_bigint != right_is_bigint {
        return Err(type_error(
            "Cannot mix BigInt and other types, use explicit conversions",
        ));
    }
    let left_bigint = bigint_from_value(machine, left)?.expect("checked as BigInt");
    let right_bigint = bigint_from_value(machine, right)?.expect("checked as BigInt");
    let result = match op {
        BigIntBinaryOp::Add => Ok(left_bigint.add(&right_bigint)),
        BigIntBinaryOp::Subtract => Ok(left_bigint.sub(&right_bigint)),
        BigIntBinaryOp::Multiply => Ok(left_bigint.mul(&right_bigint)),
        BigIntBinaryOp::Divide => left_bigint
            .div_rem(&right_bigint)
            .map(|(quotient, _)| quotient),
        BigIntBinaryOp::Remainder => left_bigint
            .div_rem(&right_bigint)
            .map(|(_, remainder)| remainder),
        BigIntBinaryOp::Exponentiate => left_bigint.exponentiate(&right_bigint),
        BigIntBinaryOp::BitAnd => Ok(left_bigint.bit_and(&right_bigint)),
        BigIntBinaryOp::BitOr => Ok(left_bigint.bit_or(&right_bigint)),
        BigIntBinaryOp::BitXor => Ok(left_bigint.bit_xor(&right_bigint)),
        BigIntBinaryOp::LeftShift => left_bigint.shl(&right_bigint),
        BigIntBinaryOp::RightShift => left_bigint.shr(&right_bigint),
        BigIntBinaryOp::UnsignedRightShift => {
            return Err(type_error("BigInt has no unsigned right shift"));
        }
    };
    let bigint = match result {
        Ok(bigint) => bigint,
        Err(error) => return Err(bigint_failure(machine, error)),
    };
    Ok(Some(allocate_bigint(machine, &bigint)?))
}

/// Unary minus on a BigInt operand; `Ok(None)` when not a BigInt.
pub(crate) fn unary_minus<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<Option<Value>, EvalFailure> {
    let Some(bigint) = bigint_from_value(machine, value)? else {
        return Ok(None);
    };
    Ok(Some(allocate_bigint(machine, &bigint.neg())?))
}

/// Bitwise NOT on a BigInt operand; `Ok(None)` when not a BigInt.
pub(crate) fn bitwise_not<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<Option<Value>, EvalFailure> {
    let Some(bigint) = bigint_from_value(machine, value)? else {
        return Ok(None);
    };
    Ok(Some(allocate_bigint(machine, &bigint.bit_not())?))
}

// -- equality and relational helpers ---------------------------------------------

/// Strict equality contribution: `Some` when at least one operand is a
/// BigInt (same types compare numerically, mixed are never strictly equal),
/// `None` when neither operand is a BigInt.
#[cfg(test)]
pub(crate) fn strict_equals<H: Host>(
    machine: &Machine<'_, H>,
    left: Value,
    right: Value,
) -> Result<Option<bool>, EvalFailure> {
    let left_has = bigint_index(machine, left)?.is_some();
    let right_has = bigint_index(machine, right)?.is_some();
    if !left_has && !right_has {
        return Ok(None);
    }
    if left_has != right_has {
        return Ok(Some(false));
    }
    let left_bigint = bigint_from_value(machine, left)?.expect("checked as BigInt");
    let right_bigint = bigint_from_value(machine, right)?.expect("checked as BigInt");
    Ok(Some(
        left_bigint.cmp(&right_bigint) == std::cmp::Ordering::Equal,
    ))
}

/// Abstract equality contribution over primitive operands (callers resolve
/// objects to primitives first, per ECMA-262 §7.2.15). `None` means no BigInt
/// participates and the caller's path applies.
pub(crate) fn loose_equals<H: Host>(
    machine: &Machine<'_, H>,
    left: Value,
    right: Value,
) -> Result<Option<bool>, EvalFailure> {
    let left_bigint = bigint_from_value(machine, left)?;
    let right_bigint = bigint_from_value(machine, right)?;
    match (left_bigint, right_bigint) {
        (Some(left), Some(right)) => Ok(Some(left.cmp(&right) == std::cmp::Ordering::Equal)),
        (Some(bigint), None) => compare_equal_with_non_bigint(machine, &bigint, right).map(Some),
        (None, Some(bigint)) => compare_equal_with_non_bigint(machine, &bigint, left).map(Some),
        (None, None) => Ok(None),
    }
}

fn compare_equal_with_non_bigint<H: Host>(
    machine: &Machine<'_, H>,
    bigint: &BigIntValue,
    other: Value,
) -> Result<bool, EvalFailure> {
    match other.decode() {
        Some(Decoded::Undefined) | Some(Decoded::Null) => Ok(false),
        Some(Decoded::Boolean(flag)) => {
            Ok(bigint.cmp(&BigIntValue::from_u64(u64::from(flag))) == std::cmp::Ordering::Equal)
        }
        Some(Decoded::Number(_)) | Some(Decoded::Int32(_)) => Ok(bigint
            .compare_with_f64(numeric_f64(other).expect("number decodes"))
            .is_some_and(|order| order == std::cmp::Ordering::Equal)),
        Some(Decoded::HeapRef(_)) => {
            let index = machine
                .runtime_slot(other)
                .map_err(EvalFailure::Runtime)?
                .expect("heap reference decodes to a slot");
            match &machine.heap[index] {
                HeapEntry::String(text) => {
                    let text = text.clone();
                    match text.to_utf8_strict() {
                        Ok(utf8) => Ok(match BigIntValue::parse_string(&utf8) {
                            Ok(parsed) => parsed.cmp(bigint) == std::cmp::Ordering::Equal,
                            Err(_) => false,
                        }),
                        Err(_) => Ok(false),
                    }
                }
                HeapEntry::Symbol { .. } | HeapEntry::PrivateName { .. } => Ok(false),
                _ => Ok(false),
            }
        }
        _ => Ok(false),
    }
}

/// Relational comparison contribution over primitive operands. The outer
/// `None` means no BigInt participates; `Some(None)` preserves unordered
/// Number comparisons such as `1n < NaN`.
pub(crate) fn compare<H: Host>(
    machine: &Machine<'_, H>,
    left: Value,
    right: Value,
) -> Result<Option<Option<std::cmp::Ordering>>, EvalFailure> {
    let left_bigint = bigint_from_value(machine, left)?;
    let right_bigint = bigint_from_value(machine, right)?;
    match (left_bigint, right_bigint) {
        (Some(left), Some(right)) => Ok(Some(Some(left.cmp(&right)))),
        (Some(bigint), None) => Ok(Some(compare_relational_non_bigint(
            machine, &bigint, right,
        )?)),
        (None, Some(bigint)) => Ok(Some(
            compare_relational_non_bigint(machine, &bigint, left)?.map(std::cmp::Ordering::reverse),
        )),
        (None, None) => Ok(None),
    }
}

fn compare_relational_non_bigint<H: Host>(
    machine: &Machine<'_, H>,
    bigint: &BigIntValue,
    other: Value,
) -> Result<Option<std::cmp::Ordering>, EvalFailure> {
    if let Some(index) = machine.runtime_slot(other).map_err(EvalFailure::Runtime)?
        && let HeapEntry::String(text) = &machine.heap[index]
    {
        let Ok(utf8) = text.to_utf8_strict() else {
            return Ok(None);
        };
        return Ok(BigIntValue::parse_string(&utf8)
            .ok()
            .map(|parsed| bigint.cmp(&parsed)));
    }
    let number = numeric_f64(machine.to_number(other)?).expect("ToNumber returns numeric");
    Ok(bigint.compare_with_f64(number))
}

// -- JSON contract ----------------------------------------------------------------

/// `SerializeJSONProperty` BigInt branch: after the spec-observable `toJSON`
/// and replacer calls, a still-BigInt value throws `TypeError`. Call from that
/// post-replacer branch, immediately before primitive serialization.
pub(crate) fn json_reject<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<(), EvalFailure> {
    if bigint_index(machine, value)?.is_some() {
        return Err(type_error("Do not know how to serialize a BigInt"));
    }
    Ok(())
}

// -- constructor and prototype -----------------------------------------------------

/// Installs the `BigInt` constructor, prototype, and global binding and
/// returns the prototype value for the caller to register in `BuiltinTable`
/// (`builtins.set_bigint_prototype(value)`), which then lets the Machine's
/// boxing path find `[[Prototype]]` for BigInt values.
pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) -> Value {
    let prototype = super::super::ordinary_prototype(heap, builtins.object_prototype());
    let constructor = install_function(heap, builtins, "BigInt", 1, constructor::<H>);
    builtins.set_bigint_constructor(constructor);
    builtins.set_constructor_prototype(heap, constructor, prototype);

    let as_int_n = install_function(heap, builtins, "asIntN", 2, as_int_n::<H>);
    let as_uint_n = install_function(heap, builtins, "asUintN", 2, as_uint_n::<H>);
    define_native_property(heap, constructor, "asIntN", as_int_n);
    define_native_property(heap, constructor, "asUintN", as_uint_n);

    let to_string = install_function(heap, builtins, "toString", 0, to_string::<H>);
    let value_of = install_function(heap, builtins, "valueOf", 0, value_of::<H>);
    let to_locale_string =
        install_function(heap, builtins, "toLocaleString", 0, to_locale_string::<H>);
    define_data(heap, prototype, "toString", to_string);
    define_data(heap, prototype, "valueOf", value_of);
    define_data(heap, prototype, "toLocaleString", to_locale_string);

    let tag = super::super::push(heap, HeapEntry::String(EcmaString::encode("BigInt")));
    let to_string_tag = builtins.symbol_to_string_tag();
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(prototype)] else {
        unreachable!("prototype is an ordinary object");
    };
    properties.insert(
        PropertyKey::Symbol(heap_index(to_string_tag) as u32),
        Property::Data {
            value: tag,
            writable: false,
            enumerable: false,
            configurable: true,
        },
    );

    globals.insert(EcmaString::encode("BigInt"), constructor);
    prototype
}

fn define_native_property(heap: &mut [HeapEntry], object: Value, name: &str, value: Value) {
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[heap_index(object)] else {
        unreachable!("constructor is a native function");
    };
    properties.insert(
        PropertyKey::Named(EcmaString::encode(name)),
        Property::Data {
            value,
            writable: true,
            enumerable: false,
            configurable: true,
        },
    );
}

/// §21.2.1.1: `BigInt(value)` is callable but not constructible.
fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(type_error("BigInt is not a constructor"));
    }
    let value = args.first().copied().unwrap_or(Value::UNDEFINED);
    let primitive = machine.coerce_primitive_default(value)?;
    if matches!(
        primitive.decode(),
        Some(Decoded::Number(_)) | Some(Decoded::Int32(_))
    ) {
        let number = numeric_f64(primitive).expect("number decodes");
        return Ok(BuiltinOutcome::Value(number_to_bigint(machine, number)?));
    }
    Ok(BuiltinOutcome::Value(to_bigint_primitive(
        machine, primitive,
    )?))
}

/// §21.2.2.1: `BigInt.asIntN(bits, bigint)`.
fn as_int_n<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let bits = to_index(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let operand = to_bigint(machine, args.get(1).copied().unwrap_or(Value::UNDEFINED))?;
    let bigint = bigint_from_value(machine, operand)?.expect("to_bigint returns a BigInt");
    Ok(BuiltinOutcome::Value(allocate_bigint(
        machine,
        &bigint.as_int_n(bits),
    )?))
}

/// §21.2.2.2: `BigInt.asUintN(bits, bigint)`.
fn as_uint_n<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let bits = to_index(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let operand = to_bigint(machine, args.get(1).copied().unwrap_or(Value::UNDEFINED))?;
    let bigint = bigint_from_value(machine, operand)?.expect("to_bigint returns a BigInt");
    Ok(BuiltinOutcome::Value(allocate_bigint(
        machine,
        &bigint.as_uint_n(bits),
    )?))
}

/// `ToIndex`: integer truncating, must be in `[0, 2^53 - 1]`.
fn to_index<H: Host>(machine: &mut Machine<'_, H>, value: Value) -> Result<usize, EvalFailure> {
    if value == Value::UNDEFINED {
        return Ok(0);
    }
    let number = numeric_f64(machine.to_number(value)?).expect("ToNumber returns numeric");
    if !number.is_finite() || !(0.0..=9_007_199_254_740_991.0).contains(&number) {
        return Err(range_error("Invalid index range"));
    }
    usize::try_from(number.trunc() as u64).map_err(|_| range_error("Invalid index range"))
}

/// §21.2.3.1: `BigInt.prototype.toString([radix])`.
fn to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let bigint = this_bigint_value(machine, this)?;
    let radix = match args.first().copied() {
        Some(value) if value != Value::UNDEFINED => {
            let number = numeric_f64(machine.to_number(value)?).expect("ToNumber returns numeric");
            let integer = number.trunc();
            if !number.is_finite() || !(2.0..=36.0).contains(&integer) {
                return Err(range_error("radix must be an integer between 2 and 36"));
            }
            integer as u32
        }
        _ => 10,
    };
    let text = bigint.to_string_radix(radix);
    let string = allocate_string(machine, EcmaString::encode(&text))?;
    Ok(BuiltinOutcome::Value(string))
}

/// §21.2.3.2: `BigInt.prototype.valueOf()`.
fn value_of<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let bigint = this_bigint_value(machine, this)?;
    Ok(BuiltinOutcome::Value(allocate_bigint(machine, &bigint)?))
}

/// ECMA-402 `BigInt.prototype.toLocaleString(locales, options)`: formats
/// through a new `Intl.NumberFormat`, exactly.
fn to_locale_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let bigint = this_bigint_value(machine, this)?;
    let locales = args.first().copied().unwrap_or(Value::UNDEFINED);
    let options = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    super::intl::bigint_to_locale_string(machine, &bigint.to_string_radix(10), locales, options)
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program};
    use super::*;
    use crate::Limits;

    fn observable_value_of(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let count = machine
            .test_global("bigintCoercions")
            .and_then(|value| match value.decode() {
                Some(Decoded::Int32(value)) => Some(value),
                _ => None,
            })
            .unwrap_or(0);
        machine.test_set_global("bigintCoercions", Value::int32(count + 1));
        if machine.test_global("bigintCoercionThrow") == Some(Value::TRUE) {
            return Err(type_error("observable BigInt valueOf failure"));
        }
        machine
            .get_named_property(this, "primitive")
            .map(BuiltinOutcome::Value)
    }

    fn observable_object(machine: &mut Machine<'_, TestHost>, primitive: Value) -> Value {
        let value_of = install_function(
            &mut machine.heap,
            &mut machine.intrinsics.builtins,
            "valueOf",
            0,
            observable_value_of,
        );
        let object = machine
            .allocate(HeapEntry::Object {
                properties: Default::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .expect("observable object allocates");
        machine
            .set_data_property(object, "valueOf", value_of)
            .expect("valueOf installs");
        machine
            .set_data_property(object, "primitive", primitive)
            .expect("primitive installs");
        object
    }

    fn install_bigint(machine: &mut Machine<'_, TestHost>) {
        assert!(
            machine.intrinsics.global("BigInt").is_some(),
            "Machine installs BigInt with its intrinsic set"
        );
    }

    fn bigint_global(machine: &Machine<'_, TestHost>) -> Value {
        machine
            .intrinsics
            .global("BigInt")
            .expect("BigInt global is installed")
    }

    fn bigint_of(machine: &mut Machine<'_, TestHost>, text: &str) -> Value {
        machine
            .allocate(HeapEntry::BigInt(text.to_owned()))
            .expect("bigint allocates")
    }

    fn string_of(machine: &mut Machine<'_, TestHost>, text: &str) -> Value {
        machine
            .allocate(HeapEntry::String(EcmaString::encode(text)))
            .expect("string allocates")
    }

    fn bigint_text(machine: &Machine<'_, TestHost>, value: Value) -> String {
        let index = machine
            .runtime_slot(value)
            .expect("slot resolves")
            .expect("value is a heap reference");
        match &machine.heap[index] {
            HeapEntry::BigInt(text) => text.clone(),
            _ => panic!("expected a BigInt value"),
        }
    }

    fn op_text(
        machine: &mut Machine<'_, TestHost>,
        op: BigIntBinaryOp,
        left: Value,
        right: Value,
    ) -> Option<String> {
        binary_op(machine, op, left, right)
            .expect("operation succeeds")
            .map(|value| bigint_text(machine, value))
    }

    fn assert_type_error(failure: EvalFailure) {
        assert!(
            matches!(failure, EvalFailure::Throw(ThrowOrigin::TypeError { .. })),
            "expected TypeError, got {failure:?}"
        );
    }

    fn assert_range_error(failure: EvalFailure) {
        assert!(
            matches!(failure, EvalFailure::Throw(ThrowOrigin::RangeError { .. })),
            "expected RangeError, got {failure:?}"
        );
    }

    #[test]
    fn constructor_converts_numbers_strings_booleans_and_bigints() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        install_bigint(&mut machine);
        let bigint = bigint_global(&machine);

        let case = |machine: &mut Machine<'_, TestHost>, argument: Value| {
            let result = machine
                .call_value(bigint, bigint, &[argument])
                .expect("constructor call succeeds");
            bigint_text(machine, result)
        };
        assert_eq!(case(&mut machine, Value::int32(123)), "123");
        assert_eq!(case(&mut machine, Value::number(-42.0)), "-42");
        assert_eq!(
            case(&mut machine, Value::number(9_007_199_254_740_992.0)),
            "9007199254740992"
        );
        assert_eq!(case(&mut machine, Value::number(-0.0)), "0");
        assert_eq!(
            case(&mut machine, Value::number(2f64.powi(200))),
            "1606938044258990275541962092341162602522202993782792835301376"
        );
        assert_eq!(case(&mut machine, Value::boolean(true)), "1");
        assert_eq!(case(&mut machine, Value::boolean(false)), "0");
        let hexadecimal = string_of(&mut machine, "  0x1F  ");
        assert_eq!(case(&mut machine, hexadecimal), "31");
        let empty = string_of(&mut machine, "");
        assert_eq!(case(&mut machine, empty), "0");
        let negative = string_of(&mut machine, " -1042 ");
        assert_eq!(case(&mut machine, negative), "-1042");
        let passthrough = bigint_of(&mut machine, "777");
        assert_eq!(case(&mut machine, passthrough), "777");
        let huge = bigint_of(&mut machine, "9007199254740993");
        let explicit_number = bigint_to_number(&machine, huge)
            .expect("explicit conversion succeeds")
            .expect("BigInt is converted");
        assert_eq!(
            numeric_f64(explicit_number).expect("conversion returns Number"),
            9_007_199_254_740_992.0,
            "Number(bigint) rounds through the exact BigInt magnitude"
        );
        assert_eq!(
            bigint_to_number(&machine, Value::int32(1)).expect("probe succeeds"),
            None
        );
    }

    #[test]
    fn constructor_rejects_non_integral_undefined_and_null() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        install_bigint(&mut machine);
        let bigint = bigint_global(&machine);

        let fractional = machine
            .call_value(bigint, bigint, &[Value::number(1.5)])
            .expect_err("fractional numbers must throw");
        assert_range_error(fractional);
        let infinity = machine
            .call_value(bigint, bigint, &[Value::number(f64::INFINITY)])
            .expect_err("infinities must throw");
        assert_range_error(infinity);
        let nan = machine
            .call_value(bigint, bigint, &[Value::number(f64::NAN)])
            .expect_err("NaN must throw");
        assert_range_error(nan);
        let undefined = machine
            .call_value(bigint, bigint, &[Value::UNDEFINED])
            .expect_err("undefined must throw");
        assert_type_error(undefined);
        let null = machine
            .call_value(bigint, bigint, &[Value::NULL])
            .expect_err("null must throw");
        assert_type_error(null);
        let symbol = machine
            .allocate(HeapEntry::Symbol {
                description: EcmaString::encode("scope"),
            })
            .expect("symbol allocates");
        let symbolized = machine
            .call_value(bigint, bigint, &[symbol])
            .expect_err("symbols must throw");
        assert_type_error(symbolized);
    }

    #[test]
    fn constructor_invalid_string_throws_real_syntax_error() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        install_bigint(&mut machine);
        let bigint = bigint_global(&machine);
        for text in ["1_0", "0x", "12 3", "-0x10", "1e5"] {
            let source = string_of(&mut machine, text);
            let EvalFailure::ThrowValue(thrown) = machine
                .call_value(bigint, bigint, &[source])
                .expect_err("invalid literal must throw")
            else {
                panic!("{text} must throw a real SyntaxError value");
            };
            let syntax_error = machine
                .intrinsics
                .global("SyntaxError")
                .expect("SyntaxError global exists");
            let prototype = machine
                .get_named_property(syntax_error, "prototype")
                .expect("SyntaxError.prototype exists");
            assert!(
                machine
                    .inherits_from_prototype(thrown, prototype)
                    .expect("thrown value has a prototype chain"),
                "{text} must produce an instance of SyntaxError"
            );
        }
    }

    #[test]
    fn constructor_is_not_constructible() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        install_bigint(&mut machine);
        let failure = constructor::<TestHost>(&mut machine, Value::UNDEFINED, &[], true)
            .expect_err("new BigInt() must be a TypeError");
        assert_type_error(failure);
    }

    #[test]
    fn constructor_and_prototype_descriptors_are_exact() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        install_bigint(&mut machine);
        let bigint = bigint_global(&machine);

        let named = |name: &str| PropertyKey::Named(EcmaString::encode(name));
        let prototype_descriptor = machine
            .own_descriptor(bigint, &named("prototype"))
            .expect("descriptor lookup succeeds")
            .expect("BigInt.prototype is defined");
        assert!(
            matches!(
                prototype_descriptor,
                Property::Data {
                    writable: false,
                    enumerable: false,
                    configurable: false,
                    ..
                }
            ),
            "prototype descriptor must be non-writable, non-enumerable, non-configurable, got {prototype_descriptor:?}"
        );
        let prototype = machine
            .get_named_property(bigint, "prototype")
            .expect("prototype readable");

        let constructor_descriptor = machine
            .own_descriptor(prototype, &named("constructor"))
            .expect("descriptor lookup succeeds")
            .expect("BigInt.prototype.constructor is defined");
        assert!(
            matches!(
                constructor_descriptor,
                Property::Data {
                    writable: true,
                    enumerable: false,
                    configurable: true,
                    ..
                }
            ),
            "constructor must be writable, non-enumerable, configurable"
        );

        for method in ["toString", "valueOf", "toLocaleString"] {
            let descriptor = machine
                .own_descriptor(prototype, &named(method))
                .expect("descriptor lookup succeeds")
                .unwrap_or_else(|| panic!("{method} is defined"));
            assert!(
                matches!(
                    descriptor,
                    Property::Data {
                        writable: true,
                        enumerable: false,
                        configurable: true,
                        ..
                    }
                ),
                "{method} must be writable, non-enumerable, configurable"
            );
        }

        let to_string_tag = machine.intrinsics.builtins.symbol_to_string_tag();
        let tag_key = PropertyKey::Symbol(heap_index(to_string_tag) as u32);
        let tag_descriptor = machine
            .own_descriptor(prototype, &tag_key)
            .expect("descriptor lookup succeeds")
            .expect("Symbol.toStringTag is defined");
        let Property::Data {
            value: tag,
            writable: false,
            enumerable: false,
            configurable: true,
        } = tag_descriptor
        else {
            panic!(
                "Symbol.toStringTag descriptor must be read-only, non-enumerable, configurable, got {tag_descriptor:?}"
            );
        };
        let text = machine.string_value(tag).expect("tag is a string");
        assert!(text.eq_ascii("BigInt"), "tag text is 'BigInt'");

        // [[Prototype]] of BigInt.prototype is Object.prototype.
        let HeapEntry::Object {
            prototype: Some(target),
            ..
        } = &machine.heap[machine
            .runtime_slot(prototype)
            .expect("slot resolves")
            .expect("prototype is a heap object")]
        else {
            panic!("BigInt.prototype is an ordinary object");
        };
        assert_eq!(*target, machine.intrinsics.object_prototype);

        // Static converters share the same descriptor profile.
        for method in ["asIntN", "asUintN"] {
            let descriptor = machine
                .own_descriptor(bigint, &named(method))
                .expect("descriptor lookup succeeds")
                .unwrap_or_else(|| panic!("{method} is defined"));
            assert!(
                matches!(
                    descriptor,
                    Property::Data {
                        writable: true,
                        enumerable: false,
                        configurable: true,
                        ..
                    }
                ),
                "{method} must be writable, non-enumerable, configurable"
            );
        }
    }

    #[test]
    fn as_int_n_and_as_uint_n_cover_boundaries() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        install_bigint(&mut machine);
        let bigint = bigint_global(&machine);
        let as_int_n = machine
            .get_named_property(bigint, "asIntN")
            .expect("asIntN exists");
        let as_uint_n = machine
            .get_named_property(bigint, "asUintN")
            .expect("asUintN exists");

        let boundary = |machine: &mut Machine<'_, TestHost>, bits: u32, operand: &str| {
            let operand = bigint_of(machine, operand);
            let signed = machine
                .call_value(as_int_n, bigint, &[Value::int32(bits), operand])
                .expect("asIntN call succeeds");
            let signed = bigint_text(machine, signed);
            let unsigned = machine
                .call_value(as_uint_n, bigint, &[Value::int32(bits), operand])
                .expect("asUintN call succeeds");
            let unsigned = bigint_text(machine, unsigned);
            (signed, unsigned)
        };
        assert_eq!(
            boundary(&mut machine, 64, "9223372036854775808"),
            (
                "-9223372036854775808".to_owned(),
                "9223372036854775808".to_owned()
            )
        );
        assert_eq!(
            boundary(&mut machine, 64, "-1"),
            ("-1".to_owned(), "18446744073709551615".to_owned())
        );
        assert_eq!(
            boundary(&mut machine, 8, "255"),
            ("-1".to_owned(), "255".to_owned())
        );
        assert_eq!(
            boundary(&mut machine, 8, "256"),
            ("0".to_owned(), "0".to_owned())
        );
        assert_eq!(
            boundary(&mut machine, 0, "9223372036854775808"),
            ("0".to_owned(), "0".to_owned())
        );
        assert_eq!(
            boundary(&mut machine, 0, "-1"),
            ("0".to_owned(), "0".to_owned())
        );
        assert_eq!(
            boundary(&mut machine, 64, "18446744073709551616"),
            ("0".to_owned(), "0".to_owned())
        );

        let core_one = BigIntValue::one();
        let two_pow_256 = core_one
            .shl(&BigIntValue::from_u64(256))
            .expect("256-bit shift succeeds");
        assert_eq!(
            boundary(&mut machine, 257, &two_pow_256.to_string_radix(10)),
            (
                format!("-{}", two_pow_256.to_string_radix(10)),
                two_pow_256.to_string_radix(10)
            ),
            "the top bit is reinterpreted only by asIntN"
        );
        let (signed, unsigned) = boundary(&mut machine, 4096, "-1");
        assert_eq!(signed, "-1", "large signed widths preserve -1 exactly");
        let expected_unsigned = core_one
            .shl(&BigIntValue::from_u64(4096))
            .expect("4096-bit shift succeeds")
            .sub(&core_one);
        assert_eq!(
            BigIntValue::parse_string(&unsigned).expect("asUintN result parses"),
            expected_unsigned,
            "asUintN(4096, -1) is exactly 2^4096 - 1"
        );

        let one = bigint_of(&mut machine, "1");
        let negative_bits = machine
            .call_value(as_int_n, bigint, &[Value::number(-1.0), one])
            .expect_err("negative width must throw");
        assert_range_error(negative_bits);
        let enormous_bits = machine
            .call_value(as_uint_n, bigint, &[Value::number(1e30), one])
            .expect_err("oversized width must throw");
        assert_range_error(enormous_bits);
    }

    #[test]
    fn prototype_to_string_handles_radixes_and_range_errors() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        install_bigint(&mut machine);
        let bigint = bigint_global(&machine);
        let prototype = machine
            .get_named_property(bigint, "prototype")
            .expect("prototype exists");
        let to_string = machine
            .get_named_property(prototype, "toString")
            .expect("toString exists");

        let call = |machine: &mut Machine<'_, TestHost>, operand: &str, radix: Option<Value>| {
            let receiver = bigint_of(machine, operand);
            let args: &[Value] = match radix {
                Some(value) => &[value],
                None => &[],
            };
            let result = machine
                .call_value(to_string, receiver, args)
                .expect("toString succeeds");
            machine.to_string(result).expect("result is text data")
        };
        assert!(call(&mut machine, "-255", Some(Value::int32(16))).eq_ascii("-ff"));
        assert!(call(&mut machine, "5", Some(Value::int32(2))).eq_ascii("101"));
        assert!(call(&mut machine, "35", Some(Value::int32(36))).eq_ascii("z"));
        assert!(call(&mut machine, "1042", None).eq_ascii("1042"));
        assert!(call(&mut machine, "1042", Some(Value::UNDEFINED)).eq_ascii("1042"));
        assert!(
            call(
                &mut machine,
                "1606938044258990275541962092341162602522202993782792835301376",
                Some(Value::int32(16))
            )
            .eq_ascii("100000000000000000000000000000000000000000000000000")
        );

        for bad in [Value::int32(1), Value::int32(37), Value::number(f64::NAN)] {
            let receiver = bigint_of(&mut machine, "9");
            let failure = machine
                .call_value(to_string, receiver, &[bad])
                .expect_err("out-of-range radix must throw");
            assert_range_error(failure);
        }

        let boxed_receiver = Value::int32(10);
        let incompatible = machine
            .call_value(to_string, boxed_receiver, &[])
            .expect_err("primitive number receiver must throw");
        assert_type_error(incompatible);
    }

    #[test]
    fn value_of_unboxes_and_to_locale_string_matches_decimal() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        install_bigint(&mut machine);
        let bigint = bigint_global(&machine);
        let prototype = machine
            .get_named_property(bigint, "prototype")
            .expect("prototype exists");
        let value_of = machine
            .get_named_property(prototype, "valueOf")
            .expect("valueOf exists");
        let to_locale_string = machine
            .get_named_property(prototype, "toLocaleString")
            .expect("toLocaleString exists");

        let receiver = bigint_of(&mut machine, "-9099");
        let unboxed = machine
            .call_value(value_of, receiver, &[])
            .expect("valueOf succeeds");
        assert_eq!(bigint_text(&machine, unboxed), "-9099");

        // call with a boxed BigInt receiver
        let forty_two = bigint_of(&mut machine, "42");
        let boxed = machine
            .allocate(HeapEntry::Object {
                properties: Default::default(),
                prototype: Some(prototype),
                boxed_primitive: Some(forty_two),
                extensible: true,
            })
            .expect("boxed allocates");
        let unboxed_boxed = machine
            .call_value(value_of, boxed, &[])
            .expect("valueOf on boxed receiver succeeds");
        assert_eq!(bigint_text(&machine, unboxed_boxed), "42");

        let locale = machine
            .call_value(to_locale_string, receiver, &[])
            .expect("toLocaleString succeeds");
        let text = machine.to_string(locale).expect("locale result is text");
        assert!(
            text.eq_ascii("-9,099"),
            "toLocaleString groups like Intl.NumberFormat"
        );
    }

    #[test]
    fn binary_op_basics_boundaries_and_mixed_rejection() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        install_bigint(&mut machine);
        let zero = bigint_of(&mut machine, "0");
        let two = bigint_of(&mut machine, "2");
        let huge = bigint_of(&mut machine, "18446744073709551616");
        let minus_seven = bigint_of(&mut machine, "-7");

        let op = |machine: &mut Machine<'_, TestHost>, kind, left, right| {
            binary_op(machine, kind, left, right)
        };
        // Neither operand BigInt -> None so the Number path applies.
        let none = op(
            &mut machine,
            BigIntBinaryOp::Add,
            Value::int32(1),
            Value::int32(2),
        )
        .expect("number/number succeeds");
        assert!(none.is_none(), "no BigInt operand must defer to the caller");

        // Mixed operand is a TypeError for arithmetic and bitwise operators.
        let mixed_add = op(&mut machine, BigIntBinaryOp::Add, two, Value::int32(1))
            .expect_err("bigint + number must throw");
        assert_type_error(mixed_add);
        let mixed_and = op(&mut machine, BigIntBinaryOp::BitAnd, Value::int32(1), two)
            .expect_err("number & bigint must throw");
        assert_type_error(mixed_and);

        // Huge exact arithmetic beyond the previous i128-bounded path.
        let doubled = op(&mut machine, BigIntBinaryOp::Add, huge, huge)
            .expect("add succeeds")
            .expect("result exists");
        assert_eq!(bigint_text(&machine, doubled), "36893488147419103232");
        let difference = op(&mut machine, BigIntBinaryOp::Subtract, huge, huge)
            .expect("subtract succeeds")
            .expect("result exists");
        assert_eq!(bigint_text(&machine, difference), "0");
        let product = op(&mut machine, BigIntBinaryOp::Multiply, huge, two)
            .expect("multiply succeeds")
            .expect("result exists");
        assert_eq!(bigint_text(&machine, product), "36893488147419103232");

        // Truncating division and dividend-signed remainder.
        let quotient = op(&mut machine, BigIntBinaryOp::Divide, minus_seven, two)
            .expect("divide succeeds")
            .expect("result exists");
        assert_eq!(bigint_text(&machine, quotient), "-3");
        let remainder = op(&mut machine, BigIntBinaryOp::Remainder, minus_seven, two)
            .expect("remainder succeeds")
            .expect("result exists");
        assert_eq!(bigint_text(&machine, remainder), "-1");

        let division_by_zero = op(&mut machine, BigIntBinaryOp::Divide, two, zero)
            .expect_err("division by zero must throw");
        assert_range_error(division_by_zero);
        let modulo_by_zero = op(&mut machine, BigIntBinaryOp::Remainder, two, zero)
            .expect_err("remainder by zero must throw");
        assert_range_error(modulo_by_zero);

        let minus_one = bigint_of(&mut machine, "-1");
        let negative_exponent = op(&mut machine, BigIntBinaryOp::Exponentiate, two, minus_one)
            .expect_err("negative exponent must throw");
        assert_range_error(negative_exponent);
    }

    #[test]
    fn shifts_and_bitwise_follow_floor_and_sign_rules() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        install_bigint(&mut machine);
        let machine = &mut machine;
        let one = bigint_of(machine, "1");
        let minus_five = bigint_of(machine, "-5");

        // -5n >> 1n === -3n (shift right floors; division truncates).
        let unsigned = binary_op(machine, BigIntBinaryOp::UnsignedRightShift, minus_five, one)
            .expect_err("BigInt unsigned right shift must throw");
        assert_type_error(unsigned);
        assert_eq!(
            op_text(machine, BigIntBinaryOp::RightShift, minus_five, one).as_deref(),
            Some("-3")
        );
        assert_eq!(
            op_text(machine, BigIntBinaryOp::LeftShift, minus_five, one).as_deref(),
            Some("-10")
        );
        let huge_shift = bigint_of(machine, "200");
        let shifted =
            op_text(machine, BigIntBinaryOp::LeftShift, one, huge_shift).expect("shift produces");
        assert_eq!(shifted.len(), 61, "2^200 decimal length");
        let enormous_shift = bigint_of(
            machine,
            "1606938044258990275541962092341162602522202993782792835301376",
        );
        assert_eq!(
            op_text(machine, BigIntBinaryOp::RightShift, one, enormous_shift).as_deref(),
            Some("0"),
            "a huge right shift saturates instead of becoming a host range error"
        );
        assert_eq!(
            op_text(
                machine,
                BigIntBinaryOp::RightShift,
                minus_five,
                enormous_shift
            )
            .as_deref(),
            Some("-1"),
            "a huge arithmetic right shift preserves infinite sign extension"
        );
        let negative_enormous_shift = bigint_of(
            machine,
            "-1606938044258990275541962092341162602522202993782792835301376",
        );
        assert_eq!(
            op_text(
                machine,
                BigIntBinaryOp::LeftShift,
                one,
                negative_enormous_shift,
            )
            .as_deref(),
            Some("0"),
            "a huge negative left shift reverses into a saturating right shift"
        );
        let five = bigint_of(machine, "5");
        let three = bigint_of(machine, "3");
        assert_eq!(
            op_text(machine, BigIntBinaryOp::BitAnd, five, three).as_deref(),
            Some("1")
        );
        assert_eq!(
            op_text(machine, BigIntBinaryOp::BitOr, five, three).as_deref(),
            Some("7")
        );
        assert_eq!(
            op_text(machine, BigIntBinaryOp::BitXor, five, three).as_deref(),
            Some("6")
        );
        let minus_one = bigint_of(machine, "-1");
        let not_case = bitwise_not(machine, minus_one).expect("bitwise not");
        assert_eq!(
            not_case.map(|value| bigint_text(machine, value)).as_deref(),
            Some("0")
        );
        let value = bigint_of(machine, "2549");
        let not_nine = bitwise_not(machine, value).expect("bitwise not");
        assert_eq!(
            not_nine.map(|value| bigint_text(machine, value)).as_deref(),
            Some("-2550")
        );
        let value = bigint_of(machine, "9007199254740993");
        let negate = unary_minus(machine, value).expect("negate");
        assert_eq!(
            negate.map(|value| bigint_text(machine, value)).as_deref(),
            Some("-9007199254740993")
        );
        let zero = bigint_of(machine, "0");
        let negate_zero = unary_minus(machine, zero).expect("negate zero");
        assert_eq!(
            negate_zero
                .map(|value| bigint_text(machine, value))
                .as_deref(),
            Some("0"),
            "negation normalizes -0n to 0n"
        );
    }

    #[test]
    fn equality_and_relational_helpers_follow_numeric_comparison() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        install_bigint(&mut machine);
        let machine = &mut machine;
        let one_bigint = bigint_of(machine, "1");
        let two_bigint = bigint_of(machine, "2");

        assert_eq!(
            strict_equals(machine, one_bigint, one_bigint).expect("strict compare"),
            Some(true)
        );
        assert_eq!(
            strict_equals(machine, one_bigint, two_bigint).expect("strict compare"),
            Some(false)
        );
        assert_eq!(
            strict_equals(machine, one_bigint, Value::int32(1)).expect("strict compare"),
            Some(false),
            "1n === 1 is false"
        );
        assert_eq!(
            strict_equals(machine, Value::number(1.0), Value::int32(2)).expect("strict compare"),
            None,
            "no BigInt participation defers to the caller"
        );

        assert_eq!(
            loose_equals(machine, one_bigint, Value::int32(1)).expect("loose compare"),
            Some(true),
            "1n == 1 is true"
        );
        assert_eq!(
            loose_equals(machine, one_bigint, Value::number(f64::NAN)).expect("loose compare"),
            Some(false)
        );
        let one_text = string_of(machine, "1");
        assert_eq!(
            loose_equals(machine, one_bigint, one_text).expect("loose compare"),
            Some(true)
        );
        let nan_text = string_of(machine, "abc");
        assert_eq!(
            loose_equals(machine, one_bigint, nan_text).expect("loose compare"),
            Some(false)
        );
        let rounded = bigint_of(machine, "9007199254740993");
        assert_eq!(
            loose_equals(machine, rounded, Value::number(9_007_199_254_740_992.0))
                .expect("loose compare keeps precision"),
            Some(false),
            "2^53 + 1 must not equal its f64 rounding"
        );

        assert_eq!(
            compare(machine, one_bigint, Value::number(2.0)).expect("compare"),
            Some(Some(std::cmp::Ordering::Less))
        );
        assert_eq!(
            compare(machine, two_bigint, Value::number(1.5)).expect("compare"),
            Some(Some(std::cmp::Ordering::Greater))
        );
        assert_eq!(
            compare(machine, Value::number(1.5), two_bigint).expect("compare"),
            Some(Some(std::cmp::Ordering::Less))
        );
        assert_eq!(
            compare(machine, one_bigint, Value::number(f64::NAN)).expect("compare"),
            Some(None),
            "NaN remains unordered"
        );
        assert_eq!(
            compare(machine, Value::number(2.0), Value::number(1.0)).expect("compare"),
            None,
            "no BigInt participation defers to the caller"
        );
    }
    #[test]
    fn machine_operators_preserve_bigint_precision_and_unordered_relations() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let huge = bigint_of(&mut machine, "9007199254740993");
        let doubled = machine
            .eval_binary(bamts_bytecode::BinaryOp::Add, huge, huge)
            .expect("arbitrary-precision addition succeeds");
        assert_eq!(bigint_text(&machine, doubled), "18014398509481986");

        let mixed = machine
            .eval_binary(bamts_bytecode::BinaryOp::Add, huge, Value::int32(1))
            .expect_err("mixed BigInt and Number addition throws");
        assert_type_error(mixed);

        for op in [
            bamts_bytecode::BinaryOp::LessThan,
            bamts_bytecode::BinaryOp::LessThanOrEqual,
            bamts_bytecode::BinaryOp::GreaterThan,
            bamts_bytecode::BinaryOp::GreaterThanOrEqual,
        ] {
            let result = machine
                .eval_binary(op, huge, Value::number(f64::NAN))
                .expect("unordered comparison completes");
            assert_eq!(result.decode(), Some(Decoded::Boolean(false)));
        }
    }

    #[test]
    fn machine_operators_cover_arbitrary_precision_shifts_equality_and_errors() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let one = bigint_of(&mut machine, "1");
        let shift = bigint_of(&mut machine, "200");
        let shifted = machine
            .eval_binary(bamts_bytecode::BinaryOp::ShiftLeft, one, shift)
            .expect("large left shift succeeds");
        assert_eq!(
            bigint_text(&machine, shifted),
            "1606938044258990275541962092341162602522202993782792835301376"
        );
        let minus_one = bigint_of(&mut machine, "-1");
        let thousand = bigint_of(&mut machine, "1000");
        let right = machine
            .eval_binary(bamts_bytecode::BinaryOp::ShiftRight, minus_one, thousand)
            .expect("arithmetic right shift saturates");
        assert_eq!(bigint_text(&machine, right), "-1");
        let one_shift = bigint_of(&mut machine, "1");
        let unsigned = machine
            .eval_binary(bamts_bytecode::BinaryOp::UnsignedShiftRight, one, one_shift)
            .expect_err("BigInt unsigned shift throws");
        assert_type_error(unsigned);

        let huge = bigint_of(&mut machine, "9007199254740993");
        let equal = machine
            .eval_binary(
                bamts_bytecode::BinaryOp::Equal,
                huge,
                Value::number(9_007_199_254_740_992.0),
            )
            .expect("mixed equality completes");
        assert_eq!(equal, Value::FALSE);
        let ordered = machine
            .eval_binary(
                bamts_bytecode::BinaryOp::GreaterThan,
                huge,
                Value::number(9_007_199_254_740_992.0),
            )
            .expect("mixed ordering completes");
        assert_eq!(ordered, Value::TRUE);

        let zero = bigint_of(&mut machine, "0");
        let division = machine
            .eval_binary(bamts_bytecode::BinaryOp::Divide, one, zero)
            .expect_err("division by zero throws");
        assert_range_error(division);
        let exponent = machine
            .eval_binary(bamts_bytecode::BinaryOp::Exponent, one, minus_one)
            .expect_err("negative exponent throws");
        assert_range_error(exponent);
    }

    #[test]
    fn cached_constructor_and_prototype_survive_global_removal_and_gc() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.builtins.bigint_constructor();
        let prototype = machine.intrinsics.builtins.bigint_prototype();
        let constructor_slot = machine
            .runtime_slot(constructor)
            .expect("constructor slot resolves")
            .expect("constructor is a heap value");
        let prototype_slot = machine
            .runtime_slot(prototype)
            .expect("prototype slot resolves")
            .expect("prototype is a heap value");
        machine
            .intrinsics
            .globals
            .remove(&EcmaString::encode("BigInt"));
        machine.collect_garbage();
        assert!(!matches!(machine.heap[constructor_slot], HeapEntry::Vacant));
        assert!(!matches!(machine.heap[prototype_slot], HeapEntry::Vacant));

        let text = string_of(&mut machine, "340282366920938463463374607431768211456");
        let bigint = machine
            .call_value(constructor, Value::UNDEFINED, &[text])
            .expect("cached constructor remains callable");
        let boxed = machine.box_primitive(bigint).expect("BigInt boxes");
        let boxed_slot = machine
            .runtime_slot(boxed)
            .expect("boxed slot resolves")
            .expect("boxed value has a slot");
        assert_eq!(
            machine
                .prototype_index(boxed_slot)
                .expect("prototype lookup"),
            Some(prototype_slot)
        );
        assert_eq!(
            machine
                .get_named_property(bigint, "toString")
                .expect("primitive uses cached BigInt prototype"),
            machine
                .get_named_property(prototype, "toString")
                .expect("prototype method exists")
        );
    }

    #[test]
    fn number_constructor_explicitly_converts_bigint() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let number = machine
            .intrinsics
            .global("Number")
            .expect("Number global is installed");
        let bigint = bigint_of(&mut machine, "340282366920938463463374607431768211456");
        let converted = machine
            .call_value(number, Value::UNDEFINED, &[bigint])
            .expect("Number(BigInt) explicitly converts");
        assert_eq!(
            numeric_f64(converted),
            Some(340282366920938463463374607431768211456_f64)
        );
        assert_type_error(
            machine
                .to_number(bigint)
                .expect_err("implicit ToNumber(BigInt) remains forbidden"),
        );
    }

    #[test]
    fn object_inputs_use_observable_default_hint_once_and_propagate_errors() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = bigint_global(&machine);
        let as_int_n = machine
            .get_named_property(constructor, "asIntN")
            .expect("asIntN exists");
        let as_uint_n = machine
            .get_named_property(constructor, "asUintN")
            .expect("asUintN exists");
        let primitive = bigint_of(&mut machine, "255");
        let boxed = machine.box_primitive(primitive).expect("BigInt boxes");
        let constructor_result = machine
            .call_value(constructor, Value::UNDEFINED, &[boxed])
            .expect("BigInt accepts a boxed BigInt");
        assert_eq!(bigint_text(&machine, constructor_result), "255");
        let signed_result = machine
            .call_value(as_int_n, constructor, &[Value::int32(8), boxed])
            .expect("asIntN accepts a boxed BigInt");
        assert_eq!(bigint_text(&machine, signed_result), "-1");
        let unsigned_result = machine
            .call_value(as_uint_n, constructor, &[Value::int32(8), boxed])
            .expect("asUintN accepts a boxed BigInt");
        assert_eq!(bigint_text(&machine, unsigned_result), "255");
        let object = observable_object(&mut machine, primitive);
        for (function, args, expected) in [
            (constructor, vec![object], "255"),
            (as_int_n, vec![Value::int32(8), object], "-1"),
            (as_uint_n, vec![Value::int32(8), object], "255"),
        ] {
            machine.test_set_global("bigintCoercions", Value::int32(0));
            let result = machine
                .call_value(function, constructor, &args)
                .expect("observable conversion succeeds");
            assert_eq!(bigint_text(&machine, result), expected);
            assert_eq!(
                machine.test_global("bigintCoercions"),
                Some(Value::int32(1)),
                "conversion must invoke valueOf exactly once"
            );
        }

        machine.test_set_global("bigintCoercions", Value::int32(0));
        let equal = machine
            .eval_binary(bamts_bytecode::BinaryOp::Equal, primitive, object)
            .expect("BigInt/object loose equality succeeds");
        assert_eq!(equal, Value::TRUE);
        assert_eq!(
            machine.test_global("bigintCoercions"),
            Some(Value::int32(1)),
            "loose equality must observably coerce the object once"
        );

        machine.test_set_global("bigintCoercionThrow", Value::TRUE);
        for (function, args) in [
            (constructor, vec![object]),
            (as_int_n, vec![Value::int32(8), object]),
            (as_uint_n, vec![Value::int32(8), object]),
        ] {
            machine.test_set_global("bigintCoercions", Value::int32(0));
            let failure = machine
                .call_value(function, constructor, &args)
                .expect_err("valueOf abrupt completion propagates");
            assert_type_error(failure);
            assert_eq!(
                machine.test_global("bigintCoercions"),
                Some(Value::int32(1))
            );
        }
        machine.test_set_global("bigintCoercions", Value::int32(0));
        let equality_failure = machine
            .eval_binary(bamts_bytecode::BinaryOp::Equal, primitive, object)
            .expect_err("loose equality propagates valueOf abrupt completion");
        assert_type_error(equality_failure);
        assert_eq!(
            machine.test_global("bigintCoercions"),
            Some(Value::int32(1))
        );
    }

    #[test]
    fn loose_equality_coerces_bigint_objects_against_boolean_and_string() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let one = bigint_of(&mut machine, "1");
        let boxed = machine.box_primitive(one).expect("BigInt boxes");
        let one_text = string_of(&mut machine, "1");
        for (left, right) in [
            (boxed, Value::TRUE),
            (Value::TRUE, boxed),
            (boxed, one_text),
            (one_text, boxed),
        ] {
            assert_eq!(
                machine
                    .eval_binary(bamts_bytecode::BinaryOp::Equal, left, right)
                    .expect("boxed BigInt equality completes"),
                Value::TRUE
            );
        }

        let object = observable_object(&mut machine, one);
        for (left, right) in [
            (object, Value::TRUE),
            (Value::TRUE, object),
            (object, one_text),
            (one_text, object),
        ] {
            machine.test_set_global("bigintCoercions", Value::int32(0));
            assert_eq!(
                machine
                    .eval_binary(bamts_bytecode::BinaryOp::Equal, left, right)
                    .expect("observable object equality completes"),
                Value::TRUE
            );
            assert_eq!(
                machine.test_global("bigintCoercions"),
                Some(Value::int32(1)),
                "each equality must coerce the object exactly once"
            );
        }

        machine.test_set_global("bigintCoercionThrow", Value::TRUE);
        machine.test_set_global("bigintCoercions", Value::int32(0));
        let failure = machine
            .eval_binary(bamts_bytecode::BinaryOp::Equal, object, one_text)
            .expect_err("object coercion error propagates against a String");
        assert_type_error(failure);
        assert_eq!(
            machine.test_global("bigintCoercions"),
            Some(Value::int32(1))
        );
    }

    #[test]
    fn relational_string_branch_uses_string_to_bigint_not_to_number() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let one = bigint_of(&mut machine, "1");
        let decimal = string_of(&mut machine, "2");
        let exponent = string_of(&mut machine, "1e1");
        let fraction = string_of(&mut machine, "1.0");

        assert_eq!(
            machine
                .eval_binary(bamts_bytecode::BinaryOp::LessThan, one, decimal)
                .expect("decimal StringToBigInt comparison succeeds"),
            Value::TRUE
        );
        for text in [exponent, fraction] {
            for op in [
                bamts_bytecode::BinaryOp::LessThan,
                bamts_bytecode::BinaryOp::GreaterThan,
                bamts_bytecode::BinaryOp::LessThanOrEqual,
                bamts_bytecode::BinaryOp::GreaterThanOrEqual,
            ] {
                assert_eq!(
                    machine
                        .eval_binary(op, one, text)
                        .expect("invalid StringToBigInt is unordered"),
                    Value::FALSE
                );
            }
        }

        let huge = bigint_of(&mut machine, "9007199254740993");
        assert_eq!(
            machine
                .eval_binary(
                    bamts_bytecode::BinaryOp::GreaterThan,
                    huge,
                    Value::number(9_007_199_254_740_992.0),
                )
                .expect("BigInt/Number comparison remains exact"),
            Value::TRUE
        );
    }

    #[test]
    fn json_rejection_contract_is_a_type_error() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        install_bigint(&mut machine);
        let operand = bigint_of(&mut machine, "9007199254740993");
        let failure = json_reject(&machine, operand).expect_err("BigInt cannot serialize");
        assert_type_error(failure);
        json_reject(&machine, Value::int32(7)).expect("numbers serialize fine");
        json_reject(&machine, machine.intrinsics.object_prototype)
            .expect("objects proceed through property serialization");
    }
}
