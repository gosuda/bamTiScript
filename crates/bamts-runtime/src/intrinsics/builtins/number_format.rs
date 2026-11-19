//! Exact ECMAScript `Number` parsing and formatting primitives.
//!
//! Callers perform the language-level coercions before entering this leaf module.
// Exact limb decomposition and language-mandated floating-point equality make
// these otherwise useful generic lints inapplicable to this numeric leaf.
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::float_cmp,
    clippy::missing_errors_doc,
    clippy::missing_panics_doc
)]

use std::cmp::Ordering;

const DIGITS: &[u8; 36] = b"0123456789abcdefghijklmnopqrstuvwxyz";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NumberFormatError {
    FractionDigits,
    Precision,
    Radix,
}

impl NumberFormatError {
    #[must_use]
    pub const fn message(self) -> &'static str {
        match self {
            Self::FractionDigits => "fractionDigits argument must be between 0 and 100",
            Self::Precision => "precision argument must be between 1 and 100",
            Self::Radix => "radix argument must be between 2 and 36",
        }
    }
}

/// An unsigned integer stored in little-endian base 2^32 limbs.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Big(Vec<u32>);

impl Big {
    fn zero() -> Self {
        Self(Vec::new())
    }

    fn one() -> Self {
        Self(vec![1])
    }

    fn from_u64(value: u64) -> Self {
        let low = value as u32;
        let high = (value >> 32) as u32;
        if high != 0 {
            Self(vec![low, high])
        } else if low != 0 {
            Self(vec![low])
        } else {
            Self::zero()
        }
    }

    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    fn normalize(&mut self) {
        while self.0.last() == Some(&0) {
            self.0.pop();
        }
    }

    fn cmp(&self, other: &Self) -> Ordering {
        match self.0.len().cmp(&other.0.len()) {
            Ordering::Equal => self.0.iter().rev().cmp(other.0.iter().rev()),
            order => order,
        }
    }

    fn add_small(&mut self, value: u32) {
        let mut carry = u64::from(value);
        let mut index = 0;
        while carry != 0 {
            if index == self.0.len() {
                self.0.push(0);
            }
            let sum = u64::from(self.0[index]) + carry;
            self.0[index] = sum as u32;
            carry = sum >> 32;
            index += 1;
        }
    }

    fn mul_small(&mut self, value: u32) {
        if value == 0 {
            self.0.clear();
            return;
        }
        let mut carry = 0_u64;
        for limb in &mut self.0 {
            let product = u64::from(*limb) * u64::from(value) + carry;
            *limb = product as u32;
            carry = product >> 32;
        }
        if carry != 0 {
            self.0.push(carry as u32);
        }
    }

    fn mul_pow10(&mut self, exponent: u32) {
        for _ in 0..exponent {
            self.mul_small(10);
        }
    }

    fn shl_bits(&mut self, count: u32) {
        if self.is_zero() || count == 0 {
            return;
        }
        let words = (count / 32) as usize;
        let bits = count % 32;
        if words != 0 {
            self.0.splice(0..0, std::iter::repeat_n(0, words));
        }
        if bits != 0 {
            let mut carry = 0_u64;
            for limb in &mut self.0 {
                let shifted = (u64::from(*limb) << bits) | carry;
                *limb = shifted as u32;
                carry = shifted >> 32;
            }
            if carry != 0 {
                self.0.push(carry as u32);
            }
        }
    }

    fn shl_one(&mut self) {
        self.shl_bits(1);
    }

    fn bit_length(&self) -> u32 {
        self.0.last().map_or(0, |top| {
            u32::try_from((self.0.len() - 1) * 32).expect("number is bounded")
                + (32 - top.leading_zeros())
        })
    }

    fn bit(&self, index: u32) -> bool {
        let word = (index / 32) as usize;
        self.0
            .get(word)
            .is_some_and(|limb| limb & (1_u32 << (index % 32)) != 0)
    }

    fn set_bit(&mut self, index: u32) {
        let word = (index / 32) as usize;
        if self.0.len() <= word {
            self.0.resize(word + 1, 0);
        }
        self.0[word] |= 1_u32 << (index % 32);
    }

    fn sub_assign(&mut self, other: &Self) {
        debug_assert_ne!(self.cmp(other), Ordering::Less);
        let mut borrow = 0_u64;
        for (index, limb) in self.0.iter_mut().enumerate() {
            let rhs = u64::from(other.0.get(index).copied().unwrap_or(0)) + borrow;
            let lhs = u64::from(*limb);
            *limb = lhs.wrapping_sub(rhs) as u32;
            borrow = u64::from(lhs < rhs);
        }
        debug_assert_eq!(borrow, 0);
        self.normalize();
    }

    fn div_rem(&self, divisor: &Self) -> (Self, Self) {
        debug_assert!(!divisor.is_zero());
        let mut quotient = Self::zero();
        let mut remainder = Self::zero();
        for index in (0..self.bit_length()).rev() {
            remainder.shl_one();
            if self.bit(index) {
                remainder.add_small(1);
            }
            if remainder.cmp(divisor) != Ordering::Less {
                remainder.sub_assign(divisor);
                quotient.set_bit(index);
            }
        }
        (quotient, remainder)
    }

    fn divmod_small(&mut self, divisor: u32) -> u32 {
        let mut remainder = 0_u64;
        for limb in self.0.iter_mut().rev() {
            let current = (remainder << 32) | u64::from(*limb);
            *limb = (current / u64::from(divisor)) as u32;
            remainder = current % u64::from(divisor);
        }
        self.normalize();
        remainder as u32
    }

    fn to_radix_string(&self, radix: u32) -> String {
        if self.is_zero() {
            return "0".to_owned();
        }
        let mut value = self.clone();
        let mut output = Vec::new();
        while !value.is_zero() {
            output.push(char::from(DIGITS[value.divmod_small(radix) as usize]));
        }
        output.reverse();
        output.into_iter().collect()
    }

    fn to_decimal_string(&self) -> String {
        self.to_radix_string(10)
    }
}

fn decompose(value: f64) -> (u64, i32) {
    debug_assert!(value.is_finite() && value >= 0.0);
    let bits = value.to_bits();
    let raw_exponent = ((bits >> 52) & 0x7ff) as i32;
    let fraction = bits & ((1_u64 << 52) - 1);
    if raw_exponent == 0 {
        (fraction, -1074)
    } else {
        (fraction | (1_u64 << 52), raw_exponent - 1023 - 52)
    }
}

fn integer_magnitude(value: f64) -> Big {
    let (significand, exponent) = decompose(value.trunc());
    let mut result = Big::from_u64(significand);
    if exponent >= 0 {
        result.shl_bits(exponent as u32);
    } else {
        let divisor = {
            let mut value = Big::one();
            value.shl_bits(exponent.unsigned_abs());
            value
        };
        result = result.div_rem(&divisor).0;
    }
    result
}

/// Returns `round(value * 10^decimal_scale)`, resolving ties toward +infinity.
fn exact_round_scaled(value: f64, decimal_scale: i32) -> Big {
    debug_assert!(value.is_finite() && value >= 0.0);
    if value == 0.0 {
        return Big::zero();
    }
    let (significand, binary_exponent) = decompose(value);
    let mut numerator = Big::from_u64(significand);
    let mut denominator = Big::one();
    if binary_exponent >= 0 {
        numerator.shl_bits(binary_exponent as u32);
    } else {
        denominator.shl_bits(binary_exponent.unsigned_abs());
    }
    if decimal_scale >= 0 {
        numerator.mul_pow10(decimal_scale as u32);
    } else {
        denominator.mul_pow10(decimal_scale.unsigned_abs());
    }

    let (mut quotient, mut remainder) = numerator.div_rem(&denominator);
    remainder.mul_small(2);
    if remainder.cmp(&denominator) != Ordering::Less {
        quotient.add_small(1);
    }
    quotient
}

fn non_finite(value: f64) -> Option<String> {
    if value.is_nan() {
        Some("NaN".to_owned())
    } else if value == f64::INFINITY {
        Some("Infinity".to_owned())
    } else if value == f64::NEG_INFINITY {
        Some("-Infinity".to_owned())
    } else {
        None
    }
}

/// Obtains the shortest round-tripping decimal digits and their base-10 exponent.
/// Final decimal ToString text is owned by `bamts_bytecode::format_number`.
fn shortest_digits(value: f64) -> (String, i32) {
    debug_assert!(value.is_finite() && value > 0.0);
    let scientific = format!("{value:e}");
    let (mantissa, exponent) = scientific
        .split_once('e')
        .expect("LowerExp always contains an exponent");
    let mut digits = mantissa.replace('.', "");
    while digits.ends_with('0') && digits.len() > 1 {
        digits.pop();
    }
    let exponent = exponent
        .parse::<i32>()
        .expect("LowerExp exponent is numeric");
    (digits, exponent)
}

fn checked_fraction_digits(value: f64) -> Result<u32, NumberFormatError> {
    if !value.is_finite() || !(0.0..=100.0).contains(&value) || value.fract() != 0.0 {
        Err(NumberFormatError::FractionDigits)
    } else {
        Ok(value as u32)
    }
}

fn checked_precision(value: f64) -> Result<u32, NumberFormatError> {
    if !value.is_finite() || !(1.0..=100.0).contains(&value) || value.fract() != 0.0 {
        Err(NumberFormatError::Precision)
    } else {
        Ok(value as u32)
    }
}

pub fn to_fixed(value: f64, fraction_digits: f64) -> Result<String, NumberFormatError> {
    let fraction_digits = checked_fraction_digits(fraction_digits)?;
    if let Some(text) = non_finite(value) {
        return Ok(text);
    }
    if value.abs() >= 1e21 {
        return Ok(bamts_bytecode::format_number(value));
    }
    let negative = value < 0.0;
    let digits = exact_round_scaled(value.abs(), fraction_digits as i32).to_decimal_string();
    let fraction_digits = fraction_digits as usize;
    let mut output = String::new();
    if negative {
        output.push('-');
    }
    if fraction_digits == 0 {
        output.push_str(&digits);
    } else if digits.len() <= fraction_digits {
        output.push_str("0.");
        output.extend(std::iter::repeat_n('0', fraction_digits - digits.len()));
        output.push_str(&digits);
    } else {
        let split = digits.len() - fraction_digits;
        output.push_str(&digits[..split]);
        output.push('.');
        output.push_str(&digits[split..]);
    }
    Ok(output)
}

fn rounded_significand(value: f64, precision: u32) -> (String, i32) {
    debug_assert!(value > 0.0 && value.is_finite());
    let (_, mut exponent) = shortest_digits(value);
    loop {
        let scale = i32::try_from(precision).expect("precision is bounded") - 1 - exponent;
        let digits = exact_round_scaled(value, scale).to_decimal_string();
        if digits.len() > precision as usize {
            exponent += 1;
            continue;
        }
        if digits.len() < precision as usize {
            exponent -= 1;
            continue;
        }
        return (digits, exponent);
    }
}

fn exponential_from_digits(digits: &str, exponent: i32, negative: bool) -> String {
    let mut output = String::new();
    if negative {
        output.push('-');
    }
    output.push(char::from(digits.as_bytes()[0]));
    if digits.len() > 1 {
        output.push('.');
        output.push_str(&digits[1..]);
    }
    output.push('e');
    if exponent >= 0 {
        output.push('+');
    }
    output.push_str(&exponent.to_string());
    output
}

pub fn to_exponential(
    value: f64,
    fraction_digits: Option<f64>,
) -> Result<String, NumberFormatError> {
    if let Some(text) = non_finite(value) {
        return Ok(text);
    }
    let requested = fraction_digits.map(checked_fraction_digits).transpose()?;
    let negative = value < 0.0;
    if value == 0.0 {
        let count = requested.unwrap_or(0) as usize;
        let digits = std::iter::repeat_n('0', count + 1).collect::<String>();
        return Ok(exponential_from_digits(&digits, 0, false));
    }
    if let Some(fraction_digits) = requested {
        let (digits, exponent) = rounded_significand(value.abs(), fraction_digits + 1);
        Ok(exponential_from_digits(&digits, exponent, negative))
    } else {
        let (digits, exponent) = shortest_digits(value.abs());
        Ok(exponential_from_digits(&digits, exponent, negative))
    }
}

pub fn to_precision(value: f64, precision: Option<f64>) -> Result<String, NumberFormatError> {
    let Some(precision) = precision else {
        return Ok(bamts_bytecode::format_number(value));
    };
    if let Some(text) = non_finite(value) {
        return Ok(text);
    }
    let precision = checked_precision(precision)?;
    let negative = value < 0.0;
    let (digits, exponent) = if value == 0.0 {
        ("0".repeat(precision as usize), 0)
    } else {
        rounded_significand(value.abs(), precision)
    };
    if exponent < -6 || exponent >= precision as i32 {
        return Ok(exponential_from_digits(&digits, exponent, negative));
    }

    let mut output = String::new();
    if negative {
        output.push('-');
    }
    if exponent >= 0 {
        let integer_digits = exponent as usize + 1;
        if integer_digits >= digits.len() {
            output.push_str(&digits);
            output.extend(std::iter::repeat_n('0', integer_digits - digits.len()));
        } else {
            output.push_str(&digits[..integer_digits]);
            output.push('.');
            output.push_str(&digits[integer_digits..]);
        }
    } else {
        output.push_str("0.");
        output.extend(std::iter::repeat_n(
            '0',
            exponent.unsigned_abs() as usize - 1,
        ));
        output.push_str(&digits);
    }
    Ok(output)
}

fn next_up(value: f64) -> f64 {
    debug_assert!(value.is_finite() && value >= 0.0);
    if value == 0.0 {
        f64::from_bits(1)
    } else {
        f64::from_bits(value.to_bits() + 1)
    }
}

fn increment_radix_digits(integer: &mut Big, fraction: &mut [u32], radix: u32) {
    for digit in fraction.iter_mut().rev() {
        *digit += 1;
        if *digit < radix {
            return;
        }
        *digit = 0;
    }
    integer.add_small(1);
}

pub fn to_string_radix(value: f64, radix: f64) -> Result<String, NumberFormatError> {
    if !radix.is_finite() || radix.fract() != 0.0 || !(2.0..=36.0).contains(&radix) {
        return Err(NumberFormatError::Radix);
    }
    let radix = radix as u32;
    if radix == 10 {
        return Ok(bamts_bytecode::format_number(value));
    }
    if let Some(text) = non_finite(value) {
        return Ok(text);
    }
    if value == 0.0 {
        return Ok("0".to_owned());
    }
    let negative = value < 0.0;
    let magnitude = value.abs();
    let mut integer = integer_magnitude(magnitude);
    let mut fraction = magnitude - magnitude.trunc();
    let mut delta = ((next_up(magnitude) - magnitude) / 2.0).max(f64::from_bits(1));
    let mut fraction_digits = Vec::new();
    while fraction >= delta {
        fraction *= f64::from(radix);
        delta *= f64::from(radix);
        let digit = fraction.floor();
        fraction -= digit;
        fraction_digits.push(digit as u32);
    }
    if fraction > 0.5
        || (fraction == 0.5 && fraction_digits.last().is_some_and(|digit| digit % 2 != 0))
    {
        increment_radix_digits(&mut integer, &mut fraction_digits, radix);
    }
    while fraction_digits.last() == Some(&0) {
        fraction_digits.pop();
    }

    let mut output = String::new();
    if negative {
        output.push('-');
    }
    output.push_str(&integer.to_radix_string(radix));
    if !fraction_digits.is_empty() {
        output.push('.');
        output.extend(
            fraction_digits
                .into_iter()
                .map(|digit| char::from(DIGITS[digit as usize])),
        );
    }
    Ok(output)
}

fn is_js_whitespace(character: char) -> bool {
    matches!(
        character,
        '\u{0009}'..='\u{000d}'
            | '\u{0020}'
            | '\u{00a0}'
            | '\u{1680}'
            | '\u{2000}'..='\u{200a}'
            | '\u{2028}'
            | '\u{2029}'
            | '\u{202f}'
            | '\u{205f}'
            | '\u{3000}'
            | '\u{feff}'
    )
}

fn digit_value(character: char) -> Option<u32> {
    match character {
        '0'..='9' => Some(u32::from(character) - u32::from('0')),
        'a'..='z' => Some(u32::from(character) - u32::from('a') + 10),
        'A'..='Z' => Some(u32::from(character) - u32::from('A') + 10),
        _ => None,
    }
}

/// The round-to-nearest-even boundary between the maximum finite value and infinity.
fn overflow_threshold() -> Big {
    let mut threshold = Big::one();
    threshold.shl_bits(1_024);
    let mut half_ulp = Big::one();
    half_ulp.shl_bits(970);
    threshold.sub_assign(&half_ulp);
    threshold
}

#[must_use]
pub fn parse_int(text: &str, mut radix: i32) -> f64 {
    let text = text.trim_start_matches(is_js_whitespace);
    let (negative, text) = if let Some(rest) = text.strip_prefix('-') {
        (true, rest)
    } else {
        (false, text.strip_prefix('+').unwrap_or(text))
    };
    let strip_prefix = radix == 0 || radix == 16;
    if radix == 0 {
        radix = 10;
    }
    if !(2..=36).contains(&radix) {
        return f64::NAN;
    }
    let text = if strip_prefix {
        text.strip_prefix("0x")
            .or_else(|| text.strip_prefix("0X"))
            .map_or(text, |rest| {
                radix = 16;
                rest
            })
    } else {
        text
    };

    let radix = radix as u32;
    let mut value = Big::zero();
    let overflow_threshold = overflow_threshold();
    let mut found = false;
    for character in text.chars() {
        let Some(digit) = digit_value(character).filter(|digit| *digit < radix) else {
            break;
        };
        found = true;
        value.mul_small(radix);
        value.add_small(digit);
        if value.cmp(&overflow_threshold) != Ordering::Less {
            return if negative {
                f64::NEG_INFINITY
            } else {
                f64::INFINITY
            };
        }
    }
    if !found {
        return f64::NAN;
    }
    let magnitude = value
        .to_decimal_string()
        .parse::<f64>()
        .unwrap_or(f64::INFINITY);
    if negative { -magnitude } else { magnitude }
}

/// `StringToNumber`. Only a decimal literal takes a sign, and this grammar has no
/// numeric separators.
#[must_use]
pub(crate) fn string_to_number(text: &str) -> f64 {
    let trimmed = text.trim_matches(is_js_whitespace);
    if trimmed.is_empty() {
        return 0.0;
    }
    for (prefixes, radix) in [(["0x", "0X"], 16), (["0o", "0O"], 8), (["0b", "0B"], 2)] {
        let Some(digits) = prefixes
            .iter()
            .find_map(|prefix| trimmed.strip_prefix(prefix))
        else {
            continue;
        };
        let valid = !digits.is_empty()
            && digits
                .chars()
                .all(|digit| digit_value(digit).is_some_and(|value| value < radix as u32));
        return if valid {
            parse_int(digits, radix)
        } else {
            f64::NAN
        };
    }
    let unsigned = trimmed.strip_prefix(['+', '-']).unwrap_or(trimmed);
    if unsigned == "Infinity" {
        return if trimmed.starts_with('-') {
            f64::NEG_INFINITY
        } else {
            f64::INFINITY
        };
    }
    // Rust's own grammar also takes `inf`, `infinity` and `nan` in any case.
    if unsigned
        .bytes()
        .all(|byte| byte.is_ascii_digit() || matches!(byte, b'.' | b'e' | b'E' | b'+' | b'-'))
    {
        trimmed.parse().unwrap_or(f64::NAN)
    } else {
        f64::NAN
    }
}

fn decimal_prefix_len(text: &str) -> usize {
    if text.starts_with("Infinity") {
        return "Infinity".len();
    }
    let bytes = text.as_bytes();
    let mut cursor = 0;
    let integer_start = cursor;
    while bytes.get(cursor).is_some_and(u8::is_ascii_digit) {
        cursor += 1;
    }
    let mut has_digit = cursor > integer_start;
    if bytes.get(cursor) == Some(&b'.') {
        cursor += 1;
        let fraction_start = cursor;
        while bytes.get(cursor).is_some_and(u8::is_ascii_digit) {
            cursor += 1;
        }
        has_digit |= cursor > fraction_start;
    }
    if !has_digit {
        return 0;
    }
    let mantissa_end = cursor;
    if matches!(bytes.get(cursor), Some(b'e' | b'E')) {
        cursor += 1;
        if matches!(bytes.get(cursor), Some(b'+' | b'-')) {
            cursor += 1;
        }
        let exponent_start = cursor;
        while bytes.get(cursor).is_some_and(u8::is_ascii_digit) {
            cursor += 1;
        }
        if cursor == exponent_start {
            return mantissa_end;
        }
    }
    cursor
}

#[must_use]
pub fn parse_float(text: &str) -> f64 {
    let text = text.trim_start_matches(is_js_whitespace);
    let (negative, unsigned) = if let Some(rest) = text.strip_prefix('-') {
        (true, rest)
    } else {
        (false, text.strip_prefix('+').unwrap_or(text))
    };
    let length = decimal_prefix_len(unsigned);
    if length == 0 {
        return f64::NAN;
    }
    if &unsigned[..length] == "Infinity" {
        return if negative {
            f64::NEG_INFINITY
        } else {
            f64::INFINITY
        };
    }
    let magnitude = unsigned[..length].parse::<f64>().unwrap_or(f64::INFINITY);
    if negative { -magnitude } else { magnitude }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_rounds_exact_binary_value_ties_up() {
        assert_eq!(to_fixed(2.5, 0.0), Ok("3".to_owned()));
        assert_eq!(to_fixed(-2.5, 0.0), Ok("-3".to_owned()));
        assert_eq!(to_fixed(1.5, 0.0), Ok("2".to_owned()));
        assert_eq!(to_fixed(0.5, 0.0), Ok("1".to_owned()));
        assert_eq!(to_fixed(1.005, 2.0), Ok("1.00".to_owned()));
        assert_eq!(to_fixed(1.45, 1.0), Ok("1.4".to_owned()));
        assert_eq!(to_fixed(8.575, 2.0), Ok("8.57".to_owned()));
        assert_eq!(to_fixed(0.999, 2.0), Ok("1.00".to_owned()));
        assert_eq!(to_fixed(9.999, 2.0), Ok("10.00".to_owned()));
        assert_eq!(to_exponential(9.996, Some(2.0)), Ok("1.00e+1".to_owned()));
        assert_eq!(to_precision(9.996, Some(3.0)), Ok("10.0".to_owned()));
    }

    #[test]
    fn decimal_notation_obeys_ecmascript_thresholds() {
        assert_eq!(bamts_bytecode::format_number(1e21), "1e+21");
        assert_eq!(bamts_bytecode::format_number(1e20), "100000000000000000000");
        assert_eq!(
            bamts_bytecode::format_number(9.999e20),
            "999900000000000000000"
        );
        assert_eq!(bamts_bytecode::format_number(1e-6), "0.000001");
        assert_eq!(bamts_bytecode::format_number(1e-7), "1e-7");
        assert_eq!(bamts_bytecode::format_number(f64::from_bits(1)), "5e-324");
        assert_eq!(
            bamts_bytecode::format_number(f64::MAX),
            "1.7976931348623157e+308"
        );
        assert_eq!(
            bamts_bytecode::format_number(123_456_789_012_345_678_901.0),
            "123456789012345680000"
        );
        assert_eq!(to_fixed(1e21, 2.0), Ok("1e+21".to_owned()));
        assert_eq!(to_string_radix(1e21, 10.0), Ok("1e+21".to_owned()));
        assert_eq!(to_string_radix(1e-7, 10.0), Ok("1e-7".to_owned()));
        assert_eq!(to_string_radix(1e-6, 10.0), Ok("0.000001".to_owned()));
        assert_eq!(to_precision(1e21, None), Ok("1e+21".to_owned()));
        assert_eq!(to_precision(1e-7, None), Ok("1e-7".to_owned()));
    }

    #[test]
    fn precision_and_exponential_use_exact_rounding_and_layout() {
        assert_eq!(to_precision(0.615, Some(2.0)), Ok("0.61".to_owned()));
        assert_eq!(
            to_precision(0.000_001, Some(1.0)),
            Ok("0.000001".to_owned())
        );
        assert_eq!(to_precision(1e-7, Some(1.0)), Ok("1e-7".to_owned()));
        assert_eq!(to_precision(123.456, Some(2.0)), Ok("1.2e+2".to_owned()));
        assert_eq!(to_precision(123.0, Some(5.0)), Ok("123.00".to_owned()));
        assert_eq!(to_exponential(2.5, Some(0.0)), Ok("3e+0".to_owned()));
        assert_eq!(to_exponential(123.456, Some(2.0)), Ok("1.23e+2".to_owned()));
        assert_eq!(to_exponential(77.0, None), Ok("7.7e+1".to_owned()));
    }

    /// `div_rem` sets quotient bits from the top down, so a quotient of 2^32 or
    /// more is only right if setting a low bit keeps the limbs above it. Losing
    /// them made `rounded_significand` oscillate between exponents forever.
    #[test]
    fn precision_past_one_limb_of_quotient_terminates_with_exact_digits() {
        let cases = [
            (1.5, 16.0, "1.500000000000000"),
            (1.1, 16.0, "1.100000000000000"),
            (123.456, 21.0, "123.456000000000003070"),
            (0.5, 16.0, "0.5000000000000000"),
            (100.0, 16.0, "100.0000000000000"),
        ];
        for (value, precision, expected) in cases {
            assert_eq!(
                to_precision(value, Some(precision)),
                Ok(expected.to_owned())
            );
        }
        assert_eq!(
            to_fixed(0.1, 25.0),
            Ok("0.1000000000000000055511151".to_owned())
        );
    }

    #[test]
    fn radix_formatting_covers_every_accepted_radix() {
        for radix in 2..=36 {
            for value in [255.0, -255.0, 1e21, 9_007_199_254_740_994.0] {
                let text = to_string_radix(value, f64::from(radix)).unwrap();
                if radix != 10 || value.abs() < 1e21 {
                    assert_eq!(parse_int(&text, radix), value, "radix {radix}: {text}");
                }
            }
        }
        assert_eq!(to_string_radix(0.5, 2.0), Ok("0.1".to_owned()));
        assert_eq!(
            to_string_radix(0.1, 2.0),
            Ok("0.0001100110011001100110011001100110011001100110011001101".to_owned())
        );
        let minimum_binary = to_string_radix(f64::from_bits(1), 2.0).unwrap();
        assert_eq!(minimum_binary.len(), 1_076);
        assert!(minimum_binary.starts_with("0."));
        assert!(minimum_binary.ends_with('1'));
        assert_eq!(to_string_radix(255.0, 16.0), Ok("ff".to_owned()));
        assert_eq!(to_string_radix(1e21, 36.0), Ok("5v1j4f4ds79m9s".to_owned()));
        assert_eq!(
            to_string_radix(9_007_199_254_740_994.0, 36.0),
            Ok("2gosa7pa2gy".to_owned())
        );
        assert_eq!(
            to_string_radix(12.0, 10.0),
            Ok(bamts_bytecode::format_number(12.0))
        );
    }

    #[test]
    fn negative_zero_is_suppressed_by_number_formatting_but_preserved_by_parsing() {
        assert_eq!(bamts_bytecode::format_number(-0.0), "0");
        assert_eq!(to_string_radix(-0.0, 10.0), Ok("0".to_owned()));
        assert_eq!(to_string_radix(-0.0, 2.0), Ok("0".to_owned()));
        assert_eq!(to_fixed(-0.0, 2.0), Ok("0.00".to_owned()));
        assert_eq!(to_exponential(-0.0, Some(2.0)), Ok("0.00e+0".to_owned()));
        assert_eq!(to_precision(-0.0, Some(3.0)), Ok("0.00".to_owned()));
        assert!(parse_float("-0").is_sign_negative());
        assert!(parse_int("-0", 10).is_sign_negative());
    }

    #[test]
    fn range_checks_and_non_finite_order_match_number_methods() {
        for invalid in [-1.0, 101.0, f64::INFINITY, f64::NEG_INFINITY] {
            assert_eq!(
                to_fixed(1.0, invalid),
                Err(NumberFormatError::FractionDigits)
            );
        }
        assert_eq!(
            to_fixed(f64::NAN, 101.0),
            Err(NumberFormatError::FractionDigits)
        );
        assert_eq!(to_exponential(f64::NAN, Some(101.0)), Ok("NaN".to_owned()));
        assert_eq!(
            to_precision(f64::INFINITY, Some(0.0)),
            Ok("Infinity".to_owned())
        );
        assert_eq!(
            to_precision(1.0, Some(0.0)),
            Err(NumberFormatError::Precision)
        );
        assert_eq!(
            to_precision(1.0, Some(101.0)),
            Err(NumberFormatError::Precision)
        );
        assert!(to_fixed(1.0, 100.0).is_ok());
        for invalid in [1.0, 37.0, f64::NAN, f64::INFINITY] {
            assert_eq!(to_string_radix(1.0, invalid), Err(NumberFormatError::Radix));
        }
    }

    #[test]
    fn string_to_number_follows_the_string_numeric_literal_grammar() {
        for (text, expected) in [
            ("", 0.0),
            ("\u{feff} \u{2029}12\t", 12.0),
            ("0x10", 16.0),
            ("0XfF", 255.0),
            ("0o17", 15.0),
            ("0b101", 5.0),
            ("1e3", 1000.0),
            (".5", 0.5),
            ("5.", 5.0),
            ("Infinity", f64::INFINITY),
            ("+Infinity", f64::INFINITY),
            ("-Infinity", f64::NEG_INFINITY),
            // Rounding after each digit loses the low bits and gives 2^57.
            ("0x200000000000011", 144_115_188_075_855_904.0),
        ] {
            assert_eq!(string_to_number(text), expected, "{text:?}");
        }
        assert!(string_to_number("-0").is_sign_negative());
        for text in [
            "-0x10", "+0b1", "0x", "0xg", "0b2", "0o8", "1_000", "infinity", "inf", "nan", "NaN",
            "INFINITY", "e5", ".", "+", "\u{85}1",
        ] {
            assert!(string_to_number(text).is_nan(), "{text:?}");
        }
    }

    #[test]
    fn parse_int_implements_prefix_radix_whitespace_and_overflow_rules() {
        assert_eq!(parse_int("0x10", 0), 16.0);
        assert_eq!(parse_int("0x10", 10), 0.0);
        assert_eq!(parse_int("10", 16), 16.0);
        assert_eq!(parse_int("\u{feff}\u{2028}\u{3000}-42xyz", 10), -42.0);
        assert!(parse_int("10", 1).is_nan());
        assert!(parse_int("10", 37).is_nan());
        assert!(parse_int("+", 10).is_nan());
        assert_eq!(
            parse_int("900719925474099267", 10),
            900_719_925_474_099_300.0
        );
        let threshold = overflow_threshold();
        let mut below_threshold = threshold.clone();
        below_threshold.sub_assign(&Big::one());
        assert_eq!(
            parse_int(&below_threshold.to_decimal_string(), 10),
            f64::MAX
        );
        let threshold = threshold.to_decimal_string();
        assert_eq!(parse_int(&threshold, 10), f64::INFINITY);
        assert_eq!(parse_int(&format!("-{threshold}"), 10), f64::NEG_INFINITY);
        assert!(parse_int(&"9".repeat(1_000_000), 10).is_infinite());
    }

    #[test]
    fn parse_float_accepts_only_the_longest_decimal_literal_prefix() {
        assert_eq!(parse_float("\u{feff}\u{3000}42abc"), 42.0);
        assert_eq!(parse_float("-.5rest"), -0.5);
        assert_eq!(parse_float("1e"), 1.0);
        assert_eq!(parse_float("1e+"), 1.0);
        assert_eq!(parse_float("0x10"), 0.0);
        assert_eq!(parse_float("Infinity!"), f64::INFINITY);
        assert_eq!(parse_float("-Infinity"), f64::NEG_INFINITY);
        assert!(parse_float("").is_nan());
        assert!(parse_float(".").is_nan());
        assert!(parse_float("+").is_nan());
        assert!(parse_float(&"9".repeat(400)).is_infinite());
    }
}
