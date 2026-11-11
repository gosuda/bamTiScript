use bamts_bytecode::{EcmaString, EcmaStringBuilder};

/// Cooks one scanned numeric lexeme into its ECMAScript number value.
pub(crate) fn number_value(lexeme: &str) -> Option<f64> {
    if let Some(rest) = lexeme
        .strip_prefix("0x")
        .or_else(|| lexeme.strip_prefix("0X"))
    {
        return radix_value(rest, 16);
    }
    if let Some(rest) = lexeme
        .strip_prefix("0o")
        .or_else(|| lexeme.strip_prefix("0O"))
    {
        return radix_value(rest, 8);
    }
    if let Some(rest) = lexeme
        .strip_prefix("0b")
        .or_else(|| lexeme.strip_prefix("0B"))
    {
        return radix_value(rest, 2);
    }
    if lexeme.len() > 1 && lexeme.as_bytes()[0] == b'0' {
        let rest = &lexeme[1..];
        let int_end = rest.find(['.', 'e', 'E']).unwrap_or(rest.len());
        let int_part = &rest[..int_end];
        let mut has_octal_digit = false;
        let mut all_octal = true;
        for ch in int_part.chars() {
            if ch == '_' {
                continue;
            }
            if ('0'..='7').contains(&ch) {
                has_octal_digit = true;
                continue;
            }
            all_octal = false;
            break;
        }
        if has_octal_digit && all_octal {
            if int_end != rest.len() {
                return None;
            }
            if let Some(value) = radix_value(rest, 8) {
                return Some(value);
            }
        }
    }
    if !lexeme.contains('_') {
        return lexeme.parse().ok();
    }
    lexeme
        .chars()
        .filter(|character| *character != '_')
        .collect::<String>()
        .parse()
        .ok()
}
pub(crate) const MAX_BIGINT_CONVERSION_LIMB_OPS: usize = 1 << 24;
/// Failure while canonicalizing BigInt source text.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum BigIntTextError {
    Invalid,
    Bytes,
    Work,
}
/// Canonicalizes a BigInt lexeme to bounded decimal text.
pub(crate) fn canonical_bigint_text(
    lexeme: &str,
    max_bytes: usize,
    max_limb_ops: usize,
) -> Result<String, BigIntTextError> {
    const LIMB_BASE: u64 = 1_000_000_000;
    const DECIMAL_LIMB_DIGITS: usize = 9;
    const LOG10_2_UPPER_NUMERATOR: usize = 30_103;
    const LOG10_2_UPPER_DENOMINATOR: usize = 100_000;
    let literal = lexeme.strip_suffix('n').ok_or(BigIntTextError::Invalid)?;
    let (digits, radix) = literal
        .strip_prefix("0x")
        .or_else(|| literal.strip_prefix("0X"))
        .map(|digits| (digits, 16))
        .or_else(|| {
            literal
                .strip_prefix("0o")
                .or_else(|| literal.strip_prefix("0O"))
                .map(|digits| (digits, 8))
        })
        .or_else(|| {
            literal
                .strip_prefix("0b")
                .or_else(|| literal.strip_prefix("0B"))
                .map(|digits| (digits, 2))
        })
        .unwrap_or((literal, 10));
    if digits.is_empty() {
        return Err(BigIntTextError::Invalid);
    }
    let mut previous_was_digit = false;
    let mut significant_digits = 0_usize;
    let mut first_significant_bits = 0_usize;
    for character in digits.chars() {
        if character == '_' {
            if !previous_was_digit {
                return Err(BigIntTextError::Invalid);
            }
            previous_was_digit = false;
            continue;
        }
        let digit = character.to_digit(radix).ok_or(BigIntTextError::Invalid)?;
        previous_was_digit = true;
        if first_significant_bits == 0 {
            if digit == 0 {
                continue;
            }
            first_significant_bits = (u32::BITS - digit.leading_zeros()) as usize;
        }
        significant_digits = significant_digits
            .checked_add(1)
            .ok_or(BigIntTextError::Work)?;
    }
    if !previous_was_digit {
        return Err(BigIntTextError::Invalid);
    }
    if radix == 10 {
        let output_bytes = significant_digits.max(1);
        if output_bytes > max_bytes {
            return Err(BigIntTextError::Bytes);
        }
        let mut output = String::with_capacity(output_bytes);
        let mut significant = false;
        for character in digits.chars().filter(|character| *character != '_') {
            if character != '0' || significant {
                significant = true;
                output.push(character);
            }
        }
        if output.is_empty() {
            output.push('0');
        }
        return Ok(output);
    }
    let bit_length = significant_digits
        .saturating_sub(1)
        .checked_mul(radix.trailing_zeros() as usize)
        .and_then(|remaining| remaining.checked_add(first_significant_bits))
        .ok_or(BigIntTextError::Work)?;
    let max_decimal_bytes = if bit_length == 0 {
        1
    } else {
        bit_length
            .checked_mul(LOG10_2_UPPER_NUMERATOR)
            .and_then(|value| value.checked_add(LOG10_2_UPPER_DENOMINATOR - 1))
            .map(|value| value / LOG10_2_UPPER_DENOMINATOR)
            .ok_or(BigIntTextError::Work)?
    };
    if max_decimal_bytes > max_bytes {
        return Err(BigIntTextError::Bytes);
    }
    let max_limb_count = max_decimal_bytes.div_ceil(DECIMAL_LIMB_DIGITS);
    let worst_case_limb_ops = significant_digits
        .checked_mul(max_limb_count)
        .ok_or(BigIntTextError::Work)?;
    if worst_case_limb_ops > max_limb_ops {
        return Err(BigIntTextError::Work);
    }
    let mut limbs = vec![0_u32];
    let mut significant = false;
    for character in digits.chars().filter(|character| *character != '_') {
        let digit = u64::from(
            character
                .to_digit(radix)
                .expect("validated BigInt digit remains valid"),
        );
        if digit == 0 && !significant {
            continue;
        }
        significant = true;
        let mut carry = digit;
        for limb in &mut limbs {
            let value = u64::from(*limb) * u64::from(radix) + carry;
            *limb = (value % LIMB_BASE) as u32;
            carry = value / LIMB_BASE;
        }
        if carry != 0 {
            limbs.push(carry as u32);
        }
    }
    let mut output = limbs.pop().ok_or(BigIntTextError::Invalid)?.to_string();
    for limb in limbs.iter().rev() {
        use std::fmt::Write as _;
        write!(output, "{limb:09}").expect("writing to String cannot fail");
    }
    if output.len() > max_bytes {
        return Err(BigIntTextError::Bytes);
    }
    Ok(output)
}

/// Cooks one quoted JavaScript string literal.
pub(crate) fn string_value(lexeme: &str) -> Option<EcmaString> {
    let quote = lexeme.as_bytes().first().copied()?;
    if !matches!(quote, b'\'' | b'"') || lexeme.as_bytes().last().copied() != Some(quote) {
        return None;
    }
    let interior = lexeme.get(1..lexeme.len().checked_sub(1)?)?;
    Some(cook(interior, true))
}

/// Cooks JavaScript escape sequences in a template interior.
pub(crate) fn cook_escapes(input: &str) -> EcmaString {
    cook(input, false)
}

/// Whether a template interior has a cooked value. Every escape must be valid, and a
/// tag reads `undefined` for an interior that fails.
pub(crate) fn has_cooked_value(input: &str) -> bool {
    let mut chars = input.chars().peekable();
    while let Some(character) = chars.next() {
        if character != '\\' {
            continue;
        }
        let valid = match chars.next() {
            Some('1'..='9') => false,
            Some('0') => !chars.peek().is_some_and(char::is_ascii_digit),
            Some('x') => has_hex_digits(&mut chars, 2),
            Some('u') if chars.peek() == Some(&'{') => has_braced_code_point(&mut chars),
            Some('u') => has_hex_digits(&mut chars, 4),
            _ => true,
        };
        if !valid {
            return false;
        }
    }
    true
}

fn has_hex_digits(chars: &mut std::iter::Peekable<std::str::Chars<'_>>, count: usize) -> bool {
    (0..count).all(|_| chars.next().is_some_and(|digit| digit.is_ascii_hexdigit()))
}

/// Reads the `{` that the cursor is on, then the code point and its `}`.
fn has_braced_code_point(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> bool {
    chars.next();
    let mut value = 0_u32;
    let mut any = false;
    for character in chars.by_ref() {
        if character == '}' {
            return any && value <= 0x0010_FFFF;
        }
        let Some(digit) = character.to_digit(16) else {
            return false;
        };
        value = value.saturating_mul(16).saturating_add(digit);
        any = true;
    }
    false
}

/// Cooks the value of a legacy octal escape, whose first digit is `first`. It reads
/// up to three digits, and stops at two when a third would pass 0o377.
fn cook_legacy_octal(first: u32, chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> u16 {
    let most_digits = if first <= 3 { 3 } else { 2 };
    let mut value = first;
    for _ in 1..most_digits {
        let Some(digit) = chars.peek().and_then(|next| next.to_digit(8)) else {
            break;
        };
        chars.next();
        value = value * 8 + digit;
    }
    u16::try_from(value).expect("three octal digits fit a code unit")
}

/// `legacy` reads the octal escapes of a string literal, which a template refuses.
fn cook(input: &str, legacy: bool) -> EcmaString {
    if !input.contains('\\') {
        return EcmaString::encode(input);
    }
    let mut output = EcmaStringBuilder::with_capacity(input.encode_utf16().count());
    let mut chars = input.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            output
                .push_code_point(u32::from(ch))
                .expect("a Rust char is a Unicode scalar");
            continue;
        }
        let Some(escape) = chars.next() else {
            output.push_unit(b'\\'.into());
            break;
        };
        match escape {
            'n' => output.push_unit(b'\n'.into()),
            't' => output.push_unit(b'\t'.into()),
            'r' => output.push_unit(b'\r'.into()),
            'b' => output.push_unit(0x0008),
            'f' => output.push_unit(0x000C),
            'v' => output.push_unit(0x000B),
            '0' if !chars.peek().is_some_and(|c| c.is_ascii_digit()) => output.push_unit(0),
            '0'..='7' if legacy => {
                let first = escape.to_digit(8).expect("an octal digit");
                output.push_unit(cook_legacy_octal(first, &mut chars));
            }
            '\n' => {}
            '\r' => {
                if chars.peek() == Some(&'\n') {
                    chars.next();
                }
            }
            // U+2028 LINE SEPARATOR and U+2029 PARAGRAPH SEPARATOR are LineTerminator
            // characters per spec; after a backslash they act as line continuations
            // (the character is consumed and emits nothing), like \n and \r above.
            '\u{2028}' => {}
            '\u{2029}' => {}
            'x' => {
                let hi = chars.next();
                let lo = chars.next();
                if let (Some(hi), Some(lo)) = (hi, lo)
                    && let (Some(h), Some(l)) = (hi.to_digit(16), lo.to_digit(16))
                {
                    output.push_unit((h * 16 + l) as u16);
                } else {
                    output.push_unit(b'x'.into());
                }
            }
            'u' => cook_unicode_escape(&mut chars, &mut output),
            other => output
                .push_code_point(u32::from(other))
                .expect("a Rust char is a Unicode scalar"),
        }
    }
    output.finish()
}

fn radix_value(digits: &str, radix: u32) -> Option<f64> {
    let bits_per_digit = radix.trailing_zeros();
    let mut any = false;
    let mut significant = false;
    let mut bit_length = 0_usize;
    // Retain the 53-bit binary64 significand plus its guard bit. Every later
    // one bit contributes only to the sticky bit, so the final rounding is
    // performed exactly once regardless of the source integer's length.
    let mut prefix = 0_u64;
    let mut sticky = false;

    for character in digits.chars().filter(|character| *character != '_') {
        let digit = character.to_digit(radix)?;
        any = true;
        for bit_index in (0..bits_per_digit).rev() {
            let bit = (digit >> bit_index) & 1;
            if !significant {
                if bit == 0 {
                    continue;
                }
                significant = true;
            }
            bit_length = bit_length.saturating_add(1);
            if bit_length <= 54 {
                prefix = (prefix << 1) | u64::from(bit);
            } else {
                sticky |= bit != 0;
            }
        }
    }

    if !any {
        return None;
    }
    if !significant {
        return Some(0.0);
    }

    let mut exponent = bit_length - 1;
    let mut significand = if bit_length <= 53 {
        prefix << (53 - bit_length)
    } else {
        let guard = prefix & 1 != 0;
        let mut rounded = prefix >> 1;
        if guard && (sticky || rounded & 1 != 0) {
            rounded += 1;
        }
        if rounded == 1 << 53 {
            exponent = exponent.saturating_add(1);
            rounded >>= 1;
        }
        rounded
    };

    if exponent > 1023 {
        return Some(f64::INFINITY);
    }
    debug_assert!((1 << 52..1 << 53).contains(&significand));
    significand &= (1 << 52) - 1;
    Some(f64::from_bits(
        ((exponent as u64 + 1023) << 52) | significand,
    ))
}

fn cook_unicode_escape(
    chars: &mut std::iter::Peekable<std::str::Chars<'_>>,
    output: &mut EcmaStringBuilder,
) {
    if chars.peek() == Some(&'{') {
        chars.next();
        let mut value = 0_u32;
        let mut any = false;
        while let Some(&character) = chars.peek() {
            if character == '}' {
                chars.next();
                break;
            }
            let Some(digit) = character.to_digit(16) else {
                break;
            };
            value = value.saturating_mul(16).saturating_add(digit);
            any = true;
            chars.next();
        }
        if any && value <= 0x10_FFFF {
            output
                .push_code_point(value)
                .expect("a bounded code point is representable");
        }
        return;
    }

    let mut value = 0_u16;
    let mut count = 0;
    while count < 4 {
        let Some(&character) = chars.peek() else {
            break;
        };
        let Some(digit) = character.to_digit(16) else {
            break;
        };
        value = value * 16 + digit as u16;
        chars.next();
        count += 1;
    }
    if count == 4 {
        output.push_unit(value);
    } else {
        output.push_unit(b'u'.into());
    }
}

#[cfg(test)]
mod tests {
    use super::{cook_escapes, has_cooked_value, number_value, string_value};

    #[test]
    fn cooks_numbers_and_utf16_strings() {
        assert_eq!(number_value("0x10"), Some(16.0));
        assert_eq!(number_value("1_024"), Some(1024.0));
        assert_eq!(
            string_value("'a\\n'").unwrap().as_units(),
            [b'a'.into(), b'\n'.into()]
        );
        assert_eq!(cook_escapes("\\uD800").as_units(), [0xD800]);
        assert_eq!(cook_escapes("\\u{1F603}").as_units(), [0xD83D, 0xDE03]);
    }

    #[test]
    fn non_decimal_numbers_round_once_to_binary64() {
        assert_eq!(
            number_value("0x20000000000001"),
            Some(9_007_199_254_740_992.0)
        );
        assert_eq!(
            number_value("0x20000000000003"),
            Some(9_007_199_254_740_996.0)
        );
        assert_eq!(
            number_value("0b100000000000000000000000000000000000000000000000000011"),
            Some(9_007_199_254_740_996.0)
        );
        assert_eq!(
            number_value(&format!("0x1{}", "0".repeat(256))),
            Some(f64::INFINITY)
        );
    }

    #[test]
    fn non_decimal_radix_bit_patterns() {
        // Leading zeros and separators are ignored without changing the value.
        assert_eq!(number_value("0x0000000000000001"), Some(1.0));
        assert_eq!(number_value("0x0000_0000_0000_0001"), Some(1.0));
        assert_eq!(number_value("0o000000000000000000001"), Some(1.0));
        assert_eq!(
            number_value("0b00000000000000000000000000000000000000000000000000001"),
            Some(1.0)
        );
        assert_eq!(number_value("0x0"), Some(0.0));
        assert_eq!(number_value("0x0_0"), Some(0.0));

        // 53-bit integers are represented exactly even when the leading 1 is
        // not the most-significant bit of its source digit.
        assert_eq!(
            number_value("0x1fffffffffffff"),
            Some(9_007_199_254_740_991.0)
        );
        assert_eq!(
            number_value("0x20000000000000"),
            Some(9_007_199_254_740_992.0)
        );

        // >53-bit halfway cases round to nearest, ties to even.
        assert_eq!(
            number_value("0x20000000000001"),
            Some(9_007_199_254_740_992.0)
        );
        assert_eq!(
            number_value("0x20000000000003"),
            Some(9_007_199_254_740_996.0)
        );
        assert_eq!(
            number_value("0x20000000000005"),
            Some(9_007_199_254_740_996.0)
        );

        // Rounding carry propagates to the exponent when all retained bits are 1.
        assert_eq!(
            number_value("0x3fffffffffffff"),
            Some(18_014_398_509_481_984.0)
        );

        // 2^54 - 2 is exactly representable.
        assert_eq!(
            number_value("0x3ffffffffffffe"),
            Some(18_014_398_509_481_982.0)
        );

        // A large but still-finite integer rounds up to the next power of two.
        assert_eq!(
            number_value("0x3fffffffffffffff"),
            Some(4_611_686_018_427_387_904.0)
        );

        // Arbitrary-length inputs overflow to Infinity without fixed-width
        // integer conversion.
        assert_eq!(
            number_value(&format!("0x1{}", "0".repeat(300))),
            Some(f64::INFINITY)
        );
        assert_eq!(
            number_value(&format!("0x{}", "f".repeat(300))),
            Some(f64::INFINITY)
        );
        assert_eq!(
            number_value(&format!("0b1{}", "0".repeat(1024))),
            Some(f64::INFINITY)
        );
        assert_eq!(
            number_value(&format!("0o1{}", "0".repeat(342))),
            Some(f64::INFINITY)
        );
    }

    #[test]
    fn cooks_legacy_octal_escapes_in_strings_only() {
        for (lexeme, units) in [
            (r#""\101""#, &[65][..]),
            (r#"'\101\102'"#, &[65, 66]),
            (r#""\0""#, &[0]),
            (r#""\08""#, &[0, 56]),
            (r#""\00""#, &[0]),
            (r#""\000""#, &[0]),
            (r#""\0000""#, &[0, 48]),
            (r#""\1""#, &[1]),
            (r#""\18""#, &[1, 56]),
            (r#""\78""#, &[7, 56]),
            (r#""\8""#, &[56]),
            (r#""\9""#, &[57]),
            (r#""\377""#, &[255]),
            (r#""\400""#, &[32, 48]),
            (r#""\777""#, &[63, 55]),
            (r#""\12a""#, &[10, 97]),
        ] {
            assert_eq!(string_value(lexeme).unwrap().as_units(), units, "{lexeme}");
        }
        assert_eq!(cook_escapes(r"\101"), string_value("'101'").unwrap());
    }

    #[test]
    fn a_template_interior_has_a_cooked_value_only_with_valid_escapes() {
        for interior in [
            "plain",
            r"\0",
            r"\0a",
            r"\n",
            r"\x41",
            r"A",
            r"\u{41}",
            r"\u{10FFFF}",
            r"\$",
            "a\\\nb",
        ] {
            assert!(has_cooked_value(interior), "{interior}");
        }
        for interior in [
            r"\1",
            r"\8",
            r"\01",
            r"\08",
            r"\x",
            r"\x4",
            r"\xg",
            r"\u",
            r"\u004",
            r"\u{",
            r"\u{}",
            r"\u{41",
            r"\u{g}",
            r"\u{110000}",
            r"a\n\1",
        ] {
            assert!(!has_cooked_value(interior), "{interior}");
        }
    }

    #[test]
    fn legacy_octal_integer_value_is_base_eight() {
        assert_eq!(
            number_value("070"),
            Some(56.0),
            "test262/language/literals/numeric/legacy-octal-integer.js 070 must be 56"
        );
        assert_eq!(
            number_value("077"),
            Some(63.0),
            "legacy-octal-integer.js 077 must be 63"
        );
        assert_eq!(
            number_value("08"),
            Some(8.0),
            "test262/language/literals/numeric/non-octal-decimal-integer.js 08 stays decimal"
        );
        assert_eq!(
            number_value("0708"),
            Some(708.0),
            "non-octal-decimal-integer.js 0708 stays decimal"
        );
    }
    #[test]
    fn legacy_octal_integer_literal_rejects_fraction_and_exponent() {
        assert_eq!(number_value("010.5"), None);
        assert_eq!(number_value("010e1"), None);
    }

    #[test]
    fn non_octal_decimal_integer_literal_allows_fraction_and_exponent() {
        assert_eq!(number_value("08.5"), Some(8.5));
        assert_eq!(number_value("09e1"), Some(90.0));
    }

    #[test]
    fn cooks_line_continuations() {
        assert_eq!(
            cook_escapes("a\\\u{2028}b").as_units(),
            [b'a'.into(), b'b'.into()]
        );
        assert_eq!(
            cook_escapes("a\\\u{2029}b").as_units(),
            [b'a'.into(), b'b'.into()]
        );
    }
}
