//! `Intl.NumberFormat`.

use bamts_native::{Decoded, Value};

use super::super::bigint::bigint_from_value;
use super::options::{
    Options, canonicalize_locale_list, coerce_options_to_object, digit_options,
    locale_matcher_option, matcher_name, read, string_option,
};
use super::{
    Class, allocate, arg, bound_function, chain_legacy_instance, define_field, install_class,
    instance_prototype, intl_record, is_type_sequence, new_object, part_object, range_error,
    register_hidden, string_outcome, string_value, supported_locales_outcome, type_error,
    unwrap_legacy_instance,
};
use crate::intl::locale_data::DATA;
use crate::intl::number_data::NoHostLocale;
use crate::intl::number_format::{
    IntlMathematicalValue, NumberFormat, NumberFormatError, NumberFormatErrorKind,
    NumberFormatOptions, NumberPart, RangeEnd, UseGrouping, UseGroupingOption,
};
use crate::intl::{IntlKind, IntlObject};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine};

const FORMAT: &str = "Intl.NumberFormat format";

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    builtins: &mut BuiltinTable<H>,
    namespace: Value,
) {
    register_hidden(builtins, FORMAT, 1, format_value::<H>);
    install_class(
        heap,
        builtins,
        namespace,
        &Class {
            kind: IntlKind::NumberFormat,
            name: "NumberFormat",
            tag: "Intl.NumberFormat",
            length: 0,
            constructor: constructor::<H>,
            statics: &[("supportedLocalesOf", 1, supported_locales_of::<H>)],
            getters: &[("format", "get format", format_getter::<H>)],
            methods: &[
                ("formatRange", 2, format_range::<H>),
                ("formatRangeToParts", 2, format_range_to_parts::<H>),
                ("formatToParts", 1, format_to_parts::<H>),
                ("resolvedOptions", 0, resolved_options::<H>),
            ],
        },
    );
}

pub(super) fn number_failure<H: Host>(
    machine: &mut Machine<'_, H>,
    error: NumberFormatError,
) -> EvalFailure {
    match error.kind {
        NumberFormatErrorKind::TypeError => type_error(machine, error.message),
        NumberFormatErrorKind::RangeError
        | NumberFormatErrorKind::MissingData
        | NumberFormatErrorKind::InvalidData => range_error(machine, error.message),
    }
}

/// SetNumberFormatUnitOptions, which validates each value as it is read.
fn unit_options<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    result: &mut NumberFormatOptions,
) -> Result<(), EvalFailure> {
    result.style = string_option(
        machine,
        options,
        "style",
        &["decimal", "percent", "currency", "unit"],
    )?;
    let style = result.style.clone();
    result.currency = string_option(machine, options, "currency", &[])?;
    match &result.currency {
        None if style.as_deref() == Some("currency") => {
            return Err(type_error(machine, "currency is required"));
        }
        Some(code) if code.len() != 3 || !code.bytes().all(|byte| byte.is_ascii_alphabetic()) => {
            let message = format!("{code} is not a well-formed currency code");
            return Err(range_error(machine, message));
        }
        _ => {}
    }
    result.currency_display = string_option(
        machine,
        options,
        "currencyDisplay",
        &["code", "symbol", "narrowSymbol", "name"],
    )?;
    result.currency_sign = string_option(
        machine,
        options,
        "currencySign",
        &["standard", "accounting"],
    )?;
    result.unit = string_option(machine, options, "unit", &[])?;
    match &result.unit {
        None if style.as_deref() == Some("unit") => {
            return Err(type_error(machine, "unit is required"));
        }
        Some(unit) if !crate::intl::number_format::is_well_formed_unit(unit) => {
            let message = format!("{unit} is not a well-formed unit identifier");
            return Err(range_error(machine, message));
        }
        _ => {}
    }
    result.unit_display = string_option(
        machine,
        options,
        "unitDisplay",
        &["short", "narrow", "long"],
    )?;
    Ok(())
}

/// GetBooleanOrStringNumberFormatOption for `useGrouping`.
fn use_grouping_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
) -> Result<Option<UseGroupingOption>, EvalFailure> {
    let value = read(machine, options, "useGrouping")?;
    if value == Value::UNDEFINED {
        return Ok(None);
    }
    if value == Value::boolean(true) {
        return Ok(Some(UseGroupingOption::Boolean(true)));
    }
    if !machine.to_boolean(value) {
        return Ok(Some(UseGroupingOption::Boolean(false)));
    }
    let text = machine.coerce_string_observable(value)?.to_utf8_lossy();
    if ["min2", "auto", "always", "true", "false"].contains(&text.as_str()) {
        Ok(Some(UseGroupingOption::String(text)))
    } else {
        Err(range_error(
            machine,
            format!("{text} is not a valid value for useGrouping"),
        ))
    }
}

/// The options of `new Intl.NumberFormat`, read in constructor order.
pub(super) fn read_number_format_options<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
) -> Result<NumberFormatOptions, EvalFailure> {
    let mut result = NumberFormatOptions::default();
    let matcher = locale_matcher_option(machine, options)?;
    result.locale_matcher = Some(matcher_name(matcher).to_owned());
    result.numbering_system = string_option(machine, options, "numberingSystem", &[])?;
    if let Some(name) = &result.numbering_system
        && !is_type_sequence(name)
    {
        let message = format!("{name} is not a valid numbering system");
        return Err(range_error(machine, message));
    }
    unit_options(machine, options, &mut result)?;
    result.notation = string_option(
        machine,
        options,
        "notation",
        &["standard", "scientific", "engineering", "compact"],
    )?;
    let compact = result.notation.as_deref() == Some("compact");
    let digits = digit_options(machine, options, compact)?;
    result.minimum_integer_digits = digits.minimum_integer_digits;
    result.minimum_fraction_digits = digits.minimum_fraction_digits;
    result.maximum_fraction_digits = digits.maximum_fraction_digits;
    result.minimum_significant_digits = digits.minimum_significant_digits;
    result.maximum_significant_digits = digits.maximum_significant_digits;
    result.rounding_increment = digits.rounding_increment;
    result.rounding_mode = digits.rounding_mode;
    result.rounding_priority = digits.rounding_priority;
    result.trailing_zero_display = digits.trailing_zero_display;
    result.compact_display = string_option(machine, options, "compactDisplay", &["short", "long"])?;
    result.use_grouping = use_grouping_option(machine, options)?;
    result.sign_display = string_option(
        machine,
        options,
        "signDisplay",
        &["auto", "never", "always", "exceptZero", "negative"],
    )?;
    Ok(result)
}

/// CreateNumberFormat over already canonicalized locales.
pub(super) fn create_number_format<H: Host>(
    machine: &mut Machine<'_, H>,
    requested: &[String],
    options: &NumberFormatOptions,
) -> Result<NumberFormat<'static>, EvalFailure> {
    let data: &'static crate::intl::locale_data::IntlData = &DATA;
    NumberFormat::new(requested, options, data, &NoHostLocale)
        .map_err(|error| number_failure(machine, error))
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let prototype = instance_prototype(machine, IntlKind::NumberFormat, constructing)?;
    let requested = canonicalize_locale_list(machine, arg(args, 0))?;
    let options = coerce_options_to_object(machine, arg(args, 1))?;
    let options = read_number_format_options(machine, options)?;
    let format = create_number_format(machine, &requested, &options)?;
    let instance = allocate(
        machine,
        IntlObject::NumberFormat(Box::new(format)),
        prototype,
    )?;
    chain_legacy_instance(
        machine,
        instance,
        IntlKind::NumberFormat,
        constructing,
        this,
    )
}

fn supported_locales_of<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    supported_locales_outcome(machine, args)
}

fn this_format<'a, H: Host>(
    machine: &'a Machine<'_, H>,
    this: Value,
) -> Result<Option<&'a NumberFormat<'static>>, EvalFailure> {
    Ok(match intl_record(machine, this)? {
        Some(IntlObject::NumberFormat(format)) => Some(format),
        _ => None,
    })
}

fn not_a_number_format<H: Host>(machine: &mut Machine<'_, H>) -> EvalFailure {
    type_error(machine, "receiver is not an Intl.NumberFormat")
}

fn format_getter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let format = unwrap_legacy_instance(machine, this, IntlKind::NumberFormat)?;
    if this_format(machine, format)?.is_none() {
        return Err(not_a_number_format(machine));
    }
    bound_function(machine, format, FORMAT, 1)
}

/// The value of a StringNumericLiteral as an exact number, as
/// ToIntlMathematicalValue reads it: a magnitude past the range of a Number
/// saturates. A magnitude below that range stays exact, as it does in V8, where the
/// specification reads it as zero. An exponent that nothing can hold reads as the
/// nearest Number. V8 hands decimal digits to ICU as digits, and reads any other
/// string as a Number.
fn string_range_end(text: &str) -> RangeEnd {
    let trimmed = text.trim_matches(super::is_string_whitespace);
    if trimmed.is_empty() {
        return RangeEnd::number(0.0);
    }
    let (negative, body) = match trimmed.as_bytes()[0] {
        b'-' => (true, &trimmed[1..]),
        b'+' => (false, &trimmed[1..]),
        _ => (false, trimmed),
    };
    if body == "Infinity" {
        return RangeEnd::number(if negative {
            f64::NEG_INFINITY
        } else {
            f64::INFINITY
        });
    }
    let radix = match body.get(..2) {
        Some("0x" | "0X") => 16,
        Some("0o" | "0O") => 8,
        Some("0b" | "0B") => 2,
        _ => 10,
    };
    if radix != 10 {
        let unsigned = trimmed.len() == body.len();
        return match (unsigned, radix_digits(&body[2..], radix)) {
            (true, Some(decimal)) => non_decimal_end(&decimal),
            _ => RangeEnd::number(f64::NAN),
        };
    }
    if !is_decimal_literal(body) {
        return RangeEnd::number(f64::NAN);
    }
    let approximate: f64 = body.parse().unwrap_or(f64::NAN);
    let number = if negative { -approximate } else { approximate };
    if approximate.is_infinite() {
        return RangeEnd::digits(IntlMathematicalValue::from_f64(number));
    }
    RangeEnd::digits(
        IntlMathematicalValue::from_decimal_string(trimmed)
            .unwrap_or_else(|_| IntlMathematicalValue::from_f64(number)),
    )
}

/// V8 reads a `0x`, `0o` or `0b` integer below this as a Number. It keeps a larger
/// one exact, and hands it to ICU as digits.
const NON_DECIMAL_NUMBER_LIMIT: u64 = (1 << 53) - 1;

/// A `0x`, `0o` or `0b` integer, given in decimal digits.
fn non_decimal_end(decimal: &str) -> RangeEnd {
    match IntlMathematicalValue::from_bigint(decimal) {
        Ok(value) => RangeEnd {
            value,
            as_double: decimal
                .parse::<u64>()
                .is_ok_and(|integer| integer < NON_DECIMAL_NUMBER_LIMIT),
        },
        Err(_) => RangeEnd::number(f64::NAN),
    }
}

/// Converts digits of `radix` to a decimal string, by long multiplication.
fn radix_digits(digits: &str, radix: u32) -> Option<String> {
    if digits.is_empty() {
        return None;
    }
    let mut decimal: Vec<u32> = vec![0];
    for character in digits.chars() {
        let mut carry = character.to_digit(radix)?;
        for digit in decimal.iter_mut().rev() {
            let value = *digit * radix + carry;
            *digit = value % 10;
            carry = value / 10;
        }
        while carry > 0 {
            decimal.insert(0, carry % 10);
            carry /= 10;
        }
    }
    decimal
        .iter()
        .map(|digit| char::from_digit(*digit, 10))
        .collect()
}

/// StrUnsignedDecimalLiteral without `Infinity`.
fn is_decimal_literal(text: &str) -> bool {
    let (mantissa, exponent) = match text.find(['e', 'E']) {
        Some(index) => (&text[..index], Some(&text[index + 1..])),
        None => (text, None),
    };
    let (whole, fraction) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let digits = |part: &str| part.bytes().all(|byte| byte.is_ascii_digit());
    if !digits(whole) || !digits(fraction) || (whole.is_empty() && fraction.is_empty()) {
        return false;
    }
    exponent.is_none_or(|exponent| {
        let exponent = exponent.strip_prefix(['+', '-']).unwrap_or(exponent);
        !exponent.is_empty() && digits(exponent)
    })
}

/// ToIntlMathematicalValue.
pub(super) fn to_mathematical_value<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<IntlMathematicalValue, EvalFailure> {
    to_range_end(machine, value).map(|end| end.value)
}

/// ToIntlMathematicalValue, with the form in which V8 hands the value to ICU.
fn to_range_end<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<RangeEnd, EvalFailure> {
    let primitive = machine.coerce_primitive_observable(value, false)?;
    if let Some(bigint) = bigint_from_value(machine, primitive)? {
        return IntlMathematicalValue::from_bigint(&bigint.to_string_radix(10))
            .map(RangeEnd::digits)
            .map_err(|error| number_failure(machine, error));
    }
    if let Some(text) = machine.string_value(primitive) {
        return Ok(string_range_end(&text.to_utf8_lossy()));
    }
    let number = machine.coerce_number_observable(primitive)?;
    let number = match number.decode() {
        Some(Decoded::Int32(number)) => f64::from(number as i32),
        Some(Decoded::Number(number)) => number,
        _ => f64::NAN,
    };
    Ok(RangeEnd::number(number))
}

/// The function `format` hands out, bound to its NumberFormat.
fn format_value<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = to_mathematical_value(machine, arg(args, 0))?;
    let Some(format) = this_format(machine, this)? else {
        return Err(not_a_number_format(machine));
    };
    let text = format.format(&value);
    let text = text.map_err(|error| number_failure(machine, error))?;
    string_outcome(machine, &text)
}

fn format_to_parts<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if this_format(machine, this)?.is_none() {
        return Err(not_a_number_format(machine));
    }
    let value = to_mathematical_value(machine, arg(args, 0))?;
    let Some(format) = this_format(machine, this)? else {
        return Err(not_a_number_format(machine));
    };
    let parts = format
        .format_to_parts(&value)
        .map_err(|error| number_failure(machine, error))?;
    parts_outcome(machine, &parts)
}

pub(super) fn parts_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    parts: &[NumberPart],
) -> Result<BuiltinOutcome, EvalFailure> {
    let mut elements = Vec::with_capacity(parts.len());
    for part in parts {
        elements.push(part_object(
            machine,
            part.part_type.as_str(),
            &part.value,
            None,
        )?);
    }
    super::super::allocate_array(machine, elements).map(BuiltinOutcome::Value)
}

/// The argument handling `formatRange` and `formatRangeToParts` share.
fn range_arguments<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
) -> Result<(RangeEnd, RangeEnd), EvalFailure> {
    if this_format(machine, this)?.is_none() {
        return Err(not_a_number_format(machine));
    }
    let (start, end) = (arg(args, 0), arg(args, 1));
    if start == Value::UNDEFINED || end == Value::UNDEFINED {
        return Err(type_error(machine, "a range needs two ends"));
    }
    let start = to_range_end(machine, start)?;
    let end = to_range_end(machine, end)?;
    Ok((start, end))
}

fn format_range<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (start, end) = range_arguments(machine, this, args)?;
    let Some(format) = this_format(machine, this)? else {
        return Err(not_a_number_format(machine));
    };
    let text = format.format_range(&start, &end);
    let text = text.map_err(|error| number_failure(machine, error))?;
    string_outcome(machine, &text)
}

fn format_range_to_parts<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (start, end) = range_arguments(machine, this, args)?;
    let Some(format) = this_format(machine, this)? else {
        return Err(not_a_number_format(machine));
    };
    let parts = format
        .format_range_to_parts(&start, &end)
        .map_err(|error| number_failure(machine, error))?;
    let mut elements = Vec::with_capacity(parts.len());
    for part in &parts {
        elements.push(part_object(
            machine,
            part.part_type.as_str(),
            &part.value,
            Some(("source", part.source.as_str())),
        )?);
    }
    super::super::allocate_array(machine, elements).map(BuiltinOutcome::Value)
}

fn resolved_options<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let format = unwrap_legacy_instance(machine, this, IntlKind::NumberFormat)?;
    let Some(format) = this_format(machine, format)? else {
        return Err(not_a_number_format(machine));
    };
    let resolved = format.resolved_options();
    let result = new_object(machine)?;
    let text = |machine: &mut Machine<'_, H>, name: &str, value: &str| {
        let value = string_value(machine, value)?;
        define_field(machine, result, name, value)
    };
    let number = |machine: &mut Machine<'_, H>, name: &str, value: u16| {
        define_field(machine, result, name, crate::number_value(f64::from(value)))
    };
    text(machine, "locale", &resolved.locale)?;
    text(machine, "numberingSystem", &resolved.numbering_system)?;
    text(machine, "style", resolved.style.as_str())?;
    if let Some(currency) = &resolved.currency {
        text(machine, "currency", currency)?;
    }
    if let Some(display) = resolved.currency_display {
        text(machine, "currencyDisplay", display.as_str())?;
    }
    if let Some(sign) = resolved.currency_sign {
        text(machine, "currencySign", sign.as_str())?;
    }
    if let Some(unit) = &resolved.unit {
        text(machine, "unit", unit)?;
    }
    if let Some(display) = resolved.unit_display {
        text(machine, "unitDisplay", display.as_str())?;
    }
    number(
        machine,
        "minimumIntegerDigits",
        u16::from(resolved.minimum_integer_digits),
    )?;
    for (name, value) in [
        ("minimumFractionDigits", resolved.minimum_fraction_digits),
        ("maximumFractionDigits", resolved.maximum_fraction_digits),
        (
            "minimumSignificantDigits",
            resolved.minimum_significant_digits,
        ),
        (
            "maximumSignificantDigits",
            resolved.maximum_significant_digits,
        ),
    ] {
        if let Some(value) = value {
            number(machine, name, u16::from(value))?;
        }
    }
    match resolved.use_grouping {
        UseGrouping::False => define_field(machine, result, "useGrouping", Value::boolean(false))?,
        UseGrouping::Min2 => text(machine, "useGrouping", "min2")?,
        UseGrouping::Auto => text(machine, "useGrouping", "auto")?,
        UseGrouping::Always => text(machine, "useGrouping", "always")?,
    }
    text(machine, "notation", resolved.notation.as_str())?;
    if let Some(display) = resolved.compact_display {
        text(machine, "compactDisplay", display.as_str())?;
    }
    text(machine, "signDisplay", resolved.sign_display.as_str())?;
    number(machine, "roundingIncrement", resolved.rounding_increment)?;
    text(machine, "roundingMode", resolved.rounding_mode.as_str())?;
    text(
        machine,
        "roundingPriority",
        resolved.rounding_priority.as_str(),
    )?;
    text(
        machine,
        "trailingZeroDisplay",
        resolved.trailing_zero_display.as_str(),
    )?;
    Ok(BuiltinOutcome::Value(result))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn exact(text: &str) -> IntlMathematicalValue {
        IntlMathematicalValue::from_decimal_string(text).expect("a decimal")
    }

    fn english(options: NumberFormatOptions) -> NumberFormat<'static> {
        let data: &'static crate::intl::locale_data::IntlData = &DATA;
        NumberFormat::new(&["en".to_owned()], &options, data, &NoHostLocale).expect("a format")
    }

    fn range(format: &NumberFormat<'_>, start: f64, end: f64) -> String {
        format
            .format_range(&RangeEnd::number(start), &RangeEnd::number(end))
            .expect("a range")
    }

    fn string_mathematical_value(text: &str) -> IntlMathematicalValue {
        string_range_end(text).value
    }

    #[test]
    fn a_currency_code_is_set_off_only_from_digits() {
        let euros = english(NumberFormatOptions {
            style: Some("currency".to_owned()),
            currency: Some("EUR".to_owned()),
            currency_display: Some("code".to_owned()),
            ..NumberFormatOptions::default()
        });
        let text = |value| euros.format_number(value).expect("a text");
        assert_eq!(text(1.0), "EUR\u{a0}1.00");
        assert_eq!(text(-1.0), "-EUR\u{a0}1.00");
        assert_eq!(text(f64::INFINITY), "EUR∞");
        assert_eq!(text(f64::NEG_INFINITY), "-EUR∞");
        assert_eq!(text(f64::NAN), "EURNaN");
        assert_eq!(range(&euros, 1.0, f64::INFINITY), "EUR\u{a0}1.00–∞");
        assert_eq!(range(&euros, f64::INFINITY, 1.0), "EUR∞–1.00");
    }

    /// ICU holds an end beyond the range of a double as `Infinity`, so the
    /// digits of such an end and `∞` are one value.
    #[test]
    fn an_end_beyond_a_double_is_one_value_with_infinity() {
        let bigint = |text: String| {
            RangeEnd::digits(IntlMathematicalValue::from_bigint(&text).expect("a BigInt"))
        };
        let huge = bigint(format!("1{}", "0".repeat(400)));
        let negative_huge = bigint(format!("-1{}", "0".repeat(400)));
        let infinity = RangeEnd::number(f64::INFINITY);
        let negative_infinity = RangeEnd::number(f64::NEG_INFINITY);
        let digits = format!("10{}", ",000".repeat(133));
        let both = |format: &NumberFormat<'_>, start: &RangeEnd, end: &RangeEnd| {
            format.format_range(start, end).expect("a range")
        };
        let plain = english(NumberFormatOptions::default());
        assert_eq!(both(&plain, &huge, &infinity), format!("~{digits}"));
        assert_eq!(both(&plain, &infinity, &huge), "~∞");
        assert_eq!(both(&plain, &negative_infinity, &negative_huge), "~-∞");
        let euros = english(NumberFormatOptions {
            style: Some("currency".to_owned()),
            currency: Some("EUR".to_owned()),
            currency_display: Some("code".to_owned()),
            ..NumberFormatOptions::default()
        });
        assert_eq!(
            both(&euros, &huge, &infinity),
            format!("~EUR\u{a0}{digits}.00")
        );
        assert_eq!(both(&euros, &infinity, &huge), "~EUR∞");
        let accounting = english(NumberFormatOptions {
            style: Some("currency".to_owned()),
            currency: Some("USD".to_owned()),
            currency_sign: Some("accounting".to_owned()),
            ..NumberFormatOptions::default()
        });
        assert_eq!(
            both(&accounting, &negative_infinity, &negative_huge),
            "($∞)"
        );
        assert_eq!(
            both(&accounting, &negative_huge, &negative_infinity),
            format!("(${digits}.00)")
        );
    }

    #[test]
    fn an_accounting_negative_has_no_place_for_the_approximately_sign() {
        let accounting = english(NumberFormatOptions {
            style: Some("currency".to_owned()),
            currency: Some("USD".to_owned()),
            currency_sign: Some("accounting".to_owned()),
            ..NumberFormatOptions::default()
        });
        assert_eq!(range(&accounting, -1.0, -1.0), "($1.00)");
        assert_eq!(range(&accounting, -0.0, -0.0), "($0.00)");
        assert_eq!(range(&accounting, 1.0, 1.0), "~$1.00");
        let standard = english(NumberFormatOptions {
            style: Some("currency".to_owned()),
            currency: Some("USD".to_owned()),
            ..NumberFormatOptions::default()
        });
        assert_eq!(range(&standard, -1.0, -1.0), "~-$1.00");
    }

    #[test]
    fn a_hidden_sign_keeps_a_range_a_range() {
        let unsigned = english(NumberFormatOptions {
            sign_display: Some("never".to_owned()),
            ..NumberFormatOptions::default()
        });
        assert_eq!(range(&unsigned, -1.0, 1.0), "1–1");
        assert_eq!(range(&unsigned, f64::NEG_INFINITY, f64::INFINITY), "∞–∞");
        assert_eq!(range(&unsigned, 1.0, 1.0), "~1");
        assert_eq!(range(&unsigned, 0.0, -0.0), "~0");
    }

    #[test]
    fn a_currency_symbol_keeps_the_short_compact_form() {
        let long = |display: &str| {
            english(NumberFormatOptions {
                style: Some("currency".to_owned()),
                currency: Some("USD".to_owned()),
                currency_display: Some(display.to_owned()),
                notation: Some("compact".to_owned()),
                compact_display: Some("long".to_owned()),
                ..NumberFormatOptions::default()
            })
        };
        let text = |format: &NumberFormat<'_>| format.format_number(1000.0).expect("a text");
        assert_eq!(text(&long("symbol")), "$1K");
        assert_eq!(text(&long("code")), "USD\u{a0}1K");
        assert_eq!(text(&long("name")), "1 thousand US dollars");
    }

    #[test]
    fn an_exponent_makes_a_name_plural() {
        let meters = |notation: &str| {
            english(NumberFormatOptions {
                style: Some("unit".to_owned()),
                unit: Some("meter".to_owned()),
                unit_display: Some("long".to_owned()),
                notation: Some(notation.to_owned()),
                ..NumberFormatOptions::default()
            })
        };
        let text = |format: &NumberFormat<'_>, value| format.format_number(value).expect("a text");
        assert_eq!(text(&meters("compact"), 1.0), "1 meter");
        assert_eq!(text(&meters("compact"), 1000.0), "1K meters");
        assert_eq!(text(&meters("scientific"), 1.0), "1E0 meter");
        assert_eq!(text(&meters("scientific"), 1000.0), "1E3 meters");
        assert_eq!(text(&meters("scientific"), 0.1), "1E-1 meters");
        let dollars = english(NumberFormatOptions {
            style: Some("currency".to_owned()),
            currency: Some("USD".to_owned()),
            currency_display: Some("name".to_owned()),
            notation: Some("compact".to_owned()),
            ..NumberFormatOptions::default()
        });
        assert_eq!(text(&dollars, 1_000_000.0), "1M US dollars");
    }

    #[test]
    fn range_ends_are_one_value_as_icu_holds_them() {
        let text_range = |format: &NumberFormat<'_>, start: &str, end: &str| {
            format
                .format_range(
                    &RangeEnd::digits(exact(start)),
                    &RangeEnd::digits(exact(end)),
                )
                .expect("a range")
        };
        let scientific = english(NumberFormatOptions {
            notation: Some("scientific".to_owned()),
            ..NumberFormatOptions::default()
        });
        assert_eq!(text_range(&scientific, "1e-400", "2e-400"), "~1E-400");
        assert_eq!(text_range(&scientific, "2e-400", "1e-400"), "~2E-400");
        // A different exponent, or a different sign, is more than the digits.
        assert_eq!(
            text_range(&scientific, "1e-400", "1e-500"),
            "1E-400 – 1E-500"
        );
        assert_eq!(
            text_range(&scientific, "-1e-400", "1e-400"),
            "-1E-400 – 1E-400"
        );

        let plain = english(NumberFormatOptions::default());
        // Integers that fit 64 bits stay exact, and those past 64 bits do not.
        assert_eq!(
            text_range(&plain, "9223372036854775806", "9223372036854775807"),
            "9,223,372,036,854,775,806–9,223,372,036,854,775,807"
        );
        assert_eq!(
            text_range(&plain, "-9223372036854775808", "-9223372036854775807"),
            "-9,223,372,036,854,775,808 – -9,223,372,036,854,775,807"
        );
        assert_eq!(
            text_range(&plain, "9223372036854775808", "9223372036854775809"),
            "~9,223,372,036,854,775,808"
        );
        // One end fits 64 bits and the other does not, so they are not one value.
        let long = english(NumberFormatOptions {
            maximum_fraction_digits: Some(20.0),
            ..NumberFormatOptions::default()
        });
        assert_eq!(
            text_range(&long, "1", "1.00000000000000001"),
            "1–1.00000000000000001"
        );
        assert_eq!(
            text_range(&long, "1.00000000000000001", "1.00000000000000002"),
            "~1.00000000000000001"
        );
    }

    #[test]
    fn a_range_end_keeps_the_form_that_v8_hands_to_icu() {
        let long = english(NumberFormatOptions {
            maximum_fraction_digits: Some(20.0),
            ..NumberFormatOptions::default()
        });
        let precise = english(NumberFormatOptions {
            maximum_significant_digits: Some(21.0),
            ..NumberFormatOptions::default()
        });
        let both = |format: &NumberFormat<'_>, start: &RangeEnd, end: &RangeEnd| {
            format.format_range(start, end).expect("a range")
        };
        let string = string_range_end;
        let number = RangeEnd::number;
        let bigint = |text: &str| {
            RangeEnd::digits(IntlMathematicalValue::from_bigint(text).expect("a BigInt"))
        };

        // A Number is a double, so it is one value with digits that round to it.
        let tiny = string("1.00000000000000001");
        assert_eq!(both(&long, &number(1.0), &tiny), "~1");
        assert_eq!(both(&long, &tiny, &number(1.0)), "~1.00000000000000001");
        assert_eq!(both(&long, &string("1"), &tiny), "1–1.00000000000000001");
        assert_eq!(both(&long, &bigint("1"), &tiny), "1–1.00000000000000001");
        assert_eq!(both(&precise, &number(0.0), &string("1e-400")), "~0");
        assert_eq!(
            both(
                &precise,
                &number(-9_223_372_036_854_775_808.0),
                &bigint("-9223372036854775809")
            ),
            "~-9,223,372,036,854,776,000"
        );
        // A Number never matches an integer that ICU holds exactly.
        assert_eq!(
            both(
                &long,
                &number(9_007_199_254_740_992.0),
                &string("9007199254740993")
            ),
            "9,007,199,254,740,992–9,007,199,254,740,993"
        );

        // An empty string reads as the Number 0.
        assert_eq!(both(&precise, &string(""), &string("1e-400")), "~0");
        assert_eq!(both(&precise, &string(" \t"), &string("1e-400")), "~0");

        // A 0x, 0o or 0b integer is a Number below 2^53 - 1, and exact from there.
        assert_eq!(both(&long, &string("0x1"), &tiny), "~1");
        assert_eq!(both(&long, &string("0b1"), &tiny), "~1");
        assert_eq!(both(&long, &string("0x00000001"), &tiny), "~1");
        assert_eq!(
            both(
                &long,
                &string("0x1ffffffffffffe"),
                &string("9007199254740990.0000000001")
            ),
            "~9,007,199,254,740,990"
        );
        assert_eq!(
            both(
                &long,
                &string("0x1fffffffffffff"),
                &string("9007199254740991.0000000001")
            ),
            "9,007,199,254,740,991–9,007,199,254,740,991.0000000001"
        );
        assert_eq!(
            both(
                &long,
                &string("0x20000000000001"),
                &number(9_007_199_254_740_992.0)
            ),
            "9,007,199,254,740,993–9,007,199,254,740,992"
        );
        assert_eq!(
            both(
                &long,
                &string("0x8000000000000000"),
                &string("9223372036854775808.0000000001")
            ),
            "~9,223,372,036,854,775,808"
        );
    }

    #[test]
    fn only_a_sign_or_symbol_of_the_start_spaces_a_range() {
        let plain = english(NumberFormatOptions::default());
        assert_eq!(range(&plain, 1.0, 2.0), "1–2");
        assert_eq!(range(&plain, 1.0, -1.0), "1–-1");
        assert_eq!(range(&plain, -1.0, 1.0), "-1 – 1");
        assert_eq!(range(&plain, -2.0, -1.0), "-2 – -1");
    }

    #[test]
    fn an_exponent_always_spaces_a_range() {
        let scientific = english(NumberFormatOptions {
            notation: Some("scientific".to_owned()),
            ..NumberFormatOptions::default()
        });
        assert_eq!(range(&scientific, 1.0, 2.0), "1E0 – 2E0");
        assert_eq!(range(&scientific, 0.0, f64::INFINITY), "0E0 – ∞");
        assert_eq!(range(&scientific, f64::INFINITY, 1.0), "∞–1E0");
    }

    #[test]
    fn a_percent_sign_is_a_name_only_in_compact_notation_or_as_a_word() {
        let compact = english(NumberFormatOptions {
            style: Some("percent".to_owned()),
            notation: Some("compact".to_owned()),
            ..NumberFormatOptions::default()
        });
        assert_eq!(range(&compact, 1.0, 2.0), "100–200%");
        assert_eq!(range(&compact, -2.0, -1.0), "-200 – -100%");
        let unit = |display: &str| {
            english(NumberFormatOptions {
                style: Some("unit".to_owned()),
                unit: Some("percent".to_owned()),
                unit_display: Some(display.to_owned()),
                ..NumberFormatOptions::default()
            })
        };
        assert_eq!(range(&unit("short"), 1.0, 2.0), "1% – 2%");
        assert_eq!(range(&unit("long"), 1.0, 2.0), "1–2 percent");
    }

    #[test]
    fn a_range_shares_its_symbols_as_one_group() {
        let percent = english(NumberFormatOptions {
            style: Some("percent".to_owned()),
            ..NumberFormatOptions::default()
        });
        assert_eq!(range(&percent, -2.0, -1.0), "-200–100%");
        assert_eq!(range(&percent, 1.0, 2.0), "100% – 200%");
        let compact = english(NumberFormatOptions {
            notation: Some("compact".to_owned()),
            ..NumberFormatOptions::default()
        });
        assert_eq!(range(&compact, 1000.0, 2000.0), "1K – 2K");
        let dollars = english(NumberFormatOptions {
            style: Some("currency".to_owned()),
            currency: Some("USD".to_owned()),
            notation: Some("compact".to_owned()),
            ..NumberFormatOptions::default()
        });
        assert_eq!(range(&dollars, 1000.0, 2000.0), "$1–2K");
        let words = english(NumberFormatOptions {
            notation: Some("compact".to_owned()),
            compact_display: Some("long".to_owned()),
            ..NumberFormatOptions::default()
        });
        assert_eq!(range(&words, 1000.0, 2000.0), "1–2 thousand");
    }

    #[test]
    fn a_range_always_shares_its_name_in_the_plural_of_a_range() {
        let meters = english(NumberFormatOptions {
            style: Some("unit".to_owned()),
            unit: Some("meter".to_owned()),
            unit_display: Some("long".to_owned()),
            ..NumberFormatOptions::default()
        });
        assert_eq!(range(&meters, 1.0, 2.0), "1–2 meters");
        assert_eq!(range(&meters, 0.0, 1.0), "0–1 meters");
        assert_eq!(range(&meters, -1.0, 1.0), "-1 – 1 meters");
        assert_eq!(range(&meters, 1.0, 1.0), "~1 meter");
        let dollars = english(NumberFormatOptions {
            style: Some("currency".to_owned()),
            currency: Some("USD".to_owned()),
            currency_display: Some("name".to_owned()),
            ..NumberFormatOptions::default()
        });
        assert_eq!(range(&dollars, 1.0, -1.0), "1.00–-1.00 US dollars");
    }

    #[test]
    fn a_string_below_the_range_of_a_number_stays_exact() {
        for text in [
            "1e-400",
            "-1e-400",
            "1.5e-400",
            "1E-400",
            "5e-324",
            "1e-1000000",
        ] {
            assert_eq!(string_mathematical_value(text), exact(text), "{text}");
        }
        assert_eq!(string_mathematical_value(" +1e-400 "), exact("1e-400"));
        assert_ne!(string_mathematical_value("1e-400"), exact("0"));
    }

    #[test]
    fn a_string_of_zero_keeps_its_sign() {
        for zero in ["0", "+0", "0e5", "0.000e-400", "0e-400", ""] {
            assert_eq!(
                string_mathematical_value(zero),
                IntlMathematicalValue::from_f64(0.0),
                "{zero:?}"
            );
        }
        for zero in ["-0", "-0e5", "-0.000e-400"] {
            assert_eq!(
                string_mathematical_value(zero),
                IntlMathematicalValue::from_f64(-0.0),
                "{zero:?}"
            );
        }
    }

    #[test]
    fn a_string_past_the_range_of_a_number_saturates() {
        for (text, number) in [
            ("1e400", f64::INFINITY),
            ("1e5000", f64::INFINITY),
            ("-1e400", f64::NEG_INFINITY),
        ] {
            assert_eq!(
                string_mathematical_value(text),
                IntlMathematicalValue::from_f64(number),
                "{text}"
            );
        }
    }

    #[test]
    fn an_exponent_that_nothing_can_hold_reads_as_the_nearest_number() {
        for (text, number) in [
            ("1e-99999999999", 0.0),
            ("-1e-99999999999", -0.0),
            ("0e99999999999", 0.0),
            ("1e99999999999", f64::INFINITY),
        ] {
            assert_eq!(
                string_mathematical_value(text),
                IntlMathematicalValue::from_f64(number),
                "{text}"
            );
        }
    }
}
