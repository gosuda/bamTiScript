//! Option reading. Every function here performs exactly the property reads and
//! conversions its abstract operation does; callers sequence them in the order
//! ECMA-402 lists them, which test262 observes through getters and Proxies.

use bamts_native::{Decoded, Value};

use super::{is_object, locale_record, range_error, type_error};
use crate::intl::locale_data::DATA;
use crate::intl::locale_negotiation::{LocaleMatcher, canonicalize_unicode_locale_id};
use crate::intrinsics::builtins::array_es2023::{index_key, length_of_array_like};
use crate::intrinsics::builtins::array_generic::tick;
use crate::{EvalFailure, Host, Machine};

/// A resolved options argument. `None` stands for the empty null-prototype
/// object of `undefined`, which no read can observe.
pub(super) type Options = Option<Value>;

/// GetOptionsObject.
pub(super) fn get_options_object<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<Options, EvalFailure> {
    if value == Value::UNDEFINED {
        Ok(None)
    } else if is_object(machine, value)? {
        Ok(Some(value))
    } else {
        Err(type_error(machine, "options must be an object"))
    }
}

/// CoerceOptionsToObject.
pub(super) fn coerce_options_to_object<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<Options, EvalFailure> {
    if value == Value::UNDEFINED {
        Ok(None)
    } else {
        machine.value_to_object(value).map(Some)
    }
}

/// The value of one option, `undefined` when absent.
pub(super) fn read<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    name: &str,
) -> Result<Value, EvalFailure> {
    match options {
        Some(object) => machine.get_named_property(object, name),
        None => Ok(Value::UNDEFINED),
    }
}

/// GetOption with type string and no default. An empty `allowed` accepts any
/// value.
pub(super) fn string_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    name: &str,
    allowed: &[&str],
) -> Result<Option<String>, EvalFailure> {
    let value = read(machine, options, name)?;
    if value == Value::UNDEFINED {
        return Ok(None);
    }
    let text = machine.coerce_string_observable(value)?.to_utf8_lossy();
    if allowed.is_empty() || allowed.contains(&text.as_str()) {
        Ok(Some(text))
    } else {
        Err(range_error(
            machine,
            format!("{text} is not a valid value for {name}"),
        ))
    }
}

/// GetOption with type boolean and no default.
pub(super) fn boolean_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    name: &str,
) -> Result<Option<bool>, EvalFailure> {
    let value = read(machine, options, name)?;
    if value == Value::UNDEFINED {
        Ok(None)
    } else {
        Ok(Some(machine.to_boolean(value)))
    }
}

/// The `localeMatcher` option every constructor reads.
pub(super) fn locale_matcher_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
) -> Result<LocaleMatcher, EvalFailure> {
    let value = string_option(machine, options, "localeMatcher", &["lookup", "best fit"])?;
    Ok(if value.as_deref() == Some("lookup") {
        LocaleMatcher::Lookup
    } else {
        LocaleMatcher::BestFit
    })
}

/// The library's spelling of a matcher.
pub(super) const fn matcher_name(matcher: LocaleMatcher) -> &'static str {
    match matcher {
        LocaleMatcher::Lookup => "lookup",
        LocaleMatcher::BestFit => "best fit",
    }
}

/// DefaultNumberOption.
pub(super) fn default_number_option<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    minimum: f64,
    maximum: f64,
    name: &str,
) -> Result<Option<f64>, EvalFailure> {
    if value == Value::UNDEFINED {
        return Ok(None);
    }
    let number = machine.coerce_number_observable(value)?;
    let number = match number.decode() {
        Some(Decoded::Int32(number)) => f64::from(number as i32),
        Some(Decoded::Number(number)) => number,
        _ => f64::NAN,
    };
    if !number.is_finite() || number < minimum || number > maximum {
        return Err(range_error(machine, format!("{name} is out of range")));
    }
    Ok(Some(number.floor()))
}

/// GetNumberOption.
pub(super) fn number_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    name: &str,
    minimum: f64,
    maximum: f64,
) -> Result<Option<f64>, EvalFailure> {
    let value = read(machine, options, name)?;
    default_number_option(machine, value, minimum, maximum, name)
}

/// CanonicalizeLocaleList. Elements are read and validated one at a time, so
/// an invalid tag stops the walk before any later element is touched.
pub(super) fn canonicalize_locale_list<H: Host>(
    machine: &mut Machine<'_, H>,
    locales: Value,
) -> Result<Vec<String>, EvalFailure> {
    let mut seen = Vec::new();
    if locales == Value::UNDEFINED {
        return Ok(seen);
    }
    if machine.string_value(locales).is_some() || locale_record(machine, locales)?.is_some() {
        add_locale(machine, &mut seen, locales)?;
        return Ok(seen);
    }
    let object = machine.value_to_object(locales)?;
    let length = length_of_array_like(machine, object)?;
    for index in 0..length {
        tick(machine)?;
        let key = index_key(&mut machine.atoms, index);
        if !machine.internal_has_property(object, &key)? {
            continue;
        }
        let element = machine.get_property_key(object, &key)?;
        if machine.string_value(element).is_none() && !is_object(machine, element)? {
            return Err(type_error(
                machine,
                "a locale must be a string or an object",
            ));
        }
        add_locale(machine, &mut seen, element)?;
    }
    Ok(seen)
}

fn add_locale<H: Host>(
    machine: &mut Machine<'_, H>,
    seen: &mut Vec<String>,
    element: Value,
) -> Result<(), EvalFailure> {
    let tag = match locale_record(machine, element)? {
        Some(tag) => tag.to_string(),
        None => machine.coerce_string_observable(element)?.to_utf8_lossy(),
    };
    let canonical = canonicalize_unicode_locale_id(&tag, &*DATA)
        .map_err(|error| range_error(machine, error.to_string()))?;
    if !seen.contains(&canonical) {
        seen.push(canonical);
    }
    Ok(())
}

/// What SetNumberFormatDigitOptions reads, shared by the services that round.
/// Only the values the resolution needs have gone through ToNumber.
pub(super) struct DigitOptions {
    pub(super) minimum_integer_digits: Option<f64>,
    pub(super) minimum_fraction_digits: Option<f64>,
    pub(super) maximum_fraction_digits: Option<f64>,
    pub(super) minimum_significant_digits: Option<f64>,
    pub(super) maximum_significant_digits: Option<f64>,
    pub(super) rounding_increment: Option<f64>,
    pub(super) rounding_mode: Option<String>,
    pub(super) rounding_priority: Option<String>,
    pub(super) trailing_zero_display: Option<String>,
}

const ROUNDING_INCREMENTS: [f64; 15] = [
    1.0, 2.0, 5.0, 10.0, 20.0, 25.0, 50.0, 100.0, 200.0, 250.0, 500.0, 1000.0, 2000.0, 2500.0,
    5000.0,
];

/// The reads of SetNumberFormatDigitOptions, in order. The four digit limits
/// are fetched early but converted late, and only when rounding uses them.
pub(super) fn digit_options<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    compact: bool,
) -> Result<DigitOptions, EvalFailure> {
    let minimum_integer_digits =
        number_option(machine, options, "minimumIntegerDigits", 1.0, 21.0)?;
    let minimum_fraction = read(machine, options, "minimumFractionDigits")?;
    let maximum_fraction = read(machine, options, "maximumFractionDigits")?;
    let minimum_significant = read(machine, options, "minimumSignificantDigits")?;
    let maximum_significant = read(machine, options, "maximumSignificantDigits")?;
    let rounding_increment = number_option(machine, options, "roundingIncrement", 1.0, 5000.0)?;
    if rounding_increment.is_some_and(|increment| !ROUNDING_INCREMENTS.contains(&increment)) {
        return Err(range_error(machine, "roundingIncrement is not allowed"));
    }
    let rounding_mode = string_option(
        machine,
        options,
        "roundingMode",
        &[
            "ceil",
            "floor",
            "expand",
            "trunc",
            "halfCeil",
            "halfFloor",
            "halfExpand",
            "halfTrunc",
            "halfEven",
        ],
    )?;
    let rounding_priority = string_option(
        machine,
        options,
        "roundingPriority",
        &["auto", "morePrecision", "lessPrecision"],
    )?;
    let trailing_zero_display = string_option(
        machine,
        options,
        "trailingZeroDisplay",
        &["auto", "stripIfInteger"],
    )?;
    let has_significant =
        minimum_significant != Value::UNDEFINED || maximum_significant != Value::UNDEFINED;
    let has_fraction = minimum_fraction != Value::UNDEFINED || maximum_fraction != Value::UNDEFINED;
    let automatic = matches!(rounding_priority.as_deref(), None | Some("auto"));
    let need_significant = !automatic || has_significant;
    let need_fraction = !automatic || !(has_significant || (!has_fraction && compact));
    let (mut minimum_significant_digits, mut maximum_significant_digits) = (None, None);
    if need_significant && has_significant {
        let minimum = default_number_option(
            machine,
            minimum_significant,
            1.0,
            21.0,
            "minimumSignificantDigits",
        )?;
        let maximum = default_number_option(
            machine,
            maximum_significant,
            minimum.unwrap_or(1.0),
            21.0,
            "maximumSignificantDigits",
        )?;
        minimum_significant_digits = minimum;
        maximum_significant_digits = maximum;
    }
    let (mut minimum_fraction_digits, mut maximum_fraction_digits) = (None, None);
    if need_fraction && has_fraction {
        minimum_fraction_digits = default_number_option(
            machine,
            minimum_fraction,
            0.0,
            100.0,
            "minimumFractionDigits",
        )?;
        maximum_fraction_digits = default_number_option(
            machine,
            maximum_fraction,
            0.0,
            100.0,
            "maximumFractionDigits",
        )?;
    }
    Ok(DigitOptions {
        minimum_integer_digits,
        minimum_fraction_digits,
        maximum_fraction_digits,
        minimum_significant_digits,
        maximum_significant_digits,
        rounding_increment,
        rounding_mode,
        rounding_priority,
        trailing_zero_display,
    })
}
