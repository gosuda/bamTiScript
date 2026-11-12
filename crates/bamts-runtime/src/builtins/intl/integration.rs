//! The `toLocale*` methods of the rest of the runtime, which ECMA-402 defines
//! as creating a formatter and using it once.

use bamts_bytecode::EcmaString;
use bamts_native::Value;

use super::super::temporal::temporal_record;
use super::collator::create_collator;
use super::date_time_format::{
    create_date_time_format, date_failure, read_options, temporal_value,
};
use super::duration_format::{create_duration_format, duration_parts};
use super::number_format::{create_number_format, number_failure, read_number_format_options};
use super::options::{canonicalize_locale_list, coerce_options_to_object};
use super::{range_error, string_outcome, type_error};
use crate::intl::date_time_format::{
    DateTimeFormat, DateTimeFormatOptions, DefaultComponents, RequiredComponents,
    TemporalFormatKind, TimeZoneNameStyle,
};
use crate::intl::locale_data::DATA;
use crate::intl::number_format::IntlMathematicalValue;
use crate::intrinsics::BuiltinOutcome;
use crate::temporal::TemporalObject;
use crate::temporal::instant_duration::Duration;
use crate::{EvalFailure, Host, Machine};

/// `Number.prototype.toLocaleString` after the receiver check.
pub(in crate::intrinsics::builtins) fn number_to_locale_string<H: Host>(
    machine: &mut Machine<'_, H>,
    number: f64,
    locales: Value,
    options: Value,
) -> Result<BuiltinOutcome, EvalFailure> {
    number_to_string(
        machine,
        &IntlMathematicalValue::from_f64(number),
        locales,
        options,
    )
}

/// `String.prototype.localeCompare` through a collator made for this call.
pub(in crate::intrinsics::builtins) fn compare_with_collator<H: Host>(
    machine: &mut Machine<'_, H>,
    left: &EcmaString,
    right: &EcmaString,
    locales: Value,
    options: Value,
) -> Result<BuiltinOutcome, EvalFailure> {
    let collator = create_collator(machine, locales, options)?;
    let result = collator.compare(&*DATA, left.as_units(), right.as_units());
    Ok(BuiltinOutcome::Value(crate::number_value(f64::from(
        result,
    ))))
}

/// `BigInt.prototype.toLocaleString` after the receiver check.
pub(in crate::intrinsics::builtins) fn bigint_to_locale_string<H: Host>(
    machine: &mut Machine<'_, H>,
    decimal: &str,
    locales: Value,
    options: Value,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = IntlMathematicalValue::from_bigint(decimal)
        .map_err(|error| number_failure(machine, error))?;
    number_to_string(machine, &value, locales, options)
}

fn number_to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    value: &IntlMathematicalValue,
    locales: Value,
    options: Value,
) -> Result<BuiltinOutcome, EvalFailure> {
    let requested = canonicalize_locale_list(machine, locales)?;
    let options = coerce_options_to_object(machine, options)?;
    let options = read_number_format_options(machine, options)?;
    let format = create_number_format(machine, &requested, &options)?;
    let text = format
        .format(value)
        .map_err(|error| number_failure(machine, error))?;
    string_outcome(machine, &text)
}

/// CreateDateTimeFormat for one `toLocale*` call.
fn date_format<H: Host>(
    machine: &mut Machine<'_, H>,
    locales: Value,
    options: Value,
    required: RequiredComponents,
    defaults: DefaultComponents,
    adjust: impl FnOnce(&mut DateTimeFormatOptions),
    zone_of_value: Option<&str>,
) -> Result<DateTimeFormat, EvalFailure> {
    let requested = canonicalize_locale_list(machine, locales)?;
    let options = coerce_options_to_object(machine, options)?;
    let mut options = read_options(machine, options, zone_of_value)?;
    adjust(&mut options);
    create_date_time_format(machine, &requested, &options, required, defaults)
}

/// `Date.prototype.toLocaleString` and its two peers, after the receiver check.
/// An invalid date never reaches the options.
pub(in crate::intrinsics::builtins) fn date_to_locale_string<H: Host>(
    machine: &mut Machine<'_, H>,
    time: f64,
    locales: Value,
    options: Value,
    required: RequiredComponents,
    defaults: DefaultComponents,
) -> Result<BuiltinOutcome, EvalFailure> {
    if time.is_nan() {
        return string_outcome(machine, "Invalid Date");
    }
    let format = date_format(machine, locales, options, required, defaults, |_| {}, None)?;
    let text = format
        .format(time, &*DATA)
        .map_err(|error| date_failure(machine, &error))?;
    string_outcome(machine, &text)
}

fn temporal_text<H: Host>(
    machine: &mut Machine<'_, H>,
    format: &DateTimeFormat,
    kind: TemporalFormatKind,
    instant: i128,
) -> Result<BuiltinOutcome, EvalFailure> {
    let parts = format
        .format_temporal_to_parts(kind, instant, &*DATA)
        .map_err(|error| date_failure(machine, &error))?;
    let Some(parts) = parts else {
        return Err(type_error(
            machine,
            "these options do not apply to the value",
        ));
    };
    let text: String = parts.iter().map(|part| part.value.as_str()).collect();
    string_outcome(machine, &text)
}

/// `toLocaleString` of a Temporal class, after its receiver check.
pub(in crate::intrinsics::builtins) fn temporal_to_locale_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    locales: Value,
    options: Value,
) -> Result<BuiltinOutcome, EvalFailure> {
    use DefaultComponents as Defaults;
    use RequiredComponents as Required;
    let Some(record) = temporal_record(machine, this)? else {
        return Err(type_error(machine, "receiver is not a Temporal object"));
    };
    if let TemporalObject::ZonedDateTime(zoned) = &record {
        let zone = zoned.time_zone_id().as_str().to_owned();
        let calendar = zoned.calendar_id().as_str().to_owned();
        let instant = zoned.epoch_nanoseconds();
        let format = date_format(
            machine,
            locales,
            options,
            Required::Any,
            Defaults::All,
            |options| {
                // The zone is part of the default rendering, not of a requested one.
                let styled = options.date_style.is_some() || options.time_style.is_some();
                if !styled && !options.components.has_any() {
                    options.components.time_zone_name = options
                        .components
                        .time_zone_name
                        .or(Some(TimeZoneNameStyle::Short));
                }
            },
            Some(&zone),
        )?;
        if calendar != "iso8601" && calendar != format.resolved_options().calendar {
            return Err(range_error(
                machine,
                format!("calendar {calendar} does not match the formatter's"),
            ));
        }
        return temporal_text(machine, &format, TemporalFormatKind::Instant, instant);
    }
    let (required, defaults) = match &record {
        TemporalObject::PlainDate { .. } => (Required::Date, Defaults::Date),
        TemporalObject::PlainTime(_) => (Required::Time, Defaults::Time),
        TemporalObject::PlainYearMonth { .. } => (Required::YearMonth, Defaults::YearMonth),
        TemporalObject::PlainMonthDay { .. } => (Required::MonthDay, Defaults::MonthDay),
        _ => (Required::Any, Defaults::All),
    };
    let format = date_format(machine, locales, options, required, defaults, |_| {}, None)?;
    let (kind, instant) = temporal_value(machine, &format, &record)?;
    temporal_text(machine, &format, kind, instant)
}

/// `Temporal.Duration.prototype.toLocaleString`, after the receiver check.
pub(in crate::intrinsics::builtins) fn duration_to_locale_string<H: Host>(
    machine: &mut Machine<'_, H>,
    duration: &Duration,
    locales: Value,
    options: Value,
) -> Result<BuiltinOutcome, EvalFailure> {
    let format = create_duration_format(machine, locales, options)?;
    let parts = duration_parts(machine, &format, duration)?;
    let mut text = String::new();
    for part in &parts {
        text.push_str(&part.value);
    }
    super::super::allocate_string(machine, EcmaString::encode(&text)).map(BuiltinOutcome::Value)
}
