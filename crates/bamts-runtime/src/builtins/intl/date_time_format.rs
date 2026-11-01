//! `Intl.DateTimeFormat`.

use bamts_native::{Decoded, Value};

use super::super::temporal::temporal_record;
use super::options::{
    Options, boolean_option, canonicalize_locale_list, coerce_options_to_object,
    locale_matcher_option, number_option, read, string_option,
};
use super::{
    Class, allocate, arg, bound_function, chain_legacy_instance, define_field, install_class,
    instance_prototype, intl_record, is_type_sequence, new_object, part_object, range_error,
    register_hidden, string_outcome, string_value, supported_locales_outcome, type_error,
    unwrap_legacy_instance,
};
use crate::intl::date_time_format::{
    DateTimeComponents, DateTimeFormat, DateTimeFormatError, DateTimeFormatErrorKind,
    DateTimeFormatOptions, DateTimePart, DateTimeRangePart, DateTimeStyle, DefaultComponents,
    FormatMatcher, HourCycle, MonthStyle, NumericStyle, RangeSource, RequiredComponents,
    TemporalFormatKind, TextWidth, TimeZoneNameStyle, is_valid_time_zone,
};
use crate::intl::locale_data::DATA;
use crate::intl::number_data::NoHostLocale;
use crate::intl::{IntlKind, IntlObject};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::temporal::TemporalObject;
use crate::temporal::instant_duration::epoch_days_from_ymd;
use crate::temporal::plain_types::{PlainDate, PlainTime};
use crate::{EvalFailure, HeapEntry, Host, Machine};

const FORMAT: &str = "Intl.DateTimeFormat format";

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
            kind: IntlKind::DateTimeFormat,
            name: "DateTimeFormat",
            tag: "Intl.DateTimeFormat",
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

pub(super) fn date_failure<H: Host>(
    machine: &mut Machine<'_, H>,
    error: &DateTimeFormatError,
) -> EvalFailure {
    match error.kind() {
        DateTimeFormatErrorKind::TypeError => type_error(machine, error.to_string()),
        _ => range_error(machine, error.to_string()),
    }
}

const WIDTHS: &[&str] = &["narrow", "short", "long"];
const NUMERIC: &[&str] = &["2-digit", "numeric"];

fn width(value: Option<String>) -> Option<TextWidth> {
    value.map(|value| match value.as_str() {
        "narrow" => TextWidth::Narrow,
        "short" => TextWidth::Short,
        _ => TextWidth::Long,
    })
}

fn numeric(value: Option<String>) -> Option<NumericStyle> {
    value.map(|value| {
        if value == "2-digit" {
            NumericStyle::TwoDigit
        } else {
            NumericStyle::Numeric
        }
    })
}

fn date_style(value: Option<String>) -> Option<DateTimeStyle> {
    value.map(|value| match value.as_str() {
        "full" => DateTimeStyle::Full,
        "long" => DateTimeStyle::Long,
        "medium" => DateTimeStyle::Medium,
        _ => DateTimeStyle::Short,
    })
}

/// The date and time component options, in table order.
fn component_options<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
) -> Result<DateTimeComponents, EvalFailure> {
    let weekday = width(string_option(machine, options, "weekday", WIDTHS)?);
    let era = width(string_option(machine, options, "era", WIDTHS)?);
    let year = numeric(string_option(machine, options, "year", NUMERIC)?);
    let month = string_option(
        machine,
        options,
        "month",
        &["2-digit", "numeric", "narrow", "short", "long"],
    )?
    .map(|value| match value.as_str() {
        "2-digit" => MonthStyle::TwoDigit,
        "numeric" => MonthStyle::Numeric,
        "narrow" => MonthStyle::Narrow,
        "short" => MonthStyle::Short,
        _ => MonthStyle::Long,
    });
    let day = numeric(string_option(machine, options, "day", NUMERIC)?);
    let day_period = width(string_option(machine, options, "dayPeriod", WIDTHS)?);
    let hour = numeric(string_option(machine, options, "hour", NUMERIC)?);
    let minute = numeric(string_option(machine, options, "minute", NUMERIC)?);
    let second = numeric(string_option(machine, options, "second", NUMERIC)?);
    let fractional_second_digits =
        number_option(machine, options, "fractionalSecondDigits", 1.0, 3.0)?
            .map(|digits| digits as u8);
    let time_zone_name = string_option(
        machine,
        options,
        "timeZoneName",
        &[
            "short",
            "long",
            "shortOffset",
            "longOffset",
            "shortGeneric",
            "longGeneric",
        ],
    )?
    .map(|value| match value.as_str() {
        "short" => TimeZoneNameStyle::Short,
        "long" => TimeZoneNameStyle::Long,
        "shortOffset" => TimeZoneNameStyle::ShortOffset,
        "longOffset" => TimeZoneNameStyle::LongOffset,
        "shortGeneric" => TimeZoneNameStyle::ShortGeneric,
        _ => TimeZoneNameStyle::LongGeneric,
    });
    Ok(DateTimeComponents {
        weekday,
        era,
        year,
        month,
        day,
        day_period,
        hour,
        minute,
        second,
        fractional_second_digits,
        time_zone_name,
    })
}

/// The options of CreateDateTimeFormat, read in its order.
pub(super) fn read_options<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    zone_of_value: Option<&str>,
) -> Result<DateTimeFormatOptions, EvalFailure> {
    let locale_matcher = locale_matcher_option(machine, options)?;
    let calendar = string_option(machine, options, "calendar", &[])?;
    if let Some(name) = &calendar
        && !is_type_sequence(name)
    {
        let message = format!("{name} is not a valid calendar");
        return Err(range_error(machine, message));
    }
    let numbering_system = string_option(machine, options, "numberingSystem", &[])?;
    if let Some(name) = &numbering_system
        && !is_type_sequence(name)
    {
        let message = format!("{name} is not a valid numbering system");
        return Err(range_error(machine, message));
    }
    let hour12 = boolean_option(machine, options, "hour12")?;
    let hour_cycle = string_option(machine, options, "hourCycle", &["h11", "h12", "h23", "h24"])?
        .map(|value| match value.as_str() {
            "h11" => HourCycle::H11,
            "h12" => HourCycle::H12,
            "h23" => HourCycle::H23,
            _ => HourCycle::H24,
        });
    let time_zone = read(machine, options, "timeZone")?;
    let time_zone = if time_zone == Value::UNDEFINED {
        zone_of_value.map(str::to_owned)
    } else if zone_of_value.is_some() {
        return Err(type_error(
            machine,
            "a ZonedDateTime already has its time zone",
        ));
    } else {
        let name = machine.coerce_string_observable(time_zone)?.to_utf8_lossy();
        if !is_valid_time_zone(&name, &*DATA) {
            let message = format!("{name} is not a supported time zone");
            return Err(range_error(machine, message));
        }
        Some(name)
    };
    let components = component_options(machine, options)?;
    let format_matcher = string_option(machine, options, "formatMatcher", &["basic", "best fit"])?;
    let styles = ["full", "long", "medium", "short"];
    let date = date_style(string_option(machine, options, "dateStyle", &styles)?);
    let time = date_style(string_option(machine, options, "timeStyle", &styles)?);
    Ok(DateTimeFormatOptions {
        locale_matcher,
        calendar,
        numbering_system,
        time_zone,
        hour12,
        hour_cycle,
        format_matcher: if format_matcher.as_deref() == Some("basic") {
            FormatMatcher::Basic
        } else {
            FormatMatcher::BestFit
        },
        date_style: date,
        time_style: time,
        components,
    })
}

/// CreateDateTimeFormat over already canonicalized locales.
pub(super) fn create_date_time_format<H: Host>(
    machine: &mut Machine<'_, H>,
    requested: &[String],
    options: &DateTimeFormatOptions,
    required: RequiredComponents,
    defaults: DefaultComponents,
) -> Result<DateTimeFormat, EvalFailure> {
    DateTimeFormat::try_new_with_mode(
        requested,
        options,
        required,
        defaults,
        &*DATA,
        &NoHostLocale,
    )
    .map_err(|error| date_failure(machine, &error))
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let prototype = instance_prototype(machine, IntlKind::DateTimeFormat, constructing)?;
    let requested = canonicalize_locale_list(machine, arg(args, 0))?;
    let options = coerce_options_to_object(machine, arg(args, 1))?;
    let options = read_options(machine, options, None)?;
    let format = create_date_time_format(
        machine,
        &requested,
        &options,
        RequiredComponents::Any,
        DefaultComponents::Date,
    )?;
    let instance = allocate(machine, IntlObject::DateTimeFormat(format), prototype)?;
    chain_legacy_instance(
        machine,
        instance,
        IntlKind::DateTimeFormat,
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
) -> Result<Option<&'a DateTimeFormat>, EvalFailure> {
    Ok(match intl_record(machine, this)? {
        Some(IntlObject::DateTimeFormat(format)) => Some(format),
        _ => None,
    })
}

fn not_a_date_time_format<H: Host>(machine: &mut Machine<'_, H>) -> EvalFailure {
    type_error(machine, "receiver is not an Intl.DateTimeFormat")
}

fn format_getter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let format = unwrap_legacy_instance(machine, this, IntlKind::DateTimeFormat)?;
    if this_format(machine, format)?.is_none() {
        return Err(not_a_date_time_format(machine));
    }
    bound_function(machine, format, FORMAT, 1)
}

/// What ToDateTimeFormattable leaves: a time value or a Temporal object.
enum Formattable {
    Time(f64),
    Temporal(TemporalObject),
}

/// ToDateTimeFormattable, with `undefined` meaning now. Temporal.Duration is
/// not a formattable Temporal object; it converts like any other object.
fn to_formattable<H: Host>(
    machine: &mut Machine<'_, H>,
    date: Value,
) -> Result<Formattable, EvalFailure> {
    if date == Value::UNDEFINED {
        return Ok(Formattable::Time(machine.host.now_ms() as f64));
    }
    match temporal_record(machine, date)? {
        None | Some(TemporalObject::Duration(_)) => {}
        Some(record) => return Ok(Formattable::Temporal(record)),
    }
    let number = machine.coerce_number_observable(date)?;
    Ok(Formattable::Time(match number.decode() {
        Some(Decoded::Int32(number)) => f64::from(number as i32),
        Some(Decoded::Number(number)) => number,
        _ => f64::NAN,
    }))
}

const NANOSECONDS_PER_DAY: i128 = 86_400_000_000_000;

fn time_nanoseconds(time: PlainTime) -> i128 {
    let seconds =
        i128::from(time.hour) * 3600 + i128::from(time.minute) * 60 + i128::from(time.second);
    seconds * 1_000_000_000
        + i128::from(time.millisecond) * 1_000_000
        + i128::from(time.microsecond) * 1000
        + i128::from(time.nanosecond)
}

fn noon(date: PlainDate) -> i128 {
    i128::from(date.epoch_days()) * NANOSECONDS_PER_DAY + NANOSECONDS_PER_DAY / 2
}

/// HandleDateTimeValue for a Temporal object: its formatter and instant, after
/// the checks each type's calendar must pass.
pub(super) fn temporal_value<H: Host>(
    machine: &mut Machine<'_, H>,
    format: &DateTimeFormat,
    record: &TemporalObject,
) -> Result<(TemporalFormatKind, i128), EvalFailure> {
    let calendar = format.resolved_options().calendar.clone();
    let check = |machine: &mut Machine<'_, H>, name: &str, iso_allowed: bool| {
        if name == calendar || (iso_allowed && name == "iso8601") {
            Ok(())
        } else {
            let message = format!("calendar {name} does not match the formatter's {calendar}");
            Err(range_error(machine, message))
        }
    };
    Ok(match record {
        TemporalObject::PlainDate { value, calendar } => {
            check(machine, calendar.as_str(), true)?;
            (TemporalFormatKind::PlainDate, noon(*value))
        }
        TemporalObject::PlainDateTime { value, calendar } => {
            check(machine, calendar.as_str(), true)?;
            let days = i128::from(value.date.epoch_days());
            let nanoseconds = days * NANOSECONDS_PER_DAY + time_nanoseconds(value.time);
            (TemporalFormatKind::PlainDateTime, nanoseconds)
        }
        TemporalObject::PlainYearMonth { value, calendar } => {
            check(machine, calendar.as_str(), false)?;
            let days = epoch_days_from_ymd(value.year, value.month, value.reference_day());
            let nanoseconds = i128::from(days) * NANOSECONDS_PER_DAY + NANOSECONDS_PER_DAY / 2;
            (TemporalFormatKind::PlainYearMonth, nanoseconds)
        }
        TemporalObject::PlainMonthDay { value, calendar } => {
            check(machine, calendar.as_str(), false)?;
            let days = epoch_days_from_ymd(value.reference_year(), value.month, value.day);
            let nanoseconds = i128::from(days) * NANOSECONDS_PER_DAY + NANOSECONDS_PER_DAY / 2;
            (TemporalFormatKind::PlainMonthDay, nanoseconds)
        }
        TemporalObject::PlainTime(value) => {
            (TemporalFormatKind::PlainTime, time_nanoseconds(*value))
        }
        TemporalObject::Instant(value) => (TemporalFormatKind::Instant, value.epoch_nanoseconds()),
        TemporalObject::ZonedDateTime(_) | TemporalObject::Duration(_) => {
            return Err(type_error(
                machine,
                "Temporal.ZonedDateTime is not formattable here",
            ));
        }
    })
}

fn format_parts<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    value: &Formattable,
) -> Result<Vec<DateTimePart>, EvalFailure> {
    let Some(format) = this_format(machine, this)? else {
        return Err(not_a_date_time_format(machine));
    };
    let parts = match value {
        Formattable::Time(date) => format.format_to_parts(*date, &*DATA).map(Some),
        Formattable::Temporal(record) => {
            let format = format.clone();
            let (kind, instant) = temporal_value(machine, &format, record)?;
            format.format_temporal_to_parts(kind, instant, &*DATA)
        }
    };
    match parts.map_err(|error| date_failure(machine, &error))? {
        Some(parts) => Ok(parts),
        None => Err(type_error(
            machine,
            "this formatter's options do not apply to the value",
        )),
    }
}

/// The function `format` hands out, bound to its DateTimeFormat.
fn format_value<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = to_formattable(machine, arg(args, 0))?;
    let parts = format_parts(machine, this, &value)?;
    let text: String = parts.iter().map(|part| part.value.as_str()).collect();
    string_outcome(machine, &text)
}

fn format_to_parts<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if this_format(machine, this)?.is_none() {
        return Err(not_a_date_time_format(machine));
    }
    let value = to_formattable(machine, arg(args, 0))?;
    let parts = format_parts(machine, this, &value)?;
    let mut elements = Vec::with_capacity(parts.len());
    for part in &parts {
        elements.push(part_object(
            machine,
            part.part_type.as_str(),
            &part.value,
            None,
        )?);
    }
    super::super::allocate_array(machine, elements).map(BuiltinOutcome::Value)
}

/// PartitionDateTimeRangePattern's dispatch on what the two ends are.
fn range_parts<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
) -> Result<Vec<DateTimeRangePart>, EvalFailure> {
    if this_format(machine, this)?.is_none() {
        return Err(not_a_date_time_format(machine));
    }
    let (start, end) = (arg(args, 0), arg(args, 1));
    if start == Value::UNDEFINED || end == Value::UNDEFINED {
        return Err(type_error(machine, "a range needs two ends"));
    }
    let start = to_formattable(machine, start)?;
    let end = to_formattable(machine, end)?;
    let Some(format) = this_format(machine, this)? else {
        return Err(not_a_date_time_format(machine));
    };
    let format = format.clone();
    let parts = match (&start, &end) {
        (Formattable::Time(start), Formattable::Time(end)) => {
            format.format_range_to_parts(*start, *end, &*DATA).map(Some)
        }
        (Formattable::Temporal(first), Formattable::Temporal(second)) => {
            let (kind, start) = temporal_value(machine, &format, first)?;
            let (other, end) = temporal_value(machine, &format, second)?;
            if kind != other {
                return Err(type_error(machine, "a range needs two ends of one type"));
            }
            format.format_temporal_range_to_parts(kind, start, end, &*DATA)
        }
        _ => return Err(type_error(machine, "a range needs two ends of one type")),
    };
    match parts.map_err(|error| date_failure(machine, &error))? {
        Some(parts) => Ok(parts),
        None => Err(type_error(
            machine,
            "this formatter's options do not apply to the value",
        )),
    }
}

fn format_range<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let parts = range_parts(machine, this, args)?;
    let text: String = parts.iter().map(|part| part.value.as_str()).collect();
    string_outcome(machine, &text)
}

const fn source_name(source: RangeSource) -> &'static str {
    match source {
        RangeSource::Shared => "shared",
        RangeSource::StartRange => "startRange",
        RangeSource::EndRange => "endRange",
    }
}

fn format_range_to_parts<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let parts = range_parts(machine, this, args)?;
    let mut elements = Vec::with_capacity(parts.len());
    for part in &parts {
        elements.push(part_object(
            machine,
            part.part_type.as_str(),
            &part.value,
            Some(("source", source_name(part.source))),
        )?);
    }
    super::super::allocate_array(machine, elements).map(BuiltinOutcome::Value)
}

const fn width_name(width: TextWidth) -> &'static str {
    match width {
        TextWidth::Narrow => "narrow",
        TextWidth::Short => "short",
        TextWidth::Long => "long",
    }
}

const fn numeric_name(style: NumericStyle) -> &'static str {
    match style {
        NumericStyle::Numeric => "numeric",
        NumericStyle::TwoDigit => "2-digit",
    }
}

const fn month_name(style: MonthStyle) -> &'static str {
    match style {
        MonthStyle::Numeric => "numeric",
        MonthStyle::TwoDigit => "2-digit",
        MonthStyle::Narrow => "narrow",
        MonthStyle::Short => "short",
        MonthStyle::Long => "long",
    }
}

const fn zone_name(style: TimeZoneNameStyle) -> &'static str {
    match style {
        TimeZoneNameStyle::Short => "short",
        TimeZoneNameStyle::Long => "long",
        TimeZoneNameStyle::ShortOffset => "shortOffset",
        TimeZoneNameStyle::LongOffset => "longOffset",
        TimeZoneNameStyle::ShortGeneric => "shortGeneric",
        TimeZoneNameStyle::LongGeneric => "longGeneric",
    }
}

const fn style_name(style: DateTimeStyle) -> &'static str {
    match style {
        DateTimeStyle::Full => "full",
        DateTimeStyle::Long => "long",
        DateTimeStyle::Medium => "medium",
        DateTimeStyle::Short => "short",
    }
}

fn resolved_options<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let format = unwrap_legacy_instance(machine, this, IntlKind::DateTimeFormat)?;
    let Some(format) = this_format(machine, format)? else {
        return Err(not_a_date_time_format(machine));
    };
    let resolved = format.resolved_options().clone();
    let result = new_object(machine)?;
    let text = |machine: &mut Machine<'_, H>, name: &str, value: &str| {
        let value = string_value(machine, value)?;
        define_field(machine, result, name, value)
    };
    text(machine, "locale", &resolved.locale)?;
    text(machine, "calendar", &resolved.calendar)?;
    text(machine, "numberingSystem", &resolved.numbering_system)?;
    text(machine, "timeZone", &resolved.time_zone)?;
    if let Some(cycle) = resolved.hour_cycle {
        text(machine, "hourCycle", cycle.as_str())?;
    }
    if let Some(hour12) = resolved.hour12 {
        define_field(machine, result, "hour12", Value::boolean(hour12))?;
    }
    let components = &resolved.components;
    let fields = [
        ("weekday", components.weekday.map(width_name)),
        ("era", components.era.map(width_name)),
        ("year", components.year.map(numeric_name)),
        ("month", components.month.map(month_name)),
        ("day", components.day.map(numeric_name)),
        ("dayPeriod", components.day_period.map(width_name)),
        ("hour", components.hour.map(numeric_name)),
        ("minute", components.minute.map(numeric_name)),
        ("second", components.second.map(numeric_name)),
    ];
    for (name, value) in fields {
        if let Some(value) = value {
            text(machine, name, value)?;
        }
    }
    if let Some(digits) = components.fractional_second_digits {
        define_field(
            machine,
            result,
            "fractionalSecondDigits",
            crate::number_value(f64::from(digits)),
        )?;
    }
    if let Some(name) = components.time_zone_name {
        text(machine, "timeZoneName", zone_name(name))?;
    }
    if let Some(style) = resolved.date_style {
        text(machine, "dateStyle", style_name(style))?;
    }
    if let Some(style) = resolved.time_style {
        text(machine, "timeStyle", style_name(style))?;
    }
    Ok(BuiltinOutcome::Value(result))
}
