//! Conversions from JavaScript values to Temporal records: the `To*` abstract
//! operations and the calendar field protocol. Property reads and their
//! conversions happen here, in the sorted order test262 observes.

use bamts_native::Value;

use super::super::value_number;
use super::options::{
    Options, disambiguation_option, get_options_object, offset_option, overflow_option,
};
use super::{OrThrow, is_object, range_error, temporal_record, type_error};
use crate::temporal::TemporalObject;
use crate::temporal::instant_duration::{Duration, Instant, Overflow};
use crate::temporal::parse::{
    UtcOffsetRecord, parse_calendar_string, parse_date_time_string, parse_date_time_utc_offset,
    parse_month_day_string, parse_time_zone_string, parse_year_month_string,
};
use crate::temporal::plain_types::{
    MONTH_DAY_REFERENCE_YEAR, PlainDate, PlainDateTime, PlainMonthDay, PlainTime, PlainYearMonth,
    regulate_iso_date,
};
use crate::temporal::zoned_date_time::{
    CalendarId, Disambiguation, FixedOffsetTimeZones, IsoCalendarProvider, OffsetMatch,
    OffsetOption, ResolveOptions, TemporalProviders, TimeZoneId, UtcOffsetNanoseconds,
    ZonedDateTime, start_of_day,
};
use crate::{EvalFailure, Host, Machine};

/// The providers behind every Temporal operation in this runtime.
pub(super) fn providers() -> TemporalProviders<'static> {
    TemporalProviders::new(&FixedOffsetTimeZones, &IsoCalendarProvider)
}

fn to_number<H: Host>(machine: &mut Machine<'_, H>, value: Value) -> Result<f64, EvalFailure> {
    Ok(value_number(machine.coerce_number_observable(value)?))
}

/// ToIntegerWithTruncation.
pub(super) fn to_integer_with_truncation<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<f64, EvalFailure> {
    let number = to_number(machine, value)?;
    if !number.is_finite() {
        return Err(range_error(machine, "value must be a finite number"));
    }
    Ok(number.trunc() + 0.0)
}

/// ToPositiveIntegerWithTruncation.
fn to_positive_integer_with_truncation<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<f64, EvalFailure> {
    let integer = to_integer_with_truncation(machine, value)?;
    if integer <= 0.0 {
        return Err(range_error(machine, "value must be a positive integer"));
    }
    Ok(integer)
}

/// ToIntegerIfIntegral. A magnitude past every valid Duration field clamps,
/// staying invalid for the range check that runs after all fields are read.
pub(super) fn to_integer_if_integral<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<i128, EvalFailure> {
    let number = to_number(machine, value)?;
    if !number.is_finite() || number.trunc() != number {
        return Err(range_error(machine, "value must be an integer"));
    }
    Ok(number.clamp(-1e30, 1e30) as i128)
}

/// A string argument's text, or the `TypeError` for anything else.
fn require_string<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    what: &str,
) -> Result<String, EvalFailure> {
    match machine.string_value(value) {
        Some(text) => Ok(text.to_utf8_lossy()),
        None => Err(type_error(machine, format!("{what} must be a string"))),
    }
}

/// CanonicalizeCalendar of a parsed annotation, ISO when there is none.
fn parsed_calendar<H: Host>(
    machine: &mut Machine<'_, H>,
    parsed: &crate::temporal::parse::ParsedIsoDateTime,
) -> Result<CalendarId, EvalFailure> {
    parsed.calendar_id().or_throw(machine)
}

/// The `calendar` constructor argument: a string naming a calendar exactly.
pub(super) fn calendar_argument<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<CalendarId, EvalFailure> {
    if value == Value::UNDEFINED {
        return Ok(CalendarId::iso8601());
    }
    let text = require_string(machine, value, "calendar")?;
    CalendarId::canonicalize(&text).or_throw(machine)
}

/// ToTemporalCalendarIdentifier.
pub(super) fn to_calendar_identifier<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<CalendarId, EvalFailure> {
    if let Some(record) = temporal_record(machine, value)?
        && let Some(calendar) = record.calendar()
    {
        return Ok(calendar);
    }
    let text = require_string(machine, value, "calendar")?;
    let identifier = parse_calendar_string(&text).or_throw(machine)?;
    CalendarId::canonicalize(&identifier).or_throw(machine)
}

/// GetTemporalCalendarIdentifierWithISODefault.
fn calendar_with_iso_default<H: Host>(
    machine: &mut Machine<'_, H>,
    item: Value,
) -> Result<CalendarId, EvalFailure> {
    let calendar = machine.get_named_property(item, "calendar")?;
    if calendar == Value::UNDEFINED {
        Ok(CalendarId::iso8601())
    } else {
        to_calendar_identifier(machine, calendar)
    }
}

/// ToTemporalTimeZoneIdentifier.
pub(super) fn to_time_zone_identifier<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<TimeZoneId, EvalFailure> {
    if let Some(TemporalObject::ZonedDateTime(zoned)) = temporal_record(machine, value)? {
        return Ok(zoned.time_zone_id().clone());
    }
    let text = require_string(machine, value, "time zone")?;
    let parsed = parse_time_zone_string(&text).or_throw(machine)?;
    TimeZoneId::from_parsed(parsed).or_throw(machine)
}

/// A set of calendar fields, named as `PrepareCalendarFields` lists them.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct FieldNames(u16);

impl FieldNames {
    pub(super) const NONE: Self = Self(0);
    pub(super) const DAY: Self = Self(1 << 0);
    const HOUR: Self = Self(1 << 1);
    const MICROSECOND: Self = Self(1 << 2);
    const MILLISECOND: Self = Self(1 << 3);
    const MINUTE: Self = Self(1 << 4);
    const MONTH: Self = Self(1 << 5);
    const MONTH_CODE: Self = Self(1 << 6);
    const NANOSECOND: Self = Self(1 << 7);
    pub(super) const OFFSET: Self = Self(1 << 8);
    const SECOND: Self = Self(1 << 9);
    pub(super) const TIME_ZONE: Self = Self(1 << 10);
    pub(super) const YEAR: Self = Self(1 << 11);

    /// «year, month, month-code, day»
    pub(super) const DATE: Self =
        Self(Self::YEAR.0 | Self::MONTH.0 | Self::MONTH_CODE.0 | Self::DAY.0);
    /// «year, month, month-code»
    pub(super) const YEAR_MONTH: Self = Self(Self::YEAR.0 | Self::MONTH.0 | Self::MONTH_CODE.0);
    /// «hour, minute, second, millisecond, microsecond, nanosecond»
    pub(super) const TIME: Self = Self(
        Self::HOUR.0
            | Self::MINUTE.0
            | Self::SECOND.0
            | Self::MILLISECOND.0
            | Self::MICROSECOND.0
            | Self::NANOSECOND.0,
    );

    pub(super) const fn with(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    const fn contains(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

/// Calendar Fields Record. Absent fields are `None`; time fields default to
/// zero when read. Numbers stay `f64` until resolution, so an enormous year is
/// rejected there, after every property has been read.
#[derive(Clone, Debug, Default, PartialEq)]
pub(super) struct CalendarFields {
    pub(super) year: Option<f64>,
    pub(super) month: Option<f64>,
    pub(super) month_code: Option<String>,
    pub(super) day: Option<f64>,
    pub(super) hour: Option<f64>,
    pub(super) minute: Option<f64>,
    pub(super) second: Option<f64>,
    pub(super) millisecond: Option<f64>,
    pub(super) microsecond: Option<f64>,
    pub(super) nanosecond: Option<f64>,
    pub(super) offset: Option<i128>,
    pub(super) time_zone: Option<TimeZoneId>,
}

impl CalendarFields {
    /// ISODateToFields of type `date`.
    pub(super) fn from_date(date: PlainDate) -> Self {
        Self {
            year: Some(f64::from(date.year)),
            month_code: Some(format!("M{:02}", date.month)),
            day: Some(f64::from(date.day)),
            ..Self::default()
        }
    }

    /// ISODateToFields of type `year-month`.
    pub(super) fn from_year_month(value: PlainYearMonth) -> Self {
        Self {
            year: Some(f64::from(value.year)),
            month_code: Some(format!("M{:02}", value.month)),
            ..Self::default()
        }
    }

    /// ISODateToFields of type `month-day`.
    pub(super) fn from_month_day(value: PlainMonthDay) -> Self {
        Self {
            month_code: Some(value.month_code()),
            day: Some(f64::from(value.day)),
            ..Self::default()
        }
    }

    pub(super) fn with_time(mut self, time: PlainTime) -> Self {
        self.hour = Some(f64::from(time.hour));
        self.minute = Some(f64::from(time.minute));
        self.second = Some(f64::from(time.second));
        self.millisecond = Some(f64::from(time.millisecond));
        self.microsecond = Some(f64::from(time.microsecond));
        self.nanosecond = Some(f64::from(time.nanosecond));
        self
    }

    /// CalendarMergeFields: `month` and `monthCode` replace each other as one
    /// field, so a new `month` cannot conflict with an inherited `monthCode`.
    pub(super) fn merged_with(mut self, additional: Self) -> Self {
        if additional.month.is_some() || additional.month_code.is_some() {
            self.month = None;
            self.month_code = None;
        }
        macro_rules! merge {
            ($($field:ident),+) => {
                $(if additional.$field.is_some() {
                    self.$field = additional.$field;
                })+
            };
        }
        merge!(
            year,
            month,
            month_code,
            day,
            hour,
            minute,
            second,
            millisecond,
            microsecond,
            nanosecond,
            offset,
            time_zone
        );
        self
    }
}

/// ToMonthCode.
fn to_month_code<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<String, EvalFailure> {
    let primitive = machine.coerce_primitive_observable(value, true)?;
    let text = require_string(machine, primitive, "monthCode")?;
    let bytes = text.as_bytes();
    let well_formed = matches!(bytes.len(), 3 | 4)
        && bytes[0] == b'M'
        && bytes[1].is_ascii_digit()
        && bytes[2].is_ascii_digit()
        && (bytes.len() == 3 || bytes[3] == b'L')
        && (bytes.len() == 4 || &text[1..3] != "00");
    if well_formed {
        Ok(text)
    } else {
        Err(range_error(machine, format!("invalid month code {text}")))
    }
}

/// ToOffsetString, keeping the value it validates.
fn to_offset_nanoseconds<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<i128, EvalFailure> {
    let primitive = machine.coerce_primitive_observable(value, true)?;
    let text = require_string(machine, primitive, "offset")?;
    parse_date_time_utc_offset(&text).or_throw(machine)
}

/// PrepareCalendarFields with a list of required fields, possibly empty.
pub(super) fn prepare_calendar_fields<H: Host>(
    machine: &mut Machine<'_, H>,
    item: Value,
    names: FieldNames,
    required: FieldNames,
) -> Result<CalendarFields, EvalFailure> {
    read_calendar_fields(machine, item, names, required).map(|(fields, _)| fields)
}

/// PrepareCalendarFields with `partial`: at least one listed field must exist.
pub(super) fn prepare_partial_fields<H: Host>(
    machine: &mut Machine<'_, H>,
    item: Value,
    names: FieldNames,
) -> Result<CalendarFields, EvalFailure> {
    let (fields, any) = read_calendar_fields(machine, item, names, FieldNames::NONE)?;
    if any {
        Ok(fields)
    } else {
        Err(type_error(machine, "no recognized properties were present"))
    }
}

/// The ISO calendar's field list has no `era`. Reads go in sorted property-name
/// order and each value converts as soon as it is read, so a throwing `valueOf`
/// stops every later read. Also reports whether any field was present.
fn read_calendar_fields<H: Host>(
    machine: &mut Machine<'_, H>,
    item: Value,
    names: FieldNames,
    required: FieldNames,
) -> Result<(CalendarFields, bool), EvalFailure> {
    let mut fields = CalendarFields::default();
    let mut any = false;
    let table = [
        ("day", FieldNames::DAY),
        ("hour", FieldNames::HOUR),
        ("microsecond", FieldNames::MICROSECOND),
        ("millisecond", FieldNames::MILLISECOND),
        ("minute", FieldNames::MINUTE),
        ("month", FieldNames::MONTH),
        ("monthCode", FieldNames::MONTH_CODE),
        ("nanosecond", FieldNames::NANOSECOND),
        ("offset", FieldNames::OFFSET),
        ("second", FieldNames::SECOND),
        ("timeZone", FieldNames::TIME_ZONE),
        ("year", FieldNames::YEAR),
    ];
    for (name, field) in table {
        if !names.contains(field) {
            continue;
        }
        let value = machine.get_named_property(item, name)?;
        if value == Value::UNDEFINED {
            if required.contains(field) {
                return Err(type_error(machine, format!("{name} is required")));
            }
            continue;
        }
        any = true;
        match field {
            FieldNames::DAY => {
                fields.day = Some(to_positive_integer_with_truncation(machine, value)?);
            }
            FieldNames::MONTH => {
                fields.month = Some(to_positive_integer_with_truncation(machine, value)?);
            }
            FieldNames::MONTH_CODE => fields.month_code = Some(to_month_code(machine, value)?),
            FieldNames::OFFSET => fields.offset = Some(to_offset_nanoseconds(machine, value)?),
            FieldNames::TIME_ZONE => {
                fields.time_zone = Some(to_time_zone_identifier(machine, value)?);
            }
            FieldNames::YEAR => fields.year = Some(to_integer_with_truncation(machine, value)?),
            FieldNames::HOUR => fields.hour = Some(to_integer_with_truncation(machine, value)?),
            FieldNames::MICROSECOND => {
                fields.microsecond = Some(to_integer_with_truncation(machine, value)?);
            }
            FieldNames::MILLISECOND => {
                fields.millisecond = Some(to_integer_with_truncation(machine, value)?);
            }
            FieldNames::MINUTE => fields.minute = Some(to_integer_with_truncation(machine, value)?),
            FieldNames::NANOSECOND => {
                fields.nanosecond = Some(to_integer_with_truncation(machine, value)?);
            }
            _ => fields.second = Some(to_integer_with_truncation(machine, value)?),
        }
    }
    Ok((fields, any))
}

/// An ISO year as the core stores it. Any year this far out is outside the
/// representable range, whatever overflow says.
pub(super) fn iso_year<H: Host>(
    machine: &mut Machine<'_, H>,
    year: f64,
) -> Result<i32, EvalFailure> {
    if year.abs() > 1_000_000.0 {
        return Err(range_error(machine, "year outside the representable range"));
    }
    Ok(year as i32)
}

/// CalendarResolveFields for the ISO calendar's month: `monthCode` must name a
/// real ISO month and agree with `month` when both are given.
fn resolve_month<H: Host>(
    machine: &mut Machine<'_, H>,
    fields: &CalendarFields,
) -> Result<f64, EvalFailure> {
    let Some(code) = &fields.month_code else {
        return match fields.month {
            Some(month) => Ok(month),
            None => Err(type_error(machine, "month or monthCode is required")),
        };
    };
    let number = (code.len() == 3)
        .then(|| code[1..].parse::<u8>().ok())
        .flatten()
        .filter(|month| (1..=12).contains(month));
    let Some(number) = number else {
        return Err(range_error(
            machine,
            format!("{code} is not a month of the ISO calendar"),
        ));
    };
    let number = f64::from(number);
    if fields.month.is_some_and(|month| month != number) {
        return Err(range_error(machine, "month and monthCode do not agree"));
    }
    Ok(number)
}

/// CalendarResolveFields for a date: the year, month, and day it will regulate.
pub(super) fn resolved_date_fields<H: Host>(
    machine: &mut Machine<'_, H>,
    fields: &CalendarFields,
) -> Result<(i32, i64, i64), EvalFailure> {
    let Some(year) = fields.year else {
        return Err(type_error(machine, "year is required"));
    };
    let Some(day) = fields.day else {
        return Err(type_error(machine, "day is required"));
    };
    let month = resolve_month(machine, fields)?;
    Ok((iso_year(machine, year)?, month as i64, day as i64))
}

/// CalendarDateFromFields.
pub(super) fn date_from_fields<H: Host>(
    machine: &mut Machine<'_, H>,
    fields: &CalendarFields,
    overflow: Overflow,
) -> Result<PlainDate, EvalFailure> {
    let (year, month, day) = resolved_date_fields(machine, fields)?;
    PlainDate::new(year, month, day, overflow).or_throw(machine)
}

/// CalendarYearMonthFromFields.
pub(super) fn year_month_from_fields<H: Host>(
    machine: &mut Machine<'_, H>,
    fields: &CalendarFields,
    overflow: Overflow,
) -> Result<PlainYearMonth, EvalFailure> {
    let Some(year) = fields.year else {
        return Err(type_error(machine, "year is required"));
    };
    let month = resolve_month(machine, fields)?;
    let year = iso_year(machine, year)?;
    PlainYearMonth::new(year, month as i64, overflow).or_throw(machine)
}

/// CalendarMonthDayFromFields. A `year`, when given, only decides which days
/// the month has, and only its leap-ness matters: the result carries the
/// reference year, so no year is too large to consult.
pub(super) fn month_day_from_fields<H: Host>(
    machine: &mut Machine<'_, H>,
    fields: &CalendarFields,
    overflow: Overflow,
) -> Result<PlainMonthDay, EvalFailure> {
    let Some(day) = fields.day else {
        return Err(type_error(machine, "day is required"));
    };
    let month = resolve_month(machine, fields)?;
    let year = fields.year.map_or(MONTH_DAY_REFERENCE_YEAR, |year| {
        year.rem_euclid(400.0) as i32 + 2000
    });
    let (_, month, day) =
        regulate_iso_date(year, month as i64, day as i64, overflow).or_throw(machine)?;
    PlainMonthDay::new(month.into(), day.into(), Overflow::Reject).or_throw(machine)
}

/// RegulateTime over a fields record; absent fields are zero.
pub(super) fn time_from_fields<H: Host>(
    machine: &mut Machine<'_, H>,
    fields: &CalendarFields,
    overflow: Overflow,
) -> Result<PlainTime, EvalFailure> {
    let field = |value: Option<f64>| value.unwrap_or(0.0) as i64;
    PlainTime::new(
        field(fields.hour),
        field(fields.minute),
        field(fields.second),
        field(fields.millisecond),
        field(fields.microsecond),
        field(fields.nanosecond),
        overflow,
    )
    .or_throw(machine)
}

/// InterpretTemporalDateTimeFields. The result is a record, with no limit of
/// its own; whoever creates an object from it applies that object's limit.
pub(super) fn date_time_from_fields<H: Host>(
    machine: &mut Machine<'_, H>,
    fields: &CalendarFields,
    overflow: Overflow,
) -> Result<PlainDateTime, EvalFailure> {
    let date = date_from_fields(machine, fields, overflow)?;
    let time = time_from_fields(machine, fields, overflow)?;
    Ok(PlainDateTime { date, time })
}

/// IsPartialTemporalObject.
pub(super) fn require_partial_temporal_object<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<(), EvalFailure> {
    if !is_object(machine, value)? {
        return Err(type_error(machine, "argument must be an object"));
    }
    if let Some(record) = temporal_record(machine, value)?
        && !matches!(
            record,
            TemporalObject::Instant(_) | TemporalObject::Duration(_)
        )
    {
        return Err(type_error(
            machine,
            "argument must not be a Temporal object",
        ));
    }
    for name in ["calendar", "timeZone"] {
        let property = machine.get_named_property(value, name)?;
        if property != Value::UNDEFINED {
            return Err(type_error(
                machine,
                format!("argument must not have a {name} property"),
            ));
        }
    }
    Ok(())
}

/// Reads and validates the options of a `from` whose argument needs no fields,
/// discarding the value: the read itself is the observable part.
fn read_overflow<H: Host>(machine: &mut Machine<'_, H>, options: Value) -> Result<(), EvalFailure> {
    let resolved = get_options_object(machine, options)?;
    overflow_option(machine, resolved)?;
    Ok(())
}

/// ToTemporalDate. `options` is `undefined` when the caller has none.
pub(super) fn to_temporal_date<H: Host>(
    machine: &mut Machine<'_, H>,
    item: Value,
    options: Value,
) -> Result<(PlainDate, CalendarId), EvalFailure> {
    if is_object(machine, item)? {
        match temporal_record(machine, item)? {
            Some(TemporalObject::PlainDate { value, calendar }) => {
                read_overflow(machine, options)?;
                return Ok((value, calendar));
            }
            Some(TemporalObject::ZonedDateTime(zoned)) => {
                let local = zoned
                    .to_plain_date_time(&FixedOffsetTimeZones)
                    .or_throw(machine)?;
                read_overflow(machine, options)?;
                return Ok((local.date, zoned.calendar_id().clone()));
            }
            Some(TemporalObject::PlainDateTime { value, calendar }) => {
                read_overflow(machine, options)?;
                return Ok((value.date, calendar));
            }
            _ => {}
        }
        let calendar = calendar_with_iso_default(machine, item)?;
        let fields = prepare_calendar_fields(machine, item, FieldNames::DATE, FieldNames::NONE)?;
        let resolved = get_options_object(machine, options)?;
        let overflow = overflow_option(machine, resolved)?;
        let date = date_from_fields(machine, &fields, overflow)?;
        return Ok((date, calendar));
    }
    let text = require_string(machine, item, "date")?;
    let parsed = parse_date_time_string(&text, false).or_throw(machine)?;
    let calendar = parsed_calendar(machine, &parsed)?;
    read_overflow(machine, options)?;
    let date = PlainDate::from_parsed(&parsed).or_throw(machine)?;
    Ok((date, calendar))
}

/// ToTemporalDateTime.
pub(super) fn to_temporal_date_time<H: Host>(
    machine: &mut Machine<'_, H>,
    item: Value,
    options: Value,
) -> Result<(PlainDateTime, CalendarId), EvalFailure> {
    if is_object(machine, item)? {
        match temporal_record(machine, item)? {
            Some(TemporalObject::PlainDateTime { value, calendar }) => {
                read_overflow(machine, options)?;
                return Ok((value, calendar));
            }
            Some(TemporalObject::ZonedDateTime(zoned)) => {
                let local = zoned
                    .to_plain_date_time(&FixedOffsetTimeZones)
                    .or_throw(machine)?;
                read_overflow(machine, options)?;
                return Ok((local, zoned.calendar_id().clone()));
            }
            Some(TemporalObject::PlainDate { value, calendar }) => {
                read_overflow(machine, options)?;
                let local =
                    PlainDateTime::from_parts(value, PlainTime::midnight()).or_throw(machine)?;
                return Ok((local, calendar));
            }
            _ => {}
        }
        let calendar = calendar_with_iso_default(machine, item)?;
        let names = FieldNames::DATE.with(FieldNames::TIME);
        let fields = prepare_calendar_fields(machine, item, names, FieldNames::NONE)?;
        let resolved = get_options_object(machine, options)?;
        let overflow = overflow_option(machine, resolved)?;
        let value = date_time_from_fields(machine, &fields, overflow)?;
        let value = PlainDateTime::from_parts(value.date, value.time).or_throw(machine)?;
        return Ok((value, calendar));
    }
    let text = require_string(machine, item, "date-time")?;
    let parsed = parse_date_time_string(&text, false).or_throw(machine)?;
    let calendar = parsed_calendar(machine, &parsed)?;
    read_overflow(machine, options)?;
    let value = PlainDateTime::from_parsed(&parsed).or_throw(machine)?;
    Ok((value, calendar))
}

/// ToTemporalTime.
pub(super) fn to_temporal_time<H: Host>(
    machine: &mut Machine<'_, H>,
    item: Value,
    options: Value,
) -> Result<PlainTime, EvalFailure> {
    if is_object(machine, item)? {
        match temporal_record(machine, item)? {
            Some(TemporalObject::PlainTime(value)) => {
                read_overflow(machine, options)?;
                return Ok(value);
            }
            Some(TemporalObject::PlainDateTime { value, .. }) => {
                read_overflow(machine, options)?;
                return Ok(value.time);
            }
            Some(TemporalObject::ZonedDateTime(zoned)) => {
                let time = zoned
                    .to_plain_time(&FixedOffsetTimeZones)
                    .or_throw(machine)?;
                read_overflow(machine, options)?;
                return Ok(time);
            }
            _ => {}
        }
        let fields = prepare_partial_fields(machine, item, FieldNames::TIME)?;
        let resolved = get_options_object(machine, options)?;
        let overflow = overflow_option(machine, resolved)?;
        return time_from_fields(machine, &fields, overflow);
    }
    let text = require_string(machine, item, "time")?;
    let time = PlainTime::parse(&text).or_throw(machine)?;
    read_overflow(machine, options)?;
    Ok(time)
}

/// ToTemporalYearMonth.
pub(super) fn to_temporal_year_month<H: Host>(
    machine: &mut Machine<'_, H>,
    item: Value,
    options: Value,
) -> Result<(PlainYearMonth, CalendarId), EvalFailure> {
    if is_object(machine, item)? {
        if let Some(TemporalObject::PlainYearMonth { value, calendar }) =
            temporal_record(machine, item)?
        {
            read_overflow(machine, options)?;
            return Ok((value, calendar));
        }
        let calendar = calendar_with_iso_default(machine, item)?;
        let fields =
            prepare_calendar_fields(machine, item, FieldNames::YEAR_MONTH, FieldNames::NONE)?;
        let resolved = get_options_object(machine, options)?;
        let overflow = overflow_option(machine, resolved)?;
        let value = year_month_from_fields(machine, &fields, overflow)?;
        return Ok((value, calendar));
    }
    let text = require_string(machine, item, "year-month")?;
    let parsed = parse_year_month_string(&text).or_throw(machine)?;
    let calendar = parsed_calendar(machine, &parsed)?;
    read_overflow(machine, options)?;
    let value = PlainYearMonth::from_parsed(&parsed).or_throw(machine)?;
    Ok((value, calendar))
}

/// ToTemporalMonthDay.
pub(super) fn to_temporal_month_day<H: Host>(
    machine: &mut Machine<'_, H>,
    item: Value,
    options: Value,
) -> Result<(PlainMonthDay, CalendarId), EvalFailure> {
    if is_object(machine, item)? {
        if let Some(TemporalObject::PlainMonthDay { value, calendar }) =
            temporal_record(machine, item)?
        {
            read_overflow(machine, options)?;
            return Ok((value, calendar));
        }
        let calendar = calendar_with_iso_default(machine, item)?;
        let fields = prepare_calendar_fields(machine, item, FieldNames::DATE, FieldNames::NONE)?;
        let resolved = get_options_object(machine, options)?;
        let overflow = overflow_option(machine, resolved)?;
        let value = month_day_from_fields(machine, &fields, overflow)?;
        return Ok((value, calendar));
    }
    let text = require_string(machine, item, "month-day")?;
    let parsed = parse_month_day_string(&text).or_throw(machine)?;
    let calendar = parsed_calendar(machine, &parsed)?;
    read_overflow(machine, options)?;
    let value = PlainMonthDay::from_parsed(&parsed).or_throw(machine)?;
    Ok((value, calendar))
}

/// How `offset` information in the input applies to a wall-clock time.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) enum OffsetBehaviour {
    Option(i128),
    Exact,
    Wall,
}

/// InterpretISODateTimeOffset.
pub(super) fn interpret_offset<H: Host>(
    machine: &mut Machine<'_, H>,
    local: PlainDateTime,
    behaviour: OffsetBehaviour,
    time_zone: TimeZoneId,
    calendar: CalendarId,
    resolve: ResolveOptions,
) -> Result<ZonedDateTime, EvalFailure> {
    let (supplied, offset) = match behaviour {
        OffsetBehaviour::Wall => (None, OffsetOption::Ignore),
        OffsetBehaviour::Exact => (Some(UtcOffsetNanoseconds::UTC), OffsetOption::Use),
        OffsetBehaviour::Option(nanoseconds) => {
            let nanoseconds = i64::try_from(nanoseconds)
                .map_err(|_| range_error(machine, "UTC offset out of range"))?;
            (
                Some(UtcOffsetNanoseconds::new(nanoseconds).or_throw(machine)?),
                resolve.offset,
            )
        }
    };
    ZonedDateTime::from_local(
        &providers(),
        local,
        time_zone,
        calendar,
        supplied,
        ResolveOptions { offset, ..resolve },
    )
    .or_throw(machine)
}

/// ToTemporalZonedDateTime.
pub(super) fn to_temporal_zoned_date_time<H: Host>(
    machine: &mut Machine<'_, H>,
    item: Value,
    options: Value,
) -> Result<ZonedDateTime, EvalFailure> {
    if is_object(machine, item)? {
        if let Some(TemporalObject::ZonedDateTime(zoned)) = temporal_record(machine, item)? {
            let resolved = get_options_object(machine, options)?;
            disambiguation_option(machine, resolved)?;
            offset_option(machine, resolved, OffsetOption::Reject)?;
            overflow_option(machine, resolved)?;
            return Ok(zoned);
        }
        let calendar = calendar_with_iso_default(machine, item)?;
        let names = FieldNames::DATE
            .with(FieldNames::TIME)
            .with(FieldNames::OFFSET)
            .with(FieldNames::TIME_ZONE);
        let fields = prepare_calendar_fields(machine, item, names, FieldNames::TIME_ZONE)?;
        let resolved = get_options_object(machine, options)?;
        let disambiguation = disambiguation_option(machine, resolved)?;
        let offset = offset_option(machine, resolved, OffsetOption::Reject)?;
        let overflow = overflow_option(machine, resolved)?;
        let local = date_time_from_fields(machine, &fields, overflow)?;
        let behaviour = fields
            .offset
            .map_or(OffsetBehaviour::Wall, OffsetBehaviour::Option);
        let time_zone = fields.time_zone.clone().expect("timeZone is required");
        return interpret_offset(
            machine,
            local,
            behaviour,
            time_zone,
            calendar,
            ResolveOptions {
                disambiguation,
                offset,
                offset_match: OffsetMatch::Exactly,
            },
        );
    }
    let text = require_string(machine, item, "zoned date-time")?;
    let parsed = parse_date_time_string(&text, true).or_throw(machine)?;
    let annotation = parsed
        .time_zone
        .clone()
        .expect("the zoned goal requires one");
    let time_zone = time_zone_from_annotation(machine, &annotation)?;
    let calendar = parsed_calendar(machine, &parsed)?;
    let resolved = get_options_object(machine, options)?;
    let disambiguation = disambiguation_option(machine, resolved)?;
    let offset = offset_option(machine, resolved, OffsetOption::Reject)?;
    overflow_option(machine, resolved)?;
    zoned_from_parsed(
        machine,
        &parsed,
        time_zone,
        calendar,
        disambiguation,
        offset,
    )
}

fn time_zone_from_annotation<H: Host>(
    machine: &mut Machine<'_, H>,
    annotation: &str,
) -> Result<TimeZoneId, EvalFailure> {
    let parsed = parse_time_zone_string(annotation).or_throw(machine)?;
    TimeZoneId::from_parsed(parsed).or_throw(machine)
}

/// The instant a parsed zoned string names: `Z` is exact, a numeric offset is
/// checked to the minute unless it has seconds, and a bare date means the
/// start of that day.
fn zoned_from_parsed<H: Host>(
    machine: &mut Machine<'_, H>,
    parsed: &crate::temporal::parse::ParsedIsoDateTime,
    time_zone: TimeZoneId,
    calendar: CalendarId,
    disambiguation: Disambiguation,
    offset: OffsetOption,
) -> Result<ZonedDateTime, EvalFailure> {
    let date = PlainDate::from_parsed(parsed).or_throw(machine)?;
    if !parsed.has_time {
        let instant = start_of_day(&FixedOffsetTimeZones, &time_zone, date).or_throw(machine)?;
        return Ok(ZonedDateTime::from_instant(instant, time_zone, calendar));
    }
    let local = PlainDateTime::from_parsed(parsed).or_throw(machine)?;
    let (behaviour, offset_match) = match parsed.offset {
        Some(UtcOffsetRecord::Zulu) => (OffsetBehaviour::Exact, OffsetMatch::Minutes),
        Some(UtcOffsetRecord::Numeric {
            nanoseconds,
            sub_minute,
        }) => (
            OffsetBehaviour::Option(nanoseconds),
            if sub_minute {
                OffsetMatch::Exactly
            } else {
                OffsetMatch::Minutes
            },
        ),
        None => (OffsetBehaviour::Wall, OffsetMatch::Minutes),
    };
    interpret_offset(
        machine,
        local,
        behaviour,
        time_zone,
        calendar,
        ResolveOptions {
            disambiguation,
            offset,
            offset_match,
        },
    )
}

/// ToTemporalInstant.
pub(super) fn to_temporal_instant<H: Host>(
    machine: &mut Machine<'_, H>,
    item: Value,
) -> Result<Instant, EvalFailure> {
    let mut primitive = item;
    if is_object(machine, item)? {
        match temporal_record(machine, item)? {
            Some(TemporalObject::Instant(value)) => return Ok(value),
            Some(TemporalObject::ZonedDateTime(zoned)) => return Ok(zoned.to_instant()),
            _ => {}
        }
        primitive = machine.coerce_primitive_observable(item, true)?;
    }
    let text = require_string(machine, primitive, "instant")?;
    Instant::parse(&text).or_throw(machine)
}

/// ToTemporalDuration.
pub(in crate::intrinsics::builtins) fn to_temporal_duration<H: Host>(
    machine: &mut Machine<'_, H>,
    item: Value,
) -> Result<Duration, EvalFailure> {
    if is_object(machine, item)? {
        if let Some(TemporalObject::Duration(value)) = temporal_record(machine, item)? {
            return Ok(value);
        }
        let partial = to_partial_duration(machine, item)?;
        return Duration::new(partial.map(|field| field.unwrap_or(0))).or_throw(machine);
    }
    let text = require_string(machine, item, "duration")?;
    Duration::parse(&text).or_throw(machine)
}

/// ToTemporalPartialDurationRecord, largest field first. Properties are read in
/// sorted order, each converting immediately.
pub(super) fn to_partial_duration<H: Host>(
    machine: &mut Machine<'_, H>,
    item: Value,
) -> Result<[Option<i128>; 10], EvalFailure> {
    if !is_object(machine, item)? {
        return Err(type_error(machine, "duration-like must be an object"));
    }
    let mut fields = [None; 10];
    let sorted = [
        ("days", 3),
        ("hours", 4),
        ("microseconds", 8),
        ("milliseconds", 7),
        ("minutes", 5),
        ("months", 1),
        ("nanoseconds", 9),
        ("seconds", 6),
        ("weeks", 2),
        ("years", 0),
    ];
    for (name, slot) in sorted {
        let value = machine.get_named_property(item, name)?;
        if value != Value::UNDEFINED {
            fields[slot] = Some(to_integer_if_integral(machine, value)?);
        }
    }
    if fields.iter().all(Option::is_none) {
        return Err(type_error(
            machine,
            "duration-like has no recognized properties",
        ));
    }
    Ok(fields)
}

/// Result of GetTemporalRelativeToOption.
#[derive(Clone, Debug)]
pub(super) enum RelativeTo {
    None,
    Plain(PlainDate, CalendarId),
    Zoned(ZonedDateTime),
}

/// GetTemporalRelativeToOption.
pub(super) fn relative_to_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
) -> Result<RelativeTo, EvalFailure> {
    let value = match options {
        Some(object) => machine.get_named_property(object, "relativeTo")?,
        None => Value::UNDEFINED,
    };
    if value == Value::UNDEFINED {
        return Ok(RelativeTo::None);
    }
    if is_object(machine, value)? {
        match temporal_record(machine, value)? {
            Some(TemporalObject::ZonedDateTime(zoned)) => return Ok(RelativeTo::Zoned(zoned)),
            Some(TemporalObject::PlainDate { value, calendar }) => {
                return Ok(RelativeTo::Plain(value, calendar));
            }
            Some(TemporalObject::PlainDateTime { value, calendar }) => {
                return Ok(RelativeTo::Plain(value.date, calendar));
            }
            _ => {}
        }
        let calendar = calendar_with_iso_default(machine, value)?;
        let names = FieldNames::DATE
            .with(FieldNames::TIME)
            .with(FieldNames::OFFSET)
            .with(FieldNames::TIME_ZONE);
        let fields = prepare_calendar_fields(machine, value, names, FieldNames::NONE)?;
        let local = date_time_from_fields(machine, &fields, Overflow::Constrain)?;
        let Some(time_zone) = fields.time_zone.clone() else {
            return Ok(RelativeTo::Plain(local.date, calendar));
        };
        let behaviour = fields
            .offset
            .map_or(OffsetBehaviour::Wall, OffsetBehaviour::Option);
        return interpret_offset(
            machine,
            local,
            behaviour,
            time_zone,
            calendar,
            ResolveOptions {
                disambiguation: Disambiguation::Compatible,
                offset: OffsetOption::Reject,
                offset_match: OffsetMatch::Exactly,
            },
        )
        .map(RelativeTo::Zoned);
    }
    let Some(text) = machine.string_value(value).map(|text| text.to_utf8_lossy()) else {
        return Err(type_error(machine, "relativeTo must be a string or object"));
    };
    let parsed = parse_date_time_string(&text, true)
        .or_else(|_| parse_date_time_string(&text, false))
        .or_throw(machine)?;
    let Some(annotation) = parsed.time_zone.clone() else {
        let calendar = parsed_calendar(machine, &parsed)?;
        let date = PlainDate::from_parsed(&parsed).or_throw(machine)?;
        return Ok(RelativeTo::Plain(date, calendar));
    };
    let time_zone = time_zone_from_annotation(machine, &annotation)?;
    let calendar = parsed_calendar(machine, &parsed)?;
    zoned_from_parsed(
        machine,
        &parsed,
        time_zone,
        calendar,
        Disambiguation::Compatible,
        OffsetOption::Reject,
    )
    .map(RelativeTo::Zoned)
}
