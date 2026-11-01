//! Conversions from JavaScript values to Temporal records: the `To*` abstract
//! operations and the calendar field protocol. Property reads and their
//! conversions happen here, in the sorted order test262 observes.

use bamts_native::Value;

use super::super::value_number;
use super::options::Options;
use super::{OrThrow, is_object, range_error, temporal_record, type_error};
use crate::temporal::TemporalObject;
use crate::temporal::instant_duration::{Duration, Overflow};
use crate::temporal::parse::{
    UtcOffsetRecord, parse_calendar_string, parse_date_time_string, parse_date_time_utc_offset,
    parse_time_zone_string,
};
use crate::temporal::plain_types::{PlainDate, PlainDateTime, PlainTime};
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

impl CalendarFields {}

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

/// ToTemporalDuration.
pub(super) fn to_temporal_duration<H: Host>(
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
