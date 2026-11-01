use std::collections::BTreeMap;
use std::fmt;

use bamts_bytecode::EcmaString;
use bamts_native::Value;

use super::{
    allocate_string, define_data, install_constructor_function, install_function, range_error,
    type_error, value_number,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap};

const MS_PER_SECOND: f64 = 1_000.0;
const MS_PER_MINUTE: f64 = 60_000.0;
const MS_PER_HOUR: f64 = 3_600_000.0;
const MS_PER_DAY: f64 = 86_400_000.0;
const MAX_TIME_VALUE: f64 = 8_640_000_000_000_000.0;

/// Host timezone configurations understood by the runtime without a bundled tzdb.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DateHostError {
    UnsupportedTimeZone(String),
    InvalidTimeZone(String),
}

impl fmt::Display for DateHostError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedTimeZone(zone) => {
                write!(
                    formatter,
                    "timezone {zone:?} requires an unavailable timezone database"
                )
            }
            Self::InvalidTimeZone(zone) => write!(formatter, "invalid POSIX timezone {zone:?}"),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TransitionRule {
    month: u8,
    week: u8,
    weekday: u8,
    seconds: i32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum TimeZoneRule {
    Fixed {
        offset_seconds: i32,
        name: String,
    },
    Dst {
        standard_offset_seconds: i32,
        daylight_offset_seconds: i32,
        standard_name: String,
        daylight_name: String,
        start: TransitionRule,
        end: TransitionRule,
    },
}

impl TimeZoneRule {
    pub(crate) fn utc() -> Self {
        Self::Fixed {
            offset_seconds: 0,
            name: "UTC".to_owned(),
        }
    }

    #[cfg(test)]
    pub(crate) fn fixed(offset_minutes: i32) -> Result<Self, DateHostError> {
        if !(-1_439..=1_439).contains(&offset_minutes) {
            return Err(DateHostError::InvalidTimeZone(offset_minutes.to_string()));
        }
        Ok(Self::Fixed {
            offset_seconds: offset_minutes * 60,
            name: offset_name(offset_minutes * 60),
        })
    }

    pub(crate) fn parse(text: &str) -> Result<Self, DateHostError> {
        if matches!(text, "" | "UTC" | "Etc/UTC" | "GMT" | "Etc/GMT") {
            return Ok(Self::utc());
        }
        if let Some(offset) = parse_iso_offset(text.strip_prefix("UTC").unwrap_or(text)) {
            return Ok(Self::Fixed {
                offset_seconds: offset,
                name: offset_name(offset),
            });
        }
        parse_posix_zone(text)
    }
    pub(crate) fn from_host<H: Host>(host: &H) -> Result<Self, DateHostError> {
        match host.env("TZ") {
            None => Err(DateHostError::UnsupportedTimeZone(
                "<host default>".to_owned(),
            )),
            Some(zone)
                if zone.contains('/')
                    && !zone.contains(',')
                    && !matches!(zone, "Etc/UTC" | "Etc/GMT") =>
            {
                Err(DateHostError::UnsupportedTimeZone(zone.to_owned()))
            }
            Some(zone) => Self::parse(zone),
        }
    }

    fn offset_at_utc(&self, utc_ms: f64) -> i32 {
        match self {
            Self::Fixed { offset_seconds, .. } => *offset_seconds,
            Self::Dst {
                standard_offset_seconds,
                daylight_offset_seconds,
                start,
                end,
                ..
            } => {
                let year = year_from_time(utc_ms);
                let start_utc = transition_local_ms(year, *start)
                    - f64::from(*standard_offset_seconds) * MS_PER_SECOND;
                let end_utc = transition_local_ms(year, *end)
                    - f64::from(*daylight_offset_seconds) * MS_PER_SECOND;
                let daylight = if start_utc < end_utc {
                    utc_ms >= start_utc && utc_ms < end_utc
                } else {
                    utc_ms >= start_utc || utc_ms < end_utc
                };
                if daylight {
                    *daylight_offset_seconds
                } else {
                    *standard_offset_seconds
                }
            }
        }
    }

    fn local_time(&self, utc_ms: f64) -> f64 {
        utc_ms + f64::from(self.offset_at_utc(utc_ms)) * MS_PER_SECOND
    }

    /// Implements the spec's compatible local-time disambiguation: the earlier
    /// instant in a repeated interval, and the pre-transition offset in a gap.
    fn utc_time(&self, local_ms: f64) -> f64 {
        match self {
            Self::Fixed { offset_seconds, .. } => {
                local_ms - f64::from(*offset_seconds) * MS_PER_SECOND
            }
            Self::Dst {
                standard_offset_seconds,
                daylight_offset_seconds,
                ..
            } => {
                let standard = local_ms - f64::from(*standard_offset_seconds) * MS_PER_SECOND;
                let daylight = local_ms - f64::from(*daylight_offset_seconds) * MS_PER_SECOND;
                let standard_valid = self.offset_at_utc(standard) == *standard_offset_seconds;
                let daylight_valid = self.offset_at_utc(daylight) == *daylight_offset_seconds;
                match (standard_valid, daylight_valid) {
                    (true, true) => standard.min(daylight),
                    (true, false) => standard,
                    (false, true) => daylight,
                    (false, false) => standard.max(daylight),
                }
            }
        }
    }

    fn name_at_utc(&self, utc_ms: f64) -> &str {
        match self {
            Self::Fixed { name, .. } => name,
            Self::Dst {
                standard_offset_seconds,
                standard_name,
                daylight_name,
                ..
            } => {
                if self.offset_at_utc(utc_ms) == *standard_offset_seconds {
                    standard_name
                } else {
                    daylight_name
                }
            }
        }
    }
}

fn parse_posix_zone(text: &str) -> Result<TimeZoneRule, DateHostError> {
    let bytes = text.as_bytes();
    let std_end = bytes
        .iter()
        .position(u8::is_ascii_digit)
        .ok_or_else(|| DateHostError::UnsupportedTimeZone(text.to_owned()))?;
    if std_end < 3 {
        return Err(DateHostError::InvalidTimeZone(text.to_owned()));
    }
    let standard_name = &text[..std_end];
    let (west_seconds, after_standard) = parse_posix_offset(&text[std_end..])
        .ok_or_else(|| DateHostError::InvalidTimeZone(text.to_owned()))?;
    let standard_offset_seconds = -west_seconds;
    let remainder = &text[std_end + after_standard..];
    if remainder.is_empty() {
        return Ok(TimeZoneRule::Fixed {
            offset_seconds: standard_offset_seconds,
            name: standard_name.to_owned(),
        });
    }
    let dst_end = remainder
        .bytes()
        .position(|byte| byte.is_ascii_digit() || byte == b',' || byte == b'+' || byte == b'-')
        .unwrap_or(remainder.len());
    if dst_end < 3 {
        return Err(DateHostError::InvalidTimeZone(text.to_owned()));
    }
    let daylight_name = &remainder[..dst_end];
    let mut cursor = dst_end;
    let daylight_offset_seconds = if remainder.as_bytes().get(cursor) == Some(&b',') {
        standard_offset_seconds + 3_600
    } else {
        let (west, used) = parse_posix_offset(&remainder[cursor..])
            .ok_or_else(|| DateHostError::InvalidTimeZone(text.to_owned()))?;
        cursor += used;
        -west
    };
    let rules = remainder
        .get(cursor..)
        .and_then(|rest| rest.strip_prefix(','))
        .ok_or_else(|| DateHostError::InvalidTimeZone(text.to_owned()))?;
    let (start, end) = rules
        .split_once(',')
        .ok_or_else(|| DateHostError::InvalidTimeZone(text.to_owned()))?;
    Ok(TimeZoneRule::Dst {
        standard_offset_seconds,
        daylight_offset_seconds,
        standard_name: standard_name.to_owned(),
        daylight_name: daylight_name.to_owned(),
        start: parse_transition(start)
            .ok_or_else(|| DateHostError::InvalidTimeZone(text.to_owned()))?,
        end: parse_transition(end)
            .ok_or_else(|| DateHostError::InvalidTimeZone(text.to_owned()))?,
    })
}

fn parse_posix_offset(text: &str) -> Option<(i32, usize)> {
    let bytes = text.as_bytes();
    let mut cursor = 0;
    let sign = match bytes.first() {
        Some(b'+') => {
            cursor += 1;
            1
        }
        Some(b'-') => {
            cursor += 1;
            -1
        }
        _ => 1,
    };
    let start = cursor;
    while bytes.get(cursor).is_some_and(u8::is_ascii_digit) {
        cursor += 1;
    }
    if cursor == start {
        return None;
    }
    let hours: i32 = text[start..cursor].parse().ok()?;
    let mut minutes = 0;
    let mut seconds = 0;
    if bytes.get(cursor) == Some(&b':') {
        cursor += 1;
        let end = cursor + 2;
        minutes = text.get(cursor..end)?.parse().ok()?;
        cursor = end;
        if bytes.get(cursor) == Some(&b':') {
            cursor += 1;
            let end = cursor + 2;
            seconds = text.get(cursor..end)?.parse().ok()?;
            cursor = end;
        }
    }
    (minutes < 60 && seconds < 60 && hours <= 24)
        .then_some((sign * (hours * 3_600 + minutes * 60 + seconds), cursor))
}

fn parse_transition(text: &str) -> Option<TransitionRule> {
    let (date, time) = text.split_once('/').unwrap_or((text, "2"));
    let mut fields = date.strip_prefix('M')?.split('.');
    let month = fields.next()?.parse().ok()?;
    let week = fields.next()?.parse().ok()?;
    let weekday = fields.next()?.parse().ok()?;
    if fields.next().is_some()
        || !(1..=12).contains(&month)
        || !(1..=5).contains(&week)
        || weekday > 6
    {
        return None;
    }
    let (seconds, used) = parse_posix_offset(time)?;
    (used == time.len()).then_some(TransitionRule {
        month,
        week,
        weekday,
        seconds,
    })
}

fn parse_iso_offset(text: &str) -> Option<i32> {
    if text == "Z" || text == "+00:00" || text == "-00:00" {
        return Some(0);
    }
    let bytes = text.as_bytes();
    if bytes.len() != 6 || !matches!(bytes[0], b'+' | b'-') || bytes[3] != b':' {
        return None;
    }
    let hours: i32 = text[1..3].parse().ok()?;
    let minutes: i32 = text[4..6].parse().ok()?;
    if hours > 23 || minutes > 59 {
        return None;
    }
    let sign = if bytes[0] == b'-' { -1 } else { 1 };
    Some(sign * (hours * 3_600 + minutes * 60))
}

fn offset_name(offset_seconds: i32) -> String {
    let sign = if offset_seconds < 0 { '-' } else { '+' };
    let absolute = offset_seconds.unsigned_abs();
    format!(
        "UTC{sign}{:02}:{:02}",
        absolute / 3_600,
        absolute % 3_600 / 60
    )
}

fn transition_local_ms(year: i64, rule: TransitionRule) -> f64 {
    let month_start = make_day(year as f64, f64::from(rule.month - 1), 1.0);
    let first_weekday = week_day(month_start * MS_PER_DAY) as i64;
    let mut date = 1
        + (i64::from(rule.weekday) - first_weekday).rem_euclid(7)
        + 7 * (i64::from(rule.week) - 1);
    let month_days = days_in_month(year, i64::from(rule.month));
    if date > month_days {
        date -= 7;
    }
    make_date(
        make_day(year as f64, f64::from(rule.month - 1), date as f64),
        f64::from(rule.seconds) * MS_PER_SECOND,
    )
}

fn day(time: f64) -> f64 {
    (time / MS_PER_DAY).floor()
}
fn time_within_day(time: f64) -> f64 {
    time.rem_euclid(MS_PER_DAY)
}
fn is_leap_year(year: i64) -> bool {
    year.rem_euclid(4) == 0 && (year.rem_euclid(100) != 0 || year.rem_euclid(400) == 0)
}
fn day_from_year(year: i64) -> i64 {
    fn leap_years_before(year: i64) -> i64 {
        let prior = year - 1;
        prior.div_euclid(4) - prior.div_euclid(100) + prior.div_euclid(400)
    }
    365 * (year - 1970) + leap_years_before(year) - leap_years_before(1970)
}
fn year_from_time(time: f64) -> i64 {
    let days = day(time) as i64;
    let mut year = 1970 + days.div_euclid(365);
    while day_from_year(year) > days {
        year -= 1;
    }
    while day_from_year(year + 1) <= days {
        year += 1;
    }
    year
}
fn day_within_year(time: f64) -> i64 {
    day(time) as i64 - day_from_year(year_from_time(time))
}
fn month_from_time(time: f64) -> i64 {
    let mut remaining = day_within_year(time);
    let year = year_from_time(time);
    for month in 1..=12 {
        let count = days_in_month(year, month);
        if remaining < count {
            return month - 1;
        }
        remaining -= count;
    }
    unreachable!("day within year belongs to a month")
}
fn date_from_time(time: f64) -> i64 {
    let month = month_from_time(time);
    day_within_year(time)
        - (1..=month)
            .map(|m| days_in_month(year_from_time(time), m))
            .sum::<i64>()
        + 1
}
fn week_day(time: f64) -> u8 {
    (day(time) as i64 + 4).rem_euclid(7) as u8
}
fn hour_from_time(time: f64) -> i64 {
    (time_within_day(time) / MS_PER_HOUR).floor() as i64
}
fn min_from_time(time: f64) -> i64 {
    (time_within_day(time) / MS_PER_MINUTE).floor() as i64 % 60
}
fn sec_from_time(time: f64) -> i64 {
    (time_within_day(time) / MS_PER_SECOND).floor() as i64 % 60
}
fn ms_from_time(time: f64) -> i64 {
    time_within_day(time).floor() as i64 % 1_000
}
fn days_in_month(year: i64, month_one_based: i64) -> i64 {
    match month_one_based {
        2 if is_leap_year(year) => 29,
        2 => 28,
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    }
}
fn to_integer(value: f64) -> f64 {
    if value.is_nan() || value == 0.0 {
        value
    } else {
        value.trunc()
    }
}
fn make_time(hour: f64, minute: f64, second: f64, millisecond: f64) -> f64 {
    if ![hour, minute, second, millisecond]
        .iter()
        .all(|v| v.is_finite())
    {
        return f64::NAN;
    }
    to_integer(hour) * MS_PER_HOUR
        + to_integer(minute) * MS_PER_MINUTE
        + to_integer(second) * MS_PER_SECOND
        + to_integer(millisecond)
}
fn make_day(year: f64, month: f64, date: f64) -> f64 {
    if ![year, month, date].iter().all(|v| v.is_finite()) {
        return f64::NAN;
    }
    let year = to_integer(year);
    let month = to_integer(month);
    let date = to_integer(date);
    if year.abs() > 1_000_000.0 || month.abs() > 12_000_000.0 || date.abs() > 100_000_000.0 {
        return f64::NAN;
    }
    let normalized_year = year as i64 + (month as i64).div_euclid(12);
    let normalized_month = (month as i64).rem_euclid(12);
    (day_from_year(normalized_year)
        + (1..=normalized_month)
            .map(|m| days_in_month(normalized_year, m))
            .sum::<i64>()) as f64
        + date
        - 1.0
}
fn make_date(day_value: f64, time: f64) -> f64 {
    if !day_value.is_finite() || !time.is_finite() {
        f64::NAN
    } else {
        day_value * MS_PER_DAY + time
    }
}
fn time_clip(time: f64) -> f64 {
    if !time.is_finite() || time.abs() > MAX_TIME_VALUE {
        return f64::NAN;
    }
    let clipped = time.trunc();
    if clipped == 0.0 { 0.0 } else { clipped }
}

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = super::super::ordinary_prototype(heap, builtins.object_prototype());
    let Some(bamts_native::Decoded::HeapRef(prototype_id)) = prototype.decode() else {
        unreachable!("Date prototype is a heap object")
    };
    heap[prototype_id.slot() as usize - 1] = HeapEntry::Date {
        time: f64::NAN,
        properties: PropertyMap::default(),
        prototype: Some(builtins.object_prototype()),
        extensible: true,
    };
    let constructor = install_constructor_function(heap, builtins, "Date", 7, constructor::<H>);
    builtins.set_constructor_prototype(heap, constructor, prototype);
    builtins.set_date_prototype(prototype);

    for (name, length, handler) in [
        ("now", 0, now::<H> as BuiltinHandler<H>),
        ("parse", 1, parse::<H>),
        ("UTC", 7, utc::<H>),
    ] {
        let function = install_function(heap, builtins, name, length, handler);
        native_properties(heap, constructor).insert(named(name), builtin_property(function));
    }

    let methods: &[(&str, u32, BuiltinHandler<H>)] = &[
        ("getTime", 0, get_time::<H>),
        ("valueOf", 0, get_time::<H>),
        ("getFullYear", 0, get_full_year::<H>),
        ("getUTCFullYear", 0, get_utc_full_year::<H>),
        ("getMonth", 0, get_month::<H>),
        ("getUTCMonth", 0, get_utc_month::<H>),
        ("getDate", 0, get_date::<H>),
        ("getUTCDate", 0, get_utc_date::<H>),
        ("getDay", 0, get_day::<H>),
        ("getUTCDay", 0, get_utc_day::<H>),
        ("getHours", 0, get_hours::<H>),
        ("getUTCHours", 0, get_utc_hours::<H>),
        ("getMinutes", 0, get_minutes::<H>),
        ("getUTCMinutes", 0, get_utc_minutes::<H>),
        ("getSeconds", 0, get_seconds::<H>),
        ("getUTCSeconds", 0, get_utc_seconds::<H>),
        ("getMilliseconds", 0, get_milliseconds::<H>),
        ("getUTCMilliseconds", 0, get_utc_milliseconds::<H>),
        ("getTimezoneOffset", 0, get_timezone_offset::<H>),
        ("getYear", 0, get_year::<H>),
        ("setTime", 1, set_time::<H>),
        ("setMilliseconds", 1, set_milliseconds::<H>),
        ("setUTCMilliseconds", 1, set_utc_milliseconds::<H>),
        ("setSeconds", 2, set_seconds::<H>),
        ("setUTCSeconds", 2, set_utc_seconds::<H>),
        ("setMinutes", 3, set_minutes::<H>),
        ("setUTCMinutes", 3, set_utc_minutes::<H>),
        ("setHours", 4, set_hours::<H>),
        ("setUTCHours", 4, set_utc_hours::<H>),
        ("setDate", 1, set_date::<H>),
        ("setUTCDate", 1, set_utc_date::<H>),
        ("setMonth", 2, set_month::<H>),
        ("setUTCMonth", 2, set_utc_month::<H>),
        ("setFullYear", 3, set_full_year::<H>),
        ("setUTCFullYear", 3, set_utc_full_year::<H>),
        ("setYear", 1, set_year::<H>),
        ("toISOString", 0, to_iso_string::<H>),
        ("toJSON", 1, to_json::<H>),
        ("toString", 0, to_string::<H>),
        ("toDateString", 0, to_date_string::<H>),
        ("toTimeString", 0, to_time_string::<H>),
        ("toUTCString", 0, to_utc_string::<H>),
        ("toLocaleString", 0, to_string::<H>),
        ("toLocaleDateString", 0, to_date_string::<H>),
        ("toLocaleTimeString", 0, to_time_string::<H>),
    ];
    let mut utc_string_function = None;
    for &(name, length, handler) in methods {
        let function = install_function(heap, builtins, name, length, handler);
        if name == "toUTCString" {
            utc_string_function = Some(function);
        }
        define_data(heap, prototype, name, function);
    }
    define_data(
        heap,
        prototype,
        "toGMTString",
        utc_string_function.expect("toUTCString is installed"),
    );
    let to_primitive = install_function(
        heap,
        builtins,
        "[Symbol.toPrimitive]",
        1,
        date_to_primitive::<H>,
    );
    super::define_symbol_property(
        heap,
        prototype,
        builtins.symbol_to_primitive(),
        Property::Data {
            value: to_primitive,
            writable: false,
            enumerable: false,
            configurable: true,
        },
    );
    globals.insert(EcmaString::encode("Date"), constructor);
}

/// `Date.prototype[@@toPrimitive]`: unlike every other object, a Date reads
/// the `default` hint as `string`.
fn date_to_primitive<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !machine.is_object(this) {
        return Err(type_error(
            "Date.prototype[Symbol.toPrimitive] requires an object receiver",
        ));
    }
    let hint = args
        .first()
        .and_then(|value| machine.string_value(*value))
        .ok_or_else(|| type_error("Invalid Date.prototype[Symbol.toPrimitive] hint"))?;
    let prefer_string = if hint.eq_ascii("string") || hint.eq_ascii("default") {
        true
    } else if hint.eq_ascii("number") {
        false
    } else {
        return Err(type_error(
            "Invalid Date.prototype[Symbol.toPrimitive] hint",
        ));
    };
    Ok(BuiltinOutcome::Value(
        machine.ordinary_to_primitive(this, prefer_string)?,
    ))
}

fn named(name: &str) -> PropertyKey {
    PropertyKey::Named(EcmaString::encode(name))
}
fn builtin_property(value: Value) -> Property {
    Property::Data {
        value,
        writable: true,
        enumerable: false,
        configurable: true,
    }
}
fn native_properties(heap: &mut [HeapEntry], object: Value) -> &mut PropertyMap {
    let Some(bamts_native::Decoded::HeapRef(id)) = object.decode() else {
        panic!("native function reference")
    };
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[id.slot() as usize - 1] else {
        panic!("native function")
    };
    properties
}
fn result(value: f64) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(crate::number_value(value)))
}
fn string_result<H: Host>(
    machine: &mut Machine<'_, H>,
    text: String,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        EcmaString::encode(&text),
    )?))
}
fn timezone<H: Host>(machine: &Machine<'_, H>) -> Result<TimeZoneRule, EvalFailure> {
    TimeZoneRule::from_host(machine.host).map_err(|_| type_error("unsupported host timezone"))
}
fn date_time<H: Host>(machine: &Machine<'_, H>, this: Value) -> Result<f64, EvalFailure> {
    let Some(index) = machine.runtime_slot(this).map_err(EvalFailure::Runtime)? else {
        return Err(type_error("Date method called on incompatible receiver"));
    };
    let HeapEntry::Date { time, .. } = &machine.heap[index] else {
        return Err(type_error("Date method called on incompatible receiver"));
    };
    Ok(*time)
}
fn write_date_time<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    time: f64,
) -> Result<BuiltinOutcome, EvalFailure> {
    let Some(index) = machine.runtime_slot(this).map_err(EvalFailure::Runtime)? else {
        return Err(type_error("Date method called on incompatible receiver"));
    };
    let HeapEntry::Date { time: slot, .. } = &mut machine.heap[index] else {
        return Err(type_error("Date method called on incompatible receiver"));
    };
    *slot = time;
    result(time)
}
fn numbers<H: Host>(machine: &mut Machine<'_, H>, args: &[Value]) -> Result<Vec<f64>, EvalFailure> {
    args.iter()
        .map(|&value| machine.coerce_number_observable(value).map(value_number))
        .collect()
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !constructing {
        let now = time_clip(machine.host.now_ms() as f64);
        return string_result(
            machine,
            date_string(now, &timezone(machine)?, DateStringKind::Full),
        );
    }
    let milliseconds = if args.is_empty() {
        time_clip(machine.host.now_ms() as f64)
    } else if args.len() == 1 {
        let value = args[0];
        let copied = machine
            .runtime_slot(value)
            .map_err(EvalFailure::Runtime)?
            .and_then(|index| match machine.heap[index] {
                HeapEntry::Date { time, .. } => Some(time),
                _ => None,
            });
        if let Some(time) = copied {
            time
        } else {
            let primitive = machine.coerce_primitive_default(value)?;
            if let Some(text) = machine.string_value(primitive) {
                let text = text.to_utf8_lossy();
                let zone = if date_text_uses_local_zone(&text) {
                    timezone(machine)?
                } else {
                    TimeZoneRule::utc()
                };
                parse_date_text(&text, &zone).unwrap_or(f64::NAN)
            } else {
                time_clip(value_number(machine.coerce_number_observable(primitive)?))
            }
        }
    } else {
        let values = numbers(machine, &args[..args.len().min(7)])?;
        components_to_time(&values, &timezone(machine)?, true)
    };
    let default_prototype = machine.intrinsics.builtins.date_prototype();
    let prototype = super::prototype_from_new_target(machine, default_prototype)?;
    let object = machine
        .allocate(HeapEntry::Date {
            time: milliseconds,
            properties: PropertyMap::default(),
            prototype: Some(prototype),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)?;
    Ok(BuiltinOutcome::Value(object))
}
fn now<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    result(time_clip(machine.host.now_ms() as f64))
}
fn parse<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let text =
        machine.coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let text = text.to_utf8_lossy();
    let zone = if date_text_uses_local_zone(&text) {
        timezone(machine)?
    } else {
        TimeZoneRule::utc()
    };
    result(parse_date_text(&text, &zone).unwrap_or(f64::NAN))
}
fn utc<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let values = numbers(machine, &args[..args.len().min(7)])?;
    if args.is_empty() {
        return result(f64::NAN);
    }
    result(components_to_time(&values, &TimeZoneRule::utc(), false))
}
fn components_to_time(values: &[f64], zone: &TimeZoneRule, local: bool) -> f64 {
    let mut c = [0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0];
    for (target, source) in c.iter_mut().zip(values) {
        *target = *source;
    }
    if !c.iter().all(|v| v.is_finite()) {
        return f64::NAN;
    }
    let year = to_integer(c[0]);
    c[0] = if (0.0..=99.0).contains(&year) {
        year + 1900.0
    } else {
        year
    };
    let made = make_date(
        make_day(c[0], c[1], c[2]),
        make_time(c[3], c[4], c[5], c[6]),
    );
    time_clip(if local { zone.utc_time(made) } else { made })
}

macro_rules! getter {
    ($name:ident, $local:expr, $extract:expr) => {
        fn $name<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _: &[Value],
            _: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let mut time = date_time(machine, this)?;
            if time.is_nan() {
                return result(f64::NAN);
            }
            if $local {
                time = timezone(machine)?.local_time(time);
            }
            result(($extract)(time) as f64)
        }
    };
}
getter!(get_full_year, true, year_from_time);
getter!(get_utc_full_year, false, year_from_time);
getter!(get_month, true, month_from_time);
getter!(get_utc_month, false, month_from_time);
getter!(get_date, true, date_from_time);
getter!(get_utc_date, false, date_from_time);
getter!(get_day, true, week_day);
getter!(get_utc_day, false, week_day);
getter!(get_hours, true, hour_from_time);
getter!(get_utc_hours, false, hour_from_time);
getter!(get_minutes, true, min_from_time);
getter!(get_utc_minutes, false, min_from_time);
getter!(get_seconds, true, sec_from_time);
getter!(get_utc_seconds, false, sec_from_time);
getter!(get_milliseconds, true, ms_from_time);
getter!(get_utc_milliseconds, false, ms_from_time);
fn get_time<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    result(date_time(machine, this)?)
}
fn get_timezone_offset<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time = date_time(machine, this)?;
    if time.is_nan() {
        result(f64::NAN)
    } else {
        result(-f64::from(timezone(machine)?.offset_at_utc(time)) / 60.0)
    }
}
fn get_year<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time = date_time(machine, this)?;
    if time.is_nan() {
        result(f64::NAN)
    } else {
        result((year_from_time(timezone(machine)?.local_time(time)) - 1900) as f64)
    }
}

fn set_time<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    date_time(machine, this)?;
    let value = numbers(machine, &args[..args.len().min(1)])?
        .first()
        .copied()
        .unwrap_or(f64::NAN);
    write_date_time(machine, this, time_clip(value))
}
fn set_time_fields<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    local: bool,
    first: usize,
) -> Result<BuiltinOutcome, EvalFailure> {
    let raw = date_time(machine, this)?;
    let mut supplied = numbers(machine, &args[..args.len().min(4 - first)])?;
    if supplied.is_empty() {
        supplied.push(f64::NAN);
    }
    if raw.is_nan() {
        return Ok(BuiltinOutcome::Value(Value::number(f64::NAN)));
    }
    let zone = if local {
        Some(timezone(machine)?)
    } else {
        None
    };
    let base = zone.as_ref().map_or(raw, |zone| zone.local_time(raw));
    let mut fields = [
        hour_from_time(base) as f64,
        min_from_time(base) as f64,
        sec_from_time(base) as f64,
        ms_from_time(base) as f64,
    ];
    for (target, value) in fields[first..].iter_mut().zip(supplied) {
        *target = value;
    }
    let made = make_date(
        day(base),
        make_time(fields[0], fields[1], fields[2], fields[3]),
    );
    let utc = zone.as_ref().map_or(made, |zone| zone.utc_time(made));
    write_date_time(machine, this, time_clip(utc))
}
fn set_calendar_fields<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    local: bool,
    first: usize,
    invalid_zero: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let raw = date_time(machine, this)?;
    let mut supplied = numbers(machine, &args[..args.len().min(3 - first)])?;
    if supplied.is_empty() {
        supplied.push(f64::NAN);
    }
    if raw.is_nan() && !invalid_zero {
        return Ok(BuiltinOutcome::Value(Value::number(f64::NAN)));
    }
    let zone = if local {
        Some(timezone(machine)?)
    } else {
        None
    };
    let base_raw = if raw.is_nan() && invalid_zero {
        0.0
    } else {
        raw
    };
    let base = zone
        .as_ref()
        .map_or(base_raw, |zone| zone.local_time(base_raw));
    let mut fields = [
        year_from_time(base) as f64,
        month_from_time(base) as f64,
        date_from_time(base) as f64,
    ];
    for (target, value) in fields[first..].iter_mut().zip(supplied) {
        *target = value;
    }
    let made = make_date(
        make_day(fields[0], fields[1], fields[2]),
        time_within_day(base),
    );
    let utc = zone.as_ref().map_or(made, |zone| zone.utc_time(made));
    write_date_time(machine, this, time_clip(utc))
}
macro_rules! time_setter {
    ($name:ident, $local:expr, $first:expr) => {
        fn $name<H: Host>(
            m: &mut Machine<'_, H>,
            t: Value,
            a: &[Value],
            _: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            set_time_fields(m, t, a, $local, $first)
        }
    };
}
time_setter!(set_milliseconds, true, 3);
time_setter!(set_utc_milliseconds, false, 3);
time_setter!(set_seconds, true, 2);
time_setter!(set_utc_seconds, false, 2);
time_setter!(set_minutes, true, 1);
time_setter!(set_utc_minutes, false, 1);
time_setter!(set_hours, true, 0);
time_setter!(set_utc_hours, false, 0);
macro_rules! calendar_setter {
    ($name:ident, $local:expr, $first:expr, $zero:expr) => {
        fn $name<H: Host>(
            m: &mut Machine<'_, H>,
            t: Value,
            a: &[Value],
            _: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            set_calendar_fields(m, t, a, $local, $first, $zero)
        }
    };
}
calendar_setter!(set_date, true, 2, false);
calendar_setter!(set_utc_date, false, 2, false);
calendar_setter!(set_month, true, 1, false);
calendar_setter!(set_utc_month, false, 1, false);
calendar_setter!(set_full_year, true, 0, true);
calendar_setter!(set_utc_full_year, false, 0, true);
fn set_year<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    date_time(machine, this)?;
    let mut value = numbers(machine, &args[..args.len().min(1)])?
        .first()
        .copied()
        .unwrap_or(f64::NAN);
    if value.is_nan() {
        return write_date_time(machine, this, f64::NAN);
    }
    value = to_integer(value);
    if (0.0..=99.0).contains(&value) {
        value += 1900.0;
    }
    set_calendar_fields(machine, this, &[crate::number_value(value)], true, 0, true)
}

fn to_iso_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let text =
        iso_string(date_time(machine, this)?).ok_or_else(|| range_error("Invalid time value"))?;
    string_result(machine, text)
}
fn to_json<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let primitive = machine.coerce_primitive_observable(this, false)?;
    if matches!(primitive.decode(), Some(bamts_native::Decoded::Number(value)) if !value.is_finite())
    {
        return Ok(BuiltinOutcome::Value(Value::NULL));
    }
    let method = machine.get_named_property(this, "toISOString")?;
    if !machine.is_callable(method)? {
        return Err(type_error("toISOString is not callable"));
    }
    Ok(BuiltinOutcome::Value(machine.call_value(
        method,
        this,
        &[],
    )?))
}
#[derive(Clone, Copy)]
enum DateStringKind {
    Full,
    Date,
    Time,
}
fn to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time = date_time(machine, this)?;
    if !time.is_finite() {
        return string_result(machine, "Invalid Date".to_owned());
    }
    let zone = timezone(machine)?;
    string_result(machine, date_string(time, &zone, DateStringKind::Full))
}
fn to_date_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time = date_time(machine, this)?;
    if !time.is_finite() {
        return string_result(machine, "Invalid Date".to_owned());
    }
    let zone = timezone(machine)?;
    string_result(machine, date_string(time, &zone, DateStringKind::Date))
}
fn to_time_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time = date_time(machine, this)?;
    if !time.is_finite() {
        return string_result(machine, "Invalid Date".to_owned());
    }
    let zone = timezone(machine)?;
    string_result(machine, date_string(time, &zone, DateStringKind::Time))
}
fn to_utc_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time = date_time(machine, this)?;
    let text = if time.is_nan() {
        "Invalid Date".to_owned()
    } else {
        utc_string(time)
    };
    string_result(machine, text)
}

const WEEKDAYS: [&str; 7] = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];
const MONTHS: [&str; 12] = [
    "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
];
fn iso_string(time: f64) -> Option<String> {
    if !time.is_finite() || time.abs() > MAX_TIME_VALUE {
        return None;
    }
    let year = year_from_time(time);
    let year_text = if (0..=9999).contains(&year) {
        format!("{year:04}")
    } else if year < 0 {
        format!("-{:06}", year.unsigned_abs())
    } else {
        format!("+{year:06}")
    };
    Some(format!(
        "{year_text}-{:02}-{:02}T{:02}:{:02}:{:02}.{:03}Z",
        month_from_time(time) + 1,
        date_from_time(time),
        hour_from_time(time),
        min_from_time(time),
        sec_from_time(time),
        ms_from_time(time)
    ))
}
/// At least four digits, after a `-` for a negative year.
fn year_string(year: impl Into<i64>) -> String {
    let year = year.into();
    let sign = if year < 0 { "-" } else { "" };
    format!("{sign}{:04}", year.unsigned_abs())
}
fn utc_string(time: f64) -> String {
    format!(
        "{}, {:02} {} {} {:02}:{:02}:{:02} GMT",
        WEEKDAYS[week_day(time) as usize],
        date_from_time(time),
        MONTHS[month_from_time(time) as usize],
        year_string(year_from_time(time)),
        hour_from_time(time),
        min_from_time(time),
        sec_from_time(time)
    )
}
fn date_string(time: f64, zone: &TimeZoneRule, kind: DateStringKind) -> String {
    if !time.is_finite() {
        return "Invalid Date".to_owned();
    }
    let local = zone.local_time(time);
    let date = format!(
        "{} {} {:02} {}",
        WEEKDAYS[week_day(local) as usize],
        MONTHS[month_from_time(local) as usize],
        date_from_time(local),
        year_string(year_from_time(local))
    );
    let offset = zone.offset_at_utc(time);
    let sign = if offset < 0 { '-' } else { '+' };
    let absolute = offset.unsigned_abs();
    let clock = format!(
        "{:02}:{:02}:{:02} GMT{sign}{:02}{:02} ({})",
        hour_from_time(local),
        min_from_time(local),
        sec_from_time(local),
        absolute / 3_600,
        absolute % 3_600 / 60,
        zone.name_at_utc(time)
    );
    match kind {
        DateStringKind::Full => format!("{date} {clock}"),
        DateStringKind::Date => date,
        DateStringKind::Time => clock,
    }
}

fn date_text_uses_local_zone(text: &str) -> bool {
    if text.contains('/') {
        return true;
    }
    let Some(time_separator) = text.find('T') else {
        return false;
    };
    let time = &text[time_separator + 1..];
    !time.ends_with('Z')
        && time
            .len()
            .checked_sub(6)
            .and_then(|start| parse_iso_offset(&time[start..]))
            .is_none()
}

fn parse_date_text(text: &str, zone: &TimeZoneRule) -> Option<f64> {
    parse_iso(text, zone)
        .or_else(|| parse_utc_output(text))
        .or_else(|| parse_local_output(text, zone))
        .or_else(|| parse_legacy_slash(text, zone))
}
fn parse_iso(text: &str, zone: &TimeZoneRule) -> Option<f64> {
    let bytes = text.as_bytes();
    let (year, mut cursor) = if bytes.first() == Some(&b'+') || bytes.first() == Some(&b'-') {
        let sign = if bytes[0] == b'-' { -1 } else { 1 };
        (sign * text.get(1..7)?.parse::<i64>().ok()?, 7)
    } else {
        (text.get(0..4)?.parse().ok()?, 4)
    };
    if text.get(0..7) == Some("-000000") {
        return None;
    }
    let mut month = 1i64;
    let mut date = 1i64;
    if cursor < text.len() {
        if bytes.get(cursor) != Some(&b'-') {
            return None;
        }
        month = text.get(cursor + 1..cursor + 3)?.parse().ok()?;
        cursor += 3;
        if cursor < text.len() && bytes.get(cursor) == Some(&b'-') {
            date = text.get(cursor + 1..cursor + 3)?.parse().ok()?;
            cursor += 3;
        }
    }
    if !(1..=12).contains(&month) || !(1..=days_in_month(year, month)).contains(&date) {
        return None;
    }
    let date_ms = make_date(make_day(year as f64, (month - 1) as f64, date as f64), 0.0);
    if cursor == text.len() {
        return Some(time_clip(date_ms));
    }
    if bytes.get(cursor) != Some(&b'T') {
        return None;
    }
    cursor += 1;
    let hour: i64 = text.get(cursor..cursor + 2)?.parse().ok()?;
    cursor += 2;
    if bytes.get(cursor) != Some(&b':') {
        return None;
    }
    cursor += 1;
    let minute: i64 = text.get(cursor..cursor + 2)?.parse().ok()?;
    cursor += 2;
    let mut second = 0i64;
    let mut millisecond = 0i64;
    if bytes.get(cursor) == Some(&b':') {
        cursor += 1;
        second = text.get(cursor..cursor + 2)?.parse().ok()?;
        cursor += 2;
    }
    if bytes.get(cursor) == Some(&b'.') {
        cursor += 1;
        let start = cursor;
        while bytes.get(cursor).is_some_and(u8::is_ascii_digit) {
            cursor += 1;
        }
        if cursor == start {
            return None;
        }
        let fraction = &text[start..cursor];
        let first_three = &fraction[..fraction.len().min(3)];
        millisecond = first_three.parse::<i64>().ok()? * 10_i64.pow((3 - first_three.len()) as u32);
    }
    if minute > 59
        || second > 59
        || hour > 24
        || (hour == 24 && (minute != 0 || second != 0 || millisecond != 0))
    {
        return None;
    }
    let local = make_date(
        day(date_ms),
        make_time(
            hour as f64,
            minute as f64,
            second as f64,
            millisecond as f64,
        ),
    );
    let utc = if cursor == text.len() {
        zone.utc_time(local)
    } else if &text[cursor..] == "Z" {
        local
    } else {
        local - f64::from(parse_iso_offset(&text[cursor..])?) * MS_PER_SECOND
    };
    Some(time_clip(utc))
}
fn parse_utc_output(text: &str) -> Option<f64> {
    let (_, rest) = text.split_once(", ")?;
    let parts: Vec<_> = rest.split_whitespace().collect();
    if parts.len() != 5 || parts[4] != "GMT" {
        return None;
    }

    let date: i64 = parts[0].parse().ok()?;
    let month = MONTHS.iter().position(|&m| m == parts[1])? as i64;
    let year: i64 = parts[2].parse().ok()?;
    let clock: Vec<_> = parts[3].split(':').collect();
    if clock.len() != 3 {
        return None;
    }
    Some(time_clip(make_date(
        make_day(year as f64, month as f64, date as f64),
        make_time(
            clock[0].parse().ok()?,
            clock[1].parse().ok()?,
            clock[2].parse().ok()?,
            0.0,
        ),
    )))
}
fn parse_legacy_slash(text: &str, zone: &TimeZoneRule) -> Option<f64> {
    let mut fields = text.split('/');
    let month: i64 = fields.next()?.parse().ok()?;
    let date: i64 = fields.next()?.parse().ok()?;
    let mut year: i64 = fields.next()?.parse().ok()?;
    if fields.next().is_some() || !(1..=12).contains(&month) {
        return None;
    }
    if (0..=99).contains(&year) {
        year += if year <= 49 { 2000 } else { 1900 };
    }
    if !(1..=days_in_month(year, month)).contains(&date) {
        return None;
    }
    Some(time_clip(zone.utc_time(make_date(
        make_day(year as f64, (month - 1) as f64, date as f64),
        0.0,
    ))))
}
fn parse_local_output(text: &str, zone: &TimeZoneRule) -> Option<f64> {
    let parts: Vec<_> = text.split_whitespace().collect();
    if parts.len() < 6 || !parts[5].starts_with("GMT") {
        return None;
    }
    let month = MONTHS.iter().position(|&m| m == parts[1])? as i64;
    let date: f64 = parts[2].parse().ok()?;
    let year: f64 = parts[3].parse().ok()?;
    let clock: Vec<_> = parts[4].split(':').collect();
    if clock.len() != 3 {
        return None;
    }
    let local = make_date(
        make_day(year, month as f64, date),
        make_time(
            clock[0].parse().ok()?,
            clock[1].parse().ok()?,
            clock[2].parse().ok()?,
            0.0,
        ),
    );
    let offset_text = &parts[5][3..];
    let offset = if offset_text.len() == 5 {
        let with_colon = format!("{}:{}", &offset_text[..3], &offset_text[3..]);
        parse_iso_offset(&with_colon)?
    } else {
        return Some(time_clip(zone.utc_time(local)));
    };
    Some(time_clip(local - f64::from(offset) * MS_PER_SECOND))
}

#[cfg(test)]
mod to_primitive_tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::{Limits, ThrowOrigin};

    fn hint(machine: &mut Machine<'_, TestHost>, text: &str) -> Value {
        machine
            .allocate(HeapEntry::String(EcmaString::encode(text)))
            .unwrap()
    }

    #[test]
    fn to_primitive_reads_each_hint_and_rejects_the_rest() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let date_constructor = machine.intrinsics.global("Date").unwrap();
        let prototype = machine
            .get_named_property(date_constructor, "prototype")
            .unwrap();
        let key = machine
            .to_property_key(machine.intrinsics.builtins.symbol_to_primitive())
            .unwrap();
        let method = machine.get_property_key(prototype, &key).unwrap();

        let object = ordinary_object(&mut machine);
        let to_string = hint(&mut machine, "from toString");
        let to_string_fn = machine
            .get_named_property(machine.intrinsics.object_prototype, "valueOf")
            .unwrap();
        machine
            .set_data_property(object, "toString", to_string_fn)
            .unwrap();
        machine.set_data_property(object, "tag", to_string).unwrap();

        for valid in ["string", "default", "number"] {
            let argument = hint(&mut machine, valid);
            assert!(matches!(
                machine.call_value(method, object, &[argument]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        }
        for invalid in [hint(&mut machine, "bogus"), Value::UNDEFINED] {
            let failure = machine.call_value(method, object, &[invalid]);
            assert!(matches!(
                failure,
                Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "Invalid Date.prototype[Symbol.toPrimitive] hint"
                }))
            ));
        }
        let number_hint = hint(&mut machine, "number");
        assert!(matches!(
            machine.call_value(method, Value::int32(1), &[number_hint]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Date.prototype[Symbol.toPrimitive] requires an object receiver"
            }))
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

    use super::super::test_support::{blank_program, ordinary_object};
    use crate::Limits;
    use crate::intrinsics::{BuiltinDef, native_function};

    struct ControlledHost {
        zone: &'static str,
    }

    impl Host for ControlledHost {
        fn env(&self, name: &str) -> Option<&str> {
            (name == "TZ").then_some(self.zone)
        }

        fn now_ms(&mut self) -> u64 {
            1_704_067_200_123
        }
    }

    fn machine<'a>(
        module: &'a bamts_bytecode::Program<bamts_bytecode::Verified>,
        host: &'a mut ControlledHost,
    ) -> Machine<'a, ControlledHost> {
        Machine::new(module, host, Limits::default())
    }

    fn invoke_date(
        machine: &mut Machine<'_, ControlledHost>,
        args: &[Value],
        constructing: bool,
    ) -> Value {
        let constructor = machine
            .intrinsics
            .global("Date")
            .expect("Date is installed");
        let index = machine.runtime_slot(constructor).unwrap().unwrap();
        let HeapEntry::NativeFunction {
            callable: crate::NativeCallable::Builtin(id),
            ..
        } = machine.heap[index]
        else {
            panic!("Date constructor is native")
        };
        let BuiltinOutcome::Value(value) = machine
            .call_builtin(id, Value::UNDEFINED, args, constructing)
            .expect("Date invocation succeeds")
        else {
            panic!("Date invocation returns a value")
        };
        value
    }

    fn construct_date(machine: &mut Machine<'_, ControlledHost>, args: &[Value]) -> Value {
        invoke_date(machine, args, true)
    }

    fn call(
        machine: &mut Machine<'_, ControlledHost>,
        receiver: Value,
        name: &str,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let function = machine.get_named_property(receiver, name)?;
        machine.call_value(function, receiver, args)
    }

    fn static_call(
        machine: &mut Machine<'_, ControlledHost>,
        name: &str,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let constructor = machine
            .intrinsics
            .global("Date")
            .expect("Date is installed");
        call(machine, constructor, name, args)
    }

    fn us_eastern() -> TimeZoneRule {
        TimeZoneRule::parse("EST5EDT,M3.2.0/2,M11.1.0/2").unwrap()
    }

    #[test]
    fn leap_years_and_month_overflow_follow_gregorian_calendar() {
        assert_eq!(days_in_month(2000, 2), 29);
        assert_eq!(days_in_month(1900, 2), 28);
        assert_eq!(days_in_month(2024, 2), 29);
        assert_eq!(
            iso_string(make_date(make_day(2024.0, 1.0, 29.0), 0.0)).unwrap(),
            "2024-02-29T00:00:00.000Z"
        );
        assert_eq!(
            iso_string(make_date(make_day(2024.0, 12.0, 1.0), 0.0)).unwrap(),
            "2025-01-01T00:00:00.000Z"
        );
        assert_eq!(
            iso_string(make_date(make_day(2024.0, 1.0, 0.0), 0.0)).unwrap(),
            "2024-01-31T00:00:00.000Z"
        );
        assert_eq!(
            iso_string(make_date(make_day(2024.0, 13.0, 1.0), 0.0)).unwrap(),
            "2025-02-01T00:00:00.000Z"
        );
    }

    #[test]
    fn negative_epochs_use_floor_not_truncating_division() {
        assert_eq!(iso_string(-1.0).unwrap(), "1969-12-31T23:59:59.999Z");
        assert_eq!(year_from_time(-1.0), 1969);
        assert_eq!(month_from_time(-1.0), 11);
        assert_eq!(hour_from_time(-1.0), 23);
    }

    #[test]
    fn time_clip_pins_bounds_non_finite_fraction_and_negative_zero() {
        assert_eq!(time_clip(8_640_000_000_000_000.0), 8_640_000_000_000_000.0);
        assert_eq!(
            time_clip(-8_640_000_000_000_000.0),
            -8_640_000_000_000_000.0
        );
        assert!(time_clip(8_640_000_000_000_001.0).is_nan());
        assert!(time_clip(f64::INFINITY).is_nan());
        assert!(time_clip(f64::NAN).is_nan());
        assert_eq!(time_clip(1.9), 1.0);
        let zero = time_clip(-0.5);
        assert_eq!(zero, 0.0);
        assert!(zero.is_sign_positive());
        assert_eq!(year_from_time(MAX_TIME_VALUE), 275_760);
        assert_eq!(year_from_time(-MAX_TIME_VALUE), -271_821);
    }

    #[test]
    fn make_time_and_invalid_values_propagate() {
        assert_eq!(make_time(24.0, 0.0, 0.0, 0.0), MS_PER_DAY);
        assert_eq!(make_time(-1.0, 0.0, 0.0, 0.0), -MS_PER_HOUR);
        assert!(make_time(f64::NAN, 0.0, 0.0, 0.0).is_nan());
        assert!(make_day(2024.0, f64::INFINITY, 1.0).is_nan());
        assert!(iso_string(f64::NAN).is_none());
        assert_eq!(
            date_string(f64::NAN, &TimeZoneRule::utc(), DateStringKind::Full),
            "Invalid Date"
        );
    }

    #[test]
    fn utc_components_are_exact_and_two_digit_years_are_annex_b_compatible() {
        assert_eq!(
            components_to_time(&[1970.0], &TimeZoneRule::utc(), false),
            0.0
        );
        assert_eq!(
            components_to_time(&[2024.0, 0.0, 1.0], &TimeZoneRule::utc(), false),
            1_704_067_200_000.0
        );
        assert_eq!(
            iso_string(components_to_time(
                &[99.0, 0.0, 1.0],
                &TimeZoneRule::utc(),
                false
            ))
            .unwrap(),
            "1999-01-01T00:00:00.000Z"
        );
        assert_eq!(
            iso_string(components_to_time(
                &[0.0, 0.0, 1.0],
                &TimeZoneRule::utc(),
                false
            ))
            .unwrap(),
            "1900-01-01T00:00:00.000Z"
        );
        assert_eq!(
            iso_string(components_to_time(
                &[100.0, 0.0, 1.0],
                &TimeZoneRule::utc(),
                false
            ))
            .unwrap(),
            "0100-01-01T00:00:00.000Z"
        );
    }

    #[test]
    fn controlled_fixed_timezone_is_exact() {
        let zone = TimeZoneRule::fixed(-300).unwrap();
        let epoch = 1_704_067_200_000.0;
        assert_eq!(hour_from_time(zone.local_time(epoch)), 19);
        assert_eq!(-zone.offset_at_utc(epoch) / 60, 300);
        assert_eq!(
            date_string(epoch, &zone, DateStringKind::Full),
            "Sun Dec 31 2023 19:00:00 GMT-0500 (UTC-05:00)"
        );
    }

    #[test]
    fn dst_boundaries_and_local_disambiguation_are_controlled() {
        let zone = us_eastern();
        let spring = parse_iso("2024-03-10T07:00:00Z", &zone).unwrap();
        assert_eq!(hour_from_time(zone.local_time(spring - 1.0)), 1);
        assert_eq!(hour_from_time(zone.local_time(spring)), 3);
        let fall = parse_iso("2024-11-03T06:00:00Z", &zone).unwrap();
        assert_eq!(hour_from_time(zone.local_time(fall - 1.0)), 1);
        assert_eq!(hour_from_time(zone.local_time(fall)), 1);
        assert_eq!(
            zone.utc_time(parse_iso("2024-11-03T01:30:00Z", &TimeZoneRule::utc()).unwrap()),
            parse_iso("2024-11-03T05:30:00Z", &TimeZoneRule::utc()).unwrap()
        );
        assert_eq!(
            zone.utc_time(parse_iso("2024-03-10T02:30:00Z", &TimeZoneRule::utc()).unwrap()),
            parse_iso("2024-03-10T07:30:00Z", &TimeZoneRule::utc()).unwrap()
        );
    }

    #[test]
    fn iso_date_only_is_utc_but_offsetless_date_time_is_local() {
        let zone = TimeZoneRule::fixed(-300).unwrap();
        assert_eq!(parse_iso("1970-01-01", &zone), Some(0.0));
        assert_eq!(
            parse_iso("1970-01-01T00:00:00", &zone),
            Some(5.0 * MS_PER_HOUR)
        );
        assert_eq!(
            parse_iso("1970-01-01T00:00:00-05:00", &zone),
            Some(5.0 * MS_PER_HOUR)
        );
        assert_eq!(parse_iso("1970-01-01T24:00:00Z", &zone), Some(MS_PER_DAY));
        assert_eq!(parse_iso("-000000-01-01T00:00:00Z", &zone), None);
        assert_eq!(
            parse_date_text("01/01/49", &zone),
            parse_iso("2049-01-01T00:00:00", &zone)
        );
        assert_eq!(
            parse_date_text("01/01/50", &zone),
            parse_iso("1950-01-01T00:00:00", &zone)
        );
    }

    #[test]
    fn emitted_iso_utc_and_local_strings_parse_back() {
        let zone = TimeZoneRule::fixed(-300).unwrap();
        let time = 1_704_067_200_000.0;
        assert!(!date_text_uses_local_zone("1970-01-01"));
        assert!(!date_text_uses_local_zone("1970-01-01T00:00:00Z"));
        assert!(!date_text_uses_local_zone("1970-01-01T00:00:00-05:00"));
        assert!(date_text_uses_local_zone("1970-01-01T00:00:00"));
        assert!(date_text_uses_local_zone("01/01/70"));
        assert_eq!(
            parse_date_text(&iso_string(time).unwrap(), &zone),
            Some(time)
        );
        assert_eq!(parse_date_text(&utc_string(time), &zone), Some(time));
        assert_eq!(
            parse_date_text(&date_string(time, &zone, DateStringKind::Full), &zone),
            Some(time)
        );
    }

    #[test]
    fn unsupported_iana_zone_is_typed_not_silently_utc() {
        assert_eq!(
            TimeZoneRule::parse("America/New_York"),
            Err(DateHostError::UnsupportedTimeZone(
                "America/New_York".to_owned()
            ))
        );
        assert!(TimeZoneRule::parse("EST5EDT,M3.2.0/2,M11.1.0/2").is_ok());
        struct NoZone;
        impl Host for NoZone {}
        assert_eq!(
            TimeZoneRule::from_host(&NoZone),
            Err(DateHostError::UnsupportedTimeZone(
                "<host default>".to_owned()
            ))
        );
    }

    #[test]
    fn installed_surface_has_spec_lengths_and_descriptors() {
        let module = blank_program("<date descriptors>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let constructor = machine.intrinsics.global("Date").unwrap();
        let date_prototype = machine.intrinsics.builtins.date_prototype();
        let Property::Data {
            writable,
            enumerable,
            configurable,
            ..
        } = machine
            .own_descriptor(constructor, &named("prototype"))
            .unwrap()
            .unwrap()
        else {
            panic!("Date.prototype is a data property")
        };
        assert!(!writable);
        assert!(!enumerable);
        assert!(!configurable);
        for (owner, name, expected) in [
            (constructor, "length", 7),
            (constructor, "parse", 1),
            (constructor, "UTC", 7),
            (machine.intrinsics.builtins.date_prototype(), "setHours", 4),
            (
                machine.intrinsics.builtins.date_prototype(),
                "setFullYear",
                3,
            ),
            (
                machine.intrinsics.builtins.date_prototype(),
                "toISOString",
                0,
            ),
        ] {
            let function = if name == "length" {
                owner
            } else {
                machine.get_named_property(owner, name).unwrap()
            };
            assert_eq!(
                value_number(machine.get_named_property(function, "length").unwrap()),
                f64::from(expected),
                "{name}"
            );
        }
        assert_eq!(
            machine
                .get_named_property(date_prototype, "toGMTString")
                .unwrap(),
            machine
                .get_named_property(date_prototype, "toUTCString")
                .unwrap()
        );
    }

    #[test]
    fn runtime_invalid_date_propagates_and_iso_throws() {
        let module = blank_program("<invalid date>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let invalid = construct_date(&mut machine, &[Value::number(f64::NAN)]);
        assert!(value_number(call(&mut machine, invalid, "getUTCFullYear", &[]).unwrap()).is_nan());
        let date_prototype = machine.intrinsics.builtins.date_prototype();
        assert!(value_number(call(&mut machine, date_prototype, "getTime", &[]).unwrap()).is_nan());
        let text = call(&mut machine, invalid, "toString", &[]).unwrap();
        assert!(machine.string_value(text).unwrap().eq_ascii("Invalid Date"));
        assert!(matches!(
            call(&mut machine, invalid, "toISOString", &[]),
            Err(EvalFailure::Throw(crate::ThrowOrigin::RangeError { .. }))
        ));
        assert_eq!(
            call(&mut machine, invalid, "toJSON", &[]).unwrap(),
            Value::NULL
        );
    }

    #[test]
    fn runtime_utc_setters_and_annex_b_years_are_exact() {
        let module = blank_program("<date setters>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        assert_eq!(
            value_number(static_call(&mut machine, "UTC", &[Value::int32(1970)]).unwrap()),
            0.0
        );
        assert!(value_number(static_call(&mut machine, "UTC", &[]).unwrap()).is_nan());
        let date = construct_date(&mut machine, &[Value::int32(0)]);
        call(&mut machine, date, "setYear", &[Value::int32(99)]).unwrap();
        assert_eq!(
            value_number(call(&mut machine, date, "getFullYear", &[]).unwrap()),
            1999.0
        );
        call(&mut machine, date, "setUTCMonth", &[Value::int32(13)]).unwrap();
        assert_eq!(
            value_number(call(&mut machine, date, "getUTCFullYear", &[]).unwrap()),
            2000.0
        );
        assert_eq!(
            value_number(call(&mut machine, date, "getUTCMonth", &[]).unwrap()),
            1.0
        );
        assert!(value_number(call(&mut machine, date, "setUTCDate", &[]).unwrap()).is_nan());
    }

    #[test]
    fn runtime_getters_observe_controlled_dst_boundary() {
        let module = blank_program("<date dst>");
        let mut host = ControlledHost {
            zone: "EST5EDT,M3.2.0/2,M11.1.0/2",
        };
        let mut machine = machine(&module, &mut host);
        let before = construct_date(
            &mut machine,
            &[Value::number(
                parse_iso("2024-03-10T06:59:59.999Z", &TimeZoneRule::utc()).unwrap(),
            )],
        );
        let after = construct_date(
            &mut machine,
            &[Value::number(
                parse_iso("2024-03-10T07:00:00.000Z", &TimeZoneRule::utc()).unwrap(),
            )],
        );
        assert_eq!(
            value_number(call(&mut machine, before, "getHours", &[]).unwrap()),
            1.0
        );
        assert_eq!(
            value_number(call(&mut machine, after, "getHours", &[]).unwrap()),
            3.0
        );
        assert_eq!(
            value_number(call(&mut machine, before, "getTimezoneOffset", &[]).unwrap()),
            300.0
        );
        assert_eq!(
            value_number(call(&mut machine, after, "getTimezoneOffset", &[]).unwrap()),
            240.0
        );
    }

    static COERCION_STEP: AtomicUsize = AtomicUsize::new(0);

    fn first_value_of(
        _machine: &mut Machine<'_, ControlledHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        assert_eq!(COERCION_STEP.fetch_add(1, Ordering::SeqCst), 0);
        Ok(BuiltinOutcome::Value(Value::int32(1)))
    }

    fn second_value_of(
        _machine: &mut Machine<'_, ControlledHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        assert_eq!(COERCION_STEP.fetch_add(1, Ordering::SeqCst), 1);
        Ok(BuiltinOutcome::Value(Value::int32(2)))
    }

    #[test]
    fn setter_coerces_all_supplied_arguments_before_invalid_propagation() {
        COERCION_STEP.store(0, Ordering::SeqCst);
        let module = blank_program("<date coercion order>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let invalid = construct_date(&mut machine, &[Value::number(f64::NAN)]);
        let first = ordinary_object(&mut machine);
        let second = ordinary_object(&mut machine);
        for (object, name, handler) in [
            (
                first,
                "first",
                first_value_of as BuiltinHandler<ControlledHost>,
            ),
            (
                second,
                "second",
                second_value_of as BuiltinHandler<ControlledHost>,
            ),
        ] {
            let id = machine.intrinsics.builtins.register(BuiltinDef {
                name,
                length: 0,
                handler,
            });
            let function = native_function(&mut machine.heap, id, name, 0);
            machine
                .set_data_property(object, "valueOf", function)
                .unwrap();
        }
        let value = call(&mut machine, invalid, "setHours", &[first, second]).unwrap();
        assert!(value_number(value).is_nan());
        assert_eq!(COERCION_STEP.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn a_setter_on_an_invalid_date_leaves_the_stored_time_alone() {
        let module = blank_program("<date invalid setter>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let date = construct_date(&mut machine, &[Value::number(f64::NAN)]);
        let result = call(&mut machine, date, "setUTCHours", &[Value::int32(1)]).unwrap();
        assert!(value_number(result).is_nan());
        assert!(value_number(call(&mut machine, date, "getTime", &[]).unwrap()).is_nan());
    }

    #[test]
    fn years_print_with_four_digits_and_a_sign() {
        assert_eq!(year_string(20), "0020");
        assert_eq!(year_string(-1), "-0001");
        assert_eq!(year_string(12345), "12345");
    }

    static RECEIVER_ARGUMENT_COERCED: AtomicBool = AtomicBool::new(false);

    fn receiver_order_value_of(
        _machine: &mut Machine<'_, ControlledHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        RECEIVER_ARGUMENT_COERCED.store(true, Ordering::SeqCst);
        Ok(BuiltinOutcome::Value(Value::int32(1)))
    }

    #[test]
    fn setters_validate_receiver_before_argument_coercion() {
        let module = blank_program("<date setter receiver order>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let receiver = ordinary_object(&mut machine);
        let argument = ordinary_object(&mut machine);
        let value_of = native(&mut machine, "valueOf", receiver_order_value_of);
        machine
            .set_data_property(argument, "valueOf", value_of)
            .unwrap();
        let prototype = machine.intrinsics.builtins.date_prototype();

        for name in ["setTime", "setHours", "setFullYear", "setYear"] {
            RECEIVER_ARGUMENT_COERCED.store(false, Ordering::SeqCst);
            let setter = machine.get_named_property(prototype, name).unwrap();
            assert!(matches!(
                machine.call_value(setter, receiver, &[argument]),
                Err(EvalFailure::Throw(crate::ThrowOrigin::TypeError { .. }))
            ));
            assert!(
                !RECEIVER_ARGUMENT_COERCED.load(Ordering::SeqCst),
                "{name} must validate thisTimeValue before coercing arguments"
            );
        }
    }

    static GENERIC_VALUE_OF_CALLED: AtomicBool = AtomicBool::new(false);
    static DATE_VALUE_OF_CALLED: AtomicBool = AtomicBool::new(false);

    fn native(
        machine: &mut Machine<'_, ControlledHost>,
        name: &'static str,
        handler: BuiltinHandler<ControlledHost>,
    ) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name,
            length: 0,
            handler,
        });
        native_function(&mut machine.heap, id, name, 0)
    }

    fn generic_value_of(
        _machine: &mut Machine<'_, ControlledHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        GENERIC_VALUE_OF_CALLED.store(true, Ordering::SeqCst);
        Ok(BuiltinOutcome::Value(Value::int32(12_345)))
    }

    fn date_value_of_override(
        _machine: &mut Machine<'_, ControlledHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        DATE_VALUE_OF_CALLED.store(true, Ordering::SeqCst);
        Ok(BuiltinOutcome::Value(Value::int32(99_999)))
    }

    #[test]
    fn call_form_ignores_arguments_and_uses_controlled_host_clock() {
        let module = blank_program("<Date call form>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let garbage = allocate_string(&mut machine, EcmaString::encode("not a date")).unwrap();
        for args in [&[][..], &[Value::int32(0)][..], &[garbage][..]] {
            let value = invoke_date(&mut machine, args, false);
            assert!(
                machine
                    .string_value(value)
                    .unwrap()
                    .eq_ascii("Mon Jan 01 2024 00:00:00 GMT+0000 (UTC)")
            );
        }
    }

    #[test]
    fn one_argument_copies_valid_and_invalid_date_values() {
        let module = blank_program("<Date copy>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let valid = construct_date(&mut machine, &[Value::int32(0)]);
        let valid_copy = construct_date(&mut machine, &[valid]);
        assert_eq!(date_time(&machine, valid_copy).unwrap(), 0.0);
        let invalid = construct_date(&mut machine, &[Value::number(f64::NAN)]);
        let invalid_copy = construct_date(&mut machine, &[invalid]);
        assert!(date_time(&machine, invalid_copy).unwrap().is_nan());
    }

    #[test]
    fn one_argument_observes_generic_object_value_of() {
        GENERIC_VALUE_OF_CALLED.store(false, Ordering::SeqCst);
        let module = blank_program("<Date object coercion>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let source = ordinary_object(&mut machine);
        let value_of = native(&mut machine, "valueOf", generic_value_of);
        machine
            .set_data_property(source, "valueOf", value_of)
            .unwrap();
        let copy = construct_date(&mut machine, &[source]);
        assert!(GENERIC_VALUE_OF_CALLED.load(Ordering::SeqCst));
        assert_eq!(date_time(&machine, copy).unwrap(), 12_345.0);
    }

    #[test]
    fn one_argument_date_copy_skips_overridden_value_of() {
        DATE_VALUE_OF_CALLED.store(false, Ordering::SeqCst);
        let module = blank_program("<Date internal-slot copy>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let source = construct_date(&mut machine, &[Value::int32(0)]);
        let value_of = native(&mut machine, "valueOf", date_value_of_override);
        machine
            .set_data_property(source, "valueOf", value_of)
            .unwrap();
        let copy = construct_date(&mut machine, &[source]);
        assert!(!DATE_VALUE_OF_CALLED.load(Ordering::SeqCst));
        assert_eq!(date_time(&machine, copy).unwrap(), 0.0);
    }

    #[test]
    fn iso_parser_retains_legacy_acceptance_and_rejection_vectors() {
        let zone = TimeZoneRule::utc();
        for (text, expected) in [
            ("+006024-02-29T23:59:59.123Z", "6024-02-29T23:59:59.123Z"),
            ("+010000-01-01T00:00:00.000Z", "+010000-01-01T00:00:00.000Z"),
            ("-000001-01-01T00:00:00.000Z", "-000001-01-01T00:00:00.000Z"),
        ] {
            let milliseconds = parse_date_text(text, &zone).expect(text);
            assert_eq!(
                iso_string(milliseconds).as_deref(),
                Some(expected),
                "{text}"
            );
        }
        for text in [
            "2024-02-30T00:00:00.000Z",
            "2023-02-29T00:00:00.000Z",
            "2024-01-01T24:00:00.001Z",
            "2024-01-01T00:60:00.000Z",
            "2024-01-01T00:00:60.000Z",
            "2024-01-01T00:00:00.Z",
            "2024-01-01 00:00:00.000Z",
            "-000000-01-01T00:00:00.000Z",
        ] {
            assert_eq!(parse_date_text(text, &zone), None, "{text}");
        }
    }
}
