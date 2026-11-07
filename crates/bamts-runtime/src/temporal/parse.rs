//! Strict RFC 9557 / Temporal ISO 8601 grammar.
//!
//! Each public entry point recognises exactly one goal symbol from the Temporal
//! grammar (`TemporalInstantString`, `TemporalDateTimeString`, ...). A string
//! either matches a goal completely or the parse fails; there is no partial
//! acceptance and no retry on a synthetic prefix. Every failure surfaces as a
//! `RangeError` at the JavaScript boundary.

use super::instant_duration::{
    NS_PER_HOUR, NS_PER_MICROSECOND, NS_PER_MILLISECOND, NS_PER_MINUTE, NS_PER_SECOND,
    TemporalError, TemporalResult, days_in_month,
};
use super::zoned_date_time::CalendarId;

/// UTC offset in a parsed string.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UtcOffsetRecord {
    /// `Z` / `z`.
    Zulu,
    /// Numeric offset in nanoseconds east of UTC.
    Numeric {
        nanoseconds: i128,
        /// Whether the text carried a seconds component. Such an offset never
        /// matches a time zone's offset by rounding to the minute.
        sub_minute: bool,
    },
}

/// Result of parsing an ISO date[-time] string with annotations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedIsoDateTime {
    pub year: i32,
    pub month: u8,
    pub day: u8,
    pub has_time: bool,
    /// Nanoseconds since midnight; 0 when `has_time` is false.
    pub time_ns: i128,
    pub offset: Option<UtcOffsetRecord>,
    /// Bracketed time zone annotation, unresolved.
    pub time_zone: Option<String>,
    /// `[u-ca=…]` value if present.
    pub calendar: Option<String>,
}

impl ParsedIsoDateTime {
    /// The string's calendar, canonicalized; ISO when it carries none.
    pub fn calendar_id(&self) -> TemporalResult<CalendarId> {
        self.calendar
            .as_deref()
            .map_or(Ok(CalendarId::iso8601()), CalendarId::canonicalize)
    }
}

/// The time zone a string names, before availability is decided.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParsedTimeZone {
    Named(String),
    OffsetMinutes(i32),
}

struct Cursor<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(text: &'a str) -> Self {
        Cursor {
            bytes: text.as_bytes(),
            pos: 0,
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn eat(&mut self, byte: u8) -> bool {
        if self.peek() == Some(byte) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_any(&mut self, set: &[u8]) -> bool {
        match self.peek() {
            Some(byte) if set.contains(&byte) => {
                self.pos += 1;
                true
            }
            _ => false,
        }
    }

    fn peek_digit(&self) -> bool {
        self.peek().is_some_and(|byte| byte.is_ascii_digit())
    }

    fn digits(&mut self, count: usize) -> Option<u32> {
        let mut value = 0_u32;
        for _ in 0..count {
            let byte = self.peek().filter(u8::is_ascii_digit)?;
            value = value * 10 + u32::from(byte - b'0');
            self.pos += 1;
        }
        Some(value)
    }

    fn done(&self) -> bool {
        self.pos >= self.bytes.len()
    }
}

fn date_year(c: &mut Cursor<'_>) -> Option<i32> {
    match c.peek() {
        Some(sign @ (b'+' | b'-')) => {
            c.pos += 1;
            let value = i32::try_from(c.digits(6)?).ok()?;
            if sign == b'-' {
                // `-000000` is the one spelling of year zero the grammar forbids.
                (value != 0).then_some(-value)
            } else {
                Some(value)
            }
        }
        _ => i32::try_from(c.digits(4)?).ok(),
    }
}

fn date_month(c: &mut Cursor<'_>) -> Option<u8> {
    let month = u8::try_from(c.digits(2)?).ok()?;
    (1..=12).contains(&month).then_some(month)
}

fn date_spec(c: &mut Cursor<'_>) -> Option<(i32, u8, u8)> {
    let year = date_year(c)?;
    let extended = c.eat(b'-');
    let month = date_month(c)?;
    if extended && !c.eat(b'-') {
        return None;
    }
    let day = u8::try_from(c.digits(2)?).ok()?;
    (1..=days_in_month(year, month))
        .contains(&day)
        .then_some((year, month, day))
}

fn year_month_spec(c: &mut Cursor<'_>) -> Option<(i32, u8)> {
    let year = date_year(c)?;
    c.eat(b'-');
    Some((year, date_month(c)?))
}

fn month_day_spec(c: &mut Cursor<'_>) -> Option<(u8, u8)> {
    if c.eat(b'-') && !c.eat(b'-') {
        return None;
    }
    let month = date_month(c)?;
    c.eat(b'-');
    let day = u8::try_from(c.digits(2)?).ok()?;
    // Validity is decided against a leap year: 02-29 is a real month-day.
    (1..=days_in_month(2000, month))
        .contains(&day)
        .then_some((month, day))
}

fn two_digits_at_most(c: &mut Cursor<'_>, max: u32) -> Option<u32> {
    let value = c.digits(2)?;
    (value <= max).then_some(value)
}

/// `TemporalDecimalFraction`: returns nanoseconds, or `Some(0)` when absent.
fn fraction_nanoseconds(c: &mut Cursor<'_>) -> Option<i128> {
    if !c.eat_any(b".,") {
        return Some(0);
    }
    let mut value = 0_i128;
    let mut count = 0;
    while count < 9 && c.peek_digit() {
        value = value * 10 + i128::from(c.digits(1)?);
        count += 1;
    }
    if count == 0 {
        return None;
    }
    for _ in count..9 {
        value *= 10;
    }
    Some(value)
}

/// `TimeSpec`, in either the extended or the basic form but never a mixture.
/// Leap seconds are accepted and clamp to `:59`, as the proposal requires.
fn time_spec(c: &mut Cursor<'_>) -> Option<i128> {
    let hour = i128::from(two_digits_at_most(c, 23)?);
    let mut ns = hour * NS_PER_HOUR;
    let extended = c.eat(b':');
    if !extended && !c.peek_digit() {
        return Some(ns);
    }
    ns += i128::from(two_digits_at_most(c, 59)?) * NS_PER_MINUTE;
    if extended {
        if !c.eat(b':') {
            return Some(ns);
        }
    } else if !c.peek_digit() {
        return Some(ns);
    }
    let second = two_digits_at_most(c, 60)?.min(59);
    ns += i128::from(second) * NS_PER_SECOND;
    Some(ns + fraction_nanoseconds(c)?)
}

/// `UTCOffset`: minute precision, or seconds and a fraction when `sub_minute`.
fn utc_offset(c: &mut Cursor<'_>, sub_minute: bool) -> Option<UtcOffsetRecord> {
    let negative = match c.peek()? {
        b'+' => false,
        b'-' => true,
        _ => return None,
    };
    c.pos += 1;
    let mut ns = i128::from(two_digits_at_most(c, 23)?) * NS_PER_HOUR;
    let extended = c.eat(b':');
    let mut has_seconds = false;
    if extended || c.peek_digit() {
        ns += i128::from(two_digits_at_most(c, 59)?) * NS_PER_MINUTE;
        let wants_seconds = if extended {
            sub_minute && c.eat(b':')
        } else {
            sub_minute && c.peek_digit()
        };
        if wants_seconds {
            ns += i128::from(two_digits_at_most(c, 59)?) * NS_PER_SECOND;
            ns += fraction_nanoseconds(c)?;
            has_seconds = true;
        }
    }
    Some(UtcOffsetRecord::Numeric {
        nanoseconds: if negative { -ns } else { ns },
        sub_minute: has_seconds,
    })
}

/// `DateTimeUTCOffset[Z]`: an absent offset is `Some(None)`.
fn date_time_offset(c: &mut Cursor<'_>, allow_zulu: bool) -> Option<Option<UtcOffsetRecord>> {
    match c.peek() {
        Some(b'Z' | b'z') if allow_zulu => {
            c.pos += 1;
            Some(Some(UtcOffsetRecord::Zulu))
        }
        Some(b'+' | b'-') => utc_offset(c, true).map(Some),
        _ => Some(None),
    }
}

fn is_iana_leading(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || matches!(byte, b'.' | b'_')
}

fn is_iana_continuing(byte: u8) -> bool {
    is_iana_leading(byte) || byte.is_ascii_digit() || matches!(byte, b'-' | b'+')
}

/// `TimeZoneIANAName`: `/`-separated parts, none of which is `.` or `..`.
fn iana_name(c: &mut Cursor<'_>) -> Option<String> {
    let start = c.pos;
    loop {
        let part = c.pos;
        if !c.peek().is_some_and(is_iana_leading) {
            return None;
        }
        c.pos += 1;
        while c.peek().is_some_and(is_iana_continuing) {
            c.pos += 1;
        }
        if matches!(&c.bytes[part..c.pos], b"." | b"..") {
            return None;
        }
        if !c.eat(b'/') {
            break;
        }
    }
    std::str::from_utf8(&c.bytes[start..c.pos])
        .ok()
        .map(str::to_owned)
}

/// `TimeZoneAnnotation`. A bracket that is not one leaves the cursor untouched
/// so the caller can read it as a key-value annotation.
fn time_zone_annotation(c: &mut Cursor<'_>) -> Option<String> {
    let start = c.pos;
    let parsed = (|| {
        if !c.eat(b'[') {
            return None;
        }
        c.eat(b'!');
        let body = c.pos;
        match c.peek()? {
            b'+' | b'-' => {
                utc_offset(c, false)?;
            }
            _ => {
                iana_name(c)?;
            }
        }
        let end = c.pos;
        if !c.eat(b']') {
            return None;
        }
        std::str::from_utf8(&c.bytes[body..end])
            .ok()
            .map(str::to_owned)
    })();
    if parsed.is_none() {
        c.pos = start;
    }
    parsed
}

fn annotation_key<'a>(c: &mut Cursor<'a>) -> Option<&'a [u8]> {
    let start = c.pos;
    if !c
        .peek()
        .is_some_and(|byte| byte.is_ascii_lowercase() || byte == b'_')
    {
        return None;
    }
    c.pos += 1;
    while c.peek().is_some_and(|byte| {
        byte.is_ascii_lowercase() || byte.is_ascii_digit() || matches!(byte, b'_' | b'-')
    }) {
        c.pos += 1;
    }
    Some(&c.bytes[start..c.pos])
}

fn annotation_value<'a>(c: &mut Cursor<'a>) -> Option<&'a [u8]> {
    let start = c.pos;
    loop {
        let component = c.pos;
        while c.peek().is_some_and(|byte| byte.is_ascii_alphanumeric()) {
            c.pos += 1;
        }
        if c.pos == component {
            return None;
        }
        if !c.eat(b'-') {
            return Some(&c.bytes[start..c.pos]);
        }
    }
}

/// `Annotations`, applying the proposal's calendar rules: the first `u-ca` wins,
/// a repeat is an error once a critical flag is involved, and an unknown key is
/// ignored unless it is critical.
fn annotations(c: &mut Cursor<'_>) -> TemporalResult<Option<String>> {
    let mut calendar = None;
    let mut calendar_was_critical = false;
    while c.eat(b'[') {
        let critical = c.eat(b'!');
        let parsed = (|| {
            let key = annotation_key(c)?;
            if !c.eat(b'=') {
                return None;
            }
            let value = annotation_value(c)?;
            c.eat(b']').then_some((key, value))
        })();
        let Some((key, value)) = parsed else {
            return Err(TemporalError::syntax("malformed annotation"));
        };
        if key == b"u-ca" {
            if calendar.is_none() {
                calendar = std::str::from_utf8(value).ok().map(str::to_owned);
                calendar_was_critical = critical;
            } else if critical || calendar_was_critical {
                return Err(TemporalError::range(
                    "a repeated calendar annotation must not be critical",
                ));
            }
        } else if critical {
            return Err(TemporalError::range("unknown critical annotation"));
        }
    }
    Ok(calendar)
}

fn annotated_date_time(
    text: &str,
    zoned: bool,
    time_required: bool,
) -> TemporalResult<ParsedIsoDateTime> {
    let syntax = || TemporalError::syntax("invalid ISO 8601 date-time string");
    let mut c = Cursor::new(text);
    let (year, month, day) = date_spec(&mut c).ok_or_else(syntax)?;
    let mut has_time = false;
    let mut time_ns = 0;
    let mut offset = None;
    if c.eat_any(b"Tt ") {
        has_time = true;
        time_ns = time_spec(&mut c).ok_or_else(syntax)?;
        offset = date_time_offset(&mut c, zoned).ok_or_else(syntax)?;
    } else if time_required {
        return Err(syntax());
    }
    let time_zone = time_zone_annotation(&mut c);
    if zoned && time_zone.is_none() {
        return Err(syntax());
    }
    let calendar = annotations(&mut c)?;
    if !c.done() {
        return Err(syntax());
    }
    Ok(ParsedIsoDateTime {
        year,
        month,
        day,
        has_time,
        time_ns,
        offset,
        time_zone,
        calendar,
    })
}

/// `TemporalDateTimeString[Zoned]`.
pub fn parse_date_time_string(text: &str, zoned: bool) -> TemporalResult<ParsedIsoDateTime> {
    annotated_date_time(text, zoned, false)
}

/// `TemporalInstantString`: a time and an offset are both required.
pub fn parse_instant_string(text: &str) -> TemporalResult<ParsedIsoDateTime> {
    let syntax = || TemporalError::syntax("invalid Instant string");
    let mut c = Cursor::new(text);
    let (year, month, day) = date_spec(&mut c).ok_or_else(syntax)?;
    if !c.eat_any(b"Tt ") {
        return Err(TemporalError::syntax(
            "Instant string requires a time component",
        ));
    }
    let time_ns = time_spec(&mut c).ok_or_else(syntax)?;
    let offset = date_time_offset(&mut c, true).ok_or_else(syntax)?;
    if offset.is_none() {
        return Err(TemporalError::syntax(
            "Instant string requires a UTC offset (Z or ±hh:mm)",
        ));
    }
    let time_zone = time_zone_annotation(&mut c);
    let calendar = annotations(&mut c)?;
    if !c.done() {
        return Err(syntax());
    }
    Ok(ParsedIsoDateTime {
        year,
        month,
        day,
        has_time: true,
        time_ns,
        offset,
        time_zone,
        calendar,
    })
}

fn parse_whole(text: &str, rule: impl FnOnce(&mut Cursor<'_>) -> bool) -> bool {
    let mut c = Cursor::new(text);
    rule(&mut c) && c.done()
}

/// A time without the `T` designator must not also read as a month-day or a
/// year-month; those strings need the designator to mean a time.
fn is_ambiguous_time(text: &str) -> bool {
    parse_whole(text, |c| month_day_spec(c).is_some())
        || parse_whole(text, |c| year_month_spec(c).is_some())
}

fn annotated_time(text: &str) -> TemporalResult<ParsedIsoDateTime> {
    let syntax = || TemporalError::syntax("invalid time string");
    let mut c = Cursor::new(text);
    let designated = c.eat_any(b"Tt");
    let start = c.pos;
    let time_ns = time_spec(&mut c).ok_or_else(syntax)?;
    let offset = date_time_offset(&mut c, false).ok_or_else(syntax)?;
    if !designated
        && std::str::from_utf8(&c.bytes[start..c.pos])
            .ok()
            .is_some_and(is_ambiguous_time)
    {
        return Err(TemporalError::syntax(
            "time string needs a T designator to be unambiguous",
        ));
    }
    let time_zone = time_zone_annotation(&mut c);
    let calendar = annotations(&mut c)?;
    if !c.done() {
        return Err(syntax());
    }
    Ok(ParsedIsoDateTime {
        year: 0,
        month: 1,
        day: 1,
        has_time: true,
        time_ns,
        offset,
        time_zone,
        calendar,
    })
}

/// `TemporalTimeString`.
pub fn parse_time_string(text: &str) -> TemporalResult<ParsedIsoDateTime> {
    annotated_date_time(text, false, true).or_else(|_| annotated_time(text))
}

/// A bare year-month or month-day may only carry the ISO calendar: without a
/// day or year there is nothing a different calendar could interpret.
fn require_iso_annotation(calendar: &Option<String>) -> TemporalResult<()> {
    match calendar {
        Some(value) if !value.eq_ignore_ascii_case("iso8601") => Err(TemporalError::range(
            "a string without a full date must use the ISO calendar",
        )),
        _ => Ok(()),
    }
}

fn annotated_year_month(text: &str) -> TemporalResult<ParsedIsoDateTime> {
    let mut c = Cursor::new(text);
    let (year, month) =
        year_month_spec(&mut c).ok_or_else(|| TemporalError::syntax("invalid year-month"))?;
    let time_zone = time_zone_annotation(&mut c);
    let calendar = annotations(&mut c)?;
    if !c.done() {
        return Err(TemporalError::syntax("invalid year-month"));
    }
    require_iso_annotation(&calendar)?;
    Ok(ParsedIsoDateTime {
        year,
        month,
        day: 1,
        has_time: false,
        time_ns: 0,
        offset: None,
        time_zone,
        calendar,
    })
}

/// `TemporalYearMonthString`.
pub fn parse_year_month_string(text: &str) -> TemporalResult<ParsedIsoDateTime> {
    annotated_year_month(text).or_else(|bare| match annotated_date_time(text, false, false) {
        Ok(full) => Ok(full),
        Err(full) => Err(prefer_semantic_error(bare, full)),
    })
}

fn annotated_month_day(text: &str) -> TemporalResult<ParsedIsoDateTime> {
    let mut c = Cursor::new(text);
    let (month, day) =
        month_day_spec(&mut c).ok_or_else(|| TemporalError::syntax("invalid month-day"))?;
    let time_zone = time_zone_annotation(&mut c);
    let calendar = annotations(&mut c)?;
    if !c.done() {
        return Err(TemporalError::syntax("invalid month-day"));
    }
    require_iso_annotation(&calendar)?;
    Ok(ParsedIsoDateTime {
        year: 1972,
        month,
        day,
        has_time: false,
        time_ns: 0,
        offset: None,
        time_zone,
        calendar,
    })
}

/// `TemporalMonthDayString`.
pub fn parse_month_day_string(text: &str) -> TemporalResult<ParsedIsoDateTime> {
    annotated_month_day(text).or_else(|bare| match annotated_date_time(text, false, false) {
        Ok(full) => Ok(full),
        Err(full) => Err(prefer_semantic_error(bare, full)),
    })
}

fn prefer_semantic_error(first: TemporalError, second: TemporalError) -> TemporalError {
    use super::instant_duration::TemporalErrorKind::Syntax;
    if first.kind == Syntax { second } else { first }
}

/// `ParseDateTimeUTCOffset`: the value of an `offset` property.
pub fn parse_date_time_utc_offset(text: &str) -> TemporalResult<i128> {
    let mut c = Cursor::new(text);
    match utc_offset(&mut c, true) {
        Some(UtcOffsetRecord::Numeric { nanoseconds, .. }) if c.done() => Ok(nanoseconds),
        _ => Err(TemporalError::syntax("invalid UTC offset string")),
    }
}

/// `ParseTimeZoneIdentifier`.
pub fn parse_time_zone_identifier(text: &str) -> TemporalResult<ParsedTimeZone> {
    let invalid = || TemporalError::range("invalid time zone identifier");
    let mut c = Cursor::new(text);
    match c.peek() {
        Some(b'+' | b'-') => match utc_offset(&mut c, false) {
            Some(UtcOffsetRecord::Numeric { nanoseconds, .. }) if c.done() => {
                let minutes = i32::try_from(nanoseconds / NS_PER_MINUTE).map_err(|_| invalid())?;
                Ok(ParsedTimeZone::OffsetMinutes(minutes))
            }
            _ => Err(invalid()),
        },
        _ => match iana_name(&mut c) {
            Some(name) if c.done() => Ok(ParsedTimeZone::Named(name)),
            _ => Err(invalid()),
        },
    }
}

/// `ParseTemporalTimeZoneString`: an identifier, or any ISO string naming one
/// through its annotation, `Z`, or numeric offset, in that order of preference.
pub fn parse_time_zone_string(text: &str) -> TemporalResult<ParsedTimeZone> {
    if let Ok(identifier) = parse_time_zone_identifier(text) {
        return Ok(identifier);
    }
    let parsed = parse_any_iso_string(text)?;
    if let Some(annotation) = &parsed.time_zone {
        return parse_time_zone_identifier(annotation);
    }
    match parsed.offset {
        Some(UtcOffsetRecord::Zulu) => Ok(ParsedTimeZone::Named("UTC".to_owned())),
        Some(UtcOffsetRecord::Numeric {
            nanoseconds,
            sub_minute: false,
        }) => {
            let minutes = i32::try_from(nanoseconds / NS_PER_MINUTE)
                .map_err(|_| TemporalError::range("invalid UTC offset"))?;
            Ok(ParsedTimeZone::OffsetMinutes(minutes))
        }
        _ => Err(TemporalError::range(
            "string does not name a time zone with minute precision",
        )),
    }
}

/// Every goal `ParseTemporalTimeZoneString` and `ParseTemporalCalendarString`
/// try, in the proposal's order.
fn parse_any_iso_string(text: &str) -> TemporalResult<ParsedIsoDateTime> {
    annotated_date_time(text, true, false)
        .or_else(|_| annotated_date_time(text, false, false))
        .or_else(|_| parse_instant_string(text))
        .or_else(|_| parse_time_string(text))
        .or_else(|_| parse_month_day_string(text))
        .or_else(|_| parse_year_month_string(text))
}

/// `ParseTemporalCalendarString`: the annotation of an ISO string, `iso8601`
/// for one without an annotation, or a bare calendar identifier.
pub fn parse_calendar_string(text: &str) -> TemporalResult<String> {
    if let Ok(parsed) = parse_any_iso_string(text) {
        return Ok(parsed.calendar.unwrap_or_else(|| "iso8601".to_owned()));
    }
    let mut c = Cursor::new(text);
    match annotation_value(&mut c) {
        Some(_) if c.done() => Ok(text.to_owned()),
        _ => Err(TemporalError::syntax("invalid calendar string")),
    }
}

/// Exact nanoseconds in `whole.fraction` of one `unit_ns`, where `fraction` is
/// scaled to nine digits.
fn fractional_nanoseconds(fraction: i128, unit_ns: i128) -> i128 {
    fraction * (unit_ns / NS_PER_SECOND)
}

/// Splits sub-unit nanoseconds into the Duration fields below `unit_ns`.
fn distribute_fraction(mut rest: i128, unit_ns: i128) -> [i128; 5] {
    let mut fields = [0; 5];
    let steps = [
        (0, NS_PER_MINUTE),
        (1, NS_PER_SECOND),
        (2, NS_PER_MILLISECOND),
        (3, NS_PER_MICROSECOND),
    ];
    for (slot, size) in steps {
        if size < unit_ns {
            fields[slot] = rest / size;
            rest %= size;
        }
    }
    fields[4] = rest;
    fields
}

/// `ParseTemporalDurationString`. Returns the ten fields, signed. Only the
/// smallest time component may carry a fraction, and it spills downward into
/// the smaller fields exactly.
pub fn parse_duration_string(text: &str) -> TemporalResult<[i128; 10]> {
    let syntax = || TemporalError::syntax("invalid duration string");
    let overflow = || TemporalError::range("duration component out of range");
    let mut c = Cursor::new(text);
    let negative = match c.peek() {
        Some(b'-') => {
            c.pos += 1;
            true
        }
        Some(b'+') => {
            c.pos += 1;
            false
        }
        _ => false,
    };
    if !c.eat_any(b"Pp") {
        return Err(syntax());
    }
    let mut fields = [0_i128; 10];
    let mut any = false;

    let whole_number = |c: &mut Cursor<'_>| -> TemporalResult<i128> {
        let start = c.pos;
        let mut value = 0_i128;
        while c.peek_digit() {
            let digit = i128::from(c.digits(1).ok_or_else(syntax)?);
            value = value
                .checked_mul(10)
                .and_then(|scaled| scaled.checked_add(digit))
                .ok_or_else(overflow)?;
        }
        if c.pos == start {
            return Err(syntax());
        }
        Ok(value)
    };

    let mut next_date_slot = 0;
    while !c.done() && !matches!(c.peek(), Some(b'T' | b't')) {
        let value = whole_number(&mut c)?;
        let slot = match c.peek().map(|byte| byte.to_ascii_uppercase()) {
            Some(b'Y') => 0,
            Some(b'M') => 1,
            Some(b'W') => 2,
            Some(b'D') => 3,
            _ => return Err(syntax()),
        };
        c.pos += 1;
        if slot < next_date_slot {
            return Err(syntax());
        }
        next_date_slot = slot + 1;
        fields[slot] = value;
        any = true;
    }

    if c.eat_any(b"Tt") {
        let mut next_time_slot = 0;
        let mut any_time = false;
        while !c.done() {
            let value = whole_number(&mut c)?;
            let before_fraction = c.pos;
            let fraction = fraction_nanoseconds(&mut c).ok_or_else(syntax)?;
            let has_fraction = c.pos != before_fraction;
            let (slot, unit_ns) = match c.peek().map(|byte| byte.to_ascii_uppercase()) {
                Some(b'H') => (4, NS_PER_HOUR),
                Some(b'M') => (5, NS_PER_MINUTE),
                Some(b'S') => (6, NS_PER_SECOND),
                _ => return Err(syntax()),
            };
            c.pos += 1;
            if slot < next_time_slot {
                return Err(syntax());
            }
            next_time_slot = slot + 1;
            fields[slot] = value;
            any = true;
            any_time = true;
            if has_fraction {
                let [minutes, seconds, milliseconds, microseconds, nanoseconds] =
                    distribute_fraction(fractional_nanoseconds(fraction, unit_ns), unit_ns);
                if slot == 4 {
                    fields[5] = minutes;
                }
                if slot <= 5 {
                    fields[6] = seconds;
                }
                fields[7] = milliseconds;
                fields[8] = microseconds;
                fields[9] = nanoseconds;
                if !c.done() {
                    return Err(TemporalError::syntax(
                        "no component may follow a fractional component",
                    ));
                }
            }
        }
        if !any_time {
            return Err(syntax());
        }
    }

    if !any || !c.done() {
        return Err(syntax());
    }
    if negative {
        for field in &mut fields {
            *field = -*field;
        }
    }
    Ok(fields)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn date_time_goal_rejects_a_utc_designator_unless_zoned() {
        assert!(parse_date_time_string("2020-01-01T00:00Z", false).is_err());
        assert!(parse_date_time_string("2020-01-01T00:00Z[UTC]", true).is_ok());
        assert!(parse_date_time_string("2020-01-01T00:00+01:00", false).is_ok());
        assert!(parse_date_time_string("2020-01-01T00:00", true).is_err());
    }

    #[test]
    fn year_zero_has_exactly_one_negative_spelling_forbidden() {
        assert!(parse_date_time_string("-000000-01-01", false).is_err());
        assert!(parse_date_time_string("+000000-01-01", false).is_ok());
        assert!(parse_date_time_string("0000-01-01", false).is_ok());
    }

    #[test]
    fn separators_may_not_mix_between_extended_and_basic_forms() {
        assert!(parse_date_time_string("2020-0101", false).is_err());
        assert!(parse_date_time_string("202001-01", false).is_err());
        assert!(parse_date_time_string("20200101T121314", false).is_ok());
        assert!(parse_date_time_string("2020-01-01T12:1314", false).is_err());
        assert!(parse_date_time_string("2020-01-01T1213:14", false).is_err());
    }

    #[test]
    fn leap_second_clamps_and_fraction_stops_at_nine_digits() {
        let parsed = parse_date_time_string("2016-12-31T23:59:60", false).unwrap();
        assert_eq!(parsed.time_ns % NS_PER_MINUTE, 59 * NS_PER_SECOND);
        assert!(parse_date_time_string("2020-01-01T00:00:00.123456789", false).is_ok());
        assert!(parse_date_time_string("2020-01-01T00:00:00.1234567890", false).is_err());
        assert!(parse_date_time_string("2020-01-01T00:00:61", false).is_err());
        assert!(parse_date_time_string("2020-01-01T24:00", false).is_err());
    }

    #[test]
    fn calendar_annotations_follow_first_wins_and_critical_rules() {
        let first = "2020-01-01[u-ca=iso8601][u-ca=hebrew]";
        assert_eq!(
            parse_date_time_string(first, false).unwrap().calendar,
            Some("iso8601".to_owned())
        );
        assert!(parse_date_time_string("2020-01-01[!u-ca=iso8601][u-ca=hebrew]", false).is_err());
        assert!(parse_date_time_string("2020-01-01[u-ca=iso8601][!u-ca=hebrew]", false).is_err());
        assert!(parse_date_time_string("2020-01-01[foo=bar]", false).is_ok());
        assert!(parse_date_time_string("2020-01-01[!foo=bar]", false).is_err());
        assert!(parse_date_time_string("2020-01-01[FOO=bar]", false).is_err());
    }

    #[test]
    fn time_zone_annotation_must_lead_and_be_unique() {
        assert!(parse_date_time_string("2020-01-01[UTC][UTC]", false).is_err());
        assert!(parse_date_time_string("2020-01-01[u-ca=iso8601][UTC]", false).is_err());
        assert!(parse_date_time_string("2020-01-01[+01:00:30]", false).is_err());
        assert_eq!(
            parse_date_time_string("2020-01-01[!Foo/Bar_Baz-1]", false)
                .unwrap()
                .time_zone,
            Some("Foo/Bar_Baz-1".to_owned())
        );
    }

    #[test]
    fn bare_times_that_read_as_dates_need_the_designator() {
        for ambiguous in ["2021-12", "1214", "0229", "1130", "12-14", "202112"] {
            assert!(parse_time_string(ambiguous).is_err(), "{ambiguous}");
            assert!(
                parse_time_string(&format!("T{ambiguous}")).is_ok(),
                "T{ambiguous}"
            );
        }
        for unambiguous in ["2021-13", "1314", "0230", "1131", "12-15:00"] {
            assert!(parse_time_string(unambiguous).is_ok(), "{unambiguous}");
        }
    }

    #[test]
    fn instant_goal_requires_both_time_and_offset() {
        assert!(parse_instant_string("2020-01-01T00:00Z").is_ok());
        assert!(parse_instant_string("2020-01-01T00:00+01:00:30.5").is_ok());
        assert!(parse_instant_string("2020-01-01T00:00").is_err());
        assert!(parse_instant_string("2020-01-01Z").is_err());
    }

    #[test]
    fn duration_fractions_spill_exactly_and_end_the_string() {
        let fields = parse_duration_string("PT1.5H").unwrap();
        assert_eq!(fields, [0, 0, 0, 0, 1, 30, 0, 0, 0, 0]);
        let fields = parse_duration_string("-PT0.000000001H").unwrap();
        assert_eq!(fields, [0, 0, 0, 0, 0, 0, 0, 0, -3, -600]);
        let fields = parse_duration_string("PT1.123456789S").unwrap();
        assert_eq!(fields, [0, 0, 0, 0, 0, 0, 1, 123, 456, 789]);
        assert!(parse_duration_string("PT1.5H1M").is_err());
        assert!(parse_duration_string("P1.5Y").is_err());
        assert!(parse_duration_string("P").is_err());
        assert!(parse_duration_string("PT").is_err());
        assert!(parse_duration_string("P1YT").is_err());
        assert!(parse_duration_string("P1M1Y").is_err());
    }
}
