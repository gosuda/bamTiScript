//! Deterministic Temporal.Now host boundary, exact rounding, and serialization.
//!
//! A host must inject civil clock readings, time-zone data, and
//! calendar projection data. This module never reads ambient process or machine
//! state. It implements the host-facing operations in Temporal sections 2 and
//! 11 together with the serialization operations shared by Temporal and Intl.
//!
//! Specification sources:
//! - <https://tc39.es/proposal-temporal/#sec-temporal-now-object>
//! - <https://tc39.es/proposal-temporal/#sec-temporal-roundnumbertoincrement>
//! - <https://tc39.es/proposal-temporal/#sec-temporal-tosecondsstringprecisionrecord>
//! - <https://tc39.es/proposal-temporal/#sec-temporal-formatcalendarannotation>

use std::fmt;

use super::instant_duration::{
    Duration, INSTANT_NS_MAX, INSTANT_NS_MIN, Instant, NS_PER_DAY, NS_PER_HOUR, NS_PER_MICROSECOND,
    NS_PER_MILLISECOND, NS_PER_MINUTE, NS_PER_SECOND, Overflow, Precision, RoundingMode,
    TemporalError, TemporalResult, Unit, format_iso_date, format_time_ns, round_to_increment,
    round_to_increment_as_if_positive, validate_rounding_increment, ymd_from_epoch_days,
};
use super::plain_types::{PlainDate, PlainDateTime, PlainTime};
pub use super::zoned_date_time::UtcOffsetNanoseconds;
use super::zoned_date_time::format_utc_offset;

/// One host clock observation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ClockSnapshot {
    instant: Instant,
}

impl ClockSnapshot {
    /// Builds a snapshot from a host reading that already satisfies the
    /// `HostSystemUTCEpochNanoseconds` range contract.
    pub fn new(epoch_nanoseconds: i128) -> TemporalResult<Self> {
        Ok(Self {
            instant: Instant::from_epoch_nanoseconds(epoch_nanoseconds)?,
        })
    }

    /// Implements the specification's default host clamping behavior.
    #[must_use]
    pub fn clamped(epoch_nanoseconds: i128) -> Self {
        match Self::new(epoch_nanoseconds.clamp(INSTANT_NS_MIN, INSTANT_NS_MAX)) {
            Ok(snapshot) => snapshot,
            Err(_) => unreachable!("clamped epoch nanoseconds are always a valid Instant"),
        }
    }

    #[must_use]
    pub const fn instant(self) -> Instant {
        self.instant
    }
}

/// Injected civil clock capability.
pub trait HostClock {
    type Error;

    fn snapshot(&mut self) -> Result<ClockSnapshot, Self::Error>;
}

/// The narrow time-zone capability required by Temporal.Now.
///
/// A C11.4 provider can implement this trait in addition to its transition and
/// local-time disambiguation operations. Identifiers are provider-owned typed
/// values; this boundary requires only cloning and canonical serialization.
pub trait NowTimeZoneProvider {
    type Error;
    type Identifier: AsRef<str> + Clone;

    fn system_time_zone_id(&mut self) -> Result<Self::Identifier, Self::Error>;

    fn offset_nanoseconds(
        &mut self,
        time_zone: &Self::Identifier,
        instant: Instant,
    ) -> Result<UtcOffsetNanoseconds, Self::Error>;
}

/// Calendar data needed by Intl to project a Temporal.Now ISO date.
///
/// Temporal.Now itself creates ISO-calendar values. Calendar-specific fields
/// remain provider data and are requested explicitly through
/// [`TemporalNow::project_calendar`].
pub trait CalendarProjectionProvider {
    type Error;
    type Identifier: AsRef<str> + Clone;
    type Projection;

    /// Returns the provider's canonical identifier for the required ISO calendar.
    fn iso8601_identifier(&self) -> Self::Identifier;

    fn project_iso_date(
        &mut self,
        calendar: &Self::Identifier,
        iso_date: PlainDate,
    ) -> Result<Self::Projection, Self::Error>;
}

/// Preserves which injected capability failed instead of flattening failures
/// into strings or pretending provider failures are ECMAScript range errors.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NowError<ClockError, TimeZoneError, CalendarError> {
    Temporal(TemporalError),
    Clock(ClockError),
    TimeZone(TimeZoneError),
    Calendar(CalendarError),
}

impl<C, T, K> From<TemporalError> for NowError<C, T, K> {
    fn from(error: TemporalError) -> Self {
        Self::Temporal(error)
    }
}

impl<C, T, K> fmt::Display for NowError<C, T, K>
where
    C: fmt::Display,
    T: fmt::Display,
    K: fmt::Display,
{
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Temporal(error) => error.fmt(formatter),
            Self::Clock(error) => write!(formatter, "clock provider: {error}"),
            Self::TimeZone(error) => write!(formatter, "time-zone provider: {error}"),
            Self::Calendar(error) => write!(formatter, "calendar provider: {error}"),
        }
    }
}

pub type NowResult<T, ClockError, TimeZoneError, CalendarError> =
    Result<T, NowError<ClockError, TimeZoneError, CalendarError>>;

/// The outcome of projecting one clock snapshot into a zone.
pub type ZonedNowResult<Clock, TimeZones, Calendars> = NowResult<
    NowZonedProjection<
        <TimeZones as NowTimeZoneProvider>::Identifier,
        <Calendars as CalendarProjectionProvider>::Identifier,
    >,
    <Clock as HostClock>::Error,
    <TimeZones as NowTimeZoneProvider>::Error,
    <Calendars as CalendarProjectionProvider>::Error,
>;

/// One clock snapshot projected into a time zone and tagged with an ISO calendar.
///
/// C11.4 can construct its `ZonedDateTime` directly from `instant`, `time_zone`,
/// and `calendar`; Intl can reuse the already-computed local ISO date-time.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NowZonedProjection<TimeZoneId, CalendarId> {
    snapshot: ClockSnapshot,
    time_zone: TimeZoneId,
    calendar: CalendarId,
    iso_date_time: PlainDateTime,
}

impl<TimeZoneId, CalendarId> NowZonedProjection<TimeZoneId, CalendarId> {
    #[must_use]
    pub const fn instant(&self) -> Instant {
        self.snapshot.instant()
    }

    #[must_use]
    pub fn time_zone_id(&self) -> &TimeZoneId {
        &self.time_zone
    }

    #[must_use]
    pub fn calendar_id(&self) -> &CalendarId {
        &self.calendar
    }

    #[must_use]
    pub const fn iso_date_time(&self) -> PlainDateTime {
        self.iso_date_time
    }
}

/// A deterministic Temporal.Now service over injected capabilities.
pub struct TemporalNow<Clock, TimeZones, Calendars> {
    clock: Clock,
    time_zones: TimeZones,
    calendars: Calendars,
}

impl<Clock, TimeZones, Calendars> TemporalNow<Clock, TimeZones, Calendars>
where
    Clock: HostClock,
    TimeZones: NowTimeZoneProvider,
    Calendars: CalendarProjectionProvider,
{
    #[must_use]
    pub const fn new(clock: Clock, time_zones: TimeZones, calendars: Calendars) -> Self {
        Self {
            clock,
            time_zones,
            calendars,
        }
    }

    /// Captures one civil reading through the host.
    pub fn capture(
        &mut self,
    ) -> NowResult<ClockSnapshot, Clock::Error, TimeZones::Error, Calendars::Error> {
        self.clock.snapshot().map_err(NowError::Clock)
    }

    /// `Temporal.Now.instant()`.
    pub fn instant(
        &mut self,
    ) -> NowResult<Instant, Clock::Error, TimeZones::Error, Calendars::Error> {
        Ok(self.capture()?.instant())
    }

    /// `Temporal.Now.timeZoneId()`.
    pub fn time_zone_id(
        &mut self,
    ) -> NowResult<TimeZones::Identifier, Clock::Error, TimeZones::Error, Calendars::Error> {
        self.time_zones
            .system_time_zone_id()
            .map_err(NowError::TimeZone)
    }

    /// Captures once and projects the instant into an explicit or system zone.
    pub fn zoned_date_time_iso(
        &mut self,
        time_zone: Option<TimeZones::Identifier>,
    ) -> ZonedNowResult<Clock, TimeZones, Calendars> {
        // SystemDateTime resolves the zone before observing the civil clock.
        let time_zone = match time_zone {
            Some(time_zone) => time_zone,
            None => self
                .time_zones
                .system_time_zone_id()
                .map_err(NowError::TimeZone)?,
        };
        let snapshot = self.capture()?;
        let offset = self
            .time_zones
            .offset_nanoseconds(&time_zone, snapshot.instant())
            .map_err(NowError::TimeZone)?;
        let iso_date_time = iso_date_time_for(snapshot.instant(), offset)?;
        Ok(NowZonedProjection {
            snapshot,
            time_zone,
            calendar: self.calendars.iso8601_identifier(),
            iso_date_time,
        })
    }

    /// `Temporal.Now.plainDateTimeISO()`.
    pub fn plain_date_time_iso(
        &mut self,
        time_zone: Option<TimeZones::Identifier>,
    ) -> NowResult<PlainDateTime, Clock::Error, TimeZones::Error, Calendars::Error> {
        Ok(self.zoned_date_time_iso(time_zone)?.iso_date_time())
    }

    /// `Temporal.Now.plainTimeISO()`.
    pub fn plain_time_iso(
        &mut self,
        time_zone: Option<TimeZones::Identifier>,
    ) -> NowResult<PlainTime, Clock::Error, TimeZones::Error, Calendars::Error> {
        Ok(self.zoned_date_time_iso(time_zone)?.iso_date_time().time)
    }

    /// Projects an already-captured ISO date through injected calendar data.
    /// This operation deliberately does not recapture the clock.
    pub fn project_calendar(
        &mut self,
        value: &NowZonedProjection<TimeZones::Identifier, Calendars::Identifier>,
        calendar: &Calendars::Identifier,
    ) -> NowResult<Calendars::Projection, Clock::Error, TimeZones::Error, Calendars::Error> {
        self.calendars
            .project_iso_date(calendar, value.iso_date_time().date)
            .map_err(NowError::Calendar)
    }
}

/// `GetISODateTimeFor` after a provider has supplied the offset.
pub fn iso_date_time_for(
    instant: Instant,
    offset: UtcOffsetNanoseconds,
) -> TemporalResult<PlainDateTime> {
    let local_ns = instant
        .epoch_nanoseconds()
        .checked_add(i128::from(offset.get()))
        .ok_or_else(|| TemporalError::range("time-zone projection overflow"))?;
    let epoch_days = local_ns.div_euclid(NS_PER_DAY);
    let time_ns = local_ns.rem_euclid(NS_PER_DAY);
    let epoch_days = i64::try_from(epoch_days)
        .map_err(|_| TemporalError::range("time-zone projection day overflow"))?;
    let (year, month, day) = ymd_from_epoch_days(epoch_days);
    let hour = time_ns / NS_PER_HOUR;
    let minute = (time_ns / NS_PER_MINUTE) % 60;
    let second = (time_ns / NS_PER_SECOND) % 60;
    let millisecond = (time_ns / NS_PER_MILLISECOND) % 1000;
    let microsecond = (time_ns / NS_PER_MICROSECOND) % 1000;
    let nanosecond = time_ns % NS_PER_MICROSECOND;
    PlainDateTime::new(
        year,
        i64::from(month),
        i64::from(day),
        [
            i64::try_from(hour).map_err(|_| TemporalError::range("hour overflow"))?,
            i64::try_from(minute).map_err(|_| TemporalError::range("minute overflow"))?,
            i64::try_from(second).map_err(|_| TemporalError::range("second overflow"))?,
            i64::try_from(millisecond).map_err(|_| TemporalError::range("millisecond overflow"))?,
            i64::try_from(microsecond).map_err(|_| TemporalError::range("microsecond overflow"))?,
            i64::try_from(nanosecond).map_err(|_| TemporalError::range("nanosecond overflow"))?,
        ],
        Overflow::Reject,
    )
}

/// Rounds a signed duration-like integer using `RoundNumberToIncrement`.
pub fn round_nanoseconds(
    value: i128,
    smallest_unit: Unit,
    increment: i128,
    mode: RoundingMode,
) -> TemporalResult<i128> {
    validate_rounding_increment(smallest_unit, increment, false)?;
    let unit_ns = smallest_unit.ns_per().ok_or_else(|| {
        TemporalError::range("exact nanosecond rounding requires day or a time unit")
    })?;
    let step = unit_ns
        .checked_mul(increment)
        .ok_or_else(|| TemporalError::range("rounding increment overflow"))?;
    round_to_increment(value, step, mode)
}

/// `RoundTemporalInstant`, whose direction is interpreted as if the epoch value
/// were positive even when it lies before 1970.
pub fn round_epoch_nanoseconds(
    value: i128,
    smallest_unit: Unit,
    increment: i128,
    mode: RoundingMode,
) -> TemporalResult<i128> {
    validate_rounding_increment(smallest_unit, increment, false)?;
    let unit_ns = smallest_unit
        .ns_per()
        .ok_or_else(|| TemporalError::range("epoch rounding requires day or a time unit"))?;
    let step = unit_ns
        .checked_mul(increment)
        .ok_or_else(|| TemporalError::range("rounding increment overflow"))?;
    round_to_increment_as_if_positive(value, step, mode)
}

/// Rounds exact time nanoseconds and balances them into a shared `Duration`.
pub fn round_and_balance_duration(
    total_nanoseconds: i128,
    smallest_unit: Unit,
    largest_unit: Unit,
    increment: i128,
    mode: RoundingMode,
) -> TemporalResult<Duration> {
    let rounded = round_nanoseconds(total_nanoseconds, smallest_unit, increment, mode)?;
    if rounded == i128::MIN {
        return Err(TemporalError::range("duration balancing overflow"));
    }
    Duration::from_time_nanoseconds(rounded, largest_unit)
}

/// Parsed value of the `fractionalSecondDigits` option.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum FractionalSecondDigits {
    #[default]
    Auto,
    Digits(u8),
}

impl FractionalSecondDigits {
    pub fn digits(count: u8) -> TemporalResult<Self> {
        Precision::digits(count)?;
        Ok(Self::Digits(count))
    }
}

/// Result of `ToSecondsStringPrecisionRecord`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SecondsStringPrecision {
    pub precision: Precision,
    pub unit: Unit,
    pub increment: i128,
}

impl SecondsStringPrecision {
    /// Resolves `smallestUnit` first; fractional digits apply only when it is absent.
    pub fn resolve(
        smallest_unit: Option<Unit>,
        fractional_digits: FractionalSecondDigits,
    ) -> TemporalResult<Self> {
        if let Some(unit) = smallest_unit {
            return match unit {
                Unit::Minute => Ok(Self {
                    precision: Precision::Minute,
                    unit,
                    increment: 1,
                }),
                Unit::Second => Ok(Self {
                    precision: Precision::Digits(0),
                    unit,
                    increment: 1,
                }),
                Unit::Millisecond => Ok(Self {
                    precision: Precision::Digits(3),
                    unit,
                    increment: 1,
                }),
                Unit::Microsecond => Ok(Self {
                    precision: Precision::Digits(6),
                    unit,
                    increment: 1,
                }),
                Unit::Nanosecond => Ok(Self {
                    precision: Precision::Digits(9),
                    unit,
                    increment: 1,
                }),
                _ => Err(TemporalError::range(
                    "seconds string smallestUnit must be minute through nanosecond",
                )),
            };
        }

        match fractional_digits {
            FractionalSecondDigits::Auto => Ok(Self {
                precision: Precision::Auto,
                unit: Unit::Nanosecond,
                increment: 1,
            }),
            FractionalSecondDigits::Digits(0) => Ok(Self {
                precision: Precision::Digits(0),
                unit: Unit::Second,
                increment: 1,
            }),
            FractionalSecondDigits::Digits(count @ 1..=3) => Ok(Self {
                precision: Precision::Digits(count),
                unit: Unit::Millisecond,
                increment: 10_i128.pow(u32::from(3 - count)),
            }),
            FractionalSecondDigits::Digits(count @ 4..=6) => Ok(Self {
                precision: Precision::Digits(count),
                unit: Unit::Microsecond,
                increment: 10_i128.pow(u32::from(6 - count)),
            }),
            FractionalSecondDigits::Digits(count @ 7..=9) => Ok(Self {
                precision: Precision::Digits(count),
                unit: Unit::Nanosecond,
                increment: 10_i128.pow(u32::from(9 - count)),
            }),
            FractionalSecondDigits::Digits(count) => Err(TemporalError::range(format!(
                "fractionalSecondDigits must be 0..=9, got {count}"
            ))),
        }
    }
}

/// Shared Temporal `toString` precision and rounding options.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ToStringRoundingOptions {
    pub smallest_unit: Option<Unit>,
    pub fractional_second_digits: FractionalSecondDigits,
    pub rounding_mode: RoundingMode,
}

impl Default for ToStringRoundingOptions {
    fn default() -> Self {
        Self {
            smallest_unit: None,
            fractional_second_digits: FractionalSecondDigits::Auto,
            rounding_mode: RoundingMode::Trunc,
        }
    }
}

impl ToStringRoundingOptions {
    pub fn precision(self) -> TemporalResult<SecondsStringPrecision> {
        SecondsStringPrecision::resolve(self.smallest_unit, self.fractional_second_digits)
    }
}

/// `calendarName` serialization option.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ShowCalendar {
    #[default]
    Auto,
    Always,
    Never,
    Critical,
}

/// `timeZoneName` serialization option.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ShowTimeZone {
    #[default]
    Auto,
    Never,
    Critical,
}

/// ZonedDateTime `offset` serialization option.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ShowOffset {
    #[default]
    Auto,
    Never,
}

/// Formats a canonical calendar annotation, including its own critical flag.
pub fn format_calendar_annotation(calendar: &str, show: ShowCalendar) -> TemporalResult<String> {
    if show == ShowCalendar::Never || (show == ShowCalendar::Auto && calendar == "iso8601") {
        return Ok(String::new());
    }
    validate_calendar_identifier(calendar)?;
    let critical = if show == ShowCalendar::Critical {
        "!"
    } else {
        ""
    };
    Ok(format!("[{critical}u-ca={calendar}]"))
}

/// Formats a time-zone annotation, including its own critical flag.
pub fn format_time_zone_annotation(time_zone: &str, show: ShowTimeZone) -> TemporalResult<String> {
    if show == ShowTimeZone::Never {
        return Ok(String::new());
    }
    validate_time_zone_annotation(time_zone)?;
    let critical = if show == ShowTimeZone::Critical {
        "!"
    } else {
        ""
    };
    Ok(format!("[{critical}{time_zone}]"))
}

fn validate_calendar_identifier(calendar: &str) -> TemporalResult<()> {
    let valid = !calendar.is_empty()
        && calendar.split('-').all(|part| {
            (3..=8).contains(&part.len())
                && part
                    .bytes()
                    .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit())
        });
    if !valid {
        return Err(TemporalError::range(format!(
            "invalid canonical calendar identifier {calendar:?}"
        )));
    }
    Ok(())
}

fn validate_time_zone_annotation(time_zone: &str) -> TemporalResult<()> {
    let valid = !time_zone.is_empty()
        && time_zone.bytes().all(|byte| {
            byte.is_ascii_alphanumeric() || matches!(byte, b'/' | b'_' | b'-' | b'+' | b':' | b'.')
        });
    if !valid {
        return Err(TemporalError::range(format!(
            "invalid time-zone annotation {time_zone:?}"
        )));
    }
    Ok(())
}

/// Formats a named-zone date-time offset after half-expand minute rounding.
pub fn format_utc_offset_rounded(offset: UtcOffsetNanoseconds) -> TemporalResult<String> {
    let rounded = round_to_increment(
        i128::from(offset.get()),
        NS_PER_MINUTE,
        RoundingMode::HalfExpand,
    )?;
    let rounded =
        i64::try_from(rounded).map_err(|_| TemporalError::range("rounded UTC offset overflow"))?;
    Ok(format_utc_offset(UtcOffsetNanoseconds::new(rounded)?))
}

/// Formats a validated ISO date-time without annotations.
#[must_use]
pub fn format_iso_date_time(value: &PlainDateTime, precision: Precision) -> String {
    let mut result = format_iso_date(value.date.year, value.date.month, value.date.day);
    result.push('T');
    result.push_str(&format_time_ns(
        value.time.to_nanoseconds_of_day(),
        precision,
    ));
    result
}

/// Rounds and serializes a PlainTime under shared Temporal precision options.
pub fn serialize_plain_time(
    value: &PlainTime,
    options: ToStringRoundingOptions,
) -> TemporalResult<String> {
    let precision = options.precision()?;
    let rounded = value.round(precision.unit, precision.increment, options.rounding_mode)?;
    Ok(format_time_ns(
        rounded.to_nanoseconds_of_day(),
        precision.precision,
    ))
}

/// Rounds and serializes a PlainDateTime with its calendar annotation.
pub fn serialize_plain_date_time(
    value: &PlainDateTime,
    calendar: &str,
    show_calendar: ShowCalendar,
    options: ToStringRoundingOptions,
) -> TemporalResult<String> {
    let precision = options.precision()?;
    let rounded = value.round(precision.unit, precision.increment, options.rounding_mode)?;
    let mut result = format_iso_date_time(&rounded, precision.precision);
    result.push_str(&format_calendar_annotation(calendar, show_calendar)?);
    Ok(result)
}

/// Inputs for annotation-aware ZonedDateTime/Intl serialization after C11.4 has
/// rounded the instant and projected it through the active time-zone provider.
pub struct ZonedSerialization<'a> {
    pub iso_date_time: &'a PlainDateTime,
    pub offset: UtcOffsetNanoseconds,
    pub time_zone: &'a str,
    pub calendar: &'a str,
    pub precision: Precision,
    pub show_offset: ShowOffset,
    pub show_time_zone: ShowTimeZone,
    pub show_calendar: ShowCalendar,
}

/// Serializes a provider-projected zoned date-time in RFC 9557 annotation order.
pub fn serialize_zoned_date_time(value: ZonedSerialization<'_>) -> TemporalResult<String> {
    let mut result = format_iso_date_time(value.iso_date_time, value.precision);
    if value.show_offset == ShowOffset::Auto {
        result.push_str(&format_utc_offset_rounded(value.offset)?);
    }
    result.push_str(&format_time_zone_annotation(
        value.time_zone,
        value.show_time_zone,
    )?);
    result.push_str(&format_calendar_annotation(
        value.calendar,
        value.show_calendar,
    )?);
    Ok(result)
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::rc::Rc;

    use super::*;

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum ClockFailure {
        Unavailable,
    }

    impl fmt::Display for ClockFailure {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("unavailable")
        }
    }

    struct FakeClock {
        readings: Vec<Result<ClockSnapshot, ClockFailure>>,
        cursor: usize,
        calls: Rc<Cell<usize>>,
    }

    impl HostClock for FakeClock {
        type Error = ClockFailure;

        fn snapshot(&mut self) -> Result<ClockSnapshot, Self::Error> {
            self.calls.set(self.calls.get() + 1);
            let reading = self
                .readings
                .get(self.cursor)
                .copied()
                .unwrap_or(Err(ClockFailure::Unavailable));
            self.cursor += 1;
            reading
        }
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum ZoneFailure {
        Offset,
    }

    impl fmt::Display for ZoneFailure {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(formatter, "{self:?}")
        }
    }

    struct FakeTimeZones {
        system_zone: Result<String, ZoneFailure>,
        offset: Result<UtcOffsetNanoseconds, ZoneFailure>,
        system_calls: Rc<Cell<usize>>,
        offset_calls: Rc<Cell<usize>>,
    }

    impl NowTimeZoneProvider for FakeTimeZones {
        type Error = ZoneFailure;
        type Identifier = String;

        fn system_time_zone_id(&mut self) -> Result<Self::Identifier, Self::Error> {
            self.system_calls.set(self.system_calls.get() + 1);
            self.system_zone.clone()
        }

        fn offset_nanoseconds(
            &mut self,
            _time_zone: &Self::Identifier,
            _instant: Instant,
        ) -> Result<UtcOffsetNanoseconds, Self::Error> {
            self.offset_calls.set(self.offset_calls.get() + 1);
            self.offset
        }
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum CalendarFailure {
        Projection,
    }

    impl fmt::Display for CalendarFailure {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("projection")
        }
    }

    struct FakeCalendars {
        fail: bool,
        calls: Rc<Cell<usize>>,
    }

    impl CalendarProjectionProvider for FakeCalendars {
        type Error = CalendarFailure;
        type Identifier = String;
        type Projection = String;

        fn iso8601_identifier(&self) -> Self::Identifier {
            "iso8601".to_owned()
        }

        fn project_iso_date(
            &mut self,
            calendar: &Self::Identifier,
            iso_date: PlainDate,
        ) -> Result<Self::Projection, Self::Error> {
            self.calls.set(self.calls.get() + 1);
            if self.fail {
                return Err(CalendarFailure::Projection);
            }
            Ok(format!(
                "{calendar}:{:04}-{:02}-{:02}",
                iso_date.year, iso_date.month, iso_date.day
            ))
        }
    }

    fn clock(readings: Vec<Result<ClockSnapshot, ClockFailure>>) -> (FakeClock, Rc<Cell<usize>>) {
        let calls = Rc::new(Cell::new(0));
        (
            FakeClock {
                readings,
                cursor: 0,
                calls: Rc::clone(&calls),
            },
            calls,
        )
    }

    fn time_zones(
        offset: Result<UtcOffsetNanoseconds, ZoneFailure>,
    ) -> (FakeTimeZones, Rc<Cell<usize>>, Rc<Cell<usize>>) {
        let system_calls = Rc::new(Cell::new(0));
        let offset_calls = Rc::new(Cell::new(0));
        (
            FakeTimeZones {
                system_zone: Ok("Test/Zone".to_owned()),
                offset,
                system_calls: Rc::clone(&system_calls),
                offset_calls: Rc::clone(&offset_calls),
            },
            system_calls,
            offset_calls,
        )
    }

    fn calendars(fail: bool) -> (FakeCalendars, Rc<Cell<usize>>) {
        let calls = Rc::new(Cell::new(0));
        (
            FakeCalendars {
                fail,
                calls: Rc::clone(&calls),
            },
            calls,
        )
    }

    #[test]
    fn signed_rounding_covers_every_mode_and_negative_ties() {
        let cases = [
            (RoundingMode::Ceil, 6, -4),
            (RoundingMode::Floor, 4, -6),
            (RoundingMode::Expand, 6, -6),
            (RoundingMode::Trunc, 4, -4),
            (RoundingMode::HalfCeil, 6, -4),
            (RoundingMode::HalfFloor, 4, -6),
            (RoundingMode::HalfExpand, 6, -6),
            (RoundingMode::HalfTrunc, 4, -4),
            (RoundingMode::HalfEven, 4, -4),
        ];
        for (mode, positive, negative) in cases {
            assert_eq!(
                round_nanoseconds(5, Unit::Nanosecond, 2, mode),
                Ok(positive)
            );
            assert_eq!(
                round_nanoseconds(-5, Unit::Nanosecond, 2, mode),
                Ok(negative)
            );
        }
        assert_eq!(
            round_nanoseconds(-7, Unit::Nanosecond, 2, RoundingMode::HalfEven),
            Ok(-8)
        );
    }

    #[test]
    fn epoch_rounding_uses_as_if_positive_directions() {
        let cases = [
            (RoundingMode::Ceil, -4),
            (RoundingMode::Floor, -6),
            (RoundingMode::Expand, -4),
            (RoundingMode::Trunc, -6),
            (RoundingMode::HalfCeil, -4),
            (RoundingMode::HalfFloor, -6),
            (RoundingMode::HalfExpand, -4),
            (RoundingMode::HalfTrunc, -6),
            (RoundingMode::HalfEven, -4),
        ];
        for (mode, expected) in cases {
            assert_eq!(
                round_epoch_nanoseconds(-5, Unit::Nanosecond, 2, mode),
                Ok(expected)
            );
        }
    }

    #[test]
    fn increment_validation_and_overflow_are_typed_errors() {
        assert!(round_nanoseconds(1, Unit::Second, 0, RoundingMode::Trunc).is_err());
        assert!(round_nanoseconds(1, Unit::Second, 7, RoundingMode::Trunc).is_err());
        assert!(round_nanoseconds(i128::MAX, Unit::Day, i128::MAX, RoundingMode::Ceil).is_err());
        assert!(
            round_and_balance_duration(
                i128::MIN,
                Unit::Nanosecond,
                Unit::Hour,
                1,
                RoundingMode::Trunc,
            )
            .is_err()
        );
    }

    #[test]
    fn duration_rounding_balances_positive_and_negative_carries() {
        let total = NS_PER_HOUR + 59 * NS_PER_MINUTE + 31 * NS_PER_SECOND;
        let positive = round_and_balance_duration(
            total,
            Unit::Minute,
            Unit::Hour,
            1,
            RoundingMode::HalfExpand,
        )
        .expect("positive balance");
        assert_eq!(positive.hours, 2);
        assert_eq!(positive.minutes, 0);

        let negative = round_and_balance_duration(
            -total,
            Unit::Minute,
            Unit::Hour,
            1,
            RoundingMode::HalfExpand,
        )
        .expect("negative balance");
        assert_eq!(negative.hours, -2);
        assert_eq!(negative.minutes, 0);
    }

    #[test]
    fn precision_resolution_covers_auto_digits_and_minute() {
        assert_eq!(
            SecondsStringPrecision::resolve(None, FractionalSecondDigits::Auto),
            Ok(SecondsStringPrecision {
                precision: Precision::Auto,
                unit: Unit::Nanosecond,
                increment: 1,
            })
        );
        assert_eq!(
            SecondsStringPrecision::resolve(
                None,
                FractionalSecondDigits::digits(2).expect("valid digits"),
            ),
            Ok(SecondsStringPrecision {
                precision: Precision::Digits(2),
                unit: Unit::Millisecond,
                increment: 10,
            })
        );
        assert_eq!(
            SecondsStringPrecision::resolve(Some(Unit::Minute), FractionalSecondDigits::Digits(9),),
            Ok(SecondsStringPrecision {
                precision: Precision::Minute,
                unit: Unit::Minute,
                increment: 1,
            })
        );
        assert!(FractionalSecondDigits::digits(10).is_err());
        assert!(
            SecondsStringPrecision::resolve(Some(Unit::Hour), FractionalSecondDigits::Auto,)
                .is_err()
        );
    }

    #[test]
    fn precision_serialization_trims_or_fixes_fraction_and_omits_seconds() {
        let time = PlainTime::new(1, 2, 3, 123, 400, 0, Overflow::Reject).expect("valid time");
        assert_eq!(
            serialize_plain_time(&time, ToStringRoundingOptions::default()),
            Ok("01:02:03.1234".to_owned())
        );
        assert_eq!(
            serialize_plain_time(
                &time,
                ToStringRoundingOptions {
                    fractional_second_digits: FractionalSecondDigits::Digits(6),
                    ..ToStringRoundingOptions::default()
                },
            ),
            Ok("01:02:03.123400".to_owned())
        );
        assert_eq!(
            serialize_plain_time(
                &time,
                ToStringRoundingOptions {
                    smallest_unit: Some(Unit::Minute),
                    ..ToStringRoundingOptions::default()
                },
            ),
            Ok("01:02".to_owned())
        );
    }

    #[test]
    fn annotations_preserve_order_and_independent_critical_flags() {
        assert_eq!(
            format_calendar_annotation("iso8601", ShowCalendar::Auto),
            Ok(String::new())
        );
        assert_eq!(
            format_calendar_annotation("iso8601", ShowCalendar::Critical),
            Ok("[!u-ca=iso8601]".to_owned())
        );
        assert_eq!(
            format_calendar_annotation("hebrew", ShowCalendar::Auto),
            Ok("[u-ca=hebrew]".to_owned())
        );
        assert_eq!(
            format_time_zone_annotation("Test/Zone", ShowTimeZone::Critical),
            Ok("[!Test/Zone]".to_owned())
        );

        let date_time = PlainDateTime::new(1970, 1, 1, [1, 2, 3, 123, 400, 0], Overflow::Reject)
            .expect("valid date-time");
        let offset = UtcOffsetNanoseconds::new(90 * 60 * 1_000_000_000).expect("valid offset");
        assert_eq!(
            serialize_zoned_date_time(ZonedSerialization {
                iso_date_time: &date_time,
                offset,
                time_zone: "Test/Zone",
                calendar: "hebrew",
                precision: Precision::Auto,
                show_offset: ShowOffset::Auto,
                show_time_zone: ShowTimeZone::Critical,
                show_calendar: ShowCalendar::Critical,
            }),
            Ok("1970-01-01T01:02:03.1234+01:30[!Test/Zone][!u-ca=hebrew]".to_owned())
        );
    }

    #[test]
    fn offset_formatting_is_exact_and_rounds_negative_ties_away_from_zero() {
        let exact = UtcOffsetNanoseconds::new(
            3_600 * 1_000_000_000 + 2 * 60 * 1_000_000_000 + 3_400_000_000,
        )
        .expect("valid offset");
        assert_eq!(format_utc_offset(exact), "+01:02:03.4");

        let negative_tie =
            UtcOffsetNanoseconds::new(-((62 * 60 + 30) * 1_000_000_000)).expect("valid offset");
        assert_eq!(
            format_utc_offset_rounded(negative_tie),
            Ok("-01:03".to_owned())
        );
        assert!(UtcOffsetNanoseconds::new(86_400 * 1_000_000_000).is_err());
    }

    #[test]
    fn now_uses_one_deterministic_snapshot_and_projects_zone_and_calendar() {
        let calls = Rc::new(Cell::new(0));
        let clock = FakeClock {
            readings: vec![
                Ok(ClockSnapshot::new(0).expect("valid snapshot")),
                Ok(ClockSnapshot::new(NS_PER_DAY).expect("valid snapshot")),
            ],
            cursor: 0,
            calls: Rc::clone(&calls),
        };
        let (zones, system_calls, offset_calls) = time_zones(Ok(UtcOffsetNanoseconds::new(
            90 * 60 * 1_000_000_000,
        )
        .expect("valid offset")));
        let (calendars, calendar_calls) = calendars(false);
        let mut now = TemporalNow::new(clock, zones, calendars);

        let projected = now.zoned_date_time_iso(None).expect("projection succeeds");
        assert_eq!(calls.get(), 1);
        assert_eq!(system_calls.get(), 1);
        assert_eq!(offset_calls.get(), 1);
        assert_eq!(projected.instant().epoch_nanoseconds(), 0);
        assert_eq!(
            projected.iso_date_time(),
            PlainDateTime::new(1970, 1, 1, [1, 30, 0, 0, 0, 0], Overflow::Reject)
                .expect("valid expected date-time")
        );
        assert_eq!(projected.calendar_id(), "iso8601");

        let calendar = "hebrew".to_owned();
        assert_eq!(
            now.project_calendar(&projected, &calendar),
            Ok("hebrew:1970-01-01".to_owned())
        );
        assert_eq!(calendar_calls.get(), 1);
        assert_eq!(
            calls.get(),
            1,
            "calendar projection must not recapture time"
        );
    }

    #[test]
    fn injected_readings_prove_no_ambient_clock_dependency() {
        let (clock_a, _) = clock(vec![Ok(ClockSnapshot::new(-1).expect("valid snapshot"))]);
        let (zones_a, _, _) = time_zones(Ok(UtcOffsetNanoseconds::new(0).expect("valid offset")));
        let (calendars_a, _) = calendars(false);
        let mut now_a = TemporalNow::new(clock_a, zones_a, calendars_a);

        let (clock_b, _) = clock(vec![Ok(ClockSnapshot::new(1).expect("valid snapshot"))]);
        let (zones_b, _, _) = time_zones(Ok(UtcOffsetNanoseconds::new(0).expect("valid offset")));
        let (calendars_b, _) = calendars(false);
        let mut now_b = TemporalNow::new(clock_b, zones_b, calendars_b);

        assert_eq!(
            now_a
                .instant()
                .expect("first injected clock")
                .epoch_nanoseconds(),
            -1
        );
        assert_eq!(
            now_b
                .instant()
                .expect("second injected clock")
                .epoch_nanoseconds(),
            1
        );
    }

    #[test]
    fn provider_failures_remain_typed_and_clock_is_not_retried() {
        let (failed_clock, clock_calls) = clock(vec![Err(ClockFailure::Unavailable)]);
        let (zones, _, _) = time_zones(Ok(UtcOffsetNanoseconds::new(0).expect("valid offset")));
        let (first_calendars, _) = calendars(false);
        let mut now = TemporalNow::new(failed_clock, zones, first_calendars);
        assert_eq!(
            now.instant(),
            Err(NowError::Clock(ClockFailure::Unavailable))
        );
        assert_eq!(clock_calls.get(), 1);

        let (good_clock, _) = clock(vec![Ok(ClockSnapshot::new(0).expect("valid snapshot"))]);
        let (failed_zones, _, _) = time_zones(Err(ZoneFailure::Offset));
        let (second_calendars, _) = calendars(false);
        let mut now = TemporalNow::new(good_clock, failed_zones, second_calendars);
        assert_eq!(
            now.zoned_date_time_iso(Some("UTC".to_owned())),
            Err(NowError::TimeZone(ZoneFailure::Offset))
        );

        let (good_clock, _) = clock(vec![Ok(ClockSnapshot::new(0).expect("valid snapshot"))]);
        let (zones, _, _) = time_zones(Ok(UtcOffsetNanoseconds::new(0).expect("valid offset")));
        let (failed_calendars, _) = calendars(true);
        let mut now = TemporalNow::new(good_clock, zones, failed_calendars);
        let projected = now
            .zoned_date_time_iso(Some("UTC".to_owned()))
            .expect("zone projection");
        assert_eq!(
            now.project_calendar(&projected, &"hebrew".to_owned()),
            Err(NowError::Calendar(CalendarFailure::Projection))
        );
    }

    #[test]
    fn clock_clamping_and_boundary_zone_projection_are_exact() {
        assert_eq!(
            ClockSnapshot::clamped(i128::MAX)
                .instant()
                .epoch_nanoseconds(),
            INSTANT_NS_MAX
        );
        assert_eq!(
            ClockSnapshot::clamped(i128::MIN)
                .instant()
                .epoch_nanoseconds(),
            INSTANT_NS_MIN
        );
        let before_epoch = iso_date_time_for(
            Instant::from_epoch_nanoseconds(-1).expect("valid instant"),
            UtcOffsetNanoseconds::new(0).expect("valid offset"),
        )
        .expect("valid projection");
        assert_eq!(before_epoch.date.year, 1969);
        assert_eq!(before_epoch.date.month, 12);
        assert_eq!(before_epoch.date.day, 31);
        assert_eq!(before_epoch.time.hour, 23);
        assert_eq!(before_epoch.time.nanosecond, 999);
    }
}
