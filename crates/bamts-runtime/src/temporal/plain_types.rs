//! Temporal plain types: `PlainTime`, `PlainDate`, `PlainDateTime`,
//! `PlainYearMonth`, `PlainMonthDay` over the ISO 8601 calendar.
//!
//! All arithmetic is exact checked integer work on proleptic-Gregorian
//! rata-die days plus nanoseconds-of-day; no floats, no ambient host access.
//! Zoned/time-zone operations are excluded — that is the jiff C11.3 boundary.

use std::fmt;

use super::instant_duration::{
    days_in_month, epoch_days_from_ymd, format_iso_date, format_time_ns, is_leap_year,
    parse_iso_datetime_string, round_to_increment, validate_rounding_increment, ymd_from_epoch_days,
    Duration, Instant, Overflow, Precision, RoundingMode, TemporalError, TemporalResult, Unit,
    INSTANT_NS_MAX, NS_PER_DAY, NS_PER_HOUR, NS_PER_MICROSECOND, NS_PER_MILLISECOND,
    NS_PER_MINUTE, NS_PER_SECOND,
};

// ---------------------------------------------------------------------------
// Limits and ISO helpers
// ---------------------------------------------------------------------------

/// ISODateTimeWithinLimits: ns strictly inside ±(8.64e21 + NS_PER_DAY).
pub fn iso_datetime_within_limits(days: i64, time_ns: i128) -> bool {
    let total = (days as i128) * NS_PER_DAY + time_ns;
    let bound = INSTANT_NS_MAX + NS_PER_DAY;
    -bound < total && total < bound
}

/// ISODateWithinLimits: check the datetime at noon (spec step 4).
pub fn iso_date_within_limits(year: i32, month: u8, day: u8) -> bool {
    let days = epoch_days_from_ymd(year, month, day);
    iso_datetime_within_limits(days, 12 * NS_PER_HOUR)
}

/// ISO-860 doctor field validation (RejectISODate range part).
fn reject_iso_date(year: i32, month: u8, day: u8) -> TemporalResult<()> {
    if !(1..=12).contains(&month) {
        return Err(TemporalError::range(format!("month {month} out of range")));
    }
    if day < 1 || day > days_in_month(year, month) {
        return Err(TemporalError::range(format!(
            "day {day} out of range for {year}-{month:02}"
        )));
    }
    Ok(())
}

/// RegulateISODate: apply overflow policy to possibly-out-of-range fields.
pub fn regulate_iso_date(year: i32, month: i64, day: i64, overflow: Overflow) -> TemporalResult<(i32, u8, u8)> {
    match overflow {
        Overflow::Reject => {
            let month = u8::try_from(month)
                .ok()
                .filter(|m| (1..=12).contains(m))
                .ok_or_else(|| TemporalError::range(format!("month {month} out of range")))?;
            let day = u8::try_from(day)
                .ok()
                .filter(|d| (1..=days_in_month(year, month)).contains(d))
                .ok_or_else(|| TemporalError::range(format!("day {day} out of range")))?;
            Ok((year, month, day))
        }
        Overflow::Constrain => {
            // ConstrainISODate: clamp month, then clamp day into the month.
            let clamped_month = month.clamp(1, 12) as u8;
            let clamped_day = day.clamp(1, i64::from(days_in_month(year, clamped_month))) as u8;
            Ok((year, clamped_month, clamped_day))
        }
    }
}

/// ISO-8601 day of week: 1 = Monday … 7 = Sunday (ISODayOfWeek).
pub fn iso_day_of_week(year: i32, month: u8, day: u8) -> u8 {
    let days = epoch_days_from_ymd(year, month, day);
    // 1970-01-01 (day 0) was Thursday = 4.
    ((days % 7 + 7) % 7 + 4 - 1) as u8 % 7 + 1
}

/// Day of year, 1-based (ISODayOfYear).
pub fn iso_day_of_year(year: i32, month: u8, day: u8) -> u16 {
    let first_of_year = epoch_days_from_ymd(year, 1, 1);
    (epoch_days_from_ymd(year, month, day) - first_of_year + 1) as u16
}

/// ISO-8601 week date: returns (week-numbering year, week 1-53).
pub fn iso_week_of_year(year: i32, month: u8, day: u8) -> (i32, u8) {
    let days = epoch_days_from_ymd(year, month, day);
    let dow = i64::from(iso_day_of_week(year, month, day));
    let thursday = days + 4 - dow;
    let (week_year, _, _) = ymd_from_epoch_days(thursday);
    let first_thursday = epoch_days_from_ymd(week_year, 1, 4)
        - (iso_day_of_week(week_year, 1, 4) as i64)
        + 3;
    let week = (thursday - first_thursday) / 7 + 1;
    (week_year, week as u8)
}

// ---------------------------------------------------------------------------
// PlainTime
// ---------------------------------------------------------------------------

///  nanosecond-precision wall-clock time, no date, no zone.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct PlainTime {
    pub hour: u8,
    pub minute: u8,
    pub second: u8,
    pub millisecond: u16,
    pub microsecond: u16,
    pub nanosecond: u16,
}

impl PlainTime {
    /// RegulateTime under the overflow option.
    pub fn new(
        hour: i64,
        minute: i64,
        second: i64,
        millisecond: i64,
        microsecond: i64,
        nanosecond: i64,
        overflow: Overflow,
    ) -> TemporalResult<PlainTime> {
        let clamp = |v: i64, max: i64| -> i64 {
            match overflow {
                Overflow::Constrain => v.clamp(0, max),
                Overflow::Reject => v,
            }
        };
        let hour = clamp(hour, 23);
        let minute = clamp(minute, 59);
        let second = clamp(second, 59);
        let millisecond = clamp(millisecond, 999);
        let microsecond = clamp(microsecond, 999);
        let nanosecond = clamp(nanosecond, 999);
        Self::from_validated(hour, minute, second, millisecond, microsecond, nanosecond)
    }

    fn from_validated(
        hour: i64,
        minute: i64,
        second: i64,
        millisecond: i64,
        microsecond: i64,
        nanosecond: i64,
    ) -> TemporalResult<PlainTime> {
        if !(0..=23).contains(&hour)
            || !(0..=59).contains(&minute)
            || !(0..=59).contains(&second)
            || !(0..=999).contains(&millisecond)
            || !(0..=999).contains(&microsecond)
            || !(0..=999).contains(&nanosecond)
        {
            return Err(TemporalError::range("PlainTime component out of range"));
        }
        Ok(PlainTime {
            hour: hour as u8,
            minute: minute as u8,
            second: second as u8,
            millisecond: millisecond as u16,
            microsecond: microsecond as u16,
            nanosecond: nanosecond as u16,
        })
    }

    pub fn midnight() -> PlainTime {
        PlainTime::default()
    }

    /// Nanoseconds since midnight.
    pub fn to_nanoseconds_of_day(&self) -> i128 {
        self.hour as i128 * NS_PER_HOUR
            + self.minute as i128 * NS_PER_MINUTE
            + self.second as i128 * NS_PER_SECOND
            + self.millisecond as i128 * NS_PER_MILLISECOND
            + self.microsecond as i128 * NS_PER_MICROSECOND
            + self.nanosecond as i128
    }

    fn from_nanoseconds_of_day(ns: i128) -> PlainTime {
        debug_assert!((0..NS_PER_DAY).contains(&ns));
        let hour = ns / NS_PER_HOUR;
        let minute = (ns / NS_PER_MINUTE) % 60;
        let second = (ns / NS_PER_SECOND) % 60;
        let frac = ns % NS_PER_SECOND;
        PlainTime {
            hour: hour as u8,
            minute: minute as u8,
            second: second as u8,
            millisecond: (frac / NS_PER_MILLISECOND) as u16,
            microsecond: (frac % NS_PER_MILLISECOND / NS_PER_MICROSECOND) as u16,
            nanosecond: (frac % NS_PER_MICROSECOND) as u16,
        }
    }

    /// AddDurationToTime: signed nanosecond shift; returns (carry days, time).
    pub fn add_signed_nanoseconds(&self, delta_ns: i128) -> (i128, PlainTime) {
        let total = self.to_nanoseconds_of_day() + delta_ns;
        let carry = total.div_euclid(NS_PER_DAY);
        (carry, PlainTime::from_nanoseconds_of_day(total.rem_euclid(NS_PER_DAY)))
    }

    pub fn add(&self, duration: &Duration) -> TemporalResult<PlainTime> {
        if duration.years != 0 || duration.months != 0 || duration.weeks != 0 || duration.days != 0 {
            return Err(TemporalError::range(
                "PlainTime arithmetic does not accept date units",
            ));
        }
        Ok(self.add_signed_nanoseconds(duration.time_total_nanoseconds()).1)
    }

    pub fn subtract(&self, duration: &Duration) -> TemporalResult<PlainTime> {
        self.add(&duration.negated())
    }

    /// DifferenceTime: rounded to `smallest_unit` and balanced to `largest`.
    pub fn until(
        &self,
        other: PlainTime,
        largest_unit: Unit,
        smallest_unit: Unit,
        increment: i128,
        mode: RoundingMode,
    ) -> TemporalResult<Duration> {
        if largest_unit.category() == super::instant_duration::UnitCategory::Date
            || smallest_unit.category() == super::instant_duration::UnitCategory::Date
        {
            return Err(TemporalError::range(
                "PlainTime difference supports time units only",
            ));
        }
        if smallest_unit < largest_unit {
            return Err(TemporalError::range("smallestUnit must not be larger than largestUnit"));
        }
        validate_rounding_increment(smallest_unit, increment, false)?;
        let diff = other.to_nanoseconds_of_day() - self.to_nanoseconds_of_day();
        let unit_ns = smallest_unit.ns_per().ok_or(TemporalErrorKindRange)?;
        let step = unit_ns.checked_mul(increment).ok_or(TemporalErrorKindRange)?;
        let rounded = round_to_increment(diff, step, mode)?;
        Duration::from_time_nanoseconds(rounded, largest_unit.max(Unit::Hour))
    }

    pub fn since(
        &self,
        other: PlainTime,
        largest_unit: Unit,
        smallest_unit: Unit,
        increment: i128,
        mode: RoundingMode,
    ) -> TemporalResult<Duration> {
        other.until(*self, largest_unit, smallest_unit, increment, mode)
    }

    pub fn round(&self, unit: Unit, increment: i128, mode: RoundingMode) -> TemporalResult<PlainTime> {
        let unit_ns = match unit {
            Unit::Day => NS_PER_DAY,
            _ => unit.ns_per().ok_or(TemporalErrorKindRange)?,
        };
        if increment < 1 {
            return Err(TemporalError::range("roundingIncrement must be >= 1"));
        }
        let per_day = NS_PER_DAY / unit_ns;
        if increment > per_day || per_day % increment != 0 {
            return Err(TemporalError::range(format!(
                "roundingIncrement {increment} must evenly divide {per_day} {}s per day",
                unit.name()
            )));
        }
        let rounded = round_to_increment(self.to_nanoseconds_of_day(), unit_ns * increment, mode)?;
        Ok(PlainTime::from_nanoseconds_of_day(rounded.rem_euclid(NS_PER_DAY)))
    }

    /// `withTime`-style field replacement; `None` keeps the current value.
    pub fn with(
        &self,
        hour: Option<i64>,
        minute: Option<i64>,
        second: Option<i64>,
        millisecond: Option<i64>,
        microsecond: Option<i64>,
        nanosecond: Option<i64>,
        overflow: Overflow,
    ) -> TemporalResult<PlainTime> {
        PlainTime::new(
            hour.unwrap_or(self.hour.into()),
            minute.unwrap_or(self.minute.into()),
            second.unwrap_or(self.second.into()),
            millisecond.unwrap_or(self.millisecond.into()),
            microsecond.unwrap_or(self.microsecond.into()),
            nanosecond.unwrap_or(self.nanosecond.into()),
            overflow,
        )
    }

    /// ParseTemporalTimeString. Accepts bare `T?HH:MM[:SS[.f{1,9}]]` (no
    /// offset/annotations allowed on a bare time) or a full date-time from
    /// which the time portion is taken.
    pub fn parse(text: &str) -> TemporalResult<PlainTime> {
        let trimmed = text.trim_start_matches(|c| c == 'T' || c == 't').trim_start();
        // Full date-time form: date component first.
        if trimmed.len() > 2 && (trimmed.as_bytes()[4.min(trimmed.len() - 1)] == b'-'
            || trimmed.starts_with(['+', '-'])
            || trimmed.chars().take(4).all(|ch| ch.is_ascii_digit()))
        {
            if let Ok(full) = parse_iso_datetime_string(text) {
                if !full.has_time {
                    return Err(TemporalError::syntax("PlainTime string requires a time component"));
                }
                return PlainTime::from_nanoseconds_of_day(full.time_ns).into_ok();
            }
        }
        match parse_iso_datetime_string(text) {
            Ok(full) => {
                if !full.has_time {
                    Err(TemporalError::syntax("PlainTime string requires a time component"))
                } else {
                    Ok(PlainTime::from_nanoseconds_of_day(full.time_ns))
                }
            }
            Err(_date_err) => {
                // Bare time form, possibly with a leading T.
                let bare = if !trimmed.is_empty() && (text.as_bytes().first() == Some(&b'T')
                    || text.as_bytes().first() == Some(&b't'))
                {
                    &text[1..]
                } else {
                    text
                };
                parse_bare_time_string(bare)
            }
        }
    }

    fn into_ok(self) -> TemporalResult<PlainTime> {
        Ok(self)
    }

    /// TemporalTimeToString.
    pub fn format(&self, precision: Precision) -> String {
        format_time_ns(self.to_nanoseconds_of_day(), precision)
    }
}

impl fmt::Display for PlainTime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.format(Precision::Auto))
    }
}

fn parse_bare_time_string(text: &str) -> TemporalResult<PlainTime> {
    // Reuse the datetime grammar on a synthetic epoch date; reject offsets
    // and annotations that would leak zone semantics into a plain time.
    let synthetic = format!("2000-01-01T{text}");
    let full = parse_iso_datetime_string(&synthetic)
        .map_err(|e| TemporalError::syntax(format!("invalid time string: {}", e.message)))?;
    if full.offset.is_some() || full.time_zone.is_some() || full.calendar.is_some() {
        return Err(TemporalError::range(
            "PlainTime string must not contain a UTC offset, time zone, or calendar",
        ));
    }
    Ok(PlainTime::from_nanoseconds_of_day(full.time_ns))
}

const TemporalErrorKindRange: TemporalError = TemporalError::const_range();

impl TemporalError {
    const fn const_range() -> TemporalError {
        TemporalError { kind: TemporalErrorKind::Range, message: String::new() }
    }
}

use super::instant_duration::TemporalErrorKind;

// ---------------------------------------------------------------------------
// PlainDate
// ---------------------------------------------------------------------------

/// Calendar date on the proleptic Gregorian ISO calendar.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PlainDate {
    pub year: i32,
    pub month: u8,
    pub day: u8,
}

impl PlainDate {
    /// CreateTemporalDate (fields + overflow policy + within-limits check).
    pub fn new(year: i32, month: i64, day: i64, overflow: Overflow) -> TemporalResult<PlainDate> {
        let (y, m, d) = regulate_iso_date(year, month, day, overflow)?;
        if !iso_date_within_limits(y, m, d) {
            return Err(TemporalError::range(format!(
                "date {} outside ISO representable range",
                format_iso_date(y, m, d)
            )));
        }
        Ok(PlainDate { year: y, month: m, day: d })
    }

    fn from_validated(year: i32, month: u8, day: u8) -> TemporalResult<PlainDate> {
        reject_iso_date(year, month, day)?;
        if !iso_date_within_limits(year, month, day) {
            return Err(TemporalError::range("date outside ISO representable range"));
        }
        Ok(PlainDate { year, month, day })
    }

    fn epoch_days(&self) -> i64 {
        epoch_days_from_ymd(self.year, self.month, self.day)
    }

    fn from_epoch_days(days: i64) -> TemporalResult<PlainDate> {
        let (y, m, d) = ymd_from_epoch_days(days);
        PlainDate::from_validated(y, m, d)
    }

    pub fn day_of_week(&self) -> u8 {
        iso_day_of_week(self.year, self.month, self.day)
    }

    pub fn day_of_year(&self) -> u16 {
        iso_day_of_year(self.year, self.month, self.day)
    }

    pub fn week_of_year(&self) -> (i32, u8) {
        iso_week_of_year(self.year, self.month, self.day)
    }

    pub fn days_in_month(&self) -> u8 {
        days_in_month(self.year, self.month)
    }

    pub fn days_in_year(&self) -> u16 {
        if is_leap_year(self.year) { 366 } else { 365 }
    }

    pub fn months_in_year(&self) -> u8 {
        12
    }

    pub fn in_leap_year(&self) -> bool {
        is_leap_year(self.year)
    }

    /// `with` per Temporal.PlainDate.prototype.with (field-wise replacement).
    pub fn with(
        &self,
        year: Option<i32>,
        month: Option<i64>,
        day: Option<i64>,
        overflow: Overflow,
    ) -> TemporalResult<PlainDate> {
        PlainDate::new(
            year.unwrap_or(self.year),
            month.unwrap_or(self.month.into()),
            day.unwrap_or(self.day.into()),
            overflow,
        )
    }

    /// AddISODate: constrain year/month movement, then add weeks+days via
    /// rata-die. Duration must not contain time units beyond day-level:
    /// spec folds sub-day duration into the date only via relativeTo rules;
    /// for a PlainDate, time fields are rejected when non-zero.
    pub fn add(&self, duration: &Duration, overflow: Overflow) -> TemporalResult<PlainDate> {
        let d = self.add_iso_date(duration, overflow)?;
        Ok(d)
    }

    pub fn subtract(&self, duration: &Duration, overflow: Overflow) -> TemporalResult<PlainDate> {
        self.add(&duration.negated(), overflow)
    }

    fn add_iso_date(&self, duration: &Duration, overflow: Overflow) -> TemporalResult<PlainDate> {
        if duration.hours != 0
            || duration.minutes != 0
            || duration.seconds != 0
            || duration.milliseconds != 0
            || duration.microseconds != 0
            || duration.nanoseconds != 0
        {
            return Err(TemporalError::range(
                "PlainDate arithmetic does not accept time units",
            ));
        }
        // 1. Add years and months by constraining into the target month.
        let total_months = i64::from(self.year) * 12 + i64::from(self.month) - 1
            + duration.years * 12
            + duration.months;
        let new_year_i = total_months.div_euclid(12);
        let new_month_i = total_months.rem_euclid(12) + 1;
        let new_year = i32::try_from(new_year_i)
            .map_err(|_| TemporalError::range("year outside i32 range after arithmetic"))?;
        let (y, m, d) = regulate_iso_date(
            new_year,
            new_month_i,
            i64::from(self.day),
            overflow,
        )?;
        // 2. Add weeks and days on the day timeline (exact).
        let days = epoch_days_from_ymd(y, m, d)
            .checked_add((duration.weeks as i64).checked_mul(7).and_then(|w| w.checked_add(duration.days)).ok_or_else(|| {
                TemporalError::range("Duration week/day arithmetic overflow")
            })?)
            .ok_or_else(|| TemporalError::range("date arithmetic overflow"))?;
        PlainDate::from_epoch_days(days)
    }

    /// DifferenceISODate: exact years/months/weeks/days (no rounding beyond
    /// integer truncation of the largest unit pair), rounded under `mode` to
    /// `smallest_unit` when the difference has a remainder in a smaller unit.
    pub fn until(
        &self,
        other: PlainDate,
        largest_unit: Unit,
        smallest_unit: Unit,
        increment: i128,
        mode: RoundingMode,
        overflow: Overflow,
    ) -> TemporalResult<Duration> {
        if !matches!(largest_unit, Unit::Year | Unit::Month | Unit::Week | Unit::Day)
            || !matches!(smallest_unit, Unit::Year | Unit::Month | Unit::Week | Unit::Day)
        {
            return Err(TemporalError::range(
                "PlainDate difference units must be year..day",
            ));
        }
        if smallest_unit < largest_unit {
            return Err(TemporalError::range("smallestUnit must not be larger than largestUnit"));
        }
        if increment < 1 {
            return Err(TemporalError::range("roundingIncrement must be >= 1"));
        }
        let sign_flip = self > &other;
        let (a, b) = if sign_flip { (other, *self) } else { (*self, other) };
        let whole = difference_iso_date_whole(&a, &b, largest_unit)?;
        let mut result = whole;
        // Round into smallest/increment if the residual day remainder exists.
        if smallest_unit != largest_unit || increment != 1 {
            if smallest_unit == Unit::Day {
                // Rounding in days: recompute whole-largest part then add rounded days.
                let mut days_only = whole;
                days_only.weeks = 0;
                days_only.days = 0;
                let rebased = a.add_iso_date(&days_only, Overflow::Constrain)?;
                let remainder_days = b.epoch_days() - rebased.epoch_days();
                let rounded_days = round_to_increment(i128::from(remainder_days), increment, mode)?;
                let mut rounded = days_only;
                rounded.days = days_only.days.checked_add(i64::try_from(rounded_days).map_err(|_| TemporalError::range("overflow"))?).ok_or_else(|| TemporalError::range("overflow"))?;
                // Balance day remainder into weeks when largest == week.
                if largest_unit == Unit::Week {
                    let weeks = rounded.days / 7;
                    rounded.days -= weeks * 7;
                    let weeks = rounded.weeks.checked_add(weeks).ok_or_else(|| TemporalError::range("overflow"))?;
                    rounded.weeks = weeks;
                }
                result = rounded;
            } else {
                // Calendar rounding beyond day granularity requires relativeTo
                // semantics handled here at whole-unit precision: truncate.
            }
        }
        if sign_flip {
            result = result.negated();
        }
        Ok(result)
    }

    pub fn since(
        &self,
        other: PlainDate,
        largest_unit: Unit,
        smallest_unit: Unit,
        increment: i128,
        mode: RoundingMode,
        overflow: Overflow,
    ) -> TemporalResult<Duration> {
        other.until(*self, largest_unit, smallest_unit, increment, mode, overflow)
    }

    pub fn to_plain_date_time(&self, time: PlainTime) -> TemporalResult<PlainDateTime> {
        PlainDateTime::from_parts(*self, time)
    }

    pub fn to_plain_year_month(&self) -> PlainYearMonth {
        PlainYearMonth { year: self.year, month: self.month, reference_day: 1 }
    }

    pub fn to_plain_month_day(&self) -> PlainMonthDay {
        PlainMonthDay { year: self.year, month: self.month, day: self.day }
    }

    /// ParseTemporalDateString.
    pub fn parse(text: &str) -> TemporalResult<PlainDate> {
        let full = parse_iso_datetime_string(text)?;
        PlainDate::from_validated(full.year, full.month, full.day)
    }

    /// TemporalDateToString ([u-ca=iso8601] shown only in showCriticalAlways
    /// mode; the default auto mode omits it).
    pub fn format(&self) -> String {
        format_iso_date(self.year, self.month, self.day)
    }
}

impl fmt::Display for PlainDate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.format())
    }
}

/// Whole-unit date difference used by `PlainDate::until`: computes the
/// largest number of `largest_unit` steps from `start` that does not pass
/// `end`, then the residual days/weeks below that unit.
fn difference_iso_date_whole(
    start: &PlainDate,
    end: &PlainDate,
    largest_unit: Unit,
) -> TemporalResult<Duration> {
    if start == end {
        return Ok(Duration::default());
    }
    let end_days = end.epoch_days();
    match largest_unit {
        Unit::Year | Unit::Month => {
            // Greedy forward fill: candidate = start + k units.
            // Bounds on iteration: total month span + 1.
            let months_total = (i64::from(end.year) - i64::from(start.year)) * 12
                + (i64::from(end.month) - i64::from(start.month));
            let steps = match largest_unit {
                Unit::Year => months_total.div_euclid(12),
                _ => months_total,
            };
            let mut best: i64 = 0;
            let mut best_date = *start;
            // Binary search in [0, steps+1] for the largest fitting k.
            let mut lo: i64 = 0;
            let mut hi: i64 = steps.saturating_add(2);
            while lo <= hi {
                let mid = lo.midpoint(hi);
                let candidate = if largest_unit == Unit::Year {
                    Duration::new(mid, 0, 0, 0, 0, 0, 0, 0, 0, 0)?
                } else {
                    Duration::new(0, mid, 0, 0, 0, 0, 0, 0, 0, 0)?
                };
                match start.add_iso_date(&candidate, Overflow::Constrain) {
                    Ok(date) if date <= *end => {
                        best = mid;
                        best_date = date;
                        lo = mid + 1;
                    }
                    _ => hi = mid - 1,
                }
            }
            let remainder_days = end_days - best_date.epoch_days();
            // Decompose remainder into months+days if largest==year? Spec
            // balancing: difference with largestUnit year yields years+months+days.
            match largest_unit {
                Unit::Year => {
                    let extra_months = (i64::from(end.year) * 12 + i64::from(end.month))
                        - (i64::from(best_date.year) * 12 + i64::from(best_date.month));
                    // Keep months in [0, 11]: binary search a fitting month count.
                    let mut m_lo = 0_i64;
                    let mut m_hi = extra_months.max(0);
                    let mut m_best = 0_i64;
                    let mut m_date = best_date;
                    while m_lo <= m_hi {
                        let mid = m_lo.midpoint(m_hi);
                        let candidate = Duration::new(0, mid, 0, 0, 0, 0, 0, 0, 0, 0)?;
                        match best_date.add_iso_date(&candidate, Overflow::Constrain) {
                            Ok(date) if date <= *end => {
                                m_best = mid;
                                m_date = date;
                                m_lo = mid + 1;
                            }
                            _ => m_hi = mid - 1,
                        }
                    }
                    let days_left = end_days - m_date.epoch_days();
                    Duration::new(best, m_best, 0, days_left, 0, 0, 0, 0, 0, 0)
                }
                _ => Duration::new(0, best, 0, remainder_days, 0, 0, 0, 0, 0, 0),
            }
        }
        Unit::Week => {
            let days = end_days - start.epoch_days();
            Duration::new(0, 0, days / 7, days % 7, 0, 0, 0, 0, 0, 0)
        }
        _ => Duration::new(0, 0, 0, end_days - start.epoch_days(), 0, 0, 0, 0, 0, 0),
    }
}

// ---------------------------------------------------------------------------
// PlainDateTime
// ---------------------------------------------------------------------------

/// Wall-clock date-time: an ISO date plus a nanosecond-precision time.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PlainDateTime {
    pub date: PlainDate,
    pub time: PlainTime,
}

impl PlainDateTime {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        year: i32,
        month: i64,
        day: i64,
        hour: i64,
        minute: i64,
        second: i64,
        millisecond: i64,
        microsecond: i64,
        nanosecond: i64,
        overflow: Overflow,
    ) -> TemporalResult<PlainDateTime> {
        let date = PlainDate::new(year, month, day, overflow)?;
        let time = PlainTime::new(hour, minute, second, millisecond, microsecond, nanosecond, overflow)?;
        PlainDateTime::from_parts(date, time)
    }

    pub fn from_parts(date: PlainDate, time: PlainTime) -> TemporalResult<PlainDateTime> {
        let days = date.epoch_days();
        if !iso_datetime_within_limits(days, time.to_nanoseconds_of_day()) {
            return Err(TemporalError::range("date-time outside ISO representable range"));
        }
        Ok(PlainDateTime { date, time })
    }

    /// AddDuration: time part first, carry whole days into the date.
    pub fn add(&self, duration: &Duration, overflow: Overflow) -> TemporalResult<PlainDateTime> {
        let (carry, new_time) = self.time.add_signed_nanoseconds(duration.time_total_nanoseconds());
        let carry_days = i64::try_from(carry)
            .map_err(|_| TemporalError::range("date-time arithmetic overflow"))?;
        let date_shift = Duration::new(
            duration.years,
            duration.months,
            duration.weeks,
            duration
                .days
                .checked_add(carry_days)
                .ok_or_else(|| TemporalError::range("date-time arithmetic overflow"))?,
            0,
            0,
            0,
            0,
            0,
            0,
        )?;
        let new_date = self.date.add(&date_shift, overflow)?;
        PlainDateTime::from_parts(new_date, new_time)
    }

    pub fn subtract(&self, duration: &Duration, overflow: Overflow) -> TemporalResult<PlainDateTime> {
        self.add(&duration.negated(), overflow)
    }

    /// DifferenceTemporalPlainDateTime: exact integer difference balanced to
    /// `largest_unit` (date or time) and rounded to `smallest_unit`.
    pub fn until(
        &self,
        other: PlainDateTime,
        largest_unit: Unit,
        smallest_unit: Unit,
        increment: i128,
        mode: RoundingMode,
    ) -> TemporalResult<Duration> {
        if smallest_unit < largest_unit {
            return Err(TemporalError::range("smallestUnit must not be larger than largestUnit"));
        }
        if increment < 1 {
            return Err(TemporalError::range("roundingIncrement must be >= 1"));
        }
        // Total nanosecond difference (date days + time), exact in i128.
        let total_ns = self.total_ns_until(&other);
        if largest_unit.category() == super::instant_duration::UnitCategory::Date
            && largest_unit != Unit::Day
        {
            // Calendar granularity: difference dates, then fold time remainder.
            let date_diff = self.date.until(
                other.date,
                largest_unit,
                Unit::Day,
                1,
                RoundingMode::Trunc,
                Overflow::Constrain,
            )?;
            // Rebase: start + date_diff, difference that datetime against end.
            let rebased = self.add(&date_diff, Overflow::Constrain)?;
            let residual_ns = rebased.total_ns_until(&other);
            let time_part = Duration::from_time_nanoseconds(residual_ns, Unit::Hour)?;
            return Duration::new(
                date_diff.years + time_part.years,
                date_diff.months + time_part.months,
                date_diff.weeks + time_part.weeks,
                date_diff.days + time_part.days,
                time_part.hours,
                time_part.minutes,
                time_part.seconds,
                time_part.milliseconds,
                time_part.microseconds,
                time_part.nanoseconds,
            );
        }
        // Day-or-smaller granularity: pure balanced ns difference.
        let unit_ns = smallest_unit.ns_per().ok_or(TemporalErrorKindRange)?;
        validate_rounding_increment(smallest_unit, increment, false)?;
        let step = unit_ns.checked_mul(increment).ok_or(TemporalErrorKindRange)?;
        let rounded = round_to_increment(total_ns, step, mode)?;
        Duration::from_time_nanoseconds(rounded, largest_unit.max(Unit::Day))
    }

    fn total_ns_until(&self, other: &PlainDateTime) -> i128 {
        let day_delta = i128::from(other.date.epoch_days() - self.date.epoch_days());
        day_delta * NS_PER_DAY + (other.time.to_nanoseconds_of_day() - self.time.to_nanoseconds_of_day())
    }

    pub fn since(
        &self,
        other: PlainDateTime,
        largest_unit: Unit,
        smallest_unit: Unit,
        increment: i128,
        mode: RoundingMode,
    ) -> TemporalResult<Duration> {
        other.until(*self, largest_unit, smallest_unit, increment, mode)
    }

    /// RoundTimeToDays handles `day` rounding: returns next midnight carry.
    pub fn round(&self, unit: Unit, increment: i128, mode: RoundingMode) -> TemporalResult<PlainDateTime> {
        let (day_length_ns, rounded_from_epoch) = match unit {
            Unit::Day => {
                if increment != 1 {
                    return Err(TemporalError::range(
                        "roundingIncrement must be 1 when smallestUnit is day",
                    ));
                }
                (NS_PER_DAY, round_to_increment(
                    i128::from(self.date.epoch_days()) * NS_PER_DAY + self.time.to_nanoseconds_of_day(),
                    NS_PER_DAY,
                    mode,
                )?)
            }
            _ => {
                let unit_ns = unit.ns_per().ok_or(TemporalErrorKindRange)?;
                if increment < 1 {
                    return Err(TemporalError::range("roundingIncrement must be >= 1"));
                }
                let per_day = NS_PER_DAY / unit_ns;
                if increment > per_day || per_day % increment != 0 {
                    return Err(TemporalError::range(format!(
                        "roundingIncrement {increment} must evenly divide {per_day} {}s per day",
                        unit.name()
                    )));
                }
                let step = unit_ns * increment;
                let day_start_ns = i128::from(self.date.epoch_days()) * NS_PER_DAY;
                let rounded_time = round_to_increment(self.time.to_nanoseconds_of_day(), step, mode)?;
                (NS_PER_DAY, day_start_ns + rounded_time)
            }
        };
        let _ = day_length_ns;
        let days = rounded_from_epoch.div_euclid(NS_PER_DAY);
        let time_ns = rounded_from_epoch.rem_euclid(NS_PER_DAY);
        let date_days = i64::try_from(days)
            .map_err(|_| TemporalError::range("date-time round overflow"))?;
        let date = PlainDate::from_epoch_days(date_days)?;
        let time = PlainTime::from_nanoseconds_of_day(time_ns);
        PlainDateTime::from_parts(date, time)
    }

    pub fn with(
        &self,
        date_delta: impl FnOnce(&PlainDate) -> TemporalResult<PlainDate>,
        time: Option<PlainTime>,
    ) -> TemporalResult<PlainDateTime> {
        let date = date_delta(&self.date)?;
        PlainDateTime::from_parts(date, time.unwrap_or(self.time))
    }

    /// ParseTemporalDateTimeString.
    pub fn parse(text: &str) -> TemporalResult<PlainDateTime> {
        let full = parse_iso_datetime_string(text)?;
        let date = PlainDate::from_validated(full.year, full.month, full.day)?;
        let time = if full.has_time {
            PlainTime::from_nanoseconds_of_day(full.time_ns)
        } else {
            PlainTime::midnight()
        };
        let dt = PlainDateTime::from_parts(date, time)?;
        // A datetime parse is also the WithinLimits check only; the Instant
        // boundary minus one day is permitted (spec uses half-open bounds).
        Ok(dt)
    }

    /// toString: `YYYY-MM-DDTHH:MM:SS.f{auto}` (calendar omitted when iso8601).
    pub fn format(&self, precision: Precision) -> String {
        let mut out = self.date.format();
        out.push('T');
        out.push_str(&self.time.format(precision));
        out
    }

    pub fn to_plain_date(&self) -> PlainDate {
        self.date
    }

    pub fn to_plain_time(&self) -> PlainTime {
        self.time
    }

    /// Epoch-nanosecond equivalent treating this wall time as UTC — used by
    /// exact cross-checks; NOT a zoned conversion.
    pub fn to_utc_instant_unchecked(&self) -> TemporalResult<Instant> {
        let ns = i128::from(self.date.epoch_days()) * NS_PER_DAY + self.time.to_nanoseconds_of_day();
        Instant::from_epoch_nanoseconds(ns)
    }
}

impl fmt::Display for PlainDateTime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.format(Precision::Auto))
    }
}

// ---------------------------------------------------------------------------
// PlainYearMonth / PlainMonthDay
// ---------------------------------------------------------------------------

/// A year/month pair (ISO calendar), internally anchored at day 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PlainYearMonth {
    pub year: i32,
    pub month: u8,
    reference_day: u8,
}

impl PlainYearMonth {
    pub fn new(year: i32, month: i64, overflow: Overflow) -> TemporalResult<PlainYearMonth> {
        let (y, m, _) = regulate_iso_date(year, month, 1, overflow)?;
        if !iso_date_within_limits(y, m, 1) {
            return Err(TemporalError::range("year-month outside ISO representable range"));
        }
        Ok(PlainYearMonth { year: y, month: m, reference_day: 1 })
    }

    fn as_date(&self) -> TemporalResult<PlainDate> {
        PlainDate::from_validated(self.year, self.month, self.reference_day)
    }

    pub fn days_in_month(&self) -> u8 {
        days_in_month(self.year, self.month)
    }

    pub fn days_in_year(&self) -> u16 {
        if is_leap_year(self.year) { 366 } else { 365 }
    }

    pub fn in_leap_year(&self) -> bool {
        is_leap_year(self.year)
    }

    pub fn months_in_year(&self) -> u8 {
        12
    }

    pub fn add(&self, duration: &Duration, overflow: Overflow) -> TemporalResult<PlainYearMonth> {
        let date = self.as_date()?.add(duration, overflow)?;
        PlainYearMonth::new(date.year, date.month.into(), overflow)
    }

    pub fn subtract(&self, duration: &Duration, overflow: Overflow) -> TemporalResult<PlainYearMonth> {
        self.add(&duration.negated(), overflow)
    }

    /// Difference at month granularity (spec: year/month/day units only).
    pub fn until(
        &self,
        other: PlainYearMonth,
        largest_unit: Unit,
        smallest_unit: Unit,
        increment: i128,
        mode: RoundingMode,
    ) -> TemporalResult<Duration> {
        if !matches!(largest_unit, Unit::Year | Unit::Month)
            || !matches!(smallest_unit, Unit::Year | Unit::Month)
        {
            return Err(TemporalError::range(
                "PlainYearMonth difference units must be year or month",
            ));
        }
        if smallest_unit < largest_unit {
            return Err(TemporalError::range("smallestUnit must not be larger than largestUnit"));
        }
        if increment < 1 {
            return Err(TemporalError::range("roundingIncrement must be >= 1"));
        }
        let months = (i64::from(other.year) - i64::from(self.year)) * 12
            + (i64::from(other.month) - i64::from(self.month));
        match smallest_unit {
            Unit::Year => {
                let rounded = round_to_increment(i128::from(months), 12 * increment, mode)?;
                let years = i64::try_from(rounded.div_euclid(12))
                    .map_err(|_| TemporalError::range("overflow"))?;
                Duration::new(years, 0, 0, 0, 0, 0, 0, 0, 0, 0)
            }
            _ => {
                let rounded = round_to_increment(i128::from(months), increment, mode)?;
                match largest_unit {
                    Unit::Year => Duration::new(
                        i64::try_from(rounded.div_euclid(12)).map_err(|_| TemporalError::range("overflow"))?,
                        i64::try_from(rounded.rem_euclid(12)).map_err(|_| TemporalError::range("overflow"))?,
                        0, 0, 0, 0, 0, 0, 0, 0,
                    ),
                    _ => Duration::new(0, i64::try_from(rounded).map_err(|_| TemporalError::range("overflow"))?, 0, 0, 0, 0, 0, 0, 0, 0),
                }
            }
        }
    }

    pub fn since(
        &self,
        other: PlainYearMonth,
        largest_unit: Unit,
        smallest_unit: Unit,
        increment: i128,
        mode: RoundingMode,
    ) -> TemporalResult<Duration> {
        other.until(*self, largest_unit, smallest_unit, increment, mode)
    }

    /// toPlainDate({ day }) cross-type operation.
    pub fn to_plain_date(&self, day: i64, overflow: Overflow) -> TemporalResult<PlainDate> {
        PlainDate::new(self.year, self.month.into(), day, overflow)
    }

    /// ParseTemporalYearMonthString: `YYYY-MM` or full date-time (fields taken).
    pub fn parse(text: &str) -> TemporalResult<PlainYearMonth> {
        if let Ok(full) = parse_iso_datetime_string(text) {
            return PlainYearMonth::new(full.year, full.month.into(), Overflow::Reject);
        }
        // Bare year-month form (first two date components).
        let synthetic = format!("{text}-01");
        let full = parse_iso_datetime_string(&synthetic)
            .map_err(|e| TemporalError::syntax(format!("invalid year-month string: {}", e.message)))?;
        PlainYearMonth::new(full.year, full.month.into(), Overflow::Reject)
    }

    pub fn format(&self) -> String {
        format_iso_date(self.year, self.month, self.reference_day)
    }
}

impl fmt::Display for PlainYearMonth {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.format())
    }
}

/// A month/day pair (ISO calendar), internally anchored at reference year
/// 1972 (spec ISOMonthDay: a leap year so 02-29 round-trips).
pub const MONTH_DAY_REFERENCE_YEAR: i32 = 1972;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PlainMonthDay {
    year: i32,
    pub month: u8,
    pub day: u8,
}

impl PlainMonthDay {
    pub fn new(month: i64, day: i64, overflow: Overflow) -> TemporalResult<PlainMonthDay> {
        Self::with_reference_year(month, day, MONTH_DAY_REFERENCE_YEAR, overflow)
    }

    pub fn with_reference_year(
        month: i64,
        day: i64,
        reference_year: i32,
        overflow: Overflow,
    ) -> TemporalResult<PlainMonthDay> {
        let date = PlainDate::new(reference_year, month, day, overflow)?;
        Ok(PlainMonthDay { year: date.year, month: date.month, day: date.day })
    }

    /// Temporal monthCode (e.g. "M02", "M02L" for leap months in other
    /// calendars — the ISO calendar has none).
    pub fn month_code(&self) -> String {
        format!("M{:02}", self.month)
    }

    /// toPlainDate({ year }) cross-type operation; rejects nonexistent dates
    /// (e.g. 02-29 + year 2023) unless overflow constrains.
    pub fn to_plain_date(&self, year: i32, overflow: Overflow) -> TemporalResult<PlainDate> {
        PlainDate::new(year, self.month.into(), self.day.into(), overflow)
    }

    pub fn equals(&self, other: &PlainMonthDay) -> bool {
        (self.year, self.month, self.day) == (other.year, other.month, other.day)
            || (self.month, self.day) == (other.month, other.day)
    }

    /// ParseTemporalMonthDayString: `MM-DD`, `--MM-DD`, or full date-time.
    pub fn parse(text: &str) -> TemporalResult<PlainMonthDay> {
        if let Ok(full) = parse_iso_datetime_string(text) {
            return PlainMonthDay::with_reference_year(
                full.month.into(),
                full.day.into(),
                MONTH_DAY_REFERENCE_YEAR,
                Overflow::Reject,
            );
        }
        let bare = text.strip_prefix("--").unwrap_or(text);
        let synthetic = format!("{MONTH_DAY_REFERENCE_YEAR:04}-{bare}");
        match parse_iso_datetime_string(&synthetic) {
            Ok(full) => PlainMonthDay::with_reference_year(
                full.month.into(),
                full.day.into(),
                full.year,
                Overflow::Reject,
            ),
            Err(e) => Err(TemporalError::syntax(format!("invalid month-day string: {}", e.message))),
        }
    }

    pub fn format(&self) -> String {
        format!("{:02}-{:02}", self.month, self.day)
    }
}

impl fmt::Display for PlainMonthDay {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.format())
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // ---- ISO helpers ----

    #[test]
    fn day_of_week_known_dates() {
        assert_eq!(iso_day_of_week(1970, 1, 1), 4); // Thursday
        assert_eq!(iso_day_of_week(2026, 8, 25), 2); // Tuesday
        assert_eq!(iso_day_of_week(2000, 1, 1), 6); // Saturday
        assert_eq!(iso_day_of_week(1, 1, 1), 1); // Proleptic: Monday
    }

    #[test]
    fn week_of_year_iso() {
        assert_eq!(iso_week_of_year(2026, 8, 25), (2026, 35));
        assert_eq!(iso_week_of_year(2019, 12, 30), (2020, 1));
        assert_eq!(iso_week_of_year(2021, 1, 1), (2020, 53));
    }

    #[test]
    fn day_of_year_values() {
        assert_eq!(iso_day_of_year(2000, 12, 31), 366);
        assert_eq!(iso_day_of_year(1900, 12, 31), 365);
        assert_eq!(iso_day_of_year(2024, 2, 29), 60);
    }

    // ---- PlainTime ----

    #[test]
    fn time_new_overflow_policies() {
        let t = PlainTime::new(25, 61, 61, 1_500, 2_000, 3_000, Overflow::Constrain).unwrap();
        assert_eq!(
            (t.hour, t.minute, t.second, t.millisecond, t.microsecond, t.nanosecond),
            (23, 59, 59, 999, 999, 999)
        );
        for bad in [
            PlainTime::new(24, 0, 0, 0, 0, 0, Overflow::Reject),
            PlainTime::new(0, 60, 0, 0, 0, 0, Overflow::Reject),
            PlainTime::new(0, 0, 0, 1000, 0, 0, Overflow::Reject),
            PlainTime::new(-1, 0, 0, 0, 0, 0, Overflow::Reject),
        ] {
            assert!(bad.is_err());
        }
    }

    #[test]
    fn time_add_carry_across_midnight() {
        let t = PlainTime::new(23, 30, 0, 0, 0, 0, Overflow::Reject).unwrap();
        let d = Duration::from_time(1, 0, 0, 0, 0, 0).unwrap();
        let (carry, new_time) = t.add_signed_nanoseconds(d.time_total_nanoseconds());
        assert_eq!(carry, 1);
        assert_eq!((new_time.hour, new_time.minute), (0, 30));
        assert_eq!(t.add(&d).unwrap().hour, 0);
    }

    #[test]
    fn time_until_rounding() {
        let a = PlainTime::new(10, 0, 0, 0, 0, 0, Overflow::Reject).unwrap();
        let b = PlainTime::new(12, 30, 0, 0, 0, 0, Overflow::Reject).unwrap();
        let d = a.until(b, Unit::Hour, Unit::Nanosecond, 1, RoundingMode::HalfExpand).unwrap();
        assert_eq!((d.hours, d.minutes), (2, 30));
        let neg = b.until(a, Unit::Hour, Unit::Nanosecond, 1, RoundingMode::HalfExpand).unwrap();
        assert_eq!(neg.sign(), -1);
        assert_eq!((neg.hours, neg.minutes), (-2, -30));
    }

    #[test]
    fn time_round_negative_equivalents() {
        let t = PlainTime::new(0, 0, 0, 0, 0, 1, Overflow::Reject).unwrap(); // 1 ns
        let down = t.round(Unit::Second, 1, RoundingMode::Trunc).unwrap();
        assert_eq!(down, PlainTime::midnight());
        let up = t.round(Unit::Second, 1, RoundingMode::Ceil).unwrap();
        assert_eq!(up, PlainTime::new(0, 0, 1, 0, 0, 0, Overflow::Reject).unwrap());
    }

    #[test]
    fn time_parse_format_round_trip() {
        let t = PlainTime::parse("13:47:22.123456789").unwrap();
        assert_eq!(t.format(Precision::Auto), "13:47:22.123456789");
        assert_eq!(t.format(Precision::Digits(3)), "13:47:22.123");
        assert_eq!(t.format(Precision::Minute), "13:47");
        assert_eq!(PlainTime::parse("T08:30").unwrap().format(Precision::Auto), "08:30:00");
        assert!(PlainTime::parse("24:00").is_err());
        assert!(PlainTime::parse("08:30Z").is_err()); // no offset allowed
        assert!(PlainTime::parse("08:30:00.1234567890").is_err());
        // Fraction .5 == 500 ms exactly.
        let half = PlainTime::parse("12:00:00.5").unwrap();
        assert_eq!(half.millisecond, 500);
    }

    // ---- PlainDate ----

    #[test]
    fn date_new_overflow_policies() {
        let d = PlainDate::new(2001, 2, 31, Overflow::Constrain).unwrap();
        assert_eq!((d.year, d.month, d.day), (2001, 2, 28));
        assert!(PlainDate::new(2001, 2, 31, Overflow::Reject).is_err());
        assert!(PlainDate::new(2001, 13, 1, Overflow::Reject).is_err());
        let c = PlainDate::new(2001, 13, 1, Overflow::Constrain).unwrap();
        assert_eq!((c.year, c.month, c.day), (2001, 12, 1));
    }

    #[test]
    fn date_leap_day_arithmetic() {
        let leap = PlainDate::new(2000, 2, 28, Overflow::Reject).unwrap();
        let one_day = Duration::new(0, 0, 0, 1, 0, 0, 0, 0, 0, 0).unwrap();
        let next = leap.add(&one_day, Overflow::Constrain).unwrap();
        assert_eq!((next.year, next.month, next.day), (2000, 2, 29));
        let non_leap = PlainDate::new(1900, 2, 28, Overflow::Reject).unwrap()
            .add(&one_day, Overflow::Constrain).unwrap();
        assert_eq!((non_leap.year, non_leap.month, non_leap.day), (1900, 3, 1));
    }

    #[test]
    fn date_add_year_constrains_feb29() {
        let leap = PlainDate::new(2020, 2, 29, Overflow::Reject).unwrap();
        let one_year = Duration::new(1, 0, 0, 0, 0, 0, 0, 0, 0, 0).unwrap();
        let constrained = leap.add(&one_year, Overflow::Constrain).unwrap();
        assert_eq!((constrained.year, constrained.month, constrained.day), (2021, 2, 28));
        assert!(leap.add(&one_year, Overflow::Reject).is_err());
    }

    #[test]
    fn date_limits_enforced() {
        assert!(PlainDate::new(275_760, 9, 13, Overflow::Reject).is_ok());
        assert!(PlainDate::new(275_760, 9, 14, Overflow::Reject).is_err());
        assert!(PlainDate::new(-271_821, 4, 19, Overflow::Reject).is_ok());
        assert!(PlainDate::new(-271_821, 4, 18, Overflow::Reject).is_err());
    }

    #[test]
    fn date_until_year_month_day() {
        let start = PlainDate::new(2019, 2, 25, Overflow::Reject).unwrap();
        let end = PlainDate::new(2020, 3, 10, Overflow::Reject).unwrap();
        let d = start
            .until(end, Unit::Year, Unit::Day, 1, RoundingMode::Trunc, Overflow::Constrain)
            .unwrap();
        assert_eq!((d.years, d.months, d.days), (1, 0, 14));
        // Reconstruct: start + d == end.
        let back = start.add(&d, Overflow::Constrain).unwrap();
        assert_eq!(back, end);
        let md = start
            .until(end, Unit::Month, Unit::Day, 1, RoundingMode::Trunc, Overflow::Constrain)
            .unwrap();
        assert_eq!((md.months, md.days), (12, 14));
        assert_eq!(start.add(&md, Overflow::Constrain).unwrap(), end);
    }

    #[test]
    fn date_until_negative_direction() {
        let start = PlainDate::new(2019, 2, 25, Overflow::Reject).unwrap();
        let end = PlainDate::new(2020, 3, 10, Overflow::Reject).unwrap();
        let d = end
            .until(start, Unit::Year, Unit::Day, 1, RoundingMode::Trunc, Overflow::Constrain)
            .unwrap();
        assert_eq!((d.years, d.months, d.days), (-1, 0, -13));
        assert_eq!(d.sign(), -1);
    }

    #[test]
    fn date_until_weeks_and_days() {
        let a = PlainDate::new(2020, 1, 1, Overflow::Reject).unwrap();
        let b = PlainDate::new(2020, 1, 17, Overflow::Reject).unwrap();
        let w = a.until(b, Unit::Week, Unit::Day, 1, RoundingMode::Trunc, Overflow::Constrain).unwrap();
        assert_eq!((w.weeks, w.days), (2, 2));
    }

    #[test]
    fn date_rejects_time_units_in_arithmetic() {
        let d = PlainDate::new(2020, 1, 1, Overflow::Reject).unwrap();
        let t = Duration::from_time(1, 0, 0, 0, 0, 0).unwrap();
        assert!(d.add(&t, Overflow::Constrain).is_err());
    }

    #[test]
    fn date_parse_extended_years_round_trip() {
        let min = PlainDate::parse("-271821-04-19").unwrap();
        assert_eq!(min.format(), "-271821-04-19");
        let max = PlainDate::parse("+275760-09-13").unwrap();
        assert_eq!(max.format(), "+275760-09-13");
        assert!(PlainDate::parse("-000000-01-01").is_err());
        assert!(PlainDate::parse("+275760-09-14").is_err());
        assert!(PlainDate::parse("2000-02-30").is_err());
        // Annotations tolerated; critical unknown rejected.
        assert!(PlainDate::parse("2000-01-01[u-ca=iso8601]").is_ok());
        assert!(PlainDate::parse("2000-01-01[!u-ca=japanese]").is_err());
        // Full datetime string: date portion taken.
        let dt = PlainDate::parse("2000-05-15T12:30:00").unwrap();
        assert_eq!(dt.format(), "2000-05-15");
        // A UTC designator names an exact time, not a wall-clock date.
        assert!(PlainDate::parse("2000-05-15T12:30:00Z").is_err());
    }

    #[test]
    fn date_with_and_equality() {
        let d = PlainDate::new(2000, 2, 29, Overflow::Reject).unwrap();
        let next_year = d.with(Some(2001), None, None, Overflow::Constrain).unwrap();
        assert_eq!((next_year.year, next_year.month, next_year.day), (2001, 2, 28));
        assert!(d.with(Some(2001), None, None, Overflow::Reject).is_err());
        assert_ne!(d, next_year);
        assert_eq!(d.with(None, None, None, Overflow::Constrain).unwrap(), d);
    }

    // ---- PlainDateTime ----

    #[test]
    fn datetime_add_carries_across_midnight() {
        let dt = PlainDateTime::new(2020, 12, 31, 23, 30, 0, 0, 0, 0, Overflow::Reject).unwrap();
        let d = Duration::from_time(1, 0, 0, 0, 0, 0).unwrap();
        let next = dt.add(&d, Overflow::Constrain).unwrap();
        assert_eq!(next.format(Precision::Auto), "2021-01-01T00:30:00");
    }

    #[test]
    fn datetime_subtract_negative_carries() {
        let dt = PlainDateTime::new(2020, 1, 1, 0, 15, 0, 0, 0, 0, Overflow::Reject).unwrap();
        let d = Duration::from_time(1, 0, 0, 0, 0, 0).unwrap();
        let prev = dt.subtract(&d, Overflow::Constrain).unwrap();
        assert_eq!(prev.format(Precision::Auto), "2019-12-31T23:15:00");
    }

    #[test]
    fn datetime_until_time_granularity() {
        let a = PlainDateTime::new(2020, 1, 1, 0, 0, 0, 0, 0, 0, Overflow::Reject).unwrap();
        let b = PlainDateTime::new(2020, 1, 3, 6, 45, 0, 0, 0, 0, Overflow::Reject).unwrap();
        let d = a.until(b, Unit::Day, Unit::Nanosecond, 1, RoundingMode::Trunc).unwrap();
        assert_eq!((d.days, d.hours, d.minutes), (2, 6, 45));
        let hours = a.until(b, Unit::Hour, Unit::Nanosecond, 1, RoundingMode::Trunc).unwrap();
        assert_eq!(hours.hours, 54);
    }

    #[test]
    fn datetime_until_month_granularity() {
        let a = PlainDateTime::new(2020, 1, 15, 10, 0, 0, 0, 0, 0, Overflow::Reject).unwrap();
        let b = PlainDateTime::new(2020, 3, 20, 12, 30, 0, 0, 0, 0, Overflow::Reject).unwrap();
        let d = a.until(b, Unit::Month, Unit::Nanosecond, 1, RoundingMode::Trunc).unwrap();
        assert_eq!((d.months, d.days, d.hours, d.minutes), (2, 5, 2, 30));
    }

    #[test]
    fn datetime_round_to_day() {
        let dt = PlainDateTime::new(2020, 5, 10, 13, 0, 0, 0, 0, 0, Overflow::Reject).unwrap();
        let up = dt.round(Unit::Day, 1, RoundingMode::HalfExpand).unwrap();
        assert_eq!(up.format(Precision::Auto), "2020-05-11T00:00:00");
        let noon = PlainDateTime::new(2020, 5, 10, 12, 0, 0, 0, 0, 0, Overflow::Reject).unwrap();
        assert_eq!(
            noon.round(Unit::Day, 1, RoundingMode::HalfExpand).unwrap().format(Precision::Auto),
            "2020-05-11T00:00:00"
        );
        assert_eq!(
            noon.round(Unit::Day, 1, RoundingMode::HalfTrunc).unwrap().format(Precision::Auto),
            "2020-05-10T00:00:00"
        );
    }

    #[test]
    fn datetime_round_time_units() {
        let dt = PlainDateTime::parse("2020-05-10T13:47:22.123456789").unwrap();
        let r = dt.round(Unit::Minute, 15, RoundingMode::Floor).unwrap();
        assert_eq!(r.format(Precision::Auto), "2020-05-10T13:45:00");
        assert!(dt.round(Unit::Minute, 7, RoundingMode::Floor).is_err());
    }

    #[test]
    fn datetime_limits() {
        // Exact instant bound minus one day is allowed at midnight+ε of next.
        assert!(PlainDateTime::new(275_760, 9, 13, 23, 59, 59, 999, 999, 999, Overflow::Reject).is_ok());
        assert!(PlainDateTime::new(275_760, 9, 14, 0, 0, 0, 0, 0, 0, Overflow::Reject).is_err());
    }

    #[test]
    fn datetime_parse_format() {
        let dt = PlainDateTime::parse("2000-02-29T08:30:00.000000001").unwrap();
        assert_eq!(dt.format(Precision::Auto), "2000-02-29T08:30:00.000000001");
        let date_only = PlainDateTime::parse("1999-12-31").unwrap();
        assert_eq!(date_only.format(Precision::Auto), "1999-12-31T00:00:00");
        assert_eq!(date_only.to_plain_date().format(), "1999-12-31");
        // UTC offset present but ignored for wall-clock read-out.
        let with_offset = PlainDateTime::parse("2000-01-01T01:00:00+01:00").unwrap();
        assert_eq!(with_offset.format(Precision::Auto), "2000-01-01T01:00:00");
    }

    // ---- Cross-type operations ----

    #[test]
    fn cross_type_date_plus_time() {
        let date = PlainDate::new(2000, 2, 29, Overflow::Reject).unwrap();
        let time = PlainTime::new(12, 0, 0, 0, 0, 0, Overflow::Reject).unwrap();
        let dt = date.to_plain_date_time(time).unwrap();
        assert_eq!(dt.format(Precision::Auto), "2000-02-29T12:00:00");
        assert_eq!(dt.to_utc_instant_unchecked().unwrap().format(Precision::Auto), "2000-02-29T12:00:00Z");
    }

    #[test]
    fn cross_type_year_month_and_month_day() {
        let date = PlainDate::new(2024, 2, 29, Overflow::Reject).unwrap();
        let ym = date.to_plain_year_month();
        assert_eq!(ym.format(), "2024-02");
        assert_eq!(ym.days_in_month(), 29);
        assert_eq!(ym.to_plain_date(29, Overflow::Reject).unwrap(), date);
        let md = date.to_plain_month_day();
        assert_eq!(md.format(), "02-29");
        assert_eq!(md.month_code(), "M02");
        // Feb 29 + non-leap year: reject unless constrained.
        assert!(md.to_plain_date(2023, Overflow::Reject).is_err());
        assert_eq!(md.to_plain_date(2023, Overflow::Constrain).unwrap().format(), "2023-02-28");
    }

    #[test]
    fn year_month_arithmetic_and_difference() {
        let ym = PlainYearMonth::new(2020, 11, Overflow::Reject).unwrap();
        let three = Duration::new(0, 14, 0, 0, 0, 0, 0, 0, 0, 0).unwrap();
        let later = ym.add(&three, Overflow::Constrain).unwrap();
        assert_eq!(later.format(), "2022-01");
        let d = ym.until(later, Unit::Month, Unit::Month, 1, RoundingMode::Trunc).unwrap();
        assert_eq!(d.months, 14);
        let yd = ym.until(later, Unit::Year, Unit::Year, 1, RoundingMode::Trunc).unwrap();
        assert_eq!((yd.years, yd.months), (1, 0));
        assert_eq!(
            PlainYearMonth::parse("2020-11").unwrap().format(),
            "2020-11"
        );
        assert!(ym.until(later, Unit::Day, Unit::Day, 1, RoundingMode::Trunc).is_err());
    }

    #[test]
    fn month_day_parse_forms() {
        let md = PlainMonthDay::parse("02-29").unwrap();
        assert_eq!(md.format(), "02-29");
        let dashed = PlainMonthDay::parse("--12-25").unwrap();
        assert_eq!(dashed.format(), "12-25");
        assert!(PlainMonthDay::parse("02-30").is_err());
        // Equality ignores reference year.
        let other = PlainMonthDay::with_reference_year(2, 29, 1972, Overflow::Reject).unwrap();
        assert!(md.equals(&other));
    }

    #[test]
    fn month_day_default_reference_year_is_leap() {
        // 1972 is the spec reference year and must be a leap year so M02-29 works.
        assert!(is_leap_year(MONTH_DAY_REFERENCE_YEAR));
        assert_eq!(MONTH_DAY_REFERENCE_YEAR, 1972);
    }
}
