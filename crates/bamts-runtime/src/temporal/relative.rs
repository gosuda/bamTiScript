//! Calendar-relative duration arithmetic.
//!
//! A duration only has a length relative to a starting point: months differ,
//! and with a time zone so do days. This module holds the operations that need
//! such a starting point: `CalendarDateUntil`, the `Difference*` family, and
//! `RoundRelativeDuration` with its nudging machinery. Epoch arithmetic is exact
//! `i128` nanoseconds; rounding decides on exact ratios and never on floats.

use std::cmp::Ordering;

use super::instant_duration::{
    Duration, Instant, MAX_TIME_DURATION, NS_PER_DAY, NS_PER_HOUR, Overflow, RoundingMode,
    TemporalError, TemporalResult, Unit, UnitCategory, days_in_month, epoch_days_from_ymd,
    exact_ratio_to_f64, round_to_increment, rounds_past_fraction,
};
use super::now_rounding::round_nanoseconds;
use super::plain_types::{PlainDate, PlainDateTime, PlainTime};
use super::zoned_date_time::{
    CalendarId, TemporalProviders, TimeZoneId, epoch_nanoseconds_for, iso_date_time_for_instant,
    local_epoch_nanoseconds,
};

/// `Internal Duration Record`: a date duration plus a normalized time duration.
/// The two parts always agree in sign. `date` has every time field zero.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct InternalDuration {
    pub date: Duration,
    pub time: i128,
}

impl InternalDuration {
    /// CombineDateAndTimeDuration.
    pub fn new(date: Duration, time: i128) -> Self {
        Self { date, time }
    }

    /// InternalDurationSign.
    pub fn sign(&self) -> i128 {
        match self.date.sign() {
            0 => self.time.signum(),
            sign => sign,
        }
    }

    /// ToInternalDurationRecord.
    pub fn from_duration(duration: &Duration) -> Self {
        Self::new(duration.date_part(), duration.time_total_nanoseconds())
    }

    /// ToInternalDurationRecordWith24HourDays.
    pub fn from_duration_with_24_hour_days(duration: &Duration) -> Self {
        let mut date = duration.date_part();
        date.days = 0;
        Self::new(date, duration.total_nanoseconds_with_24_hour_days())
    }
}

/// How a difference is rounded; `largest_unit` also bounds its balancing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DifferenceRounding {
    pub largest_unit: Unit,
    pub smallest_unit: Unit,
    pub increment: i128,
    pub mode: RoundingMode,
}

fn limit_error() -> TemporalError {
    TemporalError::range("value outside the limits of Temporal time durations")
}

/// Rejects a time duration of 2^53 seconds or more.
fn checked_time_duration(time: i128) -> TemporalResult<i128> {
    if time.abs() >= MAX_TIME_DURATION {
        return Err(limit_error());
    }
    Ok(time)
}

/// AddTimeDuration.
pub fn add_time_duration(one: i128, two: i128) -> TemporalResult<i128> {
    checked_time_duration(one + two)
}

/// Add24HourDaysToTimeDuration.
fn add_24_hour_days(time: i128, days: i128) -> TemporalResult<i128> {
    let shift = days.checked_mul(NS_PER_DAY).ok_or_else(limit_error)?;
    checked_time_duration(time.checked_add(shift).ok_or_else(limit_error)?)
}

/// RoundTimeDuration: `unit` is a time unit or day.
pub fn round_time_duration(
    time: i128,
    increment: i128,
    unit: Unit,
    mode: RoundingMode,
) -> TemporalResult<i128> {
    checked_time_duration(round_nanoseconds(time, unit, increment, mode)?)
}

/// RoundTimeDurationToIncrement.
fn round_time_duration_to_increment(
    time: i128,
    step: i128,
    mode: RoundingMode,
) -> TemporalResult<i128> {
    checked_time_duration(round_to_increment(time, step, mode)?)
}

/// TotalTimeDuration: the exact quotient, rounded once to a Number.
pub fn total_time_duration(time: i128, unit: Unit) -> TemporalResult<f64> {
    let unit_ns = unit
        .ns_per()
        .ok_or_else(|| TemporalError::range("time total requires day or a time unit"))?;
    Ok(exact_ratio_to_f64(time, unit_ns))
}

/// ToDateDurationRecordWithoutTime: time folds into whole days, truncating.
pub fn date_duration_without_time(duration: &Duration) -> TemporalResult<Duration> {
    let internal = InternalDuration::from_duration_with_24_hour_days(duration);
    let mut date = internal.date;
    date.days = internal.time / NS_PER_DAY;
    Duration::new(date.fields())
}

/// TemporalDurationFromInternal. Time balances up to `largest_unit`, with day
/// the largest bucket it can reach.
pub fn temporal_duration_from_internal(
    internal: InternalDuration,
    largest_unit: Unit,
) -> TemporalResult<Duration> {
    let time = Duration::from_time_nanoseconds(internal.time, largest_unit.max(Unit::Day))?;
    let date = internal.date;
    Duration::new([
        date.years,
        date.months,
        date.weeks,
        date.days + time.days,
        time.hours,
        time.minutes,
        time.seconds,
        time.milliseconds,
        time.microseconds,
        time.nanoseconds,
    ])
}

/// CheckISODaysRange.
pub fn check_iso_days_range(date: PlainDate) -> TemporalResult<()> {
    if epoch_days_from_ymd(date.year, date.month, date.day).abs() > 100_000_000 {
        return Err(TemporalError::range("date is too far from the epoch"));
    }
    Ok(())
}

/// BalanceISOYearMonth on an unbounded year and a 1-based month.
fn balance_year_month(year: i64, month: i64) -> (i64, i64) {
    (
        year + (month - 1).div_euclid(12),
        (month - 1).rem_euclid(12) + 1,
    )
}

/// ISODateSurpasses: whether (year, month, day), compared field by field and
/// before any clamping, lies past `target` in the direction of `sign`.
fn iso_date_surpasses(sign: i64, year: i64, month: i64, day: i64, target: PlainDate) -> bool {
    let (target_year, target_month, target_day) = (
        i64::from(target.year),
        i64::from(target.month),
        i64::from(target.day),
    );
    let difference = if year != target_year {
        year - target_year
    } else if month != target_month {
        month - target_month
    } else {
        day - target_day
    };
    sign * difference > 0
}

/// CalendarDateUntil for the ISO calendar. The walk starts at `one` in the
/// direction of `two`, so month-length asymmetry falls on the same side for
/// both signs of the result; this is why it is not `until` with swapped ends.
pub fn iso_date_until(
    one: PlainDate,
    two: PlainDate,
    largest_unit: Unit,
) -> TemporalResult<Duration> {
    let sign: i64 = match two.cmp(&one) {
        Ordering::Equal => return Ok(Duration::default()),
        Ordering::Greater => 1,
        Ordering::Less => -1,
    };
    let (one_year, one_month, one_day) = (
        i64::from(one.year),
        i64::from(one.month),
        i64::from(one.day),
    );
    let mut years = 0_i64;
    let mut months = 0_i64;
    if matches!(largest_unit, Unit::Year | Unit::Month) {
        let mut candidate_years = i64::from(two.year) - one_year;
        if candidate_years != 0 {
            candidate_years -= sign;
        }
        while !iso_date_surpasses(sign, one_year + candidate_years, one_month, one_day, two) {
            years = candidate_years;
            candidate_years += sign;
        }
        let mut candidate_months = sign;
        loop {
            let (year, month) = balance_year_month(one_year + years, one_month + candidate_months);
            if iso_date_surpasses(sign, year, month, one_day, two) {
                break;
            }
            months = candidate_months;
            candidate_months += sign;
        }
        if largest_unit == Unit::Month {
            months += years * 12;
            years = 0;
        }
    }
    let (year, month) = balance_year_month(one_year + years, one_month + months);
    let year = i32::try_from(year).map_err(|_| limit_error())?;
    let month = u8::try_from(month).map_err(|_| limit_error())?;
    let day = one.day.min(days_in_month(year, month));
    let constrained_days = epoch_days_from_ymd(year, month, day);
    let mut days = epoch_days_from_ymd(two.year, two.month, two.day) - constrained_days;
    let mut weeks = 0;
    if largest_unit == Unit::Week {
        weeks = days / 7;
        days %= 7;
    }
    Duration::from_date(years.into(), months.into(), weeks.into(), days.into())
}

/// The fixed context of one relative operation.
#[derive(Clone, Copy)]
pub struct RelativeOrigin<'a> {
    pub providers: &'a TemporalProviders<'a>,
    pub date_time: PlainDateTime,
    pub time_zone: Option<&'a TimeZoneId>,
    pub calendar: &'a CalendarId,
}

impl RelativeOrigin<'_> {
    fn date_add(&self, duration: &Duration) -> TemporalResult<PlainDate> {
        self.providers.calendar.date_add(
            self.calendar,
            self.date_time.date,
            duration,
            Overflow::Constrain,
        )
    }

    /// The exact time of `date` at the origin's wall-clock time. Without a time
    /// zone this is plain arithmetic and may lie past the Instant range, which
    /// `CalendarDateAdd` has already bounded by date.
    fn epoch_nanoseconds_at(&self, date: PlainDate) -> TemporalResult<i128> {
        let date_time = PlainDateTime {
            date,
            time: self.date_time.time,
        };
        match self.time_zone {
            Some(time_zone) => {
                epoch_nanoseconds_for(self.providers.time_zone, time_zone, date_time)
            }
            None => Ok(local_epoch_nanoseconds(date_time)),
        }
    }
}

struct NudgeWindow {
    r1: i128,
    start_epoch_ns: i128,
    end_epoch_ns: i128,
    start_duration: Duration,
    end_duration: Duration,
}

/// ComputeNudgeWindow: the two candidate multiples of `increment` around the
/// duration, and the exact times they land on.
fn compute_nudge_window(
    sign: i128,
    duration: &InternalDuration,
    origin_epoch_ns: i128,
    origin: &RelativeOrigin<'_>,
    increment: i128,
    unit: Unit,
    additional_shift: bool,
) -> TemporalResult<NudgeWindow> {
    let date = duration.date;
    let window = |truncated: i128| {
        let r1 = if additional_shift {
            truncated + increment * sign
        } else {
            truncated
        };
        (r1, r1 + increment * sign)
    };
    let (r1, start_duration, end_duration) = match unit {
        Unit::Year => {
            let truncated = round_to_increment(date.years, increment, RoundingMode::Trunc)?;
            let (r1, r2) = window(truncated);
            (
                r1,
                Duration::from_date(r1, 0, 0, 0)?,
                Duration::from_date(r2, 0, 0, 0)?,
            )
        }
        Unit::Month => {
            let truncated = round_to_increment(date.months, increment, RoundingMode::Trunc)?;
            let (r1, r2) = window(truncated);
            (
                r1,
                Duration::from_date(date.years, r1, 0, 0)?,
                Duration::from_date(date.years, r2, 0, 0)?,
            )
        }
        Unit::Week => {
            let years_months = Duration::from_date(date.years, date.months, 0, 0)?;
            let weeks_start = origin.date_add(&years_months)?;
            let weeks_end = origin.providers.calendar.date_add(
                origin.calendar,
                weeks_start,
                &Duration::from_date(0, 0, 0, date.days)?,
                Overflow::Constrain,
            )?;
            let until = origin.providers.calendar.date_until(
                origin.calendar,
                weeks_start,
                weeks_end,
                Unit::Week,
            )?;
            let truncated =
                round_to_increment(date.weeks + until.weeks, increment, RoundingMode::Trunc)?;
            let (r1, r2) = window(truncated);
            (
                r1,
                Duration::from_date(date.years, date.months, r1, 0)?,
                Duration::from_date(date.years, date.months, r2, 0)?,
            )
        }
        _ => {
            let truncated = round_to_increment(date.days, increment, RoundingMode::Trunc)?;
            let (r1, r2) = window(truncated);
            (
                r1,
                Duration::from_date(date.years, date.months, date.weeks, r1)?,
                Duration::from_date(date.years, date.months, date.weeks, r2)?,
            )
        }
    };
    // Only an empty start duration is the origin itself; with larger units
    // present, r1 = 0 still lies after them. The origin is used as given rather
    // than recomputed because a wall-clock round trip may not reproduce it.
    let start_epoch_ns = if start_duration.is_zero() {
        origin_epoch_ns
    } else {
        origin.epoch_nanoseconds_at(origin.date_add(&start_duration)?)?
    };
    let end_epoch_ns = origin.epoch_nanoseconds_at(origin.date_add(&end_duration)?)?;
    Ok(NudgeWindow {
        r1,
        start_epoch_ns,
        end_epoch_ns,
        start_duration,
        end_duration,
    })
}

fn window_contains(sign: i128, window: &NudgeWindow, dest_epoch_ns: i128) -> bool {
    if sign > 0 {
        window.start_epoch_ns <= dest_epoch_ns && dest_epoch_ns <= window.end_epoch_ns
    } else {
        window.end_epoch_ns <= dest_epoch_ns && dest_epoch_ns <= window.start_epoch_ns
    }
}

struct NudgeResult {
    duration: InternalDuration,
    nudged_epoch_ns: i128,
    did_expand: bool,
}

struct CalendarNudge {
    result: NudgeResult,
    /// The exact unit count `numerator / denominator`, for `total()`.
    total_numerator: i128,
    total_denominator: i128,
}

/// The exact times a relative operation starts from and is rounding toward.
#[derive(Clone, Copy)]
struct Endpoints {
    origin_epoch_ns: i128,
    dest_epoch_ns: i128,
}

/// NudgeToCalendarUnit.
fn nudge_to_calendar_unit(
    sign: i128,
    duration: &InternalDuration,
    endpoints: Endpoints,
    origin: &RelativeOrigin<'_>,
    increment: i128,
    unit: Unit,
    mode: RoundingMode,
) -> TemporalResult<CalendarNudge> {
    let Endpoints {
        origin_epoch_ns,
        dest_epoch_ns,
    } = endpoints;
    let mut did_expand = false;
    let mut window = compute_nudge_window(
        sign,
        duration,
        origin_epoch_ns,
        origin,
        increment,
        unit,
        false,
    )?;
    if !window_contains(sign, &window, dest_epoch_ns) {
        window = compute_nudge_window(
            sign,
            duration,
            origin_epoch_ns,
            origin,
            increment,
            unit,
            true,
        )?;
        if !window_contains(sign, &window, dest_epoch_ns) {
            return Err(TemporalError::range(
                "calendar arithmetic could not bracket the rounding target",
            ));
        }
        did_expand = true;
    }
    let span = window.end_epoch_ns - window.start_epoch_ns;
    let progress = dest_epoch_ns - window.start_epoch_ns;
    if span == 0 {
        return Err(TemporalError::range(
            "calendar arithmetic produced an empty rounding window",
        ));
    }
    // total = r1 + (progress / span) × increment × sign, over a positive
    // denominator. `progress` and `span` share a sign, so the fraction is in
    // [0, 1] and the comparison below is on magnitudes.
    let total_denominator = span.abs();
    let total_numerator = window.r1 * total_denominator + progress.abs() * increment * sign;
    let expanded = progress.abs() == span.abs()
        || (progress != 0
            && rounds_past_fraction(
                progress.unsigned_abs(),
                span.unsigned_abs(),
                (window.r1.abs() / increment).unsigned_abs(),
                mode,
                sign < 0,
            ));
    let (nudged, nudged_epoch_ns) = if expanded {
        did_expand = true;
        (window.end_duration, window.end_epoch_ns)
    } else {
        (window.start_duration, window.start_epoch_ns)
    };
    Ok(CalendarNudge {
        result: NudgeResult {
            duration: InternalDuration::new(nudged, 0),
            nudged_epoch_ns,
            did_expand,
        },
        total_numerator,
        total_denominator,
    })
}

/// NudgeToZonedTime: rounds a time unit inside one wall-clock day of a time zone
/// and detects a result that passes the end of that day.
fn nudge_to_zoned_time(
    sign: i128,
    duration: &InternalDuration,
    origin: &RelativeOrigin<'_>,
    increment: i128,
    unit: Unit,
    mode: RoundingMode,
) -> TemporalResult<NudgeResult> {
    let start = origin.date_add(&duration.date)?;
    let end = origin.providers.calendar.date_add(
        origin.calendar,
        start,
        &Duration::from_date(0, 0, 0, sign)?,
        Overflow::Constrain,
    )?;
    let start_epoch_ns = origin.epoch_nanoseconds_at(start)?;
    let end_epoch_ns = origin.epoch_nanoseconds_at(end)?;
    let day_span = end_epoch_ns - start_epoch_ns;
    if day_span.signum() != sign {
        return Err(TemporalError::range("a wall-clock day has no length"));
    }
    let unit_ns = unit
        .ns_per()
        .ok_or_else(|| TemporalError::range("zoned rounding requires a time unit"))?;
    let step = increment * unit_ns;
    let mut rounded = round_time_duration_to_increment(duration.time, step, mode)?;
    let beyond_day = add_time_duration(rounded, -day_span)?;
    let (did_expand, day_delta, nudged_epoch_ns) = if beyond_day.signum() == -sign {
        (false, 0, start_epoch_ns + rounded)
    } else {
        rounded = round_time_duration_to_increment(beyond_day, step, mode)?;
        (true, sign, end_epoch_ns + rounded)
    };
    let mut date = duration.date;
    date.days += day_delta;
    Ok(NudgeResult {
        duration: InternalDuration::new(Duration::new(date.fields())?, rounded),
        nudged_epoch_ns,
        did_expand,
    })
}

/// NudgeToDayOrTime: days are exactly 24 hours here.
fn nudge_to_day_or_time(
    duration: &InternalDuration,
    dest_epoch_ns: i128,
    rounding: DifferenceRounding,
) -> TemporalResult<NudgeResult> {
    let time = add_24_hour_days(duration.time, duration.date.days)?;
    let unit_ns = rounding
        .smallest_unit
        .ns_per()
        .ok_or_else(|| TemporalError::range("time rounding requires day or a time unit"))?;
    let rounded =
        round_time_duration_to_increment(time, unit_ns * rounding.increment, rounding.mode)?;
    let difference = add_time_duration(rounded, -time)?;
    let whole_days = time / NS_PER_DAY;
    let rounded_whole_days = rounded / NS_PER_DAY;
    let day_delta = rounded_whole_days - whole_days;
    let did_expand = day_delta.signum() == time.signum();
    let nudged_epoch_ns = dest_epoch_ns + difference;
    let (days, remainder) = if rounding.largest_unit.category() == UnitCategory::Date {
        (
            rounded_whole_days,
            add_time_duration(rounded, -(rounded_whole_days * 24 * NS_PER_HOUR))?,
        )
    } else {
        (0, rounded)
    };
    let mut date = duration.date;
    date.days = days;
    Ok(NudgeResult {
        duration: InternalDuration::new(Duration::new(date.fields())?, remainder),
        nudged_epoch_ns,
        did_expand,
    })
}

/// BubbleRelativeDuration: after rounding carried into a larger unit, walks
/// upward and absorbs each unit the nudged time has reached.
fn bubble_relative_duration(
    sign: i128,
    mut duration: InternalDuration,
    nudged_epoch_ns: i128,
    origin: &RelativeOrigin<'_>,
    largest_unit: Unit,
    smallest_unit: Unit,
) -> TemporalResult<InternalDuration> {
    if smallest_unit == largest_unit {
        return Ok(duration);
    }
    for unit in [Unit::Week, Unit::Month, Unit::Year] {
        if unit >= smallest_unit || unit < largest_unit {
            continue;
        }
        if unit == Unit::Week && largest_unit != Unit::Week {
            continue;
        }
        let date = duration.date;
        let end_duration = match unit {
            Unit::Year => Duration::from_date(date.years + sign, 0, 0, 0)?,
            Unit::Month => Duration::from_date(date.years, date.months + sign, 0, 0)?,
            _ => Duration::from_date(date.years, date.months, date.weeks + sign, 0)?,
        };
        let end_epoch_ns = origin.epoch_nanoseconds_at(origin.date_add(&end_duration)?)?;
        if (nudged_epoch_ns - end_epoch_ns).signum() == -sign {
            break;
        }
        duration = InternalDuration::new(end_duration, 0);
    }
    Ok(duration)
}

/// RoundRelativeDuration.
fn round_relative_duration(
    duration: InternalDuration,
    endpoints: Endpoints,
    origin: &RelativeOrigin<'_>,
    rounding: DifferenceRounding,
) -> TemporalResult<InternalDuration> {
    let smallest_unit = rounding.smallest_unit;
    let irregular =
        smallest_unit < Unit::Day || (origin.time_zone.is_some() && smallest_unit == Unit::Day);
    let sign = if duration.sign() < 0 { -1 } else { 1 };
    let nudge = if irregular {
        nudge_to_calendar_unit(
            sign,
            &duration,
            endpoints,
            origin,
            rounding.increment,
            smallest_unit,
            rounding.mode,
        )?
        .result
    } else if origin.time_zone.is_some() {
        nudge_to_zoned_time(
            sign,
            &duration,
            origin,
            rounding.increment,
            smallest_unit,
            rounding.mode,
        )?
    } else {
        nudge_to_day_or_time(&duration, endpoints.dest_epoch_ns, rounding)?
    };
    if nudge.did_expand && smallest_unit != Unit::Week {
        return bubble_relative_duration(
            sign,
            nudge.duration,
            nudge.nudged_epoch_ns,
            origin,
            rounding.largest_unit,
            smallest_unit.larger(Unit::Day),
        );
    }
    Ok(nudge.duration)
}

/// TotalRelativeDuration.
fn total_relative_duration(
    duration: InternalDuration,
    endpoints: Endpoints,
    origin: &RelativeOrigin<'_>,
    unit: Unit,
) -> TemporalResult<f64> {
    if unit < Unit::Day || (origin.time_zone.is_some() && unit == Unit::Day) {
        let sign = if duration.sign() < 0 { -1 } else { 1 };
        let nudge = nudge_to_calendar_unit(
            sign,
            &duration,
            endpoints,
            origin,
            1,
            unit,
            RoundingMode::Trunc,
        )?;
        return Ok(exact_ratio_to_f64(
            nudge.total_numerator,
            nudge.total_denominator,
        ));
    }
    total_time_duration(add_24_hour_days(duration.time, duration.date.days)?, unit)
}

/// CombineISODateAndTimeRecord at midnight. A record has no limit of its own:
/// the first representable date's midnight lies just before the range.
fn midnight_record(date: PlainDate) -> PlainDateTime {
    PlainDateTime {
        date,
        time: PlainTime::midnight(),
    }
}

/// DifferenceTime.
pub fn difference_time(one: PlainTime, two: PlainTime) -> i128 {
    two.to_nanoseconds_of_day() - one.to_nanoseconds_of_day()
}

/// DifferenceISODateTime.
fn difference_iso_date_time(
    providers: &TemporalProviders<'_>,
    one: PlainDateTime,
    two: PlainDateTime,
    calendar: &CalendarId,
    largest_unit: Unit,
) -> TemporalResult<InternalDuration> {
    let mut time = difference_time(one.time, two.time);
    let time_sign = time.signum();
    // CompareISODate(one, two): equal to the time's sign exactly when the time
    // difference runs against the date difference and must borrow a day.
    let date_sign = match one.date.cmp(&two.date) {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    };
    let mut adjusted = two.date;
    if time_sign == date_sign {
        adjusted = providers.calendar.date_add(
            calendar,
            adjusted,
            &Duration::from_date(0, 0, 0, time_sign)?,
            Overflow::Constrain,
        )?;
        time = add_24_hour_days(time, -time_sign)?;
    }
    let date_largest = largest_unit.larger(Unit::Day);
    let mut date = providers
        .calendar
        .date_until(calendar, one.date, adjusted, date_largest)?;
    if largest_unit != date_largest {
        time = add_24_hour_days(time, date.days)?;
        date.days = 0;
    }
    Ok(InternalDuration::new(date, time))
}

/// DifferencePlainDateTimeWithRounding.
pub fn difference_plain_date_time_with_rounding(
    providers: &TemporalProviders<'_>,
    one: PlainDateTime,
    two: PlainDateTime,
    calendar: &CalendarId,
    rounding: DifferenceRounding,
) -> TemporalResult<InternalDuration> {
    if one == two {
        return Ok(InternalDuration::default());
    }
    PlainDateTime::from_parts(one.date, one.time)?;
    PlainDateTime::from_parts(two.date, two.time)?;
    let difference =
        difference_iso_date_time(providers, one, two, calendar, rounding.largest_unit)?;
    if rounding.smallest_unit == Unit::Nanosecond && rounding.increment == 1 {
        return Ok(difference);
    }
    let origin = RelativeOrigin {
        providers,
        date_time: one,
        time_zone: None,
        calendar,
    };
    let endpoints = Endpoints {
        origin_epoch_ns: local_epoch_nanoseconds(one),
        dest_epoch_ns: local_epoch_nanoseconds(two),
    };
    round_relative_duration(difference, endpoints, &origin, rounding)
}

/// DifferencePlainDateTimeWithTotal.
pub fn difference_plain_date_time_with_total(
    providers: &TemporalProviders<'_>,
    one: PlainDateTime,
    two: PlainDateTime,
    calendar: &CalendarId,
    unit: Unit,
) -> TemporalResult<f64> {
    if one == two {
        return Ok(0.0);
    }
    PlainDateTime::from_parts(one.date, one.time)?;
    PlainDateTime::from_parts(two.date, two.time)?;
    let difference = difference_iso_date_time(providers, one, two, calendar, unit)?;
    if unit == Unit::Nanosecond {
        return total_time_duration(difference.time, unit);
    }
    let origin = RelativeOrigin {
        providers,
        date_time: one,
        time_zone: None,
        calendar,
    };
    let endpoints = Endpoints {
        origin_epoch_ns: local_epoch_nanoseconds(one),
        dest_epoch_ns: local_epoch_nanoseconds(two),
    };
    total_relative_duration(difference, endpoints, &origin, unit)
}

/// The date-only difference behind `PlainDate.prototype.until`.
pub fn difference_plain_date(
    providers: &TemporalProviders<'_>,
    one: PlainDate,
    two: PlainDate,
    calendar: &CalendarId,
    rounding: DifferenceRounding,
) -> TemporalResult<Duration> {
    if one == two {
        return Ok(Duration::default());
    }
    let date = providers
        .calendar
        .date_until(calendar, one, two, rounding.largest_unit)?;
    let mut duration = InternalDuration::new(date, 0);
    if rounding.smallest_unit != Unit::Day || rounding.increment != 1 {
        let start = midnight_record(one);
        let end = midnight_record(two);
        let origin = RelativeOrigin {
            providers,
            date_time: start,
            time_zone: None,
            calendar,
        };
        let endpoints = Endpoints {
            origin_epoch_ns: local_epoch_nanoseconds(start),
            dest_epoch_ns: local_epoch_nanoseconds(end),
        };
        duration = round_relative_duration(duration, endpoints, &origin, rounding)?;
    }
    temporal_duration_from_internal(duration, Unit::Day)
}

/// The year-month difference behind `PlainYearMonth.prototype.until`: both ends
/// are read at the first of their month, and only years and months survive.
pub fn difference_plain_year_month(
    providers: &TemporalProviders<'_>,
    one: PlainDate,
    two: PlainDate,
    calendar: &CalendarId,
    rounding: DifferenceRounding,
) -> TemporalResult<Duration> {
    let until = providers
        .calendar
        .date_until(calendar, one, two, rounding.largest_unit)?;
    let years_months = Duration::from_date(until.years, until.months, 0, 0)?;
    let mut duration = InternalDuration::new(years_months, 0);
    if rounding.smallest_unit != Unit::Month || rounding.increment != 1 {
        let start = midnight_record(one);
        let end = midnight_record(two);
        let origin = RelativeOrigin {
            providers,
            date_time: start,
            time_zone: None,
            calendar,
        };
        let endpoints = Endpoints {
            origin_epoch_ns: local_epoch_nanoseconds(start),
            dest_epoch_ns: local_epoch_nanoseconds(end),
        };
        duration = round_relative_duration(duration, endpoints, &origin, rounding)?;
    }
    temporal_duration_from_internal(duration, Unit::Day)
}

/// DifferenceInstant.
pub fn difference_instant(
    one: i128,
    two: i128,
    increment: i128,
    unit: Unit,
    mode: RoundingMode,
) -> TemporalResult<InternalDuration> {
    let time = round_time_duration(two - one, increment, unit, mode)?;
    Ok(InternalDuration::new(Duration::default(), time))
}

/// DifferenceZonedDateTime.
fn difference_zoned_date_time(
    providers: &TemporalProviders<'_>,
    start_ns: i128,
    end_ns: i128,
    time_zone: &TimeZoneId,
    calendar: &CalendarId,
    largest_unit: Unit,
) -> TemporalResult<InternalDuration> {
    if start_ns == end_ns {
        return Ok(InternalDuration::default());
    }
    let start = iso_date_time_for_instant(providers.time_zone, time_zone, start_ns)?;
    let end = iso_date_time_for_instant(providers.time_zone, time_zone, end_ns)?;
    if start.date == end.date {
        return Ok(InternalDuration::new(
            Duration::default(),
            end_ns - start_ns,
        ));
    }
    let sign = (end_ns - start_ns).signum();
    let max_day_correction = if sign == 1 { 2 } else { 1 };
    let mut day_correction = 0;
    if difference_time(start.time, end.time).signum() == -sign {
        day_correction += 1;
    }
    while day_correction <= max_day_correction {
        let intermediate_date = providers.calendar.date_add(
            calendar,
            end.date,
            &Duration::from_date(0, 0, 0, day_correction * -sign)?,
            Overflow::Constrain,
        )?;
        let intermediate = PlainDateTime::from_parts(intermediate_date, start.time)?;
        let intermediate_ns = epoch_nanoseconds_for(providers.time_zone, time_zone, intermediate)?;
        let time = end_ns - intermediate_ns;
        if sign != -time.signum() {
            let date = providers.calendar.date_until(
                calendar,
                start.date,
                intermediate_date,
                largest_unit.larger(Unit::Day),
            )?;
            return Ok(InternalDuration::new(date, time));
        }
        day_correction += 1;
    }
    Err(TemporalError::range(
        "time zone data prevented a zoned difference from converging",
    ))
}

/// DifferenceZonedDateTimeWithRounding.
pub fn difference_zoned_date_time_with_rounding(
    providers: &TemporalProviders<'_>,
    start_ns: i128,
    end_ns: i128,
    time_zone: &TimeZoneId,
    calendar: &CalendarId,
    rounding: DifferenceRounding,
) -> TemporalResult<InternalDuration> {
    if rounding.largest_unit.category() == UnitCategory::Time {
        return difference_instant(
            start_ns,
            end_ns,
            rounding.increment,
            rounding.smallest_unit,
            rounding.mode,
        );
    }
    let difference = difference_zoned_date_time(
        providers,
        start_ns,
        end_ns,
        time_zone,
        calendar,
        rounding.largest_unit,
    )?;
    if rounding.smallest_unit == Unit::Nanosecond && rounding.increment == 1 {
        return Ok(difference);
    }
    let origin = RelativeOrigin {
        providers,
        date_time: iso_date_time_for_instant(providers.time_zone, time_zone, start_ns)?,
        time_zone: Some(time_zone),
        calendar,
    };
    let endpoints = Endpoints {
        origin_epoch_ns: start_ns,
        dest_epoch_ns: end_ns,
    };
    round_relative_duration(difference, endpoints, &origin, rounding)
}

/// DifferenceZonedDateTimeWithTotal.
pub fn difference_zoned_date_time_with_total(
    providers: &TemporalProviders<'_>,
    start_ns: i128,
    end_ns: i128,
    time_zone: &TimeZoneId,
    calendar: &CalendarId,
    unit: Unit,
) -> TemporalResult<f64> {
    if unit.category() == UnitCategory::Time {
        return total_time_duration(end_ns - start_ns, unit);
    }
    let difference =
        difference_zoned_date_time(providers, start_ns, end_ns, time_zone, calendar, unit)?;
    let origin = RelativeOrigin {
        providers,
        date_time: iso_date_time_for_instant(providers.time_zone, time_zone, start_ns)?,
        time_zone: Some(time_zone),
        calendar,
    };
    let endpoints = Endpoints {
        origin_epoch_ns: start_ns,
        dest_epoch_ns: end_ns,
    };
    total_relative_duration(difference, endpoints, &origin, unit)
}

/// The two ends of a duration laid against a plain `relativeTo`: midnight of
/// that date, and the wall-clock time the whole duration reaches.
pub fn plain_relative_endpoints(
    providers: &TemporalProviders<'_>,
    date: PlainDate,
    calendar: &CalendarId,
    duration: &Duration,
) -> TemporalResult<(PlainDateTime, PlainDateTime)> {
    let internal = InternalDuration::from_duration_with_24_hour_days(duration);
    let (carry, time) = PlainTime::midnight().add_signed_nanoseconds(internal.time);
    let mut date_duration = internal.date;
    date_duration.days = carry;
    let date_duration = Duration::new(date_duration.fields())?;
    let target =
        providers
            .calendar
            .date_add(calendar, date, &date_duration, Overflow::Constrain)?;
    Ok((midnight_record(date), PlainDateTime { date: target, time }))
}

/// DateDurationDays: a date duration's whole length in days from `date`.
pub fn date_duration_days(
    providers: &TemporalProviders<'_>,
    duration: &Duration,
    date: PlainDate,
    calendar: &CalendarId,
) -> TemporalResult<i128> {
    let without_days = Duration::from_date(duration.years, duration.months, duration.weeks, 0)?;
    if without_days.sign() == 0 {
        return Ok(duration.days);
    }
    let later = providers
        .calendar
        .date_add(calendar, date, &without_days, Overflow::Constrain)?;
    Ok(duration.days + i128::from(later.epoch_days() - date.epoch_days()))
}

/// CompareTimeDuration after folding `days` into each side as 24-hour days.
pub fn compare_with_days(
    one: &InternalDuration,
    days_one: i128,
    two: &InternalDuration,
    days_two: i128,
) -> TemporalResult<Ordering> {
    Ok(add_24_hour_days(one.time, days_one)?.cmp(&add_24_hour_days(two.time, days_two)?))
}

/// AddInstant.
pub fn add_instant(epoch_ns: i128, time: i128) -> TemporalResult<Instant> {
    Instant::from_epoch_nanoseconds(epoch_ns + time)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::temporal::zoned_date_time::IsoCalendarProvider;

    fn date(year: i32, month: i64, day: i64) -> PlainDate {
        PlainDate::new(year, month, day, Overflow::Reject).unwrap()
    }

    #[test]
    fn date_until_walks_from_the_receiver_in_both_directions() {
        let start = date(2019, 2, 25);
        let end = date(2020, 3, 10);
        let forward = iso_date_until(start, end, Unit::Year).unwrap();
        assert_eq!((forward.years, forward.months, forward.days), (1, 0, 14));
        let backward = iso_date_until(end, start, Unit::Year).unwrap();
        assert_eq!(
            (backward.years, backward.months, backward.days),
            (-1, 0, -13)
        );
    }

    #[test]
    fn date_until_compares_the_unclamped_day_of_month() {
        // January 31 plus one month is not yet past February 28: the unclamped
        // day 31 is, so the month does not count.
        let until = iso_date_until(date(2021, 1, 31), date(2021, 2, 28), Unit::Month).unwrap();
        assert_eq!((until.months, until.days), (0, 28));
    }

    #[test]
    fn date_until_reports_weeks_only_when_asked() {
        let until = iso_date_until(date(2020, 1, 1), date(2020, 1, 17), Unit::Week).unwrap();
        assert_eq!((until.weeks, until.days), (2, 2));
        let days = iso_date_until(date(2020, 1, 1), date(2020, 1, 17), Unit::Day).unwrap();
        assert_eq!((days.weeks, days.days), (0, 16));
    }

    #[test]
    fn time_duration_sum_rejects_exactly_two_to_the_53_seconds() {
        assert!(add_time_duration(MAX_TIME_DURATION - 1, 0).is_ok());
        assert!(add_time_duration(MAX_TIME_DURATION - 1, 1).is_err());
        assert!(add_time_duration(-MAX_TIME_DURATION, 0).is_err());
    }

    #[test]
    fn date_duration_without_time_truncates_toward_zero() {
        let negative = Duration::new([0, 0, 0, -1, -25, 0, 0, 0, 0, 0]).unwrap();
        assert_eq!(date_duration_without_time(&negative).unwrap().days, -2);
    }

    #[test]
    fn calendar_rounding_rounds_on_the_exact_position_in_the_window() {
        let provider = IsoCalendarProvider;
        let zones = crate::temporal::zoned_date_time::FixedOffsetTimeZones;
        let providers = TemporalProviders::new(&zones, &provider);
        let calendar = CalendarId::iso8601();
        let rounding = DifferenceRounding {
            largest_unit: Unit::Year,
            smallest_unit: Unit::Month,
            increment: 1,
            mode: RoundingMode::HalfExpand,
        };
        // 15 days into a 31-day January rounds down, 16 rounds up.
        let down = difference_plain_date(
            &providers,
            date(2021, 1, 1),
            date(2021, 1, 16),
            &calendar,
            rounding,
        )
        .unwrap();
        assert_eq!((down.months, down.days), (0, 0));
        let up = difference_plain_date(
            &providers,
            date(2021, 1, 1),
            date(2021, 1, 17),
            &calendar,
            rounding,
        )
        .unwrap();
        assert_eq!((up.months, up.days), (1, 0));
    }
}
