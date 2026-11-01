//! Temporal core: typed errors, units, rounding, `Instant`, and `Duration`.
//!
//! Grounded in ECMA-262 + the Temporal proposal (tc39/proposal-temporal, ECMA-402
//! aligned option semantics). All arithmetic is exact checked `i128`; no floats
//! participate in any date/time computation. No ambient host access (no clock,
//! no environment, no time zone database) — zoned/tzdb work is the jiff-backed
//! C11.3 boundary and is intentionally absent here.

use std::fmt;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// ECMAScript error class a Temporal abstract operation would throw.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TemporalErrorKind {
    /// `RangeError`: value outside representable/allowed range.
    Range,
    /// `TypeError`: wrong kind of argument (e.g. missing required property).
    Type,
    /// `RangeError` raised specifically by ISO 8601 string grammar violations.
    /// Kept distinct so callers can map syntax failures precisely; it still
    /// surfaces as a `RangeError` at the JS boundary.
    Syntax,
}

/// Typed Temporal error carrying the throwing operation's message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TemporalError {
    pub kind: TemporalErrorKind,
    pub message: String,
}

impl TemporalError {
    pub fn range(message: impl Into<String>) -> Self {
        Self { kind: TemporalErrorKind::Range, message: message.into() }
    }
    pub fn type_error(message: impl Into<String>) -> Self {
        Self { kind: TemporalErrorKind::Type, message: message.into() }
    }
    pub fn syntax(message: impl Into<String>) -> Self {
        Self { kind: TemporalErrorKind::Syntax, message: message.into() }
    }
}

impl fmt::Display for TemporalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let class = match self.kind {
            TemporalErrorKind::Range => "RangeError",
            TemporalErrorKind::Type => "TypeError",
            TemporalErrorKind::Syntax => "RangeError(syntax)",
        };
        write!(f, "{class}: {}", self.message)
    }
}

pub type TemporalResult<T> = Result<T, TemporalError>;

fn overflow_err(op: &str) -> TemporalError {
    TemporalError::range(format!("{op}: arithmetic overflow outside Temporal limits"))
}

// ---------------------------------------------------------------------------
// Units
// ---------------------------------------------------------------------------

pub const NS_PER_MICROSECOND: i128 = 1_000;
pub const NS_PER_MILLISECOND: i128 = 1_000_000;
pub const NS_PER_SECOND: i128 = 1_000_000_000;
pub const NS_PER_MINUTE: i128 = 60 * NS_PER_SECOND;
pub const NS_PER_HOUR: i128 = 60 * NS_PER_MINUTE;
pub const NS_PER_DAY: i128 = 24 * NS_PER_HOUR;

/// Temporal unit, largest to smallest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Unit {
    Year,
    Month,
    Week,
    Day,
    Hour,
    Minute,
    Second,
    Millisecond,
    Microsecond,
    Nanosecond,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnitCategory {
    Date,
    Time,
}

impl Unit {
    pub const ALL: [Unit; 10] = [
        Unit::Year,
        Unit::Month,
        Unit::Week,
        Unit::Day,
        Unit::Hour,
        Unit::Minute,
        Unit::Second,
        Unit::Millisecond,
        Unit::Microsecond,
        Unit::Nanosecond,
    ];

    pub fn category(self) -> UnitCategory {
        if self <= Unit::Day { UnitCategory::Date } else { UnitCategory::Time }
    }

    /// Nanoseconds per unit for time units (and Day, defined as exactly 24h in
    /// contexts with no time zone). Calendar units have no fixed length.
    pub fn ns_per(self) -> Option<i128> {
        match self {
            Unit::Day => Some(NS_PER_DAY),
            Unit::Hour => Some(NS_PER_HOUR),
            Unit::Minute => Some(NS_PER_MINUTE),
            Unit::Second => Some(NS_PER_SECOND),
            Unit::Millisecond => Some(NS_PER_MILLISECOND),
            Unit::Microsecond => Some(NS_PER_MICROSECOND),
            Unit::Nanosecond => Some(1),
            _ => None,
        }
    }

    /// LargerOfTwoTemporalUnits.
    pub fn larger(self, other: Unit) -> Unit {
        if self <= other { self } else { other }
    }

    /// GetTemporalUnitValuedOption name table: singular and plural accepted.
    pub fn from_name(name: &str) -> Option<Unit> {
        Some(match name {
            "year" | "years" => Unit::Year,
            "month" | "months" => Unit::Month,
            "week" | "weeks" => Unit::Week,
            "day" | "days" => Unit::Day,
            "hour" | "hours" => Unit::Hour,
            "minute" | "minutes" => Unit::Minute,
            "second" | "seconds" => Unit::Second,
            "millisecond" | "milliseconds" => Unit::Millisecond,
            "microsecond" | "microseconds" => Unit::Microsecond,
            "nanosecond" | "nanoseconds" => Unit::Nanosecond,
            _ => return None,
        })
    }

    pub fn name(self) -> &'static str {
        match self {
            Unit::Year => "year",
            Unit::Month => "month",
            Unit::Week => "week",
            Unit::Day => "day",
            Unit::Hour => "hour",
            Unit::Minute => "minute",
            Unit::Second => "second",
            Unit::Millisecond => "millisecond",
            Unit::Microsecond => "microsecond",
            Unit::Nanosecond => "nanosecond",
        }
    }

    /// MaximumTemporalDurationRoundingIncrement: `None` means unbounded
    /// (calendar units and day).
    pub fn max_rounding_increment(self) -> Option<i128> {
        match self {
            Unit::Hour => Some(24),
            Unit::Minute | Unit::Second => Some(60),
            Unit::Millisecond | Unit::Microsecond | Unit::Nanosecond => Some(1000),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Options
// ---------------------------------------------------------------------------

/// Temporal rounding mode (GetRoundingModeOption).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum RoundingMode {
    Ceil,
    Floor,
    Expand,
    Trunc,
    HalfCeil,
    HalfFloor,
    HalfExpand,
    #[default]
    HalfTrunc,
    HalfEven,
}

impl RoundingMode {
    pub fn from_name(name: &str) -> Option<RoundingMode> {
        Some(match name {
            "ceil" => RoundingMode::Ceil,
            "floor" => RoundingMode::Floor,
            "expand" => RoundingMode::Expand,
            "trunc" => RoundingMode::Trunc,
            "halfCeil" => RoundingMode::HalfCeil,
            "halfFloor" => RoundingMode::HalfFloor,
            "halfExpand" => RoundingMode::HalfExpand,
            "halfTrunc" => RoundingMode::HalfTrunc,
            "halfEven" => RoundingMode::HalfEven,
            _ => return None,
        })
    }

    /// NegateRoundingMode: mode applied to `-x` so that rounding `x` with the
    /// original mode equals negating the result.
    pub fn negated(self) -> RoundingMode {
        match self {
            RoundingMode::Ceil => RoundingMode::Floor,
            RoundingMode::Floor => RoundingMode::Ceil,
            RoundingMode::HalfCeil => RoundingMode::HalfFloor,
            RoundingMode::HalfFloor => RoundingMode::HalfCeil,
            other => other,
        }
    }
}

/// GetTemporalOverflowOption.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Overflow {
    #[default]
    Constrain,
    Reject,
}

impl Overflow {
    pub fn from_name(name: &str) -> Option<Overflow> {
        match name {
            "constrain" => Some(Overflow::Constrain),
            "reject" => Some(Overflow::Reject),
            _ => None,
        }
    }
}

/// Fractional second digit precision (GetTemporalFractionalSecondDigitsOption
/// combined with smallestUnit precision resolution).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Precision {
    /// Emit exactly the digits needed (trailing zeros trimmed in groups of 3).
    #[default]
    Auto,
    /// Truncate the seconds part entirely (smallestUnit: "minute").
    Minute,
    /// Fixed digit count 0..=9.
    Digits(u8),
}

impl Precision {
    pub fn digits(count: u8) -> TemporalResult<Precision> {
        if count > 9 {
            return Err(TemporalError::range(format!(
                "fractionalSecondDigits must be 0..=9, got {count}"
            )));
        }
        Ok(Precision::Digits(count))
    }
}

// ---------------------------------------------------------------------------
// Rounding core
// ---------------------------------------------------------------------------

/// RoundNumberToIncrement on exact integers: rounds `x` to a multiple of
/// `increment` (> 0) under `mode`. Errors only on i128 overflow at the extreme
/// edge of the domain.
pub fn round_to_increment(x: i128, increment: i128, mode: RoundingMode) -> TemporalResult<i128> {
    debug_assert!(increment > 0);
    let quotient = x.div_euclid(increment);
    let remainder = x.rem_euclid(increment); // 0 <= remainder < increment
    if remainder == 0 {
        return Ok(x);
    }
    // `floor` result is quotient; `ceil` result is quotient + 1.
    let is_negative = x < 0;
    let double_rem = remainder.checked_mul(2).ok_or_else(|| overflow_err("round"))?;
    let round_up = match mode {
        RoundingMode::Ceil => true,
        RoundingMode::Floor => false,
        RoundingMode::Expand => !is_negative,
        RoundingMode::Trunc => is_negative,
        RoundingMode::HalfCeil => double_rem >= increment,
        RoundingMode::HalfFloor => double_rem > increment,
        RoundingMode::HalfExpand => {
            if is_negative { double_rem <= increment } else { double_rem >= increment }
        }
        RoundingMode::HalfTrunc => {
            if is_negative { double_rem >= increment } else { double_rem > increment }
        }
        RoundingMode::HalfEven => {
            if double_rem > increment {
                true
            } else if double_rem < increment {
                false
            } else {
                quotient.rem_euclid(2) == 1
            }
        }
    };
    let q = if round_up {
        quotient.checked_add(1).ok_or_else(|| overflow_err("round"))?
    } else {
        quotient
    };
    q.checked_mul(increment).ok_or_else(|| overflow_err("round"))
}

/// ValidateTemporalRoundingIncrement: `increment` must be >= 1, and when the
/// unit is bounded, `increment` must be < max and divide max evenly.
pub fn validate_rounding_increment(unit: Unit, increment: i128, inclusive: bool) -> TemporalResult<()> {
    if increment < 1 {
        return Err(TemporalError::range(format!("roundingIncrement must be >= 1, got {increment}")));
    }
    if let Some(max) = unit.max_rounding_increment() {
        let bound = if inclusive { max } else { max - 1 };
        if increment > bound {
            return Err(TemporalError::range(format!(
                "roundingIncrement {increment} too large for unit {}",
                unit.name()
            )));
        }
        if max % increment != 0 {
            return Err(TemporalError::range(format!(
                "roundingIncrement {increment} does not divide {} evenly for unit {}",
                max,
                unit.name()
            )));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Instant
// ---------------------------------------------------------------------------

/// Nanoseconds in ±10^8 days: the Temporal.Instant representable range.
pub const INSTANT_NS_MAX: i128 = 8_640_000_000_000_000_000_000;
pub const INSTANT_NS_MIN: i128 = -INSTANT_NS_MAX;

/// Exact point on the UTC timeline, nanosecond precision.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Instant {
    epoch_ns: i128,
}

impl Instant {
    /// CreateTemporalInstant with IsValidEpochNanoseconds check.
    pub fn from_epoch_nanoseconds(epoch_ns: i128) -> TemporalResult<Instant> {
        if !(INSTANT_NS_MIN..=INSTANT_NS_MAX).contains(&epoch_ns) {
            return Err(TemporalError::range(format!(
                "epoch nanoseconds {epoch_ns} outside ±8.64e21"
            )));
        }
        Ok(Instant { epoch_ns })
    }

    pub fn from_epoch_milliseconds(epoch_ms: i64) -> TemporalResult<Instant> {
        Instant::from_epoch_nanoseconds((epoch_ms as i128) * NS_PER_MILLISECOND)
    }

    pub fn epoch_nanoseconds(self) -> i128 {
        self.epoch_ns
    }

    /// Floor-division epoch milliseconds (matches spec's ℝ(ns) / 10^6 floor).
    pub fn epoch_milliseconds(self) -> i64 {
        self.epoch_ns.div_euclid(NS_PER_MILLISECOND) as i64
    }

    pub fn epoch_seconds(self) -> i64 {
        self.epoch_ns.div_euclid(NS_PER_SECOND) as i64
    }

    /// AddDurationToInstant (sign = +1). Date units are rejected: an instant
    /// has no calendar.
    pub fn add(self, duration: &Duration) -> TemporalResult<Instant> {
        self.add_signed(duration, 1)
    }

    pub fn subtract(self, duration: &Duration) -> TemporalResult<Instant> {
        self.add_signed(duration, -1)
    }

    fn add_signed(self, duration: &Duration, sign: i128) -> TemporalResult<Instant> {
        if duration.years != 0 || duration.months != 0 || duration.weeks != 0 || duration.days != 0 {
            return Err(TemporalError::range(
                "Instant arithmetic does not accept date units (years/months/weeks/days)",
            ));
        }
        let delta = duration.time_total_nanoseconds();
        let shifted = self
            .epoch_ns
            .checked_add(sign.checked_mul(delta).ok_or_else(|| overflow_err("Instant.add"))?)
            .ok_or_else(|| overflow_err("Instant.add"))?;
        Instant::from_epoch_nanoseconds(shifted)
    }

    /// DifferenceTemporalInstant → time-only Duration balanced to
    /// `largest_unit`, rounded to `smallest_unit`/`increment`/`mode`.
    pub fn until(
        self,
        other: Instant,
        largest_unit: Unit,
        smallest_unit: Unit,
        increment: i128,
        mode: RoundingMode,
    ) -> TemporalResult<Duration> {
        if largest_unit.category() == UnitCategory::Date || smallest_unit.category() == UnitCategory::Date {
            return Err(TemporalError::range(
                "Instant difference supports time units only (hour..nanosecond)",
            ));
        }
        if smallest_unit < largest_unit {
            return Err(TemporalError::range(
                "smallestUnit must not be larger than largestUnit",
            ));
        }
        validate_rounding_increment(smallest_unit, increment, false)?;
        let diff = other.epoch_ns - self.epoch_ns; // both within ±8.64e21: no overflow
        let unit_ns = smallest_unit.ns_per().ok_or_else(|| overflow_err("until"))?;
        let step = unit_ns.checked_mul(increment).ok_or_else(|| overflow_err("until"))?;
        let rounded = round_to_increment(diff, step, mode)?;
        Duration::from_time_nanoseconds(rounded, largest_unit)
    }

    pub fn since(
        self,
        other: Instant,
        largest_unit: Unit,
        smallest_unit: Unit,
        increment: i128,
        mode: RoundingMode,
    ) -> TemporalResult<Duration> {
        other.until(self, largest_unit, smallest_unit, increment, mode)
    }

    /// Temporal.Instant.prototype.round. `unit` must be a time unit; the
    /// increment must divide one day's worth of that unit evenly.
    pub fn round(self, unit: Unit, increment: i128, mode: RoundingMode) -> TemporalResult<Instant> {
        let unit_ns = unit.ns_per().filter(|_| unit != Unit::Day).ok_or_else(|| {
            TemporalError::range("Instant.round requires a time unit (hour..nanosecond)")
        })?;
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
        let step = unit_ns * increment; // <= NS_PER_DAY: no overflow
        let rounded = round_to_increment(self.epoch_ns, step, mode)?;
        Instant::from_epoch_nanoseconds(rounded)
    }

    /// ParseTemporalInstantString: full date-time with a required UTC offset
    /// (`Z`, `z`, or numeric ±hh[:mm[:ss[.f{1,9}]]]), optional annotations.
    pub fn parse(text: &str) -> TemporalResult<Instant> {
        let parsed = parse_iso_datetime_string(text)?;
        let offset_ns = match parsed.offset {
            Some(UtcOffsetRecord::Zulu) => 0,
            Some(UtcOffsetRecord::Numeric(ns)) => ns,
            None => {
                return Err(TemporalError::syntax(
                    "Instant string requires a UTC offset (Z or ±hh:mm)",
                ))
            }
        };
        if !parsed.has_time {
            return Err(TemporalError::syntax("Instant string requires a time component"));
        }
        let days = epoch_days_checked(parsed.year, parsed.month, parsed.day)?;
        let ns = (days as i128)
            .checked_mul(NS_PER_DAY)
            .and_then(|d| d.checked_add(parsed.time_ns))
            .and_then(|d| d.checked_sub(offset_ns))
            .ok_or_else(|| overflow_err("Instant.parse"))?;
        Instant::from_epoch_nanoseconds(ns)
    }

    /// TemporalInstantToString with UTC ("Z") output.
    pub fn format(self, precision: Precision) -> String {
        let days = self.epoch_ns.div_euclid(NS_PER_DAY);
        let time_ns = self.epoch_ns.rem_euclid(NS_PER_DAY);
        let (year, month, day) = ymd_from_epoch_days(days as i64);
        let mut out = format_iso_date(year, month, day);
        out.push('T');
        out.push_str(&format_time_ns(time_ns, precision));
        out.push('Z');
        out
    }
}

impl fmt::Display for Instant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.format(Precision::Auto))
    }
}

// ---------------------------------------------------------------------------
// Duration
// ---------------------------------------------------------------------------

/// |years|, |months|, |weeks| must each be < 2^32 (IsValidDuration).
const CALENDAR_FIELD_LIMIT: i64 = 1 << 32;
/// Normalized time duration bound: |days·86400 + h·3600 + … + s| ≤ 2^53 − 1
/// seconds with the sub-second remainder attached (IsValidDuration step 6).
const MAX_TIME_DURATION_SECONDS: i128 = (1_i128 << 53) - 1;

/// Ten-field Temporal.Duration. All fields are exact integers; a duration is
/// valid only when every field shares one sign (or is zero) and magnitudes are
/// within the spec bounds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Duration {
    pub years: i64,
    pub months: i64,
    pub weeks: i64,
    pub days: i64,
    pub hours: i64,
    pub minutes: i64,
    pub seconds: i64,
    pub milliseconds: i64,
    pub microseconds: i64,
    pub nanoseconds: i64,
}

impl Duration {
    #[allow(clippy::too_many_arguments)] // mirrors the ten-argument spec constructor
    pub fn new(
        years: i64,
        months: i64,
        weeks: i64,
        days: i64,
        hours: i64,
        minutes: i64,
        seconds: i64,
        milliseconds: i64,
        microseconds: i64,
        nanoseconds: i64,
    ) -> TemporalResult<Duration> {
        let d = Duration {
            years,
            months,
            weeks,
            days,
            hours,
            minutes,
            seconds,
            milliseconds,
            microseconds,
            nanoseconds,
        };
        d.validate()?;
        Ok(d)
    }

    pub fn from_time(
        hours: i64,
        minutes: i64,
        seconds: i64,
        milliseconds: i64,
        microseconds: i64,
        nanoseconds: i64,
    ) -> TemporalResult<Duration> {
        Duration::new(0, 0, 0, 0, hours, minutes, seconds, milliseconds, microseconds, nanoseconds)
    }

    fn fields(&self) -> [i64; 10] {
        [
            self.years,
            self.months,
            self.weeks,
            self.days,
            self.hours,
            self.minutes,
            self.seconds,
            self.milliseconds,
            self.microseconds,
            self.nanoseconds,
        ]
    }

    /// IsValidDuration.
    fn validate(&self) -> TemporalResult<()> {
        let mut sign = 0_i64;
        for v in self.fields() {
            let s = v.signum();
            if s != 0 {
                if sign != 0 && s != sign {
                    return Err(TemporalError::range(
                        "mixed-sign Duration fields are not allowed",
                    ));
                }
                sign = s;
            }
        }
        for name_value in [
            ("years", self.years),
            ("months", self.months),
            ("weeks", self.weeks),
        ] {
            if name_value.1.abs() >= CALENDAR_FIELD_LIMIT {
                return Err(TemporalError::range(format!(
                    "|{}| must be < 2^32, got {}",
                    name_value.0, name_value.1
                )));
            }
        }
        // Normalized seconds bound, computed exactly in i128.
        let total_ns = self.time_total_nanoseconds_with_days()?;
        let bound = MAX_TIME_DURATION_SECONDS
            .checked_mul(NS_PER_SECOND)
            .and_then(|v| v.checked_add(NS_PER_SECOND - 1))
            .ok_or_else(|| overflow_err("Duration"))?;
        if total_ns.abs() > bound {
            return Err(TemporalError::range(
                "Duration time total exceeds 2^53 seconds",
            ));
        }
        Ok(())
    }

    /// DurationSign.
    pub fn sign(&self) -> i64 {
        for v in self.fields() {
            if v != 0 {
                return v.signum();
            }
        }
        0
    }

    pub fn is_zero(&self) -> bool {
        self.sign() == 0
    }

    pub fn negated(&self) -> Duration {
        Duration {
            years: -self.years,
            months: -self.months,
            weeks: -self.weeks,
            days: -self.days,
            hours: -self.hours,
            minutes: -self.minutes,
            seconds: -self.seconds,
            milliseconds: -self.milliseconds,
            microseconds: -self.microseconds,
            nanoseconds: -self.nanoseconds,
        }
    }

    pub fn abs(&self) -> Duration {
        if self.sign() < 0 { self.negated() } else { *self }
    }

    /// Total nanoseconds of the time portion (hours and smaller). Exact:
    /// worst case magnitudes fit i128 with vast headroom.
    pub fn time_total_nanoseconds(&self) -> i128 {
        (self.hours as i128) * NS_PER_HOUR
            + (self.minutes as i128) * NS_PER_MINUTE
            + (self.seconds as i128) * NS_PER_SECOND
            + (self.milliseconds as i128) * NS_PER_MILLISECOND
            + (self.microseconds as i128) * NS_PER_MICROSECOND
            + (self.nanoseconds as i128)
    }

    fn time_total_nanoseconds_with_days(&self) -> TemporalResult<i128> {
        (self.days as i128)
            .checked_mul(NS_PER_DAY)
            .and_then(|d| d.checked_add(self.time_total_nanoseconds()))
            .ok_or_else(|| overflow_err("Duration"))
    }

    /// BalanceTimeDuration: build a duration from total nanoseconds, carrying
    /// upward into `largest_unit` (which must be Day or a time unit).
    pub fn from_time_nanoseconds(total_ns: i128, largest_unit: Unit) -> TemporalResult<Duration> {
        if largest_unit < Unit::Day {
            return Err(TemporalError::range(
                "balancing calendar units requires a relativeTo (C11.3 boundary)",
            ));
        }
        let sign: i128 = if total_ns < 0 { -1 } else { 1 };
        let mut rest = total_ns.abs();
        let mut out = Duration::default();
        let order = [
            (Unit::Day, NS_PER_DAY),
            (Unit::Hour, NS_PER_HOUR),
            (Unit::Minute, NS_PER_MINUTE),
            (Unit::Second, NS_PER_SECOND),
            (Unit::Millisecond, NS_PER_MILLISECOND),
            (Unit::Microsecond, NS_PER_MICROSECOND),
        ];
        for (unit, ns) in order {
            if largest_unit <= unit {
                let amount = rest / ns;
                rest %= ns;
                let field = i64::try_from(amount * sign).map_err(|_| overflow_err("balance"))?;
                match unit {
                    Unit::Day => out.days = field,
                    Unit::Hour => out.hours = field,
                    Unit::Minute => out.minutes = field,
                    Unit::Second => out.seconds = field,
                    Unit::Millisecond => out.milliseconds = field,
                    Unit::Microsecond => out.microseconds = field,
                    _ => unreachable!("order contains only day..microsecond"),
                }
            }
        }
        out.nanoseconds = i64::try_from(rest * sign).map_err(|_| overflow_err("balance"))?;
        out.validate()?;
        Ok(out)
    }

    /// Temporal.Duration.prototype.round without relativeTo: valid only when
    /// no calendar unit (year/month/week) is present or requested. Days are
    /// treated as exactly 24 hours.
    pub fn round(
        &self,
        smallest_unit: Unit,
        largest_unit: Unit,
        increment: i128,
        mode: RoundingMode,
    ) -> TemporalResult<Duration> {
        if self.years != 0 || self.months != 0 || self.weeks != 0 {
            return Err(TemporalError::range(
                "rounding a duration with calendar units requires relativeTo (C11.3 boundary)",
            ));
        }
        if smallest_unit < Unit::Day || largest_unit < Unit::Day {
            return Err(TemporalError::range(
                "rounding to calendar units requires relativeTo (C11.3 boundary)",
            ));
        }
        if smallest_unit < largest_unit {
            return Err(TemporalError::range(
                "smallestUnit must not be larger than largestUnit",
            ));
        }
        validate_rounding_increment(smallest_unit, increment, false)?;
        let total = self.time_total_nanoseconds_with_days()?;
        let unit_ns = smallest_unit.ns_per().ok_or_else(|| overflow_err("round"))?;
        let step = unit_ns.checked_mul(increment).ok_or_else(|| overflow_err("round"))?;
        let rounded = round_to_increment(total, step, mode)?;
        Duration::from_time_nanoseconds(rounded, largest_unit)
    }

    /// Temporal.Duration.prototype.total without relativeTo (unit must be Day
    /// or smaller; day = 24h). Exact division result as (quotient, remainder
    /// numerator, unit nanoseconds); `total_as_f64` renders the spec's Number.
    pub fn total_exact(&self, unit: Unit) -> TemporalResult<(i128, i128, i128)> {
        if self.years != 0 || self.months != 0 || self.weeks != 0 {
            return Err(TemporalError::range(
                "totaling a duration with calendar units requires relativeTo (C11.3 boundary)",
            ));
        }
        let unit_ns = unit.ns_per().ok_or_else(|| {
            TemporalError::range("total unit must be day..nanosecond without relativeTo")
        })?;
        let total = self.time_total_nanoseconds_with_days()?;
        Ok((total.div_euclid(unit_ns), total.rem_euclid(unit_ns), unit_ns))
    }

    /// Presentation-only float conversion of `total_exact` (the JS `total()`
    /// return value). Never feeds back into arithmetic.
    pub fn total_as_f64(&self, unit: Unit) -> TemporalResult<f64> {
        let (q, r, unit_ns) = self.total_exact(unit)?;
        Ok(q as f64 + (r as f64) / (unit_ns as f64))
    }

    /// ParseTemporalDurationString (ISO 8601-2 duration).
    pub fn parse(text: &str) -> TemporalResult<Duration> {
        let bytes = text.as_bytes();
        let mut pos = 0_usize;
        let sign: i64 = match bytes.first() {
            Some(b'-') => {
                pos += 1;
                -1
            }
            Some(b'+') => {
                pos += 1;
                1
            }
            _ => 1,
        };
        if !matches!(bytes.get(pos), Some(b'P') | Some(b'p')) {
            return Err(TemporalError::syntax("duration string must contain 'P'"));
        }
        pos += 1;

        let mut d = Duration::default();
        let mut any = false;
        let mut fraction_seen = false;

        // Date part designators, in mandatory order.
        let date_slots: [(u8, u8); 4] = [(b'Y', 0), (b'M', 1), (b'W', 2), (b'D', 3)];
        let mut slot_idx = 0;
        while pos < bytes.len() && !matches!(bytes[pos], b'T' | b't') {
            let (value, digits, frac) = parse_duration_number(bytes, &mut pos)?;
            if frac.is_some() {
                return Err(TemporalError::syntax("fractions are only allowed on time components"));
            }
            if digits == 0 {
                return Err(TemporalError::syntax("expected digits in duration"));
            }
            let designator = *bytes
                .get(pos)
                .ok_or_else(|| TemporalError::syntax("missing duration designator"))?;
            pos += 1;
            let upper = designator.to_ascii_uppercase();
            let slot = date_slots
                .iter()
                .position(|&(c, _)| c == upper)
                .ok_or_else(|| TemporalError::syntax("invalid date designator in duration"))?;
            if slot < slot_idx {
                return Err(TemporalError::syntax("duration designators out of order"));
            }
            slot_idx = slot + 1;
            let field = value.checked_mul(sign as i128).ok_or_else(|| overflow_err("parse"))?;
            let field = i64::try_from(field).map_err(|_| overflow_err("Duration.parse"))?;
            match upper {
                b'Y' => d.years = field,
                b'M' => d.months = field,
                b'W' => d.weeks = field,
                _ => d.days = field,
            }
            any = true;
        }

        if pos < bytes.len() {
            // Time part.
            pos += 1; // consume 'T'
            let mut time_any = false;
            let mut time_slot = 0; // H=0, M=1, S=2
            while pos < bytes.len() {
                if fraction_seen {
                    return Err(TemporalError::syntax(
                        "no components may follow a fractional component",
                    ));
                }
                let (value, digits, frac) = parse_duration_number(bytes, &mut pos)?;
                if digits == 0 {
                    return Err(TemporalError::syntax("expected digits in duration"));
                }
                let designator = *bytes
                    .get(pos)
                    .ok_or_else(|| TemporalError::syntax("missing duration designator"))?;
                pos += 1;
                let (slot, unit_ns): (usize, i128) = match designator.to_ascii_uppercase() {
                    b'H' => (0, NS_PER_HOUR),
                    b'M' => (1, NS_PER_MINUTE),
                    b'S' => (2, NS_PER_SECOND),
                    _ => return Err(TemporalError::syntax("invalid time designator in duration")),
                };
                if slot < time_slot {
                    return Err(TemporalError::syntax("duration designators out of order"));
                }
                time_slot = slot + 1;
                let whole = value.checked_mul(sign as i128).ok_or_else(|| overflow_err("parse"))?;
                match slot {
                    0 => d.hours = i64::try_from(whole).map_err(|_| overflow_err("Duration.parse"))?,
                    1 => d.minutes = i64::try_from(whole).map_err(|_| overflow_err("Duration.parse"))?,
                    _ => d.seconds = i64::try_from(whole).map_err(|_| overflow_err("Duration.parse"))?,
                }
                if let Some(frac_ns_of_unit) = frac {
                    fraction_seen = true;
                    // frac_ns_of_unit is the fraction scaled to 10^-9 of one
                    // unit; convert exactly to nanoseconds of that unit.
                    let frac_ns = frac_ns_of_unit
                        .checked_mul(unit_ns / NS_PER_SECOND * (sign as i128))
                        .ok_or_else(|| overflow_err("parse"))?;
                    // Distribute into ms/us/ns exactly.
                    let extra = if unit_ns == NS_PER_SECOND {
                        frac_ns_of_unit * (sign as i128)
                    } else {
                        frac_ns
                    };
                    d.milliseconds = i64::try_from(extra / NS_PER_MILLISECOND)
                        .map_err(|_| overflow_err("Duration.parse"))?;
                    d.microseconds = i64::try_from((extra % NS_PER_MILLISECOND) / NS_PER_MICROSECOND)
                        .map_err(|_| overflow_err("Duration.parse"))?;
                    d.nanoseconds = i64::try_from(extra % NS_PER_MICROSECOND)
                        .map_err(|_| overflow_err("Duration.parse"))?;
                }
                time_any = true;
                any = true;
            }
            if !time_any {
                return Err(TemporalError::syntax("'T' must be followed by a time component"));
            }
        }

        if !any {
            return Err(TemporalError::syntax("duration must contain at least one component"));
        }
        d.validate()?;
        Ok(d)
    }

    /// TemporalDurationToString (auto precision).
    pub fn format(&self) -> String {
        let sign = self.sign();
        let a = self.abs();
        let mut out = String::new();
        if sign < 0 {
            out.push('-');
        }
        out.push('P');
        if a.years != 0 {
            out.push_str(&format!("{}Y", a.years));
        }
        if a.months != 0 {
            out.push_str(&format!("{}M", a.months));
        }
        if a.weeks != 0 {
            out.push_str(&format!("{}W", a.weeks));
        }
        if a.days != 0 {
            out.push_str(&format!("{}D", a.days));
        }
        let sub_ns =
            a.milliseconds as i128 * NS_PER_MILLISECOND + a.microseconds as i128 * NS_PER_MICROSECOND
                + a.nanoseconds as i128;
        // Carry sub-second overflow into seconds for canonical output.
        let extra_seconds = (sub_ns / NS_PER_SECOND) as i64;
        let frac_ns = (sub_ns % NS_PER_SECOND) as u64;
        let seconds = a.seconds + extra_seconds;
        let has_time = a.hours != 0 || a.minutes != 0 || seconds != 0 || frac_ns != 0;
        let date_empty = a.years == 0 && a.months == 0 && a.weeks == 0 && a.days == 0;
        if has_time || date_empty {
            out.push('T');
            if a.hours != 0 {
                out.push_str(&format!("{}H", a.hours));
            }
            if a.minutes != 0 {
                out.push_str(&format!("{}M", a.minutes));
            }
            if seconds != 0 || frac_ns != 0 || (a.hours == 0 && a.minutes == 0 && date_empty) {
                out.push_str(&seconds.to_string());
                if frac_ns != 0 {
                    let mut frac = format!("{frac_ns:09}");
                    while frac.ends_with('0') {
                        frac.pop();
                    }
                    out.push('.');
                    out.push_str(&frac);
                }
                out.push('S');
            }
        }
        out
    }
}

impl fmt::Display for Duration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.format())
    }
}

/// Parses digits (and optional `.`/`,` fraction of up to 9 digits) at `pos`.
/// Returns (whole value, digit count, optional fraction scaled to 10^-9).
fn parse_duration_number(
    bytes: &[u8],
    pos: &mut usize,
) -> TemporalResult<(i128, usize, Option<i128>)> {
    let mut value: i128 = 0;
    let mut digits = 0_usize;
    while let Some(&b) = bytes.get(*pos) {
        if !b.is_ascii_digit() {
            break;
        }
        value = value
            .checked_mul(10)
            .and_then(|v| v.checked_add((b - b'0') as i128))
            .ok_or_else(|| overflow_err("Duration.parse"))?;
        digits += 1;
        *pos += 1;
    }
    let mut fraction = None;
    if matches!(bytes.get(*pos), Some(b'.') | Some(b',')) {
        *pos += 1;
        let mut frac: i128 = 0;
        let mut frac_digits = 0_usize;
        while let Some(&b) = bytes.get(*pos) {
            if !b.is_ascii_digit() {
                break;
            }
            if frac_digits < 9 {
                frac = frac * 10 + (b - b'0') as i128;
                frac_digits += 1;
            } else {
                return Err(TemporalError::syntax("fraction exceeds 9 digits"));
            }
            *pos += 1;
        }
        if frac_digits == 0 {
            return Err(TemporalError::syntax("fraction requires at least one digit"));
        }
        for _ in frac_digits..9 {
            frac *= 10;
        }
        fraction = Some(frac);
    }
    Ok((value, digits, fraction))
}

// ---------------------------------------------------------------------------
// Shared ISO date/time helpers (also used by plain_types)
// ---------------------------------------------------------------------------

/// Proleptic Gregorian leap-year test.
pub fn is_leap_year(year: i32) -> bool {
    (year % 4 == 0 && year % 100 != 0) || year % 400 == 0
}

pub fn days_in_month(year: i32, month: u8) -> u8 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => {
            if is_leap_year(year) {
                29
            } else {
                28
            }
        }
        _ => 0,
    }
}

pub fn days_in_year(year: i32) -> u16 {
    if is_leap_year(year) { 366 } else { 365 }
}

/// Days from 1970-01-01 to year-month-day (proleptic Gregorian), exact
/// integer computation (Howard Hinnant's `days_from_civil`, i64 domain).
pub fn epoch_days_from_ymd(year: i32, month: u8, day: u8) -> i64 {
    let y = year as i64 - if month <= 2 { 1 } else { 0 };
    let era = y.div_euclid(400);
    let yoe = y.rem_euclid(400); // [0, 399]
    let m = month as i64;
    let doy = (153 * (m + if m > 2 { -3 } else { 9 }) + 2) / 5 + day as i64 - 1; // [0, 365]
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy; // [0, 146096]
    era * 146_097 + doe - 719_468
}

/// Inverse of `epoch_days_from_ymd` (Hinnant `civil_from_days`).
pub fn ymd_from_epoch_days(days: i64) -> (i32, u8, u8) {
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097); // [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365; // [0, 399]
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // [0, 365]
    let mp = (5 * doy + 2) / 153; // [0, 11]
    let d = (doy - (153 * mp + 2) / 5 + 1) as u8; // [1, 31]
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u8; // [1, 12]
    ((y + if m <= 2 { 1 } else { 0 }) as i32, m, d)
}

fn epoch_days_checked(year: i32, month: u8, day: u8) -> TemporalResult<i64> {
    if !(1..=12).contains(&month) || day < 1 || day > days_in_month(year, month) {
        return Err(TemporalError::range(format!(
            "invalid ISO date {year:+07}-{month:02}-{day:02}"
        )));
    }
    Ok(epoch_days_from_ymd(year, month, day))
}

/// Formats an ISO date, using the 6-digit signed extended form outside 0..=9999.
pub fn format_iso_date(year: i32, month: u8, day: u8) -> String {
    if (0..=9999).contains(&year) {
        format!("{year:04}-{month:02}-{day:02}")
    } else {
        let sign = if year < 0 { '-' } else { '+' };
        format!("{sign}{:06}-{month:02}-{day:02}", year.unsigned_abs())
    }
}

/// Formats a nanoseconds-of-day time value under a precision policy.
pub fn format_time_ns(time_ns: i128, precision: Precision) -> String {
    debug_assert!((0..NS_PER_DAY).contains(&time_ns));
    let hour = time_ns / NS_PER_HOUR;
    let minute = (time_ns / NS_PER_MINUTE) % 60;
    let second = (time_ns / NS_PER_SECOND) % 60;
    let frac = (time_ns % NS_PER_SECOND) as u64;
    let mut out = format!("{hour:02}:{minute:02}");
    match precision {
        Precision::Minute => out,
        Precision::Auto => {
            out.push_str(&format!(":{second:02}"));
            if frac != 0 {
                let mut digits = format!("{frac:09}");
                while digits.len() > 3 && digits[digits.len() - 3..].bytes().all(|b| b == b'0') {
                    digits.truncate(digits.len() - 3);
                }
                while digits.ends_with('0') && digits.len() % 3 != 0 {
                    // keep groups of 3 per spec auto precision
                    break;
                }
                out.push('.');
                out.push_str(&digits);
            }
            out
        }
        Precision::Digits(n) => {
            out.push_str(&format!(":{second:02}"));
            if n > 0 {
                let digits = format!("{frac:09}");
                out.push('.');
                out.push_str(&digits[..n as usize]);
            }
            out
        }
    }
}

// ---------------------------------------------------------------------------
// ISO 8601 string parsing (shared with plain_types)
// ---------------------------------------------------------------------------

/// UTC offset in a parsed string.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UtcOffsetRecord {
    /// `Z` / `z`.
    Zulu,
    /// Numeric offset in nanoseconds east of UTC.
    Numeric(i128),
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
    /// Bracketed time zone annotation (e.g. `UTC`, `+01:00`, `America/New_York`),
    /// unresolved: resolution is the jiff/tzdb C11.3 boundary.
    pub time_zone: Option<String>,
    /// `[u-ca=…]` value if present.
    pub calendar: Option<String>,
}

struct Cursor<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(text: &'a str) -> Self {
        Cursor { bytes: text.as_bytes(), pos: 0 }
    }
    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }
    fn bump(&mut self) -> Option<u8> {
        let b = self.peek()?;
        self.pos += 1;
        Some(b)
    }
    fn eat(&mut self, b: u8) -> bool {
        if self.peek() == Some(b) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn digits(&mut self, count: usize) -> TemporalResult<u32> {
        let mut value: u32 = 0;
        for _ in 0..count {
            match self.bump() {
                Some(b) if b.is_ascii_digit() => value = value * 10 + (b - b'0') as u32,
                _ => return Err(TemporalError::syntax("expected digit")),
            }
        }
        Ok(value)
    }
    fn done(&self) -> bool {
        self.pos >= self.bytes.len()
    }
}

fn parse_iso_year(c: &mut Cursor) -> TemporalResult<i32> {
    match c.peek() {
        Some(b'+') | Some(b'-') => {
            let neg = c.bump() == Some(b'-');
            let v = c.digits(6)? as i32;
            if neg && v == 0 {
                return Err(TemporalError::syntax("-000000 is not a valid extended year"));
            }
            Ok(if neg { -v } else { v })
        }
        _ => Ok(c.digits(4)? as i32),
    }
}

/// Parses `hh[:mm[:ss[.f{1,9}]]]` (with or without separators, but
/// consistently) returning nanoseconds since midnight.
fn parse_iso_time(c: &mut Cursor) -> TemporalResult<i128> {
    let hour = c.digits(2)?;
    if hour > 23 {
        return Err(TemporalError::syntax("hour out of range"));
    }
    let mut ns = hour as i128 * NS_PER_HOUR;
    let sep = c.peek() == Some(b':');
    if sep {
        c.pos += 1;
    }
    if matches!(c.peek(), Some(b) if b.is_ascii_digit()) {
        let minute = c.digits(2)?;
        if minute > 59 {
            return Err(TemporalError::syntax("minute out of range"));
        }
        ns += minute as i128 * NS_PER_MINUTE;
        let had_sep = c.peek() == Some(b':');
        if had_sep != sep && had_sep {
            return Err(TemporalError::syntax("inconsistent time separators"));
        }
        if had_sep {
            c.pos += 1;
        }
        if (had_sep || !sep) && matches!(c.peek(), Some(b) if b.is_ascii_digit()) {
            if !had_sep && sep {
                return Err(TemporalError::syntax("inconsistent time separators"));
            }
            let second = c.digits(2)?;
            if second > 59 {
                return Err(TemporalError::syntax("second out of range"));
            }
            ns += second as i128 * NS_PER_SECOND;
            if matches!(c.peek(), Some(b'.') | Some(b',')) {
                c.pos += 1;
                let mut frac: i128 = 0;
                let mut count = 0;
                while let Some(b) = c.peek() {
                    if !b.is_ascii_digit() {
                        break;
                    }
                    if count >= 9 {
                        return Err(TemporalError::syntax("fraction exceeds 9 digits"));
                    }
                    frac = frac * 10 + (b - b'0') as i128;
                    count += 1;
                    c.pos += 1;
                }
                if count == 0 {
                    return Err(TemporalError::syntax("fraction requires at least one digit"));
                }
                for _ in count..9 {
                    frac *= 10;
                }
                ns += frac;
            }
        }
    } else if sep {
        return Err(TemporalError::syntax("expected minutes after ':'"));
    }
    Ok(ns)
}

fn parse_utc_offset(c: &mut Cursor) -> TemporalResult<Option<UtcOffsetRecord>> {
    match c.peek() {
        Some(b'Z') | Some(b'z') => {
            c.pos += 1;
            Ok(Some(UtcOffsetRecord::Zulu))
        }
        Some(b'+') | Some(b'-') => {
            let neg = c.bump() == Some(b'-');
            let hour = c.digits(2)?;
            if hour > 23 {
                return Err(TemporalError::syntax("offset hour out of range"));
            }
            let mut ns = hour as i128 * NS_PER_HOUR;
            let sep = c.eat(b':');
            if matches!(c.peek(), Some(b) if b.is_ascii_digit()) {
                let minute = c.digits(2)?;
                if minute > 59 {
                    return Err(TemporalError::syntax("offset minute out of range"));
                }
                ns += minute as i128 * NS_PER_MINUTE;
                let sep2 = c.eat(b':');
                if sep2 && !sep {
                    return Err(TemporalError::syntax("inconsistent offset separators"));
                }
                if (sep2 || !sep) && matches!(c.peek(), Some(b) if b.is_ascii_digit()) {
                    let second = c.digits(2)?;
                    if second > 59 {
                        return Err(TemporalError::syntax("offset second out of range"));
                    }
                    ns += second as i128 * NS_PER_SECOND;
                    if matches!(c.peek(), Some(b'.') | Some(b',')) {
                        c.pos += 1;
                        let mut frac: i128 = 0;
                        let mut count = 0;
                        while let Some(b) = c.peek() {
                            if !b.is_ascii_digit() {
                                break;
                            }
                            if count >= 9 {
                                return Err(TemporalError::syntax("offset fraction exceeds 9 digits"));
                            }
                            frac = frac * 10 + (b - b'0') as i128;
                            count += 1;
                            c.pos += 1;
                        }
                        if count == 0 {
                            return Err(TemporalError::syntax("offset fraction requires digits"));
                        }
                        for _ in count..9 {
                            frac *= 10;
                        }
                        ns += frac;
                    }
                }
            } else if sep {
                return Err(TemporalError::syntax("expected offset minutes after ':'"));
            }
            Ok(Some(UtcOffsetRecord::Numeric(if neg { -ns } else { ns })))
        }
        _ => Ok(None),
    }
}

fn parse_annotations(
    c: &mut Cursor,
    time_zone: &mut Option<String>,
    calendar: &mut Option<String>,
) -> TemporalResult<()> {
    let mut calendar_seen = false;
    while c.eat(b'[') {
        let critical = c.eat(b'!');
        let start = c.pos;
        while let Some(b) = c.peek() {
            if b == b']' {
                break;
            }
            c.pos += 1;
        }
        if !c.eat(b']') {
            return Err(TemporalError::syntax("unterminated annotation"));
        }
        let body = std::str::from_utf8(&c.bytes[start..c.pos - 1])
            .map_err(|_| TemporalError::syntax("annotation is not valid UTF-8"))?;
        if body.is_empty() {
            return Err(TemporalError::syntax("empty annotation"));
        }
        if let Some(value) = body.strip_prefix("u-ca=") {
            if value.is_empty() {
                return Err(TemporalError::syntax("empty u-ca annotation value"));
            }
            if calendar_seen {
                if critical {
                    return Err(TemporalError::range("duplicate critical u-ca annotation"));
                }
                continue; // first annotation wins per spec
            }
            calendar_seen = true;
            if value != "iso8601" && critical {
                return Err(TemporalError::range(format!(
                    "unsupported critical calendar annotation '{value}'"
                )));
            }
            if value != "iso8601" {
                return Err(TemporalError::range(format!(
                    "only the iso8601 calendar is supported, got '{value}'"
                )));
            }
            *calendar = Some(value.to_string());
        } else if body.contains('=') {
            // Unknown key=value annotation: ignored unless critical.
            if critical {
                return Err(TemporalError::range(format!(
                    "unknown critical annotation '{body}'"
                )));
            }
        } else {
            // Time zone annotation: first bracketed non key=value item only,
            // and it must come before any other annotation.
            if time_zone.is_some() || calendar_seen {
                return Err(TemporalError::syntax(
                    "time zone annotation must be the first annotation",
                ));
            }
            *time_zone = Some(body.to_string());
        }
    }
    Ok(())
}

/// Parses `date[T time[offset]][annotations]`. Central grammar for Instant and
/// the plain types (which apply their own presence rules on the result).
pub fn parse_iso_datetime_string(text: &str) -> TemporalResult<ParsedIsoDateTime> {
    let mut c = Cursor::new(text);
    let year = parse_iso_year(&mut c)?;
    let dash = c.eat(b'-');
    let month = c.digits(2)? as u8;
    if dash && !c.eat(b'-') {
        return Err(TemporalError::syntax("inconsistent date separators"));
    }
    if !dash && c.peek() == Some(b'-') {
        return Err(TemporalError::syntax("inconsistent date separators"));
    }
    let day = c.digits(2)? as u8;
    if !(1..=12).contains(&month) {
        return Err(TemporalError::range(format!("month {month} out of range")));
    }
    if day < 1 || day > days_in_month(year, month) {
        return Err(TemporalError::range(format!("day {day} out of range")));
    }

    let mut has_time = false;
    let mut time_ns = 0_i128;
    let mut offset = None;
    if matches!(c.peek(), Some(b'T') | Some(b't') | Some(b' ')) {
        c.pos += 1;
        has_time = true;
        time_ns = parse_iso_time(&mut c)?;
        offset = parse_utc_offset(&mut c)?;
    }

    let mut time_zone = None;
    let mut calendar = None;
    parse_annotations(&mut c, &mut time_zone, &mut calendar)?;
    if !c.done() {
        return Err(TemporalError::syntax(format!(
            "unexpected trailing characters at position {}",
            c.pos
        )));
    }
    Ok(ParsedIsoDateTime { year, month, day, has_time, time_ns, offset, time_zone, calendar })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // ---- Instant bounds ----

    #[test]
    fn instant_exact_bounds() {
        assert!(Instant::from_epoch_nanoseconds(INSTANT_NS_MAX).is_ok());
        assert!(Instant::from_epoch_nanoseconds(INSTANT_NS_MIN).is_ok());
        let over = Instant::from_epoch_nanoseconds(INSTANT_NS_MAX + 1);
        assert_eq!(over.unwrap_err().kind, TemporalErrorKind::Range);
        let under = Instant::from_epoch_nanoseconds(INSTANT_NS_MIN - 1);
        assert_eq!(under.unwrap_err().kind, TemporalErrorKind::Range);
    }

    #[test]
    fn instant_add_overflow_at_boundary() {
        let max = Instant::from_epoch_nanoseconds(INSTANT_NS_MAX).unwrap();
        let one_ns = Duration::from_time(0, 0, 0, 0, 0, 1).unwrap();
        assert_eq!(max.add(&one_ns).unwrap_err().kind, TemporalErrorKind::Range);
        assert_eq!(max.subtract(&one_ns).unwrap().epoch_nanoseconds(), INSTANT_NS_MAX - 1);
    }

    #[test]
    fn instant_rejects_date_units() {
        let i = Instant::from_epoch_nanoseconds(0).unwrap();
        let d = Duration::new(0, 0, 0, 1, 0, 0, 0, 0, 0, 0).unwrap();
        assert_eq!(i.add(&d).unwrap_err().kind, TemporalErrorKind::Range);
    }

    #[test]
    fn instant_epoch_milliseconds_floors_negative() {
        let i = Instant::from_epoch_nanoseconds(-1).unwrap();
        assert_eq!(i.epoch_milliseconds(), -1);
        assert_eq!(i.epoch_seconds(), -1);
    }

    // ---- Rounding, including negative operands ----

    #[test]
    fn round_negative_matrix() {
        // x = -7, increment 3: floor→-9, ceil→-6, trunc→-6, expand→-9.
        assert_eq!(round_to_increment(-7, 3, RoundingMode::Floor).unwrap(), -9);
        assert_eq!(round_to_increment(-7, 3, RoundingMode::Ceil).unwrap(), -6);
        assert_eq!(round_to_increment(-7, 3, RoundingMode::Trunc).unwrap(), -6);
        assert_eq!(round_to_increment(-7, 3, RoundingMode::Expand).unwrap(), -9);
        // Half cases at exact midpoint: x = -3, increment 2.
        assert_eq!(round_to_increment(-3, 2, RoundingMode::HalfExpand).unwrap(), -4);
        assert_eq!(round_to_increment(-3, 2, RoundingMode::HalfTrunc).unwrap(), -2);
        assert_eq!(round_to_increment(-3, 2, RoundingMode::HalfCeil).unwrap(), -2);
        assert_eq!(round_to_increment(-3, 2, RoundingMode::HalfFloor).unwrap(), -4);
        assert_eq!(round_to_increment(-3, 2, RoundingMode::HalfEven).unwrap(), -4);
        assert_eq!(round_to_increment(-1, 2, RoundingMode::HalfEven).unwrap(), 0);
    }

    #[test]
    fn instant_round_negative_epoch() {
        // -1 ns rounded to nearest second: halfExpand → 0.
        let i = Instant::from_epoch_nanoseconds(-1).unwrap();
        let r = i.round(Unit::Second, 1, RoundingMode::HalfExpand).unwrap();
        assert_eq!(r.epoch_nanoseconds(), 0);
        let f = i.round(Unit::Second, 1, RoundingMode::Floor).unwrap();
        assert_eq!(f.epoch_nanoseconds(), -NS_PER_SECOND);
    }

    #[test]
    fn instant_round_increment_must_divide_day() {
        let i = Instant::from_epoch_nanoseconds(0).unwrap();
        assert!(i.round(Unit::Hour, 7, RoundingMode::Trunc).is_err()); // 24 % 7 != 0
        assert!(i.round(Unit::Hour, 6, RoundingMode::Trunc).is_ok());
        assert!(i.round(Unit::Day, 1, RoundingMode::Trunc).is_err()); // not a time unit
    }

    // ---- Instant parse/format ----

    #[test]
    fn instant_parse_epoch_and_offset() {
        let i = Instant::parse("1970-01-01T00:00:00Z").unwrap();
        assert_eq!(i.epoch_nanoseconds(), 0);
        let j = Instant::parse("1970-01-01T01:00:00+01:00").unwrap();
        assert_eq!(j.epoch_nanoseconds(), 0);
        let k = Instant::parse("1969-12-31T19:00:00-05:00").unwrap();
        assert_eq!(k.epoch_nanoseconds(), 0);
    }

    #[test]
    fn instant_parse_fractional_seconds_exact() {
        let i = Instant::parse("1970-01-01T00:00:00.5Z").unwrap();
        assert_eq!(i.epoch_nanoseconds(), 500_000_000);
        let j = Instant::parse("1970-01-01T00:00:00.123456789Z").unwrap();
        assert_eq!(j.epoch_nanoseconds(), 123_456_789);
        assert!(Instant::parse("1970-01-01T00:00:00.1234567890Z").is_err());
    }

    #[test]
    fn instant_parse_requires_offset_and_time() {
        assert!(Instant::parse("1970-01-01").is_err());
        assert!(Instant::parse("1970-01-01T00:00:00").is_err());
    }

    #[test]
    fn instant_parse_annotations() {
        let i = Instant::parse("1970-01-01T00:00:00Z[UTC][u-ca=iso8601]").unwrap();
        assert_eq!(i.epoch_nanoseconds(), 0);
        assert!(Instant::parse("1970-01-01T00:00:00Z[!u-ca=japanese]").is_ok());
        assert!(Instant::parse("1970-01-01T00:00:00Z[!unknown=x]").is_err());
        // Non-critical unknown annotation ignored.
        assert!(Instant::parse("1970-01-01T00:00:00Z[unknown=x]").is_ok());
    }

    #[test]
    fn instant_format_round_trip_and_bounds() {
        let max = Instant::from_epoch_nanoseconds(INSTANT_NS_MAX).unwrap();
        let s = max.format(Precision::Auto);
        assert_eq!(s, "+275760-09-13T00:00:00Z");
        assert_eq!(Instant::parse(&s).unwrap(), max);
        let min = Instant::from_epoch_nanoseconds(INSTANT_NS_MIN).unwrap();
        let s = min.format(Precision::Auto);
        assert_eq!(s, "-271821-04-20T00:00:00Z");
        assert_eq!(Instant::parse(&s).unwrap(), min);
    }

    #[test]
    fn instant_format_precision() {
        let i = Instant::from_epoch_nanoseconds(1_500_000_000).unwrap();
        assert_eq!(i.format(Precision::Auto), "1970-01-01T00:00:01.5Z");
        assert_eq!(i.format(Precision::Digits(0)), "1970-01-01T00:00:01Z");
        assert_eq!(i.format(Precision::Digits(6)), "1970-01-01T00:00:01.500000Z");
        assert_eq!(i.format(Precision::Minute), "1970-01-01T00:00Z");
    }

    // ---- Instant difference ----

    #[test]
    fn instant_until_balances_to_largest_unit() {
        let a = Instant::from_epoch_nanoseconds(0).unwrap();
        let b = Instant::from_epoch_nanoseconds(NS_PER_HOUR * 25 + NS_PER_MINUTE * 30).unwrap();
        let d = a
            .until(b, Unit::Hour, Unit::Nanosecond, 1, RoundingMode::HalfExpand)
            .unwrap();
        assert_eq!((d.hours, d.minutes), (25, 30));
        let neg = b
            .until(a, Unit::Hour, Unit::Nanosecond, 1, RoundingMode::HalfExpand)
            .unwrap();
        assert_eq!((neg.hours, neg.minutes), (-25, -30));
        assert_eq!(neg.sign(), -1);
    }

    #[test]
    fn instant_until_rejects_date_units() {
        let a = Instant::from_epoch_nanoseconds(0).unwrap();
        assert!(a.until(a, Unit::Day, Unit::Nanosecond, 1, RoundingMode::Trunc).is_err());
    }

    // ---- Duration validation ----

    #[test]
    fn duration_mixed_sign_rejected() {
        let err = Duration::new(1, 0, 0, -1, 0, 0, 0, 0, 0, 0).unwrap_err();
        assert_eq!(err.kind, TemporalErrorKind::Range);
        let err = Duration::new(0, 0, 0, 0, 1, 0, 0, 0, 0, -1).unwrap_err();
        assert_eq!(err.kind, TemporalErrorKind::Range);
        assert!(Duration::new(0, 0, 0, 0, -1, -30, 0, 0, 0, 0).is_ok());
    }

    #[test]
    fn duration_calendar_field_limit() {
        let limit = 1_i64 << 32;
        assert!(Duration::new(limit, 0, 0, 0, 0, 0, 0, 0, 0, 0).is_err());
        assert!(Duration::new(limit - 1, 0, 0, 0, 0, 0, 0, 0, 0, 0).is_ok());
    }

    #[test]
    fn duration_time_limit_2_pow_53_seconds() {
        let max_s = (1_i64 << 53) - 1;
        assert!(Duration::new(0, 0, 0, 0, 0, 0, max_s, 0, 0, 999_999_999).is_ok());
        assert!(Duration::new(0, 0, 0, 0, 0, 0, max_s + 1, 0, 0, 0).is_err());
        // Days participate in the time bound.
        let max_days = max_s / 86_400;
        assert!(Duration::new(0, 0, 0, max_days + 1, 0, 0, 0, 0, 0, 0).is_err());
    }

    #[test]
    fn duration_sign_and_negate() {
        let d = Duration::new(0, 0, 0, 0, 0, 0, 0, 0, 0, -5).unwrap();
        assert_eq!(d.sign(), -1);
        assert_eq!(d.negated().sign(), 1);
        assert_eq!(d.abs().nanoseconds, 5);
        assert_eq!(Duration::default().sign(), 0);
    }

    // ---- Duration balance / round / total ----

    #[test]
    fn duration_balance_to_days() {
        let d = Duration::from_time_nanoseconds(NS_PER_DAY + NS_PER_HOUR + 1, Unit::Day).unwrap();
        assert_eq!((d.days, d.hours, d.nanoseconds), (1, 1, 1));
        let n = Duration::from_time_nanoseconds(-(NS_PER_DAY + NS_PER_HOUR), Unit::Hour).unwrap();
        assert_eq!((n.days, n.hours), (0, -25));
    }

    #[test]
    fn duration_balance_calendar_needs_relative_to() {
        assert!(Duration::from_time_nanoseconds(1, Unit::Month).is_err());
    }

    #[test]
    fn duration_round_time_only() {
        let d = Duration::from_time(0, 90, 0, 0, 0, 0).unwrap();
        let r = d.round(Unit::Hour, Unit::Hour, 1, RoundingMode::HalfExpand).unwrap();
        assert_eq!(r.hours, 2);
        let neg = d.negated().round(Unit::Hour, Unit::Hour, 1, RoundingMode::HalfExpand).unwrap();
        assert_eq!(neg.hours, -2);
        let cal = Duration::new(1, 0, 0, 0, 0, 0, 0, 0, 0, 0).unwrap();
        assert!(cal.round(Unit::Hour, Unit::Hour, 1, RoundingMode::Trunc).is_err());
        assert!(d.round(Unit::Month, Unit::Month, 1, RoundingMode::Trunc).is_err());
    }

    #[test]
    fn duration_total_exact_and_float() {
        let d = Duration::from_time(1, 30, 0, 0, 0, 0).unwrap();
        let (q, r, unit) = d.total_exact(Unit::Hour).unwrap();
        assert_eq!((q, r, unit), (1, NS_PER_HOUR / 2, NS_PER_HOUR));
        assert_eq!(d.total_as_f64(Unit::Hour).unwrap(), 1.5);
        assert_eq!(d.total_as_f64(Unit::Minute).unwrap(), 90.0);
        let cal = Duration::new(0, 1, 0, 0, 0, 0, 0, 0, 0, 0).unwrap();
        assert!(cal.total_exact(Unit::Day).is_err());
    }

    // ---- Duration parse / format ----

    #[test]
    fn duration_parse_basic_and_sign() {
        let d = Duration::parse("P1Y2M3W4DT5H6M7S").unwrap();
        assert_eq!(
            (d.years, d.months, d.weeks, d.days, d.hours, d.minutes, d.seconds),
            (1, 2, 3, 4, 5, 6, 7)
        );
        let n = Duration::parse("-PT1H").unwrap();
        assert_eq!(n.hours, -1);
        assert_eq!(Duration::parse("+PT0S").unwrap().sign(), 0);
    }

    #[test]
    fn duration_parse_fractional_seconds() {
        let d = Duration::parse("PT1.5S").unwrap();
        assert_eq!((d.seconds, d.milliseconds), (1, 500));
        let n = Duration::parse("-PT0.000000001S").unwrap();
        assert_eq!(n.nanoseconds, -1);
        let h = Duration::parse("PT0.5H").unwrap();
        assert_eq!((h.hours, h.minutes, h.milliseconds), (0, 30, 0));
        assert!(Duration::parse("PT1.5H30M").is_err()); // fraction must be last
        assert!(Duration::parse("PT1.1234567890S").is_err()); // >9 digits
    }

    #[test]
    fn duration_parse_rejects_malformed() {
        assert!(Duration::parse("P").is_err());
        assert!(Duration::parse("PT").is_err());
        assert!(Duration::parse("P1S").is_err()); // S needs T
        assert!(Duration::parse("P1D2Y").is_err()); // out of order
        assert!(Duration::parse("PT1H2H").is_err()); // repeated designator
        assert!(Duration::parse("P1.5Y").is_err()); // date fraction
        assert!(Duration::parse("1Y").is_err());
    }

    #[test]
    fn duration_format_canonical() {
        assert_eq!(Duration::default().format(), "PT0S");
        let d = Duration::new(1, 0, 0, 2, 3, 0, 4, 500, 0, 0).unwrap();
        assert_eq!(d.format(), "P1Y2DT3H4.5S");
        assert_eq!(Duration::parse("-PT1H").unwrap().format(), "-PT1H");
        // Round trip.
        let p = Duration::parse("P1Y2DT3H4.5S").unwrap();
        assert_eq!(p.format(), "P1Y2DT3H4.5S");
    }

    // ---- ISO helpers ----

    #[test]
    fn leap_year_rules() {
        assert!(is_leap_year(2000));
        assert!(!is_leap_year(1900));
        assert!(is_leap_year(2024));
        assert!(!is_leap_year(2026));
        assert!(is_leap_year(-4)); // proleptic
        assert_eq!(days_in_month(2000, 2), 29);
        assert_eq!(days_in_month(1900, 2), 28);
    }

    #[test]
    fn epoch_days_round_trip_extended_years() {
        for &(y, m, d) in &[
            (1970, 1, 1),
            (2000, 2, 29),
            (275_760, 9, 13),
            (-271_821, 4, 19),
            (0, 1, 1),
            (-1, 12, 31),
        ] {
            let days = epoch_days_from_ymd(y, m, d);
            assert_eq!(ymd_from_epoch_days(days), (y, m as u8, d as u8), "case {y}-{m}-{d}");
        }
        assert_eq!(epoch_days_from_ymd(1970, 1, 1), 0);
        assert_eq!(epoch_days_from_ymd(1969, 12, 31), -1);
    }

    #[test]
    fn unit_ordering_and_names() {
        assert!(Unit::Year < Unit::Nanosecond);
        assert_eq!(Unit::Hour.larger(Unit::Day), Unit::Day);
        assert_eq!(Unit::from_name("weeks"), Some(Unit::Week));
        assert_eq!(Unit::from_name("Weeks"), None);
        assert_eq!(Unit::Minute.category(), UnitCategory::Time);
        assert_eq!(Unit::Day.category(), UnitCategory::Date);
    }

    #[test]
    fn precision_digits_bound() {
        assert!(Precision::digits(9).is_ok());
        assert!(Precision::digits(10).is_err());
    }

    #[test]
    fn rounding_mode_negation() {
        assert_eq!(RoundingMode::Ceil.negated(), RoundingMode::Floor);
        assert_eq!(RoundingMode::HalfCeil.negated(), RoundingMode::HalfFloor);
        assert_eq!(RoundingMode::HalfEven.negated(), RoundingMode::HalfEven);
    }
}
