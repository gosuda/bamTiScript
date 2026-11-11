//! Temporal core: typed errors, units, rounding, `Instant`, and `Duration`.
//!
//! Grounded in ECMA-262 + the Temporal proposal (tc39/proposal-temporal, ECMA-402
//! aligned option semantics). All arithmetic is exact checked `i128`; no floats
//! participate in any date/time computation. No ambient host access (no clock,
//! no environment, no time zone database).

use std::fmt;

use super::now_rounding::round_and_balance_duration;
use super::parse::{
    ParsedIsoDateTime, UtcOffsetRecord, parse_duration_string, parse_instant_string,
};

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
        Self {
            kind: TemporalErrorKind::Range,
            message: message.into(),
        }
    }
    pub fn type_error(message: impl Into<String>) -> Self {
        Self {
            kind: TemporalErrorKind::Type,
            message: message.into(),
        }
    }
    pub fn syntax(message: impl Into<String>) -> Self {
        Self {
            kind: TemporalErrorKind::Syntax,
            message: message.into(),
        }
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
        if self <= Unit::Day {
            UnitCategory::Date
        } else {
            UnitCategory::Time
        }
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
    /// Emit exactly the digits needed (every trailing zero trimmed).
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

/// Which neighbour `ApplyUnsignedRoundingMode` selects for a magnitude strictly
/// between two adjacent multiples.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UnsignedRounding {
    Zero,
    Infinity,
    HalfZero,
    HalfInfinity,
    HalfEven,
}

/// GetUnsignedRoundingMode.
fn unsigned_rounding(mode: RoundingMode, is_negative: bool) -> UnsignedRounding {
    match (mode, is_negative) {
        (RoundingMode::Ceil, false) | (RoundingMode::Floor, true) | (RoundingMode::Expand, _) => {
            UnsignedRounding::Infinity
        }
        (RoundingMode::Ceil, true) | (RoundingMode::Floor, false) | (RoundingMode::Trunc, _) => {
            UnsignedRounding::Zero
        }
        (RoundingMode::HalfCeil, false)
        | (RoundingMode::HalfFloor, true)
        | (RoundingMode::HalfExpand, _) => UnsignedRounding::HalfInfinity,
        (RoundingMode::HalfCeil, true)
        | (RoundingMode::HalfFloor, false)
        | (RoundingMode::HalfTrunc, _) => UnsignedRounding::HalfZero,
        (RoundingMode::HalfEven, _) => UnsignedRounding::HalfEven,
    }
}

/// ApplyUnsignedRoundingMode: whether a non-exact magnitude with this
/// `remainder` above the lower quotient rounds up to the next multiple.
fn rounds_up(
    remainder: u128,
    increment: u128,
    lower_quotient: u128,
    mode: UnsignedRounding,
) -> bool {
    match mode {
        UnsignedRounding::Zero => false,
        UnsignedRounding::Infinity => true,
        UnsignedRounding::HalfZero
        | UnsignedRounding::HalfInfinity
        | UnsignedRounding::HalfEven => {
            // `distance_up` is positive because the magnitude is not an exact
            // multiple, so this compares the two neighbours without doubling.
            let distance_up = increment - remainder;
            match remainder.cmp(&distance_up) {
                std::cmp::Ordering::Less => false,
                std::cmp::Ordering::Greater => true,
                std::cmp::Ordering::Equal => match mode {
                    UnsignedRounding::HalfInfinity => true,
                    UnsignedRounding::HalfEven => lower_quotient % 2 == 1,
                    _ => false,
                },
            }
        }
    }
}

/// Whether a value lying `remainder / divisor` of the way from one multiple to
/// the next rounds to the farther one. `lower_quotient` is the nearer multiple's
/// count and `is_negative` the sign of the value being rounded. The fraction
/// must be strictly between 0 and 1.
pub fn rounds_past_fraction(
    remainder: u128,
    divisor: u128,
    lower_quotient: u128,
    mode: RoundingMode,
    is_negative: bool,
) -> bool {
    rounds_up(
        remainder,
        divisor,
        lower_quotient,
        unsigned_rounding(mode, is_negative),
    )
}

/// RoundNumberToIncrement on exact integers: rounds `x` to a multiple of
/// `increment` (> 0) under `mode`. The direction is decided on the magnitude,
/// so negative ties follow the mode's sign-aware meaning. Errors only on i128
/// overflow at the extreme edge of the domain.
pub fn round_to_increment(x: i128, increment: i128, mode: RoundingMode) -> TemporalResult<i128> {
    debug_assert!(increment > 0);
    let is_negative = x < 0;
    let divisor = increment.unsigned_abs();
    let magnitude = x.unsigned_abs();
    let lower = magnitude / divisor;
    let remainder = magnitude % divisor;
    if remainder == 0 {
        return Ok(x);
    }
    let up = rounds_up(
        remainder,
        divisor,
        lower,
        unsigned_rounding(mode, is_negative),
    );
    let quotient = if up { lower + 1 } else { lower };
    let quotient = i128::try_from(quotient).map_err(|_| overflow_err("round"))?;
    let signed = if is_negative { -quotient } else { quotient };
    signed
        .checked_mul(increment)
        .ok_or_else(|| overflow_err("round"))
}

/// RoundNumberToIncrementAsIfPositive: rounds an epoch value, whose direction
/// is interpreted as if it were positive even before 1970. Euclidean division
/// keeps the lower neighbour the numerically smaller one.
pub fn round_to_increment_as_if_positive(
    x: i128,
    increment: i128,
    mode: RoundingMode,
) -> TemporalResult<i128> {
    debug_assert!(increment > 0);
    let lower = x.div_euclid(increment);
    let remainder = x.rem_euclid(increment);
    if remainder == 0 {
        return Ok(x);
    }
    let up = rounds_up(
        remainder.unsigned_abs(),
        increment.unsigned_abs(),
        lower.rem_euclid(2).unsigned_abs(),
        unsigned_rounding(mode, false),
    );
    let quotient = if up {
        lower.checked_add(1).ok_or_else(|| overflow_err("round"))?
    } else {
        lower
    };
    quotient
        .checked_mul(increment)
        .ok_or_else(|| overflow_err("round"))
}

/// ValidateTemporalRoundingIncrement: `increment` must be >= 1, and when the
/// unit is bounded, `increment` must be < max and divide max evenly.
pub fn validate_rounding_increment(
    unit: Unit,
    increment: i128,
    inclusive: bool,
) -> TemporalResult<()> {
    if increment < 1 {
        return Err(TemporalError::range(format!(
            "roundingIncrement must be >= 1, got {increment}"
        )));
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

    /// AddDurationToInstant (sign = +1). Date units are rejected: an instant
    /// has no calendar.
    pub fn add(&self, duration: &Duration) -> TemporalResult<Instant> {
        self.add_signed(duration, 1)
    }

    pub fn subtract(self, duration: &Duration) -> TemporalResult<Instant> {
        self.add_signed(duration, -1)
    }

    fn add_signed(self, duration: &Duration, sign: i128) -> TemporalResult<Instant> {
        if duration.years != 0 || duration.months != 0 || duration.weeks != 0 || duration.days != 0
        {
            return Err(TemporalError::range(
                "Instant arithmetic does not accept date units (years/months/weeks/days)",
            ));
        }
        let delta = duration.time_total_nanoseconds();
        let shifted = self
            .epoch_ns
            .checked_add(
                sign.checked_mul(delta)
                    .ok_or_else(|| overflow_err("Instant.add"))?,
            )
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
        if largest_unit.category() == UnitCategory::Date
            || smallest_unit.category() == UnitCategory::Date
        {
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
        let unit_ns = smallest_unit
            .ns_per()
            .ok_or_else(|| overflow_err("until"))?;
        let step = unit_ns
            .checked_mul(increment)
            .ok_or_else(|| overflow_err("until"))?;
        let rounded = round_to_increment(diff, step, mode)?;
        Duration::from_time_nanoseconds(rounded, largest_unit)
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
        let rounded = round_to_increment_as_if_positive(self.epoch_ns, step, mode)?;
        Instant::from_epoch_nanoseconds(rounded)
    }

    /// The exact time an already-parsed Instant string names. Calendar
    /// annotations are ignored here, critical or not: an Instant has no
    /// calendar for one to apply to.
    pub fn from_parsed(parsed: &ParsedIsoDateTime) -> TemporalResult<Instant> {
        let offset_ns = match parsed.offset {
            Some(UtcOffsetRecord::Numeric { nanoseconds, .. }) => nanoseconds,
            _ => 0,
        };
        let days = epoch_days_checked(parsed.year, parsed.month, parsed.day)?;
        let ns = (days as i128)
            .checked_mul(NS_PER_DAY)
            .and_then(|d| d.checked_add(parsed.time_ns))
            .and_then(|d| d.checked_sub(offset_ns))
            .ok_or_else(|| overflow_err("Instant.parse"))?;
        Instant::from_epoch_nanoseconds(ns)
    }

    /// ParseTemporalInstantString.
    pub fn parse(text: &str) -> TemporalResult<Instant> {
        Instant::from_parsed(&parse_instant_string(text)?)
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
const CALENDAR_FIELD_LIMIT: i128 = 1 << 32;
/// A time duration's magnitude must stay below 2^53 seconds, in nanoseconds.
pub const MAX_TIME_DURATION: i128 = (1_i128 << 53) * NS_PER_SECOND;

/// Ten-field Temporal.Duration. Fields hold exact integers that a Number can
/// represent: `Duration::new` rounds each through a double, as the proposal's
/// `𝔽(value)` does, so a field reads back as the same Number the object reports.
/// `i128` is required because a valid `nanoseconds` reaches about 9e24, past
/// the range of `i64`. A duration is valid only when every field shares one
/// sign (or is zero) and magnitudes are within the spec bounds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Duration {
    pub years: i128,
    pub months: i128,
    pub weeks: i128,
    pub days: i128,
    pub hours: i128,
    pub minutes: i128,
    pub seconds: i128,
    pub milliseconds: i128,
    pub microseconds: i128,
    pub nanoseconds: i128,
}

/// The integer a Number holds after `𝔽(value)`.
fn float64_representable(value: i128) -> i128 {
    value as f64 as i128
}

impl Duration {
    /// CreateTemporalDuration, fields largest to smallest.
    pub fn new(fields: [i128; 10]) -> TemporalResult<Duration> {
        let [
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
        ] = fields.map(float64_representable);
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

    /// CreateDateDurationRecord.
    pub fn from_date(
        years: i128,
        months: i128,
        weeks: i128,
        days: i128,
    ) -> TemporalResult<Duration> {
        Duration::new([years, months, weeks, days, 0, 0, 0, 0, 0, 0])
    }

    pub fn fields(&self) -> [i128; 10] {
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

    /// The date portion alone, with every time field zero.
    pub fn date_part(&self) -> Duration {
        Duration {
            years: self.years,
            months: self.months,
            weeks: self.weeks,
            days: self.days,
            ..Duration::default()
        }
    }

    /// IsValidDuration.
    fn validate(&self) -> TemporalResult<()> {
        let mut sign = 0_i128;
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
        for (name, value) in [
            ("years", self.years),
            ("months", self.months),
            ("weeks", self.weeks),
        ] {
            if value.abs() >= CALENDAR_FIELD_LIMIT {
                return Err(TemporalError::range(format!(
                    "|{name}| must be < 2^32, got {value}"
                )));
            }
        }
        // Every field carries one sign, so overflow in this sum can only mean
        // a magnitude far beyond the limit.
        let total_ns = self
            .checked_time_total_nanoseconds()
            .ok_or_else(|| TemporalError::range("Duration time total exceeds 2^53 seconds"))?;
        if total_ns.abs() >= MAX_TIME_DURATION {
            return Err(TemporalError::range(
                "Duration time total exceeds 2^53 seconds",
            ));
        }
        Ok(())
    }

    fn checked_time_total_nanoseconds(&self) -> Option<i128> {
        let terms = [
            (self.days, NS_PER_DAY),
            (self.hours, NS_PER_HOUR),
            (self.minutes, NS_PER_MINUTE),
            (self.seconds, NS_PER_SECOND),
            (self.milliseconds, NS_PER_MILLISECOND),
            (self.microseconds, NS_PER_MICROSECOND),
            (self.nanoseconds, 1),
        ];
        terms.iter().try_fold(0_i128, |total, &(value, unit)| {
            total.checked_add(value.checked_mul(unit)?)
        })
    }

    /// DurationSign.
    pub fn sign(&self) -> i128 {
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
        if self.sign() < 0 {
            self.negated()
        } else {
            *self
        }
    }

    /// DefaultTemporalLargestUnit: the largest unit with a non-zero field,
    /// `nanosecond` for a blank duration.
    pub fn default_largest_unit(&self) -> Unit {
        self.fields()
            .iter()
            .position(|&value| value != 0)
            .map_or(Unit::Nanosecond, |index| Unit::ALL[index])
    }

    /// Total nanoseconds of the time portion (hours and smaller). Exact: a
    /// validated duration keeps this below `MAX_TIME_DURATION`.
    pub fn time_total_nanoseconds(&self) -> i128 {
        self.hours * NS_PER_HOUR
            + self.minutes * NS_PER_MINUTE
            + self.seconds * NS_PER_SECOND
            + self.milliseconds * NS_PER_MILLISECOND
            + self.microseconds * NS_PER_MICROSECOND
            + self.nanoseconds
    }

    /// Time portion plus days taken as exactly 24 hours.
    pub fn total_nanoseconds_with_24_hour_days(&self) -> i128 {
        self.days * NS_PER_DAY + self.time_total_nanoseconds()
    }

    /// BalanceTimeDuration: build a duration from total nanoseconds, carrying
    /// upward into `largest_unit` (which must be Day or a time unit).
    pub fn from_time_nanoseconds(total_ns: i128, largest_unit: Unit) -> TemporalResult<Duration> {
        if largest_unit < Unit::Day {
            return Err(TemporalError::range(
                "balancing calendar units requires a relativeTo",
            ));
        }
        let sign: i128 = if total_ns < 0 { -1 } else { 1 };
        let mut rest = total_ns.abs();
        let mut fields = [0_i128; 10];
        let order = [
            (3, Unit::Day, NS_PER_DAY),
            (4, Unit::Hour, NS_PER_HOUR),
            (5, Unit::Minute, NS_PER_MINUTE),
            (6, Unit::Second, NS_PER_SECOND),
            (7, Unit::Millisecond, NS_PER_MILLISECOND),
            (8, Unit::Microsecond, NS_PER_MICROSECOND),
        ];
        for (slot, unit, ns) in order {
            if largest_unit <= unit {
                fields[slot] = rest / ns * sign;
                rest %= ns;
            }
        }
        fields[9] = rest * sign;
        Duration::new(fields)
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
                "rounding a duration with calendar units requires relativeTo",
            ));
        }
        if smallest_unit < Unit::Day || largest_unit < Unit::Day {
            return Err(TemporalError::range(
                "rounding to calendar units requires relativeTo",
            ));
        }
        if smallest_unit < largest_unit {
            return Err(TemporalError::range(
                "smallestUnit must not be larger than largestUnit",
            ));
        }
        round_and_balance_duration(
            self.total_nanoseconds_with_24_hour_days(),
            smallest_unit,
            largest_unit,
            increment,
            mode,
        )
    }

    /// Temporal.Duration.prototype.total without relativeTo (unit must be Day
    /// or smaller; day = 24h). Exact division result as (quotient, remainder
    /// numerator, unit nanoseconds); `total_as_f64` renders the spec's Number.
    pub fn total_exact(&self, unit: Unit) -> TemporalResult<(i128, i128, i128)> {
        if self.years != 0 || self.months != 0 || self.weeks != 0 {
            return Err(TemporalError::range(
                "totaling a duration with calendar units requires relativeTo",
            ));
        }
        let unit_ns = unit.ns_per().ok_or_else(|| {
            TemporalError::range("total unit must be day..nanosecond without relativeTo")
        })?;
        let total = self.total_nanoseconds_with_24_hour_days();
        Ok((
            total.div_euclid(unit_ns),
            total.rem_euclid(unit_ns),
            unit_ns,
        ))
    }

    /// The JS `total()` return value: the exact quotient rounded once to the
    /// nearest Number. Never feeds back into arithmetic.
    pub fn total_as_f64(&self, unit: Unit) -> TemporalResult<f64> {
        let (quotient, remainder, unit_ns) = self.total_exact(unit)?;
        Ok(exact_ratio_to_f64(quotient * unit_ns + remainder, unit_ns))
    }

    /// ParseTemporalDurationString (ISO 8601-2 duration).
    pub fn parse(text: &str) -> TemporalResult<Duration> {
        Duration::new(parse_duration_string(text)?)
    }

    /// TemporalDurationToString (auto precision).
    pub fn format(&self) -> String {
        self.format_with_precision(Precision::Auto)
    }

    /// TemporalDurationToString. Sub-second fields carry exactly into seconds,
    /// so a field past 1000 still serializes in canonical form.
    pub fn format_with_precision(&self, precision: Precision) -> String {
        let sign = self.sign();
        let a = self.abs();
        let mut out = String::new();
        if sign < 0 {
            out.push('-');
        }
        out.push('P');
        for (value, designator) in [
            (a.years, 'Y'),
            (a.months, 'M'),
            (a.weeks, 'W'),
            (a.days, 'D'),
        ] {
            if value != 0 {
                out.push_str(&format!("{value}{designator}"));
            }
        }
        let total_seconds_ns = a.seconds * NS_PER_SECOND
            + a.milliseconds * NS_PER_MILLISECOND
            + a.microseconds * NS_PER_MICROSECOND
            + a.nanoseconds;
        let seconds = total_seconds_ns / NS_PER_SECOND;
        let fraction = total_seconds_ns % NS_PER_SECOND;
        let date_empty = a.years == 0 && a.months == 0 && a.weeks == 0 && a.days == 0;
        let zero_clock = a.hours == 0 && a.minutes == 0;
        let show_seconds = seconds != 0
            || (date_empty && zero_clock)
            || !matches!(precision, Precision::Auto)
            || fraction != 0;
        if !zero_clock || show_seconds {
            out.push('T');
            if a.hours != 0 {
                out.push_str(&format!("{}H", a.hours));
            }
            if a.minutes != 0 {
                out.push_str(&format!("{}M", a.minutes));
            }
            if show_seconds {
                out.push_str(&seconds.to_string());
                out.push_str(&format_fractional_seconds(fraction, precision));
                out.push('S');
            }
        }
        out
    }
}

/// FormatFractionalSeconds: the leading `.` and digits, or nothing when none
/// are called for. `fraction_ns` is below one second.
pub fn format_fractional_seconds(fraction_ns: i128, precision: Precision) -> String {
    let digits = format!("{fraction_ns:09}");
    match precision {
        Precision::Digits(0) | Precision::Minute => String::new(),
        Precision::Digits(count) => format!(".{}", &digits[..usize::from(count)]),
        Precision::Auto if fraction_ns == 0 => String::new(),
        Precision::Auto => format!(".{}", digits.trim_end_matches('0')),
    }
}

/// The Number nearest `numerator / denominator` (`denominator` > 0), rounded
/// once from the exact quotient. Dividing two rounded doubles would round
/// twice, which is observable in `total()`.
pub fn exact_ratio_to_f64(numerator: i128, denominator: i128) -> f64 {
    debug_assert!(denominator > 0);
    if numerator == 0 {
        return 0.0;
    }
    let divisor = denominator.unsigned_abs();
    let dividend = numerator.unsigned_abs();
    let mut quotient = dividend / divisor;
    let mut remainder = dividend % divisor;
    let mut exponent = 0_i32;
    // Binary long division until the quotient holds more bits than a double
    // keeps, leaving `remainder` as the sticky information below them.
    while quotient < (1_u128 << 64) && remainder != 0 {
        let doubled = remainder << 1;
        let bit = doubled >= divisor;
        quotient = (quotient << 1) | u128::from(bit);
        remainder = if bit { doubled - divisor } else { doubled };
        exponent -= 1;
    }
    let excess = (128 - quotient.leading_zeros()).saturating_sub(64);
    let kept = quotient >> excess;
    let lost = quotient & ((1_u128 << excess) - 1);
    let sticky = u64::from(lost != 0 || remainder != 0);
    let magnitude = (kept as u64 | sticky) as f64 * 2_f64.powi(exponent + excess as i32);
    if numerator < 0 { -magnitude } else { magnitude }
}

impl fmt::Display for Duration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.format())
    }
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
                let digits = format!("{frac:09}");
                let digits = digits.trim_end_matches('0');
                out.push('.');
                out.push_str(digits);
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
        let one_ns = Duration::new([0, 0, 0, 0, 0, 0, 0, 0, 0, 1]).unwrap();
        assert_eq!(max.add(&one_ns).unwrap_err().kind, TemporalErrorKind::Range);
        assert_eq!(
            max.subtract(&one_ns).unwrap().epoch_nanoseconds(),
            INSTANT_NS_MAX - 1
        );
    }

    #[test]
    fn instant_rejects_date_units() {
        let i = Instant::from_epoch_nanoseconds(0).unwrap();
        let d = Duration::new([0, 0, 0, 1, 0, 0, 0, 0, 0, 0]).unwrap();
        assert_eq!(i.add(&d).unwrap_err().kind, TemporalErrorKind::Range);
    }

    #[test]
    fn instant_epoch_milliseconds_floors_negative() {
        let i = Instant::from_epoch_nanoseconds(-1).unwrap();
        assert_eq!(i.epoch_milliseconds(), -1);
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
        assert_eq!(
            round_to_increment(-3, 2, RoundingMode::HalfExpand).unwrap(),
            -4
        );
        assert_eq!(
            round_to_increment(-3, 2, RoundingMode::HalfTrunc).unwrap(),
            -2
        );
        assert_eq!(
            round_to_increment(-3, 2, RoundingMode::HalfCeil).unwrap(),
            -2
        );
        assert_eq!(
            round_to_increment(-3, 2, RoundingMode::HalfFloor).unwrap(),
            -4
        );
        assert_eq!(
            round_to_increment(-3, 2, RoundingMode::HalfEven).unwrap(),
            -4
        );
        assert_eq!(
            round_to_increment(-1, 2, RoundingMode::HalfEven).unwrap(),
            0
        );
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
        assert_eq!(
            i.format(Precision::Digits(6)),
            "1970-01-01T00:00:01.500000Z"
        );
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
        assert!(
            a.until(a, Unit::Day, Unit::Nanosecond, 1, RoundingMode::Trunc)
                .is_err()
        );
    }

    // ---- Duration validation ----

    #[test]
    fn duration_mixed_sign_rejected() {
        let err = Duration::new([1, 0, 0, -1, 0, 0, 0, 0, 0, 0]).unwrap_err();
        assert_eq!(err.kind, TemporalErrorKind::Range);
        let err = Duration::new([0, 0, 0, 0, 1, 0, 0, 0, 0, -1]).unwrap_err();
        assert_eq!(err.kind, TemporalErrorKind::Range);
        assert!(Duration::new([0, 0, 0, 0, -1, -30, 0, 0, 0, 0]).is_ok());
    }

    #[test]
    fn duration_calendar_field_limit() {
        let limit = 1_i128 << 32;
        assert!(Duration::new([limit, 0, 0, 0, 0, 0, 0, 0, 0, 0]).is_err());
        assert!(Duration::new([limit - 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]).is_ok());
    }

    #[test]
    fn duration_time_limit_2_pow_53_seconds() {
        let max_s = (1_i128 << 53) - 1;
        assert!(Duration::new([0, 0, 0, 0, 0, 0, max_s, 0, 0, 999_999_999]).is_ok());
        assert!(Duration::new([0, 0, 0, 0, 0, 0, max_s + 1, 0, 0, 0]).is_err());
        // Days participate in the time bound.
        let max_days = max_s / 86_400;
        assert!(Duration::new([0, 0, 0, max_days + 1, 0, 0, 0, 0, 0, 0]).is_err());
    }

    #[test]
    fn duration_sign_and_negate() {
        let d = Duration::new([0, 0, 0, 0, 0, 0, 0, 0, 0, -5]).unwrap();
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
        let d = Duration::new([0, 0, 0, 0, 0, 90, 0, 0, 0, 0]).unwrap();
        let r = d
            .round(Unit::Hour, Unit::Hour, 1, RoundingMode::HalfExpand)
            .unwrap();
        assert_eq!(r.hours, 2);
        let neg = d
            .negated()
            .round(Unit::Hour, Unit::Hour, 1, RoundingMode::HalfExpand)
            .unwrap();
        assert_eq!(neg.hours, -2);
        let cal = Duration::new([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]).unwrap();
        assert!(
            cal.round(Unit::Hour, Unit::Hour, 1, RoundingMode::Trunc)
                .is_err()
        );
        assert!(
            d.round(Unit::Month, Unit::Month, 1, RoundingMode::Trunc)
                .is_err()
        );
    }

    #[test]
    fn duration_total_exact_and_float() {
        let d = Duration::new([0, 0, 0, 0, 1, 30, 0, 0, 0, 0]).unwrap();
        let (q, r, unit) = d.total_exact(Unit::Hour).unwrap();
        assert_eq!((q, r, unit), (1, NS_PER_HOUR / 2, NS_PER_HOUR));
        assert_eq!(d.total_as_f64(Unit::Hour).unwrap(), 1.5);
        assert_eq!(d.total_as_f64(Unit::Minute).unwrap(), 90.0);
        let cal = Duration::new([0, 1, 0, 0, 0, 0, 0, 0, 0, 0]).unwrap();
        assert!(cal.total_exact(Unit::Day).is_err());
    }

    // ---- Duration parse / format ----

    #[test]
    fn duration_parse_basic_and_sign() {
        let d = Duration::parse("P1Y2M3W4DT5H6M7S").unwrap();
        assert_eq!(
            (
                d.years, d.months, d.weeks, d.days, d.hours, d.minutes, d.seconds
            ),
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
        let d = Duration::new([1, 0, 0, 2, 3, 0, 4, 500, 0, 0]).unwrap();
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
            assert_eq!(ymd_from_epoch_days(days), (y, m, d), "case {y}-{m}-{d}");
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
