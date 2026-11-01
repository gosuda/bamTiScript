//! Deterministic ECMA-402 `Intl.DateTimeFormat` core.
//!
//! Locale, calendar, numbering-system, pattern, and time-zone data are injected
//! through [`DateTimeFormatDataProvider`]. This module never reads the clock,
//! process environment, or an operating-system time-zone database.

use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;

use super::locale_negotiation::{
    HostLocaleHook, LocaleDataProvider, LocaleError, LocaleMatcher, default_locale, resolve_locale,
};

const MAX_TIME_MILLISECONDS: f64 = 8_640_000_000_000_000.0;
const NANOS_PER_MILLISECOND: i128 = 1_000_000;
const NANOS_PER_MINUTE: i128 = 60_000_000_000;
const NANOS_PER_DAY: i128 = 86_400_000_000_000;

/// The ECMAScript error class represented by a DateTimeFormat failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DateTimeFormatErrorKind {
    RangeError,
    TypeError,
    ProviderError,
}

/// A deterministic provider failure. Valid ECMA-402 input reaches this error
/// only when the injected data set is incomplete or internally inconsistent.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProviderError {
    MissingData { kind: &'static str, key: String },
    InvalidData { kind: &'static str, detail: String },
}

impl ProviderError {
    #[must_use]
    pub fn missing(kind: &'static str, key: impl Into<String>) -> Self {
        Self::MissingData {
            kind,
            key: key.into(),
        }
    }

    #[must_use]
    pub fn invalid(kind: &'static str, detail: impl Into<String>) -> Self {
        Self::InvalidData {
            kind,
            detail: detail.into(),
        }
    }
}

impl fmt::Display for ProviderError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingData { kind, key } => write!(f, "missing {kind} data for {key}"),
            Self::InvalidData { kind, detail } => write!(f, "invalid {kind} data: {detail}"),
        }
    }
}

impl Error for ProviderError {}

/// Initialization or formatting failure with a stable JavaScript error class.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DateTimeFormatError {
    Locale(LocaleError),
    Range { option: &'static str, value: String },
    Type { message: &'static str },
    Provider(ProviderError),
}

impl DateTimeFormatError {
    #[must_use]
    pub const fn kind(&self) -> DateTimeFormatErrorKind {
        match self {
            Self::Locale(_) | Self::Range { .. } => DateTimeFormatErrorKind::RangeError,
            Self::Type { .. } => DateTimeFormatErrorKind::TypeError,
            Self::Provider(_) => DateTimeFormatErrorKind::ProviderError,
        }
    }

    fn range(option: &'static str, value: impl Into<String>) -> Self {
        Self::Range {
            option,
            value: value.into(),
        }
    }
}

impl fmt::Display for DateTimeFormatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Locale(error) => error.fmt(f),
            Self::Range { option, value } => write!(f, "invalid {option}: {value}"),
            Self::Type { message } => f.write_str(message),
            Self::Provider(error) => error.fmt(f),
        }
    }
}

impl Error for DateTimeFormatError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Locale(error) => Some(error),
            Self::Provider(error) => Some(error),
            Self::Range { .. } | Self::Type { .. } => None,
        }
    }
}

impl From<LocaleError> for DateTimeFormatError {
    fn from(value: LocaleError) -> Self {
        Self::Locale(value)
    }
}

impl From<ProviderError> for DateTimeFormatError {
    fn from(value: ProviderError) -> Self {
        Self::Provider(value)
    }
}

/// ECMA-402 hour-cycle identifiers.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum HourCycle {
    H11,
    H12,
    H23,
    H24,
}

impl HourCycle {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::H11 => "h11",
            Self::H12 => "h12",
            Self::H23 => "h23",
            Self::H24 => "h24",
        }
    }

    pub fn parse(value: &str) -> Result<Self, DateTimeFormatError> {
        match value {
            "h11" => Ok(Self::H11),
            "h12" => Ok(Self::H12),
            "h23" => Ok(Self::H23),
            "h24" => Ok(Self::H24),
            _ => Err(DateTimeFormatError::range("hourCycle", value)),
        }
    }

    #[must_use]
    pub const fn is_twelve_hour(self) -> bool {
        matches!(self, Self::H11 | Self::H12)
    }
}

/// Provider preferences used when `hour12` suppresses the `hc` option.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HourCyclePreferences {
    pub default: HourCycle,
    pub twelve_hour: HourCycle,
    pub twenty_four_hour: HourCycle,
}

impl HourCyclePreferences {
    fn validate(self) -> Result<Self, ProviderError> {
        if !self.twelve_hour.is_twelve_hour() {
            return Err(ProviderError::invalid(
                "hour-cycle",
                "twelve_hour must be h11 or h12",
            ));
        }
        if self.twenty_four_hour.is_twelve_hour() {
            return Err(ProviderError::invalid(
                "hour-cycle",
                "twenty_four_hour must be h23 or h24",
            ));
        }
        Ok(self)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NumericStyle {
    Numeric,
    TwoDigit,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TextWidth {
    Narrow,
    Short,
    Long,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MonthStyle {
    Numeric,
    TwoDigit,
    Narrow,
    Short,
    Long,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TimeZoneNameStyle {
    Short,
    Long,
    ShortOffset,
    LongOffset,
    ShortGeneric,
    LongGeneric,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DateTimeStyle {
    Full,
    Long,
    Medium,
    Short,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FormatMatcher {
    Basic,
    BestFit,
}

/// Component options from ECMA-402 Table 16.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DateTimeComponents {
    pub weekday: Option<TextWidth>,
    pub era: Option<TextWidth>,
    pub year: Option<NumericStyle>,
    pub month: Option<MonthStyle>,
    pub day: Option<NumericStyle>,
    pub day_period: Option<TextWidth>,
    pub hour: Option<NumericStyle>,
    pub minute: Option<NumericStyle>,
    pub second: Option<NumericStyle>,
    pub fractional_second_digits: Option<u8>,
    pub time_zone_name: Option<TimeZoneNameStyle>,
}

impl DateTimeComponents {
    fn validate(&self) -> Result<(), DateTimeFormatError> {
        if let Some(digits) = self.fractional_second_digits
            && !(1..=3).contains(&digits)
        {
            return Err(DateTimeFormatError::range(
                "fractionalSecondDigits",
                digits.to_string(),
            ));
        }
        Ok(())
    }

    /// Whether every component is unset, which a style needs of them.
    fn is_empty(&self) -> bool {
        !self.has_any() && self.era.is_none() && self.time_zone_name.is_none()
    }

    /// Whether anything in the `any` required list is set. `era` and
    /// `timeZoneName` qualify a date or time but do not ask for one.
    fn has_any(&self) -> bool {
        self.has_date() || self.has_time()
    }

    /// Whether anything in the `date` required list is set.
    fn has_date(&self) -> bool {
        self.weekday.is_some() || self.year.is_some() || self.month.is_some() || self.day.is_some()
    }

    fn has_time(&self) -> bool {
        self.day_period.is_some()
            || self.hour.is_some()
            || self.minute.is_some()
            || self.second.is_some()
            || self.fractional_second_digits.is_some()
    }

    fn add_date_defaults(&mut self) {
        self.year = Some(NumericStyle::Numeric);
        self.month = Some(MonthStyle::Numeric);
        self.day = Some(NumericStyle::Numeric);
    }

    fn add_time_defaults(&mut self) {
        self.hour = Some(NumericStyle::Numeric);
        self.minute = Some(NumericStyle::Numeric);
        self.second = Some(NumericStyle::Numeric);
    }
}

/// Typed DateTimeFormat options after JavaScript property access and primitive
/// coercion. Calendar, numbering-system, and time-zone identifiers remain
/// strings because this module performs their provider-driven canonicalization.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DateTimeFormatOptions {
    pub locale_matcher: LocaleMatcher,
    pub calendar: Option<String>,
    pub numbering_system: Option<String>,
    pub time_zone: Option<String>,
    pub hour12: Option<bool>,
    pub hour_cycle: Option<HourCycle>,
    pub format_matcher: FormatMatcher,
    pub date_style: Option<DateTimeStyle>,
    pub time_style: Option<DateTimeStyle>,
    pub components: DateTimeComponents,
}

impl Default for DateTimeFormatOptions {
    fn default() -> Self {
        Self {
            locale_matcher: LocaleMatcher::BestFit,
            calendar: None,
            numbering_system: None,
            time_zone: None,
            hour12: None,
            hour_cycle: None,
            format_matcher: FormatMatcher::BestFit,
            date_style: None,
            time_style: None,
            components: DateTimeComponents::default(),
        }
    }
}

/// Calendar fields for a local wall-clock nanosecond value. `year` is the
/// calendar's display year; `related_year` and `year_name` support calendars
/// whose primary year representation is not a simple integer.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CalendarDateTime {
    pub era: Option<String>,
    pub year: i32,
    pub related_year: Option<i32>,
    pub year_name: Option<String>,
    pub month: u8,
    pub month_code: String,
    pub day: u8,
    /// ISO weekday in the range 1 (Monday) through 7 (Sunday).
    pub weekday: u8,
    pub hour: u8,
    pub minute: u8,
    pub second: u8,
    pub millisecond: u16,
}

impl CalendarDateTime {
    fn validate(&self) -> Result<(), ProviderError> {
        if !(1..=13).contains(&self.month) {
            return Err(ProviderError::invalid(
                "calendar",
                "month must be in 1..=13",
            ));
        }
        if self.month_code.is_empty() {
            return Err(ProviderError::invalid(
                "calendar",
                "month_code must not be empty",
            ));
        }
        if !(1..=31).contains(&self.day) {
            return Err(ProviderError::invalid("calendar", "day must be in 1..=31"));
        }
        if !(1..=7).contains(&self.weekday) {
            return Err(ProviderError::invalid(
                "calendar",
                "weekday must be in 1..=7",
            ));
        }
        if self.hour > 23 || self.minute > 59 || self.second > 59 || self.millisecond > 999 {
            return Err(ProviderError::invalid(
                "calendar",
                "time fields are outside their permitted ranges",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PatternField {
    Weekday(TextWidth),
    Era(TextWidth),
    Year(NumericStyle),
    RelatedYear(NumericStyle),
    YearName(TextWidth),
    Month(MonthStyle),
    Day(NumericStyle),
    DayPeriod(TextWidth),
    /// The AM or PM of a 12-hour clock.
    AmPm,
    Hour(NumericStyle),
    Minute(NumericStyle),
    Second(NumericStyle),
    FractionalSecond(u8),
    TimeZoneName(TimeZoneNameStyle),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PatternItem {
    Literal(String),
    Field(PatternField),
}

/// A provider-selected locale pattern and its resolved component metadata.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DateTimePattern {
    pub components: DateTimeComponents,
    pub items: Vec<PatternItem>,
}

impl DateTimePattern {
    fn validate(&self) -> Result<(), ProviderError> {
        if self.items.is_empty() {
            return Err(ProviderError::invalid(
                "pattern",
                "pattern must not be empty",
            ));
        }
        for item in &self.items {
            if let PatternItem::Field(PatternField::FractionalSecond(digits)) = item
                && !(1..=3).contains(digits)
            {
                return Err(ProviderError::invalid(
                    "pattern",
                    "fractional-second width must be in 1..=3",
                ));
            }
        }
        Ok(())
    }

    fn has_hour(&self) -> bool {
        self.items
            .iter()
            .any(|item| matches!(item, PatternItem::Field(PatternField::Hour(_))))
    }

    fn has_field(&self, difference: RangeDifference) -> bool {
        self.items.iter().any(|item| {
            matches!(
                (difference, item),
                (
                    RangeDifference::Era,
                    PatternItem::Field(PatternField::Era(_))
                ) | (
                    RangeDifference::Year,
                    PatternItem::Field(
                        PatternField::Year(_)
                            | PatternField::RelatedYear(_)
                            | PatternField::YearName(_)
                    )
                ) | (
                    RangeDifference::Month,
                    PatternItem::Field(PatternField::Month(_))
                ) | (
                    RangeDifference::Day,
                    PatternItem::Field(PatternField::Day(_))
                ) | (
                    RangeDifference::DayPeriod,
                    PatternItem::Field(PatternField::DayPeriod(_) | PatternField::AmPm)
                ) | (
                    RangeDifference::Hour,
                    PatternItem::Field(PatternField::Hour(_))
                ) | (
                    RangeDifference::Minute,
                    PatternItem::Field(PatternField::Minute(_))
                ) | (
                    RangeDifference::Second,
                    PatternItem::Field(PatternField::Second(_))
                ) | (
                    RangeDifference::FractionalSecond,
                    PatternItem::Field(PatternField::FractionalSecond(_))
                )
            )
        })
    }

    fn day_period_field(&self) -> Option<TextField> {
        self.items.iter().find_map(|item| match item {
            PatternItem::Field(PatternField::DayPeriod(width)) => {
                Some(TextField::DayPeriod(*width))
            }
            PatternItem::Field(PatternField::AmPm) => Some(TextField::AmPm),
            PatternItem::Literal(_) | PatternItem::Field(_) => None,
        })
    }

    fn fractional_second_digits(&self) -> Option<u8> {
        self.items.iter().find_map(|item| match item {
            PatternItem::Field(PatternField::FractionalSecond(digits)) => Some(*digits),
            PatternItem::Literal(_) | PatternItem::Field(_) => None,
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RangeSource {
    Shared,
    StartRange,
    EndRange,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RangePatternItem {
    pub source: RangeSource,
    pub item: PatternItem,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DateTimeRangePattern {
    pub items: Vec<RangePatternItem>,
}

impl DateTimeRangePattern {
    fn validate(&self) -> Result<(), ProviderError> {
        if self.items.is_empty() {
            return Err(ProviderError::invalid(
                "range pattern",
                "pattern must not be empty",
            ));
        }
        for item in &self.items {
            if let PatternItem::Field(PatternField::FractionalSecond(digits)) = &item.item
                && !(1..=3).contains(digits)
            {
                return Err(ProviderError::invalid(
                    "range pattern",
                    "fractional-second width must be in 1..=3",
                ));
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RangeDifference {
    Era,
    Year,
    Month,
    Day,
    DayPeriod,
    Hour,
    Minute,
    Second,
    FractionalSecond,
}

/// Immutable request for provider pattern selection.
pub struct PatternRequest<'a> {
    pub locale: &'a str,
    pub data_locale: &'a str,
    pub calendar: &'a str,
    pub numbering_system: &'a str,
    pub time_zone: &'a str,
    pub hour_cycle: HourCycle,
    pub format_matcher: FormatMatcher,
    pub date_style: Option<DateTimeStyle>,
    pub time_style: Option<DateTimeStyle>,
    pub components: &'a DateTimeComponents,
}

pub struct RangePatternRequest<'a> {
    pub locale: &'a str,
    pub data_locale: &'a str,
    pub calendar: &'a str,
    pub numbering_system: &'a str,
    pub time_zone: &'a str,
    pub hour_cycle: HourCycle,
    pub pattern: &'a DateTimePattern,
    /// `None` requests the provider's mandatory default interval pattern.
    pub largest_difference: Option<RangeDifference>,
}

pub struct IntegerFormatRequest<'a> {
    pub locale: &'a str,
    pub numbering_system: &'a str,
    pub value: i64,
    pub minimum_digits: u8,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TextField {
    Weekday(TextWidth),
    Era(TextWidth),
    YearName(TextWidth),
    Month(TextWidth),
    DayPeriod(TextWidth),
    AmPm,
    TimeZoneName(TimeZoneNameStyle),
}

pub struct TextFormatRequest<'a> {
    pub locale: &'a str,
    pub data_locale: &'a str,
    pub calendar: &'a str,
    pub numbering_system: &'a str,
    pub time_zone: &'a str,
    pub epoch_nanoseconds: i128,
    pub local: &'a CalendarDateTime,
    pub field: TextField,
}

/// All locale and implementation-dependent behavior needed by DateTimeFormat.
/// Named-zone offsets are queried by instant, not by local wall time; this makes
/// skipped and repeated wall-clock times at DST transitions unambiguous.
pub trait DateTimeFormatDataProvider: LocaleDataProvider {
    fn default_time_zone(&self) -> Result<String, ProviderError>;

    fn canonicalize_time_zone(&self, identifier: &str) -> Result<Option<String>, ProviderError>;

    fn hour_cycle_preferences(
        &self,
        data_locale: &str,
    ) -> Result<HourCyclePreferences, ProviderError>;

    fn select_pattern(
        &self,
        request: &PatternRequest<'_>,
    ) -> Result<DateTimePattern, ProviderError>;

    /// Returns a difference-specific range pattern or `None` when the caller
    /// must request the mandatory default pattern with `largest_difference=None`.
    fn select_range_pattern(
        &self,
        request: &RangePatternRequest<'_>,
    ) -> Result<Option<DateTimeRangePattern>, ProviderError>;

    fn named_time_zone_offset_nanoseconds(
        &self,
        identifier: &str,
        epoch_nanoseconds: i128,
    ) -> Result<i64, ProviderError>;

    /// Converts an offset-adjusted epoch nanosecond value into fields in the
    /// requested calendar. The input is a local time line, not a UTC instant.
    fn calendar_date_time(
        &self,
        calendar: &str,
        local_epoch_nanoseconds: i128,
    ) -> Result<CalendarDateTime, ProviderError>;

    fn format_integer(&self, request: &IntegerFormatRequest<'_>) -> Result<String, ProviderError>;

    fn format_text(&self, request: &TextFormatRequest<'_>) -> Result<String, ProviderError>;

    /// The components a `dateStyle` and `timeStyle` amount to, for a Temporal
    /// type that can show only some of them.
    fn style_components(
        &self,
        _date: Option<DateTimeStyle>,
        _time: Option<DateTimeStyle>,
    ) -> DateTimeComponents {
        DateTimeComponents::default()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum CanonicalTimeZone {
    Named(String),
    Offset {
        identifier: String,
        nanoseconds: i64,
    },
}

impl CanonicalTimeZone {
    fn identifier(&self) -> &str {
        match self {
            Self::Named(identifier) | Self::Offset { identifier, .. } => identifier,
        }
    }
}

/// Stable resolved-options snapshot for a DateTimeFormat instance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedDateTimeFormatOptions {
    pub locale: String,
    pub data_locale: String,
    pub calendar: String,
    pub numbering_system: String,
    pub time_zone: String,
    pub hour_cycle: Option<HourCycle>,
    pub hour12: Option<bool>,
    pub date_style: Option<DateTimeStyle>,
    pub time_style: Option<DateTimeStyle>,
    pub components: DateTimeComponents,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DateTimePartType {
    Literal,
    Weekday,
    Era,
    Year,
    RelatedYear,
    YearName,
    Month,
    Day,
    DayPeriod,
    Hour,
    Minute,
    Second,
    FractionalSecond,
    TimeZoneName,
}

impl DateTimePartType {
    #[must_use]
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::Literal => "literal",
            Self::Weekday => "weekday",
            Self::Era => "era",
            Self::Year => "year",
            Self::RelatedYear => "relatedYear",
            Self::YearName => "yearName",
            Self::Month => "month",
            Self::Day => "day",
            Self::DayPeriod => "dayPeriod",
            Self::Hour => "hour",
            Self::Minute => "minute",
            Self::Second => "second",
            Self::FractionalSecond => "fractionalSecond",
            Self::TimeZoneName => "timeZoneName",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DateTimePart {
    pub part_type: DateTimePartType,
    pub value: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DateTimeRangePart {
    pub part_type: DateTimePartType,
    pub value: String,
    pub source: RangeSource,
}

#[derive(Clone, Debug)]
pub struct DateTimeFormat {
    resolved: ResolvedDateTimeFormatOptions,
    time_zone: CanonicalTimeZone,
    pattern: DateTimePattern,
    /// The cycle in effect, whether or not the main pattern has an hour.
    hour_cycle: HourCycle,
    format_matcher: FormatMatcher,
    /// The components as requested, before defaults.
    requested: DateTimeComponents,
}

/// A Temporal type with its own formatter, per CreateDateTimeFormat.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TemporalFormatKind {
    PlainDate,
    PlainYearMonth,
    PlainMonthDay,
    PlainTime,
    PlainDateTime,
    Instant,
}

/// The components of `base` a Temporal type can show, or `None` when it can
/// show none of them.
fn filter_components(
    base: &DateTimeComponents,
    kind: TemporalFormatKind,
) -> Option<DateTimeComponents> {
    let date = |result: &mut DateTimeComponents, weekday: bool, day: bool, era: bool| {
        if weekday {
            result.weekday = base.weekday;
        }
        if era {
            result.era = base.era;
        }
        result.year = base.year;
        result.month = base.month;
        if day {
            result.day = base.day;
        }
    };
    let time = |result: &mut DateTimeComponents| {
        result.day_period = base.day_period;
        result.hour = base.hour;
        result.minute = base.minute;
        result.second = base.second;
        result.fractional_second_digits = base.fractional_second_digits;
    };
    let mut result = DateTimeComponents::default();
    match kind {
        TemporalFormatKind::PlainDate => date(&mut result, true, true, true),
        TemporalFormatKind::PlainYearMonth => date(&mut result, false, false, true),
        TemporalFormatKind::PlainMonthDay => {
            date(&mut result, false, true, false);
            result.year = None;
        }
        TemporalFormatKind::PlainTime => time(&mut result),
        TemporalFormatKind::PlainDateTime => {
            date(&mut result, true, true, true);
            time(&mut result);
        }
        TemporalFormatKind::Instant => result = base.clone(),
    }
    Some(result)
}

/// The fields a Temporal type falls back on when no requested one applies.
fn default_components(kind: TemporalFormatKind, components: &mut DateTimeComponents) {
    use TemporalFormatKind as Kind;
    if matches!(
        kind,
        Kind::PlainDate | Kind::PlainYearMonth | Kind::PlainDateTime | Kind::Instant
    ) {
        components.year = Some(NumericStyle::Numeric);
    }
    if kind != Kind::PlainTime {
        components.month = Some(MonthStyle::Numeric);
    }
    if matches!(
        kind,
        Kind::PlainDate | Kind::PlainMonthDay | Kind::PlainDateTime | Kind::Instant
    ) {
        components.day = Some(NumericStyle::Numeric);
    }
    if matches!(kind, Kind::PlainTime | Kind::PlainDateTime | Kind::Instant) {
        components.add_time_defaults();
    }
}

fn shows_required(components: &DateTimeComponents, kind: TemporalFormatKind) -> bool {
    use TemporalFormatKind as Kind;
    match kind {
        Kind::PlainDate => components.has_date(),
        Kind::PlainYearMonth => components.year.is_some() || components.month.is_some(),
        Kind::PlainMonthDay => components.month.is_some() || components.day.is_some(),
        Kind::PlainTime => components.has_time(),
        Kind::PlainDateTime | Kind::Instant => components.has_any(),
    }
}

/// Which components a formatter must end up with, or take the defaults.
#[derive(Clone, Copy)]
pub enum RequiredComponents {
    Date,
    Time,
    Any,
}

/// Which components the defaults add.
#[derive(Clone, Copy)]
pub enum DefaultComponents {
    Date,
    Time,
    All,
}

impl DateTimeFormat {
    /// Constructs an `Intl.DateTimeFormat` core using the constructor's
    /// `required=any`, `defaults=date` option mode.
    pub fn try_new(
        locales: &[String],
        options: &DateTimeFormatOptions,
        provider: &dyn DateTimeFormatDataProvider,
        host_locale: &dyn HostLocaleHook,
    ) -> Result<Self, DateTimeFormatError> {
        Self::try_new_with_mode(
            locales,
            options,
            RequiredComponents::Any,
            DefaultComponents::Date,
            provider,
            host_locale,
        )
    }

    /// Constructs a formatter for the given component requirements, as
    /// `Date.prototype.toLocaleDateString` and its peers do.
    pub fn try_new_with_mode(
        locales: &[String],
        options: &DateTimeFormatOptions,
        required: RequiredComponents,
        defaults: DefaultComponents,
        provider: &dyn DateTimeFormatDataProvider,
        host_locale: &dyn HostLocaleHook,
    ) -> Result<Self, DateTimeFormatError> {
        options.components.validate()?;
        let components = resolve_component_options(options, required, defaults)?;

        let requested = if locales.is_empty() {
            vec![default_locale(host_locale, provider)?]
        } else {
            locales.to_vec()
        };

        let mut locale_options = BTreeMap::new();
        if let Some(calendar) = &options.calendar {
            locale_options.insert(
                "ca".to_owned(),
                canonicalize_unicode_type("calendar", "ca", calendar, provider)?,
            );
        }
        match (options.hour12, options.hour_cycle) {
            // hour12 overrides any requested cycle, and the extension with it.
            (Some(_), _) => {
                locale_options.insert("hc".to_owned(), String::new());
            }
            (None, Some(hour_cycle)) => {
                locale_options.insert("hc".to_owned(), hour_cycle.as_str().to_owned());
            }
            (None, None) => {}
        }
        if let Some(numbering_system) = &options.numbering_system {
            locale_options.insert(
                "nu".to_owned(),
                canonicalize_unicode_type("numberingSystem", "nu", numbering_system, provider)?,
            );
        }

        let relevant_keys = vec!["ca".to_owned(), "hc".to_owned(), "nu".to_owned()];
        let locale = resolve_locale(
            &requested,
            &locale_options,
            &relevant_keys,
            options.locale_matcher,
            provider,
        )?;
        let calendar = resolved_keyword(&locale.values, "ca")?;
        let numbering_system = resolved_keyword(&locale.values, "nu")?;
        let preferences = provider
            .hour_cycle_preferences(&locale.data_locale)?
            .validate()?;
        let hour_cycle = match options.hour12 {
            Some(true) => preferences.twelve_hour,
            Some(false) => preferences.twenty_four_hour,
            None => locale
                .values
                .get("hc")
                .filter(|value| !value.is_empty())
                .map_or(Ok(preferences.default), |value| {
                    HourCycle::parse(value).map_err(|_| {
                        DateTimeFormatError::from(ProviderError::invalid(
                            "hour-cycle",
                            format!("unsupported resolved value {value}"),
                        ))
                    })
                })?,
        };

        let requested_time_zone = match &options.time_zone {
            Some(time_zone) => time_zone.clone(),
            None => provider.default_time_zone()?,
        };
        let time_zone = canonicalize_time_zone(&requested_time_zone, provider)?;

        let pattern = provider.select_pattern(&PatternRequest {
            locale: &locale.locale,
            data_locale: &locale.data_locale,
            calendar: &calendar,
            numbering_system: &numbering_system,
            time_zone: time_zone.identifier(),
            hour_cycle,
            format_matcher: options.format_matcher,
            date_style: options.date_style,
            time_style: options.time_style,
            components: &components,
        })?;
        pattern.validate()?;

        let pattern_has_hour = pattern.has_hour();
        let resolved_components = if options.date_style.is_some() || options.time_style.is_some() {
            DateTimeComponents::default()
        } else {
            pattern.components.clone()
        };
        let resolved_hour_cycle = pattern_has_hour.then_some(hour_cycle);
        let resolved = ResolvedDateTimeFormatOptions {
            locale: locale.locale,
            data_locale: locale.data_locale,
            calendar,
            numbering_system,
            time_zone: time_zone.identifier().to_owned(),
            hour_cycle: resolved_hour_cycle,
            hour12: resolved_hour_cycle.map(HourCycle::is_twelve_hour),
            date_style: options.date_style,
            time_style: options.time_style,
            components: resolved_components,
        };

        Ok(Self {
            resolved,
            time_zone,
            pattern,
            hour_cycle,
            format_matcher: options.format_matcher,
            requested: options.components.clone(),
        })
    }

    /// GetDateTimeFormat for a Temporal type: the pattern that type uses, or
    /// `None` when the options and the type do not overlap.
    fn temporal_pattern(
        &self,
        kind: TemporalFormatKind,
        provider: &dyn DateTimeFormatDataProvider,
    ) -> Result<Option<DateTimePattern>, DateTimeFormatError> {
        let (date_style, time_style) = (self.resolved.date_style, self.resolved.time_style);
        let components = if date_style.is_some() || time_style.is_some() {
            if matches!(kind, TemporalFormatKind::Instant) {
                return Ok(Some(self.pattern.clone()));
            }
            let needs_date = matches!(
                kind,
                TemporalFormatKind::PlainDate
                    | TemporalFormatKind::PlainYearMonth
                    | TemporalFormatKind::PlainMonthDay
            );
            if (needs_date && date_style.is_none())
                || (kind == TemporalFormatKind::PlainTime && time_style.is_none())
            {
                return Ok(None);
            }
            filter_components(&provider.style_components(date_style, time_style), kind)
        } else {
            let mut filtered = filter_components(&self.requested, kind);
            if let Some(components) = &mut filtered
                && !shows_required(components, kind)
            {
                if kind != TemporalFormatKind::Instant && self.requested.has_any() {
                    return Ok(None);
                }
                default_components(kind, components);
            }
            filtered
        };
        let Some(components) = components else {
            return Ok(None);
        };
        let pattern = provider.select_pattern(&PatternRequest {
            locale: &self.resolved.locale,
            data_locale: &self.resolved.data_locale,
            calendar: &self.resolved.calendar,
            numbering_system: &self.resolved.numbering_system,
            time_zone: self.time_zone.identifier(),
            hour_cycle: self.hour_cycle,
            format_matcher: self.format_matcher,
            date_style: None,
            time_style: None,
            components: &components,
        })?;
        pattern.validate()?;
        Ok(Some(pattern))
    }

    /// The zone a Temporal type renders in. Only an Instant has a place on
    /// the time line; the plain types show their fields as they are.
    fn temporal_zone(&self, kind: TemporalFormatKind) -> CanonicalTimeZone {
        if kind == TemporalFormatKind::Instant {
            self.time_zone.clone()
        } else {
            CanonicalTimeZone::Offset {
                identifier: String::from("+00:00"),
                nanoseconds: 0,
            }
        }
    }

    /// Partitions a Temporal value, given as epoch nanoseconds. `Ok(None)`
    /// means the type has no format here, which is a TypeError.
    pub fn format_temporal_to_parts(
        &self,
        kind: TemporalFormatKind,
        epoch_nanoseconds: i128,
        provider: &dyn DateTimeFormatDataProvider,
    ) -> Result<Option<Vec<DateTimePart>>, DateTimeFormatError> {
        let Some(pattern) = self.temporal_pattern(kind, provider)? else {
            return Ok(None);
        };
        let zone = self.temporal_zone(kind);
        let local = self.local_time_in(&zone, epoch_nanoseconds, provider)?;
        self.render_pattern(&pattern.items, epoch_nanoseconds, &local, provider)
            .map(Some)
    }

    /// Partitions a range of two values of one Temporal type.
    pub fn format_temporal_range_to_parts(
        &self,
        kind: TemporalFormatKind,
        start: i128,
        end: i128,
        provider: &dyn DateTimeFormatDataProvider,
    ) -> Result<Option<Vec<DateTimeRangePart>>, DateTimeFormatError> {
        let Some(pattern) = self.temporal_pattern(kind, provider)? else {
            return Ok(None);
        };
        let zone = self.temporal_zone(kind);
        self.range_parts(&pattern, &zone, start, end, provider)
            .map(Some)
    }

    #[must_use]
    pub const fn resolved_options(&self) -> &ResolvedDateTimeFormatOptions {
        &self.resolved
    }

    pub fn format(
        &self,
        epoch_milliseconds: f64,
        provider: &dyn DateTimeFormatDataProvider,
    ) -> Result<String, DateTimeFormatError> {
        let parts = self.format_to_parts(epoch_milliseconds, provider)?;
        Ok(concatenate_parts(&parts))
    }

    pub fn format_to_parts(
        &self,
        epoch_milliseconds: f64,
        provider: &dyn DateTimeFormatDataProvider,
    ) -> Result<Vec<DateTimePart>, DateTimeFormatError> {
        let instant = time_clip_to_nanoseconds(epoch_milliseconds)?;
        let local = self.to_local_time(instant, provider)?;
        self.render_pattern(&self.pattern.items, instant, &local, provider)
    }

    pub fn format_range(
        &self,
        start_epoch_milliseconds: f64,
        end_epoch_milliseconds: f64,
        provider: &dyn DateTimeFormatDataProvider,
    ) -> Result<String, DateTimeFormatError> {
        let parts =
            self.format_range_to_parts(start_epoch_milliseconds, end_epoch_milliseconds, provider)?;
        let mut result = String::new();
        for part in parts {
            result.push_str(&part.value);
        }
        Ok(result)
    }

    pub fn format_range_to_parts(
        &self,
        start_epoch_milliseconds: f64,
        end_epoch_milliseconds: f64,
        provider: &dyn DateTimeFormatDataProvider,
    ) -> Result<Vec<DateTimeRangePart>, DateTimeFormatError> {
        let start_instant = time_clip_to_nanoseconds(start_epoch_milliseconds)?;
        let end_instant = time_clip_to_nanoseconds(end_epoch_milliseconds)?;
        let zone = self.time_zone.clone();
        self.range_parts(&self.pattern, &zone, start_instant, end_instant, provider)
    }

    fn range_parts(
        &self,
        pattern: &DateTimePattern,
        zone: &CanonicalTimeZone,
        start_instant: i128,
        end_instant: i128,
        provider: &dyn DateTimeFormatDataProvider,
    ) -> Result<Vec<DateTimeRangePart>, DateTimeFormatError> {
        let start_local = self.local_time_in(zone, start_instant, provider)?;
        let end_local = self.local_time_in(zone, end_instant, provider)?;

        let difference = self.largest_range_difference(
            pattern,
            start_instant,
            &start_local,
            end_instant,
            &end_local,
            provider,
        )?;
        let Some(difference) = difference else {
            return Ok(self
                .render_pattern(&pattern.items, start_instant, &start_local, provider)?
                .into_iter()
                .map(|part| DateTimeRangePart {
                    part_type: part.part_type,
                    value: part.value,
                    source: RangeSource::Shared,
                })
                .collect());
        };

        let request = |largest_difference| RangePatternRequest {
            locale: &self.resolved.locale,
            data_locale: &self.resolved.data_locale,
            calendar: &self.resolved.calendar,
            numbering_system: &self.resolved.numbering_system,
            time_zone: self.time_zone.identifier(),
            hour_cycle: self.hour_cycle,
            pattern,
            largest_difference,
        };
        let range_pattern = match provider.select_range_pattern(&request(Some(difference)))? {
            Some(pattern) => pattern,
            None => provider
                .select_range_pattern(&request(None))?
                .ok_or_else(|| ProviderError::missing("range pattern", "default"))?,
        };
        range_pattern.validate()?;

        let mut result = Vec::with_capacity(range_pattern.items.len());
        for item in &range_pattern.items {
            let (instant, local) = match item.source {
                RangeSource::Shared | RangeSource::StartRange => (start_instant, &start_local),
                RangeSource::EndRange => (end_instant, &end_local),
            };
            let part = self.render_item(&item.item, instant, local, provider)?;
            result.push(DateTimeRangePart {
                part_type: part.part_type,
                value: part.value,
                source: item.source,
            });
        }
        Ok(result)
    }

    fn to_local_time(
        &self,
        epoch_nanoseconds: i128,
        provider: &dyn DateTimeFormatDataProvider,
    ) -> Result<CalendarDateTime, DateTimeFormatError> {
        self.local_time_in(&self.time_zone, epoch_nanoseconds, provider)
    }

    fn local_time_in(
        &self,
        zone: &CanonicalTimeZone,
        epoch_nanoseconds: i128,
        provider: &dyn DateTimeFormatDataProvider,
    ) -> Result<CalendarDateTime, DateTimeFormatError> {
        let offset = match zone {
            CanonicalTimeZone::Offset { nanoseconds, .. } => i128::from(*nanoseconds),
            CanonicalTimeZone::Named(identifier) => {
                let offset =
                    provider.named_time_zone_offset_nanoseconds(identifier, epoch_nanoseconds)?;
                let offset = i128::from(offset);
                if !(-NANOS_PER_DAY..NANOS_PER_DAY).contains(&offset) {
                    return Err(ProviderError::invalid(
                        "time-zone offset",
                        format!("{offset}ns is outside (-24h, +24h)"),
                    )
                    .into());
                }
                offset
            }
        };
        let local_nanoseconds = epoch_nanoseconds.checked_add(offset).ok_or_else(|| {
            ProviderError::invalid("time-zone offset", "local epoch nanoseconds overflowed")
        })?;
        let local = provider.calendar_date_time(&self.resolved.calendar, local_nanoseconds)?;
        local.validate()?;
        Ok(local)
    }

    fn render_pattern(
        &self,
        items: &[PatternItem],
        epoch_nanoseconds: i128,
        local: &CalendarDateTime,
        provider: &dyn DateTimeFormatDataProvider,
    ) -> Result<Vec<DateTimePart>, DateTimeFormatError> {
        let mut parts = Vec::with_capacity(items.len());
        for item in items {
            parts.push(self.render_item(item, epoch_nanoseconds, local, provider)?);
        }
        Ok(parts)
    }

    fn render_item(
        &self,
        item: &PatternItem,
        epoch_nanoseconds: i128,
        local: &CalendarDateTime,
        provider: &dyn DateTimeFormatDataProvider,
    ) -> Result<DateTimePart, DateTimeFormatError> {
        let (part_type, value) = match item {
            PatternItem::Literal(value) => (DateTimePartType::Literal, value.clone()),
            PatternItem::Field(field) => {
                self.render_field(field, epoch_nanoseconds, local, provider)?
            }
        };
        Ok(DateTimePart { part_type, value })
    }

    fn render_field(
        &self,
        field: &PatternField,
        epoch_nanoseconds: i128,
        local: &CalendarDateTime,
        provider: &dyn DateTimeFormatDataProvider,
    ) -> Result<(DateTimePartType, String), DateTimeFormatError> {
        let integer = |value, minimum_digits| {
            provider
                .format_integer(&IntegerFormatRequest {
                    locale: &self.resolved.locale,
                    numbering_system: &self.resolved.numbering_system,
                    value,
                    minimum_digits,
                })
                .map_err(DateTimeFormatError::from)
        };
        let text = |field| {
            provider
                .format_text(&TextFormatRequest {
                    locale: &self.resolved.locale,
                    data_locale: &self.resolved.data_locale,
                    calendar: &self.resolved.calendar,
                    numbering_system: &self.resolved.numbering_system,
                    time_zone: self.time_zone.identifier(),
                    epoch_nanoseconds,
                    local,
                    field,
                })
                .map_err(DateTimeFormatError::from)
        };
        let numeric_width = |style: NumericStyle| match style {
            NumericStyle::Numeric => 1,
            NumericStyle::TwoDigit => 2,
        };

        match *field {
            PatternField::Weekday(width) => {
                Ok((DateTimePartType::Weekday, text(TextField::Weekday(width))?))
            }
            PatternField::Era(width) => Ok((DateTimePartType::Era, text(TextField::Era(width))?)),
            PatternField::Year(style) => {
                let year = i64::from(local.year);
                let year = match style {
                    NumericStyle::Numeric => year,
                    NumericStyle::TwoDigit => year.rem_euclid(100),
                };
                Ok((DateTimePartType::Year, integer(year, numeric_width(style))?))
            }
            PatternField::RelatedYear(style) => {
                let year = local.related_year.ok_or_else(|| {
                    ProviderError::missing("calendar related year", &self.resolved.calendar)
                })?;
                Ok((
                    DateTimePartType::RelatedYear,
                    integer(i64::from(year), numeric_width(style))?,
                ))
            }
            PatternField::YearName(width) => Ok((
                DateTimePartType::YearName,
                text(TextField::YearName(width))?,
            )),
            PatternField::Month(style) => match style {
                MonthStyle::Numeric => {
                    Ok((DateTimePartType::Month, integer(i64::from(local.month), 1)?))
                }
                MonthStyle::TwoDigit => {
                    Ok((DateTimePartType::Month, integer(i64::from(local.month), 2)?))
                }
                MonthStyle::Narrow => Ok((
                    DateTimePartType::Month,
                    text(TextField::Month(TextWidth::Narrow))?,
                )),
                MonthStyle::Short => Ok((
                    DateTimePartType::Month,
                    text(TextField::Month(TextWidth::Short))?,
                )),
                MonthStyle::Long => Ok((
                    DateTimePartType::Month,
                    text(TextField::Month(TextWidth::Long))?,
                )),
            },
            PatternField::Day(style) => Ok((
                DateTimePartType::Day,
                integer(i64::from(local.day), numeric_width(style))?,
            )),
            PatternField::DayPeriod(width) => Ok((
                DateTimePartType::DayPeriod,
                text(TextField::DayPeriod(width))?,
            )),
            PatternField::AmPm => Ok((DateTimePartType::DayPeriod, text(TextField::AmPm)?)),
            PatternField::Hour(style) => {
                let hour = match self.hour_cycle {
                    HourCycle::H11 => local.hour % 12,
                    HourCycle::H12 => {
                        let hour = local.hour % 12;
                        if hour == 0 { 12 } else { hour }
                    }
                    HourCycle::H23 => local.hour,
                    HourCycle::H24 => {
                        if local.hour == 0 {
                            24
                        } else {
                            local.hour
                        }
                    }
                };
                Ok((
                    DateTimePartType::Hour,
                    integer(i64::from(hour), numeric_width(style))?,
                ))
            }
            PatternField::Minute(style) => Ok((
                DateTimePartType::Minute,
                integer(i64::from(local.minute), numeric_width(style))?,
            )),
            PatternField::Second(style) => Ok((
                DateTimePartType::Second,
                integer(i64::from(local.second), numeric_width(style))?,
            )),
            PatternField::FractionalSecond(digits) => {
                let divisor = match digits {
                    1 => 100,
                    2 => 10,
                    3 => 1,
                    _ => {
                        return Err(ProviderError::invalid(
                            "pattern",
                            "fractional-second width must be in 1..=3",
                        )
                        .into());
                    }
                };
                Ok((
                    DateTimePartType::FractionalSecond,
                    integer(i64::from(local.millisecond / divisor), digits)?,
                ))
            }
            PatternField::TimeZoneName(style) => Ok((
                DateTimePartType::TimeZoneName,
                text(TextField::TimeZoneName(style))?,
            )),
        }
    }

    fn largest_range_difference(
        &self,
        pattern: &DateTimePattern,
        start_instant: i128,
        start: &CalendarDateTime,
        end_instant: i128,
        end: &CalendarDateTime,
        provider: &dyn DateTimeFormatDataProvider,
    ) -> Result<Option<RangeDifference>, DateTimeFormatError> {
        let differences = [
            RangeDifference::Era,
            RangeDifference::Year,
            RangeDifference::Month,
            RangeDifference::Day,
            RangeDifference::DayPeriod,
            RangeDifference::Hour,
            RangeDifference::Minute,
            RangeDifference::Second,
            RangeDifference::FractionalSecond,
        ];
        for difference in differences {
            if !pattern.has_field(difference) {
                continue;
            }
            let equal = match difference {
                RangeDifference::Era => start.era == end.era,
                RangeDifference::Year => {
                    start.year == end.year
                        && start.related_year == end.related_year
                        && start.year_name == end.year_name
                }
                RangeDifference::Month => {
                    start.month == end.month && start.month_code == end.month_code
                }
                RangeDifference::Day => start.day == end.day,
                RangeDifference::DayPeriod => {
                    let period = pattern.day_period_field().ok_or_else(|| {
                        ProviderError::invalid("pattern", "missing day-period width")
                    })?;
                    let format = |instant, local| {
                        provider.format_text(&TextFormatRequest {
                            locale: &self.resolved.locale,
                            data_locale: &self.resolved.data_locale,
                            calendar: &self.resolved.calendar,
                            numbering_system: &self.resolved.numbering_system,
                            time_zone: self.time_zone.identifier(),
                            epoch_nanoseconds: instant,
                            local,
                            field: period,
                        })
                    };
                    format(start_instant, start)? == format(end_instant, end)?
                }
                RangeDifference::Hour => start.hour == end.hour,
                RangeDifference::Minute => start.minute == end.minute,
                RangeDifference::Second => start.second == end.second,
                RangeDifference::FractionalSecond => {
                    let digits = pattern.fractional_second_digits().ok_or_else(|| {
                        ProviderError::invalid("pattern", "missing fractional-second width")
                    })?;
                    let divisor = match digits {
                        1 => 100,
                        2 => 10,
                        3 => 1,
                        _ => unreachable!("validated pattern width"),
                    };
                    start.millisecond / divisor == end.millisecond / divisor
                }
            };
            if !equal {
                return Ok(Some(difference));
            }
        }
        Ok(None)
    }
}

fn resolve_component_options(
    options: &DateTimeFormatOptions,
    required: RequiredComponents,
    defaults: DefaultComponents,
) -> Result<DateTimeComponents, DateTimeFormatError> {
    if (options.date_style.is_some() || options.time_style.is_some())
        && !options.components.is_empty()
    {
        return Err(DateTimeFormatError::Type {
            message: "dateStyle/timeStyle may not be combined with explicit components",
        });
    }
    if matches!(required, RequiredComponents::Date) && options.time_style.is_some() {
        return Err(DateTimeFormatError::Type {
            message: "timeStyle is not permitted by Date.prototype.toLocaleDateString",
        });
    }
    if matches!(required, RequiredComponents::Time) && options.date_style.is_some() {
        return Err(DateTimeFormatError::Type {
            message: "dateStyle is not permitted by Date.prototype.toLocaleTimeString",
        });
    }

    let mut components = options.components.clone();
    if options.date_style.is_some() || options.time_style.is_some() {
        return Ok(components);
    }
    let need_defaults = match required {
        RequiredComponents::Date => !components.has_date(),
        RequiredComponents::Time => !components.has_time(),
        RequiredComponents::Any => !components.has_any(),
    };
    if need_defaults {
        if matches!(defaults, DefaultComponents::Date | DefaultComponents::All) {
            components.add_date_defaults();
        }
        if matches!(defaults, DefaultComponents::Time | DefaultComponents::All) {
            components.add_time_defaults();
        }
    }
    Ok(components)
}

fn canonicalize_unicode_type(
    option: &'static str,
    key: &str,
    value: &str,
    provider: &dyn DateTimeFormatDataProvider,
) -> Result<String, DateTimeFormatError> {
    if value.is_empty()
        || value.split('-').any(|part| {
            !(3..=8).contains(&part.len()) || !part.bytes().all(|byte| byte.is_ascii_alphanumeric())
        })
    {
        return Err(DateTimeFormatError::range(option, value));
    }
    let canonical = value.to_ascii_lowercase();
    Ok(provider
        .unicode_type_alias(key, &canonical)
        .unwrap_or(&canonical)
        .to_owned())
}

fn resolved_keyword(
    values: &BTreeMap<String, String>,
    key: &'static str,
) -> Result<String, DateTimeFormatError> {
    values
        .get(key)
        .filter(|value| !value.is_empty())
        .cloned()
        .ok_or_else(|| ProviderError::missing("locale keyword", key).into())
}

/// Whether a `timeZone` option names something the provider can use.
#[must_use]
pub fn is_valid_time_zone(value: &str, provider: &dyn DateTimeFormatDataProvider) -> bool {
    canonicalize_time_zone(value, provider).is_ok()
}

fn canonicalize_time_zone(
    value: &str,
    provider: &dyn DateTimeFormatDataProvider,
) -> Result<CanonicalTimeZone, DateTimeFormatError> {
    if let Some(offset_minutes) = parse_offset_minutes(value)? {
        let sign = if offset_minutes < 0 { '-' } else { '+' };
        let absolute = offset_minutes.unsigned_abs();
        let identifier = format!("{sign}{:02}:{:02}", absolute / 60, absolute % 60);
        return Ok(CanonicalTimeZone::Offset {
            identifier,
            nanoseconds: i64::from(offset_minutes) * NANOS_PER_MINUTE as i64,
        });
    }
    let canonical = provider
        .canonicalize_time_zone(value)?
        .ok_or_else(|| DateTimeFormatError::range("timeZone", value))?;
    if canonical.is_empty() || parse_offset_minutes(&canonical)?.is_some() {
        return Err(ProviderError::invalid(
            "time-zone canonicalization",
            format!("named zone {value} resolved to {canonical}"),
        )
        .into());
    }
    Ok(CanonicalTimeZone::Named(canonical))
}

/// A time zone offset: a sign, then `hh`, `hhmm`, or `hh:mm`.
fn parse_offset_minutes(value: &str) -> Result<Option<i32>, DateTimeFormatError> {
    let (sign, body) = if let Some(body) = value.strip_prefix('+') {
        (1, body)
    } else if let Some(body) = value.strip_prefix('-') {
        (-1, body)
    } else {
        return Ok(None);
    };
    let invalid = || DateTimeFormatError::range("timeZone", value);
    let (hours, minutes) = match body.len() {
        2 => (body, "00"),
        4 => body.split_at(2),
        5 if body.as_bytes()[2] == b':' => (&body[..2], &body[3..]),
        _ => return Err(invalid()),
    };
    if !hours
        .bytes()
        .chain(minutes.bytes())
        .all(|byte| byte.is_ascii_digit())
    {
        return Err(invalid());
    }
    let hours: i32 = hours.parse().map_err(|_| invalid())?;
    let minutes: i32 = minutes.parse().map_err(|_| invalid())?;
    if hours > 23 || minutes > 59 {
        return Err(invalid());
    }
    let total = hours * 60 + minutes;
    Ok(Some(if total == 0 { 0 } else { sign * total }))
}

fn time_clip_to_nanoseconds(value: f64) -> Result<i128, DateTimeFormatError> {
    if !value.is_finite() || value.abs() > MAX_TIME_MILLISECONDS {
        return Err(DateTimeFormatError::range("date", value.to_string()));
    }
    Ok((value.trunc() as i128) * NANOS_PER_MILLISECOND)
}

fn is_invalid_date_value(value: f64) -> bool {
    !value.is_finite() || value.abs() > MAX_TIME_MILLISECONDS
}

fn concatenate_parts(parts: &[DateTimePart]) -> String {
    let capacity = parts.iter().map(|part| part.value.len()).sum();
    let mut result = String::with_capacity(capacity);
    for part in parts {
        result.push_str(&part.value);
    }
    result
}

/// Pure contract for `Date.prototype.toLocaleString`. An invalid Date returns
/// the ECMAScript literal `"Invalid Date"` before locales/options are examined.
pub fn date_to_locale_string(
    epoch_milliseconds: f64,
    locales: &[String],
    options: &DateTimeFormatOptions,
    provider: &dyn DateTimeFormatDataProvider,
    host_locale: &dyn HostLocaleHook,
) -> Result<String, DateTimeFormatError> {
    date_adapter(
        epoch_milliseconds,
        locales,
        options,
        RequiredComponents::Any,
        DefaultComponents::All,
        provider,
        host_locale,
    )
}

/// Pure contract for `Date.prototype.toLocaleDateString`.
pub fn date_to_locale_date_string(
    epoch_milliseconds: f64,
    locales: &[String],
    options: &DateTimeFormatOptions,
    provider: &dyn DateTimeFormatDataProvider,
    host_locale: &dyn HostLocaleHook,
) -> Result<String, DateTimeFormatError> {
    date_adapter(
        epoch_milliseconds,
        locales,
        options,
        RequiredComponents::Date,
        DefaultComponents::Date,
        provider,
        host_locale,
    )
}

/// Pure contract for `Date.prototype.toLocaleTimeString`.
pub fn date_to_locale_time_string(
    epoch_milliseconds: f64,
    locales: &[String],
    options: &DateTimeFormatOptions,
    provider: &dyn DateTimeFormatDataProvider,
    host_locale: &dyn HostLocaleHook,
) -> Result<String, DateTimeFormatError> {
    date_adapter(
        epoch_milliseconds,
        locales,
        options,
        RequiredComponents::Time,
        DefaultComponents::Time,
        provider,
        host_locale,
    )
}

fn date_adapter(
    epoch_milliseconds: f64,
    locales: &[String],
    options: &DateTimeFormatOptions,
    required: RequiredComponents,
    defaults: DefaultComponents,
    provider: &dyn DateTimeFormatDataProvider,
    host_locale: &dyn HostLocaleHook,
) -> Result<String, DateTimeFormatError> {
    if is_invalid_date_value(epoch_milliseconds) {
        return Ok("Invalid Date".to_owned());
    }
    DateTimeFormat::try_new_with_mode(locales, options, required, defaults, provider, host_locale)?
        .format(epoch_milliseconds, provider)
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use super::*;
    use crate::intl::locale_negotiation::{LanguageId, LanguageTag};

    const SPRING_TRANSITION_SECONDS: i128 = 1_710_054_000;
    const FALL_TRANSITION_SECONDS: i128 = 1_730_613_600;

    struct FixtureHost;

    impl HostLocaleHook for FixtureHost {
        fn preferred_locales(&self) -> Vec<String> {
            vec!["en".to_owned()]
        }
    }

    struct FixtureProvider {
        locales: Vec<String>,
        calendars: Vec<String>,
        hour_cycles: Vec<String>,
        numbering_systems: Vec<String>,
        log: RefCell<Vec<String>>,
    }

    impl FixtureProvider {
        fn new() -> Self {
            Self {
                locales: vec!["en".to_owned(), "th".to_owned()],
                calendars: vec!["gregory".to_owned(), "buddhist".to_owned()],
                hour_cycles: vec![
                    "h23".to_owned(),
                    "h11".to_owned(),
                    "h12".to_owned(),
                    "h24".to_owned(),
                ],
                numbering_systems: vec!["latn".to_owned(), "arab".to_owned()],
                log: RefCell::new(Vec::new()),
            }
        }

        fn record(&self, entry: impl Into<String>) {
            self.log.borrow_mut().push(entry.into());
        }

        fn take_log(&self) -> Vec<String> {
            std::mem::take(&mut *self.log.borrow_mut())
        }
    }

    impl LocaleDataProvider for FixtureProvider {
        fn available_locales(&self) -> &[String] {
            self.record("locale:available");
            &self.locales
        }

        fn language_alias(&self, language: &str) -> Option<&str> {
            self.record(format!("locale:language-alias:{language}"));
            None
        }

        fn unicode_type_alias(&self, key: &str, value: &str) -> Option<&str> {
            self.record(format!("locale:type-alias:{key}:{value}"));
            match (key, value) {
                ("ca", "gregorian") => Some("gregory"),
                _ => None,
            }
        }

        fn key_values(&self, data_locale: &str, key: &str) -> &[String] {
            self.record(format!("locale:key-values:{data_locale}:{key}"));
            match key {
                "ca" => &self.calendars,
                "hc" => &self.hour_cycles,
                "nu" => &self.numbering_systems,
                _ => &[],
            }
        }

        fn add_likely_subtags(&self, locale: &LanguageId) -> Option<LanguageId> {
            self.record(format!(
                "locale:likely:{}.{}",
                locale.language,
                locale.region.as_deref().unwrap_or("")
            ));
            Some(LanguageId {
                language: locale.language.clone(),
                script: Some("Latn".to_owned()),
                region: Some(locale.region.clone().unwrap_or_else(|| "US".to_owned())),
                variants: locale.variants.clone(),
            })
        }

        fn fallback_locale(&self) -> Option<&str> {
            self.record("locale:fallback");
            Some("en")
        }
    }

    impl DateTimeFormatDataProvider for FixtureProvider {
        fn default_time_zone(&self) -> Result<String, ProviderError> {
            self.record("time-zone:default");
            Ok("UTC".to_owned())
        }

        fn canonicalize_time_zone(
            &self,
            identifier: &str,
        ) -> Result<Option<String>, ProviderError> {
            self.record(format!("time-zone:canonical:{identifier}"));
            Ok(match identifier.to_ascii_lowercase().as_str() {
                "utc" | "etc/utc" => Some("UTC".to_owned()),
                "america/test" => Some("America/Test".to_owned()),
                _ => None,
            })
        }

        fn hour_cycle_preferences(
            &self,
            data_locale: &str,
        ) -> Result<HourCyclePreferences, ProviderError> {
            self.record(format!("hour-cycle:{data_locale}"));
            Ok(HourCyclePreferences {
                default: HourCycle::H23,
                twelve_hour: HourCycle::H12,
                twenty_four_hour: HourCycle::H23,
            })
        }

        fn select_pattern(
            &self,
            request: &PatternRequest<'_>,
        ) -> Result<DateTimePattern, ProviderError> {
            self.record(format!(
                "pattern:{}:{}:{}",
                request.data_locale,
                request.calendar,
                request.hour_cycle.as_str()
            ));
            let components = request.components.clone();
            let mut items = Vec::new();
            let mut date_items = Vec::new();
            if let Some(width) = components.weekday {
                date_items.push(PatternItem::Field(PatternField::Weekday(width)));
                date_items.push(PatternItem::Literal(", ".to_owned()));
            }
            if let Some(width) = components.era {
                date_items.push(PatternItem::Field(PatternField::Era(width)));
                date_items.push(PatternItem::Literal(" ".to_owned()));
            }
            if let Some(style) = components.year {
                date_items.push(PatternItem::Field(PatternField::Year(style)));
            }
            if let Some(style) = components.month {
                if !date_items.is_empty()
                    && !matches!(date_items.last(), Some(PatternItem::Literal(_)))
                {
                    date_items.push(PatternItem::Literal("/".to_owned()));
                }
                date_items.push(PatternItem::Field(PatternField::Month(style)));
            }
            if let Some(style) = components.day {
                if !date_items.is_empty()
                    && !matches!(date_items.last(), Some(PatternItem::Literal(_)))
                {
                    date_items.push(PatternItem::Literal("/".to_owned()));
                }
                date_items.push(PatternItem::Field(PatternField::Day(style)));
            }

            let mut time_items = Vec::new();
            if let Some(style) = components.hour {
                time_items.push(PatternItem::Field(PatternField::Hour(style)));
            }
            if let Some(style) = components.minute {
                if !time_items.is_empty() {
                    time_items.push(PatternItem::Literal(":".to_owned()));
                }
                time_items.push(PatternItem::Field(PatternField::Minute(style)));
            }
            if let Some(style) = components.second {
                if !time_items.is_empty() {
                    time_items.push(PatternItem::Literal(":".to_owned()));
                }
                time_items.push(PatternItem::Field(PatternField::Second(style)));
            }
            if let Some(digits) = components.fractional_second_digits {
                time_items.push(PatternItem::Literal(".".to_owned()));
                time_items.push(PatternItem::Field(PatternField::FractionalSecond(digits)));
            }
            if let Some(width) = components.day_period {
                if !time_items.is_empty() {
                    time_items.push(PatternItem::Literal(" ".to_owned()));
                }
                time_items.push(PatternItem::Field(PatternField::DayPeriod(width)));
            }
            if let Some(style) = components.time_zone_name {
                if !time_items.is_empty() {
                    time_items.push(PatternItem::Literal(" ".to_owned()));
                }
                time_items.push(PatternItem::Field(PatternField::TimeZoneName(style)));
            }

            if request.date_style.is_some() && date_items.is_empty() {
                date_items.extend([
                    PatternItem::Field(PatternField::Year(NumericStyle::Numeric)),
                    PatternItem::Literal("/".to_owned()),
                    PatternItem::Field(PatternField::Month(MonthStyle::TwoDigit)),
                    PatternItem::Literal("/".to_owned()),
                    PatternItem::Field(PatternField::Day(NumericStyle::TwoDigit)),
                ]);
            }
            if request.time_style.is_some() && time_items.is_empty() {
                time_items.extend([
                    PatternItem::Field(PatternField::Hour(NumericStyle::TwoDigit)),
                    PatternItem::Literal(":".to_owned()),
                    PatternItem::Field(PatternField::Minute(NumericStyle::TwoDigit)),
                ]);
            }
            items.extend(date_items);
            if !items.is_empty() && !time_items.is_empty() {
                items.push(PatternItem::Literal(", ".to_owned()));
            }
            items.extend(time_items);
            Ok(DateTimePattern { components, items })
        }

        fn select_range_pattern(
            &self,
            request: &RangePatternRequest<'_>,
        ) -> Result<Option<DateTimeRangePattern>, ProviderError> {
            self.record(format!("range:{:?}", request.largest_difference));
            let Some(difference) = request.largest_difference else {
                return Ok(Some(simple_hour_range()));
            };
            Ok(
                matches!(difference, RangeDifference::Hour | RangeDifference::Minute)
                    .then(simple_hour_range),
            )
        }

        fn named_time_zone_offset_nanoseconds(
            &self,
            identifier: &str,
            epoch_nanoseconds: i128,
        ) -> Result<i64, ProviderError> {
            self.record(format!("offset:{identifier}:{epoch_nanoseconds}"));
            let seconds = epoch_nanoseconds.div_euclid(1_000_000_000);
            let hours = match identifier {
                "UTC" => 0,
                "America/Test" if seconds < SPRING_TRANSITION_SECONDS => -5,
                "America/Test" if seconds < FALL_TRANSITION_SECONDS => -4,
                "America/Test" => -5,
                _ => return Err(ProviderError::missing("time-zone offset", identifier)),
            };
            Ok(hours * 3_600_000_000_000)
        }

        fn calendar_date_time(
            &self,
            calendar: &str,
            local_epoch_nanoseconds: i128,
        ) -> Result<CalendarDateTime, ProviderError> {
            self.record(format!("calendar:{calendar}:{local_epoch_nanoseconds}"));
            let milliseconds = local_epoch_nanoseconds.div_euclid(1_000_000);
            let seconds = milliseconds.div_euclid(1_000);
            let millisecond = milliseconds.rem_euclid(1_000) as u16;
            let days = seconds.div_euclid(86_400);
            let second_of_day = seconds.rem_euclid(86_400);
            let (gregorian_year, month, day) = civil_from_days(days as i64);
            let weekday = (days + 3).rem_euclid(7) as u8 + 1;
            let (era, year) = match calendar {
                "gregory" => (
                    Some(if gregorian_year >= 1 { "ce" } else { "bce" }.to_owned()),
                    if gregorian_year >= 1 {
                        gregorian_year
                    } else {
                        1 - gregorian_year
                    },
                ),
                "buddhist" => (Some("be".to_owned()), gregorian_year + 543),
                _ => return Err(ProviderError::missing("calendar", calendar)),
            };
            Ok(CalendarDateTime {
                era,
                year,
                related_year: (calendar != "gregory").then_some(gregorian_year),
                year_name: None,
                month,
                month_code: format!("M{month:02}"),
                day,
                weekday,
                hour: (second_of_day / 3_600) as u8,
                minute: ((second_of_day % 3_600) / 60) as u8,
                second: (second_of_day % 60) as u8,
                millisecond,
            })
        }

        fn format_integer(
            &self,
            request: &IntegerFormatRequest<'_>,
        ) -> Result<String, ProviderError> {
            self.record(format!(
                "integer:{}:{}:{}",
                request.numbering_system, request.value, request.minimum_digits
            ));
            let negative = request.value < 0;
            let magnitude = request.value.unsigned_abs();
            let mut value = format!(
                "{magnitude:0width$}",
                width = usize::from(request.minimum_digits)
            );
            if request.numbering_system == "arab" {
                const DIGITS: [char; 10] = ['٠', '١', '٢', '٣', '٤', '٥', '٦', '٧', '٨', '٩'];
                value = value
                    .bytes()
                    .map(|byte| DIGITS[usize::from(byte - b'0')])
                    .collect();
            } else if request.numbering_system != "latn" {
                return Err(ProviderError::missing(
                    "numbering system",
                    request.numbering_system,
                ));
            }
            if negative {
                value.insert(0, '-');
            }
            Ok(value)
        }

        fn format_text(&self, request: &TextFormatRequest<'_>) -> Result<String, ProviderError> {
            self.record(format!(
                "text:{:?}:{}",
                request.field, request.epoch_nanoseconds
            ));
            let value = match request.field {
                TextField::Weekday(_) => ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
                    [usize::from(request.local.weekday - 1)]
                .to_owned(),
                TextField::Era(_) => match request.local.era.as_deref() {
                    Some("ce") => "AD".to_owned(),
                    Some("bce") => "BC".to_owned(),
                    Some("be") => "BE".to_owned(),
                    Some(era) => era.to_owned(),
                    None => return Err(ProviderError::missing("era", request.calendar)),
                },
                TextField::YearName(_) => request
                    .local
                    .year_name
                    .clone()
                    .ok_or_else(|| ProviderError::missing("year name", request.calendar))?,
                TextField::Month(_) => [
                    "January",
                    "February",
                    "March",
                    "April",
                    "May",
                    "June",
                    "July",
                    "August",
                    "September",
                    "October",
                    "November",
                    "December",
                    "Undecimber",
                ][usize::from(request.local.month - 1)]
                .to_owned(),
                TextField::DayPeriod(_) | TextField::AmPm => {
                    if request.local.hour < 12 { "AM" } else { "PM" }.to_owned()
                }
                TextField::TimeZoneName(_) => match request.time_zone {
                    "UTC" => "UTC".to_owned(),
                    "America/Test" => {
                        if request.epoch_nanoseconds.div_euclid(1_000_000_000)
                            < SPRING_TRANSITION_SECONDS
                            || request.epoch_nanoseconds.div_euclid(1_000_000_000)
                                >= FALL_TRANSITION_SECONDS
                        {
                            "EST".to_owned()
                        } else {
                            "EDT".to_owned()
                        }
                    }
                    zone => return Err(ProviderError::missing("time-zone name", zone)),
                },
            };
            Ok(value)
        }
    }

    fn simple_hour_range() -> DateTimeRangePattern {
        DateTimeRangePattern {
            items: vec![
                RangePatternItem {
                    source: RangeSource::StartRange,
                    item: PatternItem::Field(PatternField::Hour(NumericStyle::Numeric)),
                },
                RangePatternItem {
                    source: RangeSource::Shared,
                    item: PatternItem::Literal("–".to_owned()),
                },
                RangePatternItem {
                    source: RangeSource::EndRange,
                    item: PatternItem::Field(PatternField::Hour(NumericStyle::Numeric)),
                },
            ],
        }
    }

    fn civil_from_days(days_since_epoch: i64) -> (i32, u8, u8) {
        let z = days_since_epoch + 719_468;
        let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
        let day_of_era = z - era * 146_097;
        let year_of_era =
            (day_of_era - day_of_era / 1_460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
        let mut year = year_of_era + era * 400;
        let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
        let month_prime = (5 * day_of_year + 2) / 153;
        let day = day_of_year - (153 * month_prime + 2) / 5 + 1;
        let month = month_prime + if month_prime < 10 { 3 } else { -9 };
        year += i64::from(month <= 2);
        (year as i32, month as u8, day as u8)
    }

    fn options_with_time_zone(time_zone: &str) -> DateTimeFormatOptions {
        DateTimeFormatOptions {
            time_zone: Some(time_zone.to_owned()),
            ..DateTimeFormatOptions::default()
        }
    }

    fn utc_milliseconds(year: i32, month: u8, day: u8, hour: u8, minute: u8) -> f64 {
        let adjusted_year = i64::from(year) - i64::from(month <= 2);
        let era = if adjusted_year >= 0 {
            adjusted_year
        } else {
            adjusted_year - 399
        } / 400;
        let year_of_era = adjusted_year - era * 400;
        let adjusted_month = i64::from(month) + if month > 2 { -3 } else { 9 };
        let day_of_year = (153 * adjusted_month + 2) / 5 + i64::from(day) - 1;
        let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
        let days = era * 146_097 + day_of_era - 719_468;
        (days * 86_400_000 + i64::from(hour) * 3_600_000 + i64::from(minute) * 60_000) as f64
    }

    #[test]
    fn option_conflicts_and_adapter_restrictions_are_type_errors() {
        let provider = FixtureProvider::new();
        let host = FixtureHost;
        let options = DateTimeFormatOptions {
            date_style: Some(DateTimeStyle::Short),
            components: DateTimeComponents {
                year: Some(NumericStyle::Numeric),
                ..DateTimeComponents::default()
            },
            ..DateTimeFormatOptions::default()
        };
        assert_eq!(
            DateTimeFormat::try_new(&[], &options, &provider, &host)
                .expect_err("styles and components conflict")
                .kind(),
            DateTimeFormatErrorKind::TypeError
        );

        let date_style = DateTimeFormatOptions {
            date_style: Some(DateTimeStyle::Short),
            ..DateTimeFormatOptions::default()
        };
        assert_eq!(
            date_to_locale_time_string(0.0, &[], &date_style, &provider, &host)
                .expect_err("dateStyle is invalid for toLocaleTimeString")
                .kind(),
            DateTimeFormatErrorKind::TypeError
        );
        let time_style = DateTimeFormatOptions {
            time_style: Some(DateTimeStyle::Short),
            ..DateTimeFormatOptions::default()
        };
        assert_eq!(
            date_to_locale_date_string(0.0, &[], &time_style, &provider, &host)
                .expect_err("timeStyle is invalid for toLocaleDateString")
                .kind(),
            DateTimeFormatErrorKind::TypeError
        );
    }

    #[test]
    fn invalid_zones_and_identifiers_are_range_errors() {
        let provider = FixtureProvider::new();
        let host = FixtureHost;
        for time_zone in ["Mars/Phobos", "+24:00", "+01:00:01", "+1:00"] {
            let error =
                DateTimeFormat::try_new(&[], &options_with_time_zone(time_zone), &provider, &host)
                    .expect_err("invalid zone must fail");
            assert_eq!(
                error.kind(),
                DateTimeFormatErrorKind::RangeError,
                "{time_zone}"
            );
        }
        for (calendar, numbering_system) in [(Some("a"), None), (None, Some("ab"))] {
            let options = DateTimeFormatOptions {
                calendar: calendar.map(str::to_owned),
                numbering_system: numbering_system.map(str::to_owned),
                ..DateTimeFormatOptions::default()
            };
            assert_eq!(
                DateTimeFormat::try_new(&[], &options, &provider, &host)
                    .expect_err("malformed Unicode type must fail")
                    .kind(),
                DateTimeFormatErrorKind::RangeError
            );
        }

        let offset =
            DateTimeFormat::try_new(&[], &options_with_time_zone("-2359"), &provider, &host)
                .expect("valid offset zone");
        assert_eq!(offset.resolved_options().time_zone, "-23:59");
        let zero =
            DateTimeFormat::try_new(&[], &options_with_time_zone("-00:00"), &provider, &host)
                .expect("negative zero canonicalizes");
        assert_eq!(zero.resolved_options().time_zone, "+00:00");
    }

    #[test]
    fn era_calendar_and_numbering_data_are_provider_driven() {
        let provider = FixtureProvider::new();
        let host = FixtureHost;
        let options = DateTimeFormatOptions {
            calendar: Some("buddhist".to_owned()),
            numbering_system: Some("arab".to_owned()),
            time_zone: Some("UTC".to_owned()),
            components: DateTimeComponents {
                era: Some(TextWidth::Short),
                year: Some(NumericStyle::Numeric),
                month: Some(MonthStyle::TwoDigit),
                day: Some(NumericStyle::TwoDigit),
                ..DateTimeComponents::default()
            },
            ..DateTimeFormatOptions::default()
        };
        let format = DateTimeFormat::try_new(&["th".to_owned()], &options, &provider, &host)
            .expect("buddhist formatter");
        let result = format
            .format(utc_milliseconds(2024, 1, 2, 0, 0), &provider)
            .expect("format date");
        assert_eq!(result, "BE ٢٥٦٧/٠١/٠٢");
        assert_eq!(format.resolved_options().calendar, "buddhist");
        assert_eq!(format.resolved_options().numbering_system, "arab");
    }

    #[test]
    fn hour_cycle_edges_and_hour12_precedence_are_exact() {
        let provider = FixtureProvider::new();
        let host = FixtureHost;
        let midnight = utc_milliseconds(2024, 1, 2, 0, 0);
        let noon = utc_milliseconds(2024, 1, 2, 12, 0);
        for (cycle, midnight_expected, noon_expected) in [
            (HourCycle::H11, "0 AM", "0 PM"),
            (HourCycle::H12, "12 AM", "12 PM"),
            (HourCycle::H23, "0 AM", "12 PM"),
            (HourCycle::H24, "24 AM", "12 PM"),
        ] {
            let options = DateTimeFormatOptions {
                time_zone: Some("UTC".to_owned()),
                hour_cycle: Some(cycle),
                components: DateTimeComponents {
                    hour: Some(NumericStyle::Numeric),
                    day_period: Some(TextWidth::Short),
                    ..DateTimeComponents::default()
                },
                ..DateTimeFormatOptions::default()
            };
            let format =
                DateTimeFormat::try_new(&[], &options, &provider, &host).expect("hour formatter");
            assert_eq!(
                format.format(midnight, &provider).expect("midnight"),
                midnight_expected
            );
            assert_eq!(format.format(noon, &provider).expect("noon"), noon_expected);
        }

        let options = DateTimeFormatOptions {
            time_zone: Some("UTC".to_owned()),
            hour12: Some(true),
            hour_cycle: Some(HourCycle::H23),
            components: DateTimeComponents {
                hour: Some(NumericStyle::Numeric),
                ..DateTimeComponents::default()
            },
            ..DateTimeFormatOptions::default()
        };
        let format = DateTimeFormat::try_new(&[], &options, &provider, &host)
            .expect("hour12 overrides hourCycle");
        assert_eq!(format.resolved_options().hour_cycle, Some(HourCycle::H12));
        assert_eq!(format.format(midnight, &provider).expect("midnight"), "12");
    }

    #[test]
    fn negative_epoch_uses_time_clip_and_floor_safe_calendar_conversion() {
        let provider = FixtureProvider::new();
        let host = FixtureHost;
        let options = DateTimeFormatOptions {
            time_zone: Some("+00".to_owned()),
            components: DateTimeComponents {
                hour: Some(NumericStyle::TwoDigit),
                minute: Some(NumericStyle::TwoDigit),
                second: Some(NumericStyle::TwoDigit),
                fractional_second_digits: Some(3),
                ..DateTimeComponents::default()
            },
            ..DateTimeFormatOptions::default()
        };
        let format =
            DateTimeFormat::try_new(&[], &options, &provider, &host).expect("time formatter");
        assert_eq!(
            format.format(-1.9, &provider).expect("negative epoch"),
            "23:59:59.999"
        );
    }

    #[test]
    fn epoch_based_offset_contract_is_dst_gap_and_fold_safe() {
        let provider = FixtureProvider::new();
        let host = FixtureHost;
        let options = DateTimeFormatOptions {
            time_zone: Some("America/Test".to_owned()),
            components: DateTimeComponents {
                hour: Some(NumericStyle::TwoDigit),
                minute: Some(NumericStyle::TwoDigit),
                time_zone_name: Some(TimeZoneNameStyle::Short),
                ..DateTimeComponents::default()
            },
            ..DateTimeFormatOptions::default()
        };
        let format =
            DateTimeFormat::try_new(&[], &options, &provider, &host).expect("transition formatter");
        provider.take_log();

        let spring_before = (SPRING_TRANSITION_SECONDS - 1_800) as f64 * 1_000.0;
        let spring_after = (SPRING_TRANSITION_SECONDS + 1_800) as f64 * 1_000.0;
        assert_eq!(
            format.format(spring_before, &provider).expect("before gap"),
            "01:30 EST"
        );
        assert_eq!(
            format.format(spring_after, &provider).expect("after gap"),
            "03:30 EDT"
        );

        let fall_before = (FALL_TRANSITION_SECONDS - 1_800) as f64 * 1_000.0;
        let fall_after = (FALL_TRANSITION_SECONDS + 1_800) as f64 * 1_000.0;
        assert_eq!(
            format.format(fall_before, &provider).expect("first fold"),
            "01:30 EDT"
        );
        assert_eq!(
            format.format(fall_after, &provider).expect("second fold"),
            "01:30 EST"
        );

        let log = provider.take_log();
        for milliseconds in [spring_before, spring_after, fall_before, fall_after] {
            let nanos = time_clip_to_nanoseconds(milliseconds).expect("valid test instant");
            assert!(
                log.contains(&format!("offset:America/Test:{nanos}")),
                "offset must be queried by exact instant"
            );
        }
    }

    #[test]
    fn range_parts_have_stable_sources_and_identical_ranges_collapse() {
        let provider = FixtureProvider::new();
        let host = FixtureHost;
        let options = DateTimeFormatOptions {
            time_zone: Some("UTC".to_owned()),
            components: DateTimeComponents {
                hour: Some(NumericStyle::Numeric),
                ..DateTimeComponents::default()
            },
            ..DateTimeFormatOptions::default()
        };
        let format =
            DateTimeFormat::try_new(&[], &options, &provider, &host).expect("range formatter");
        let start = utc_milliseconds(2024, 1, 2, 1, 0);
        let end = utc_milliseconds(2024, 1, 2, 3, 0);
        let parts = format
            .format_range_to_parts(start, end, &provider)
            .expect("range parts");
        assert_eq!(
            parts,
            vec![
                DateTimeRangePart {
                    part_type: DateTimePartType::Hour,
                    value: "1".to_owned(),
                    source: RangeSource::StartRange,
                },
                DateTimeRangePart {
                    part_type: DateTimePartType::Literal,
                    value: "–".to_owned(),
                    source: RangeSource::Shared,
                },
                DateTimeRangePart {
                    part_type: DateTimePartType::Hour,
                    value: "3".to_owned(),
                    source: RangeSource::EndRange,
                },
            ]
        );
        assert_eq!(
            format.format_range(start, end, &provider).expect("range"),
            "1–3"
        );

        provider.take_log();
        let collapsed = format
            .format_range_to_parts(start, start, &provider)
            .expect("collapsed range");
        assert!(
            collapsed
                .iter()
                .all(|part| part.source == RangeSource::Shared)
        );
        assert!(
            !provider
                .take_log()
                .iter()
                .any(|entry| entry.starts_with("range:"))
        );
    }

    #[test]
    fn non_finite_format_is_range_error_but_invalid_date_adapter_is_literal() {
        let provider = FixtureProvider::new();
        let host = FixtureHost;
        let format = DateTimeFormat::try_new(&[], &options_with_time_zone("UTC"), &provider, &host)
            .expect("formatter");
        for value in [f64::NAN, f64::INFINITY, MAX_TIME_MILLISECONDS + 1.0] {
            assert_eq!(
                format
                    .format(value, &provider)
                    .expect_err("invalid time")
                    .kind(),
                DateTimeFormatErrorKind::RangeError
            );
        }

        provider.take_log();
        assert_eq!(
            date_to_locale_string(
                f64::NAN,
                &[],
                &DateTimeFormatOptions::default(),
                &provider,
                &host
            )
            .expect("invalid Date is a string"),
            "Invalid Date"
        );
        assert!(
            provider.take_log().is_empty(),
            "invalid Date must not access Intl data"
        );
    }

    #[test]
    fn provider_access_is_deterministic() {
        let provider = FixtureProvider::new();
        let host = FixtureHost;
        let options = DateTimeFormatOptions {
            calendar: Some("GREGORY".to_owned()),
            numbering_system: Some("latn".to_owned()),
            time_zone: Some("UTC".to_owned()),
            components: DateTimeComponents {
                year: Some(NumericStyle::Numeric),
                month: Some(MonthStyle::TwoDigit),
                day: Some(NumericStyle::TwoDigit),
                hour: Some(NumericStyle::TwoDigit),
                minute: Some(NumericStyle::TwoDigit),
                ..DateTimeComponents::default()
            },
            ..DateTimeFormatOptions::default()
        };
        let format = DateTimeFormat::try_new(
            &[LanguageTag::parse("en-US-u-hc-h24")
                .expect("locale")
                .to_string()],
            &options,
            &provider,
            &host,
        )
        .expect("formatter");
        assert_eq!(format.resolved_options().calendar, "gregory");
        provider.take_log();
        let instant = utc_milliseconds(2024, 2, 3, 4, 5);
        let first = format.format(instant, &provider).expect("first");
        let first_log = provider.take_log();
        let second = format.format(instant, &provider).expect("second");
        let second_log = provider.take_log();
        assert_eq!(first, second);
        assert_eq!(first_log, second_log);
        assert_eq!(
            first_log[0],
            format!("offset:UTC:{}", time_clip_to_nanoseconds(instant).unwrap())
        );
        assert!(first_log[1].starts_with("calendar:gregory:"));
    }
}
