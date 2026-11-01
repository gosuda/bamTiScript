//! Calendars other than ISO 8601 that have arithmetic rules.
//!
//! A date keeps its ISO fields; these calendars interpret them. Every calendar
//! here is a pair of conversions to and from a day count, plus the shape of its
//! years. `chinese`, `dangi`, and the observational Islamic calendars need
//! astronomical tables this runtime does not have, so they are not here.

use std::sync::Arc;

use super::instant_duration::{
    Duration, Overflow, TemporalError, TemporalResult, Unit, epoch_days_from_ymd,
    ymd_from_epoch_days,
};
use super::plain_types::{PlainDate, PlainMonthDay, PlainYearMonth, iso_day_of_week};
use super::relative::iso_date_until;
use super::zoned_date_time::{
    CalendarDateFields, CalendarId, CalendarProvider, IsoCalendarProvider,
};

/// Rata Die of the Unix epoch.
const RATA_DIE_OF_UNIX_EPOCH: i64 = 719_163;

const COPTIC_EPOCH: i64 = 103_605;
const ETHIOPIC_EPOCH: i64 = 2796;
const ETHIOAA_YEAR_OFFSET: i64 = 5500;
const ISLAMIC_CIVIL_EPOCH: i64 = 227_015;
const ISLAMIC_TBLA_EPOCH: i64 = 227_014;
const HEBREW_EPOCH: i64 = -1_373_427;
const PERSIAN_EPOCH: i64 = 226_896;
const INDIAN_YEAR_OFFSET: i64 = 78;

/// Calendars reach this far at most, in any year numbering. Anything past it is
/// out of range for every date, which keeps the arithmetic in `i64`.
const YEAR_LIMIT: i64 = 1_000_000;

/// How far back a month-day's reference search looks. Every combination of
/// leap rules the calendars have recurs within this many years.
const REFERENCE_SEARCH_YEARS: i64 = 60;

/// Identifiers `CanonicalizeCalendar` accepts, with their canonical form.
const CALENDAR_ALIASES: [(&str, &str); 2] = [
    ("ethiopic-amete-alem", "ethioaa"),
    ("islamicc", "islamic-civil"),
];

/// The canonical identifier of a supported calendar, ASCII case-insensitively.
#[must_use]
pub fn canonical_calendar(identifier: &str) -> Option<&'static str> {
    let lower = identifier.to_ascii_lowercase();
    if lower == "iso8601" {
        return Some("iso8601");
    }
    if let Some((_, canonical)) = CALENDAR_ALIASES.iter().find(|(alias, _)| *alias == lower) {
        return Some(canonical);
    }
    Calendar::ALL
        .iter()
        .map(|calendar| calendar.id())
        .find(|id| *id == lower)
}

/// The non-ISO calendars.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Calendar {
    Buddhist,
    Coptic,
    Ethioaa,
    Ethiopic,
    Gregory,
    Hebrew,
    Indian,
    IslamicCivil,
    IslamicTbla,
    Persian,
    Roc,
}

/// A month code: its number and whether it is a leap month.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MonthCode {
    pub number: u8,
    pub leap: bool,
}

impl MonthCode {
    /// Reads a well-formed `Mnn` or `MnnL`.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        let leap = text.ends_with('L');
        let digits = text.strip_prefix('M')?;
        let digits = digits.strip_suffix('L').unwrap_or(digits);
        (digits.len() == 2)
            .then(|| digits.parse().ok())
            .flatten()
            .map(|number| Self { number, leap })
    }

    /// The code's text.
    #[must_use]
    pub fn render(self) -> String {
        format!("M{:02}{}", self.number, if self.leap { "L" } else { "" })
    }
}

/// A calendar date: arithmetic year, ordinal month, day.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CalendarDate {
    pub year: i64,
    pub month: u8,
    pub day: u8,
}

const fn gregorian_leap(year: i64) -> bool {
    year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)
}

fn iso_days_in_month(year: i64, month: u8) -> u8 {
    match month {
        2 if gregorian_leap(year) => 29,
        2 => 28,
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    }
}

fn iso_days(year: i64, month: u8, day: u8) -> i64 {
    // Only the year's position in the 400-year cycle matters past `i32`.
    let cycles = year.div_euclid(400);
    let within = year.rem_euclid(400) as i32;
    cycles * 146_097 + epoch_days_from_ymd(within, month, day)
}

fn iso_from_days(days: i64) -> (i64, u8, u8) {
    let cycles = days.div_euclid(146_097);
    let (year, month, day) = ymd_from_epoch_days(days.rem_euclid(146_097));
    (i64::from(year) + cycles * 400, month, day)
}

/// The ordinal month and day of a day of the year, counted from zero.
fn month_of_year(mut remaining: i64, days_in_month: impl Fn(u8) -> u8) -> (u8, u8) {
    let mut month = 1;
    loop {
        let length = i64::from(days_in_month(month));
        if remaining < length {
            return (month, remaining as u8 + 1);
        }
        remaining -= length;
        month += 1;
    }
}

fn coptic_like_days(epoch: i64, year: i64, month: u8, day: u8) -> i64 {
    epoch - 1 + 365 * (year - 1) + year.div_euclid(4) + 30 * (i64::from(month) - 1) + i64::from(day)
        - RATA_DIE_OF_UNIX_EPOCH
}

fn coptic_like_date(epoch: i64, days: i64) -> (i64, u8, u8) {
    let rata_die = days + RATA_DIE_OF_UNIX_EPOCH;
    let year = (4 * (rata_die - epoch) + 1463).div_euclid(1461);
    let start = coptic_like_days(epoch, year, 1, 1);
    let month = (days - start).div_euclid(30) as u8 + 1;
    let day = days - coptic_like_days(epoch, year, month, 1) + 1;
    (year, month, day as u8)
}

fn islamic_days(epoch: i64, year: i64, month: u8, day: u8) -> i64 {
    let month_index = i64::from(month);
    epoch - 1
        + (year - 1) * 354
        + (3 + 11 * year).div_euclid(30)
        + 29 * (month_index - 1)
        + month_index.div_euclid(2)
        + i64::from(day)
        - RATA_DIE_OF_UNIX_EPOCH
}

fn islamic_date(epoch: i64, days: i64) -> (i64, u8, u8) {
    let rata_die = days + RATA_DIE_OF_UNIX_EPOCH;
    let year = (30 * (rata_die - epoch) + 10_646).div_euclid(10_631);
    let prior = days - islamic_days(epoch, year, 1, 1);
    let month = ((11 * prior + 330).div_euclid(325) as u8).min(12);
    let day = days - islamic_days(epoch, year, month, 1) + 1;
    (year, month, day as u8)
}

const fn islamic_leap(year: i64) -> bool {
    (14 + 11 * year).rem_euclid(30) < 11
}

/// Days before Tishri 1 of `year`, counting from the Hebrew epoch.
fn hebrew_elapsed_days(year: i64) -> i64 {
    let months = (235 * year - 234).div_euclid(19);
    let parts = 12_084 + 13_753 * months;
    let days = 29 * months + parts.div_euclid(25_920);
    if (3 * (days + 1)).rem_euclid(7) < 3 {
        days + 1
    } else {
        days
    }
}

fn hebrew_new_year(year: i64) -> i64 {
    let (previous, current, next) = (
        hebrew_elapsed_days(year - 1),
        hebrew_elapsed_days(year),
        hebrew_elapsed_days(year + 1),
    );
    let delay = if next - current == 356 {
        2
    } else if current - previous == 382 {
        1
    } else {
        0
    };
    HEBREW_EPOCH + current + delay
}

const fn hebrew_leap(year: i64) -> bool {
    (7 * year + 1).rem_euclid(19) < 7
}

fn hebrew_year_length(year: i64) -> i64 {
    hebrew_new_year(year + 1) - hebrew_new_year(year)
}

fn hebrew_days_in_month(year: i64, month: u8) -> u8 {
    let length = hebrew_year_length(year);
    let leap = hebrew_leap(year);
    let month = if !leap && month >= 6 {
        month + 1
    } else {
        month
    };
    match month {
        1 | 5 | 6 | 8 | 10 | 12 => 30,
        2 if length.rem_euclid(10) == 5 => 30,
        3 if length.rem_euclid(10) != 3 => 30,
        _ => 29,
    }
}

fn hebrew_days(year: i64, month: u8, day: u8) -> i64 {
    let before: i64 = (1..month)
        .map(|earlier| i64::from(hebrew_days_in_month(year, earlier)))
        .sum();
    hebrew_new_year(year) + before + i64::from(day) - 1 - RATA_DIE_OF_UNIX_EPOCH
}

fn hebrew_date(days: i64) -> (i64, u8, u8) {
    let rata_die = days + RATA_DIE_OF_UNIX_EPOCH;
    let mut year = ((rata_die - HEBREW_EPOCH) * 10_000).div_euclid(3_652_468) + 1;
    while hebrew_new_year(year) > rata_die {
        year -= 1;
    }
    while hebrew_new_year(year + 1) <= rata_die {
        year += 1;
    }
    let (month, day) = month_of_year(rata_die - hebrew_new_year(year), |month| {
        hebrew_days_in_month(year, month)
    });
    (year, month, day)
}

const fn persian_leap(year: i64) -> bool {
    (25 * year + 11).rem_euclid(33) < 8
}

fn persian_days_in_month(year: i64, month: u8) -> u8 {
    match month {
        1..=6 => 31,
        7..=11 => 30,
        _ if persian_leap(year) => 30,
        _ => 29,
    }
}

fn persian_new_year(year: i64) -> i64 {
    PERSIAN_EPOCH - 1 + 365 * (year - 1) + (8 * year + 21).div_euclid(33) - RATA_DIE_OF_UNIX_EPOCH
}

fn persian_days(year: i64, month: u8, day: u8) -> i64 {
    let month_index = i64::from(month) - 1;
    let before = if month <= 7 {
        31 * month_index
    } else {
        30 * month_index + 6
    };
    persian_new_year(year) + before + i64::from(day) - 1
}

fn persian_date(days: i64) -> (i64, u8, u8) {
    let mut year = ((days - persian_new_year(1)) * 10_000).div_euclid(3_652_425) + 1;
    while persian_new_year(year) > days {
        year -= 1;
    }
    while persian_new_year(year + 1) <= days {
        year += 1;
    }
    let (month, day) = month_of_year(days - persian_new_year(year), |month| {
        persian_days_in_month(year, month)
    });
    (year, month, day)
}

fn indian_days_in_month(year: i64, month: u8) -> u8 {
    match month {
        1 if gregorian_leap(year + INDIAN_YEAR_OFFSET) => 31,
        1 | 7..=12 => 30,
        _ => 31,
    }
}

fn indian_new_year(year: i64) -> i64 {
    let gregorian = year + INDIAN_YEAR_OFFSET;
    iso_days(
        gregorian,
        3,
        if gregorian_leap(gregorian) { 21 } else { 22 },
    )
}

fn indian_days(year: i64, month: u8, day: u8) -> i64 {
    let before: i64 = (1..month)
        .map(|earlier| i64::from(indian_days_in_month(year, earlier)))
        .sum();
    indian_new_year(year) + before + i64::from(day) - 1
}

fn indian_date(days: i64) -> (i64, u8, u8) {
    let (iso_year, _, _) = iso_from_days(days);
    let mut year = iso_year - INDIAN_YEAR_OFFSET;
    if days < indian_new_year(year) {
        year -= 1;
    }
    let (month, day) = month_of_year(days - indian_new_year(year), |month| {
        indian_days_in_month(year, month)
    });
    (year, month, day)
}

impl Calendar {
    const ALL: [Self; 11] = [
        Self::Buddhist,
        Self::Coptic,
        Self::Ethioaa,
        Self::Ethiopic,
        Self::Gregory,
        Self::Hebrew,
        Self::Indian,
        Self::IslamicCivil,
        Self::IslamicTbla,
        Self::Persian,
        Self::Roc,
    ];

    /// The calendar behind a canonical identifier; ISO has none.
    #[must_use]
    pub fn from_id(calendar: &CalendarId) -> Option<Self> {
        Self::from_name(calendar.as_str())
    }

    /// The calendar of a canonical name.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL
            .iter()
            .copied()
            .find(|candidate| candidate.id() == name)
    }

    #[must_use]
    pub const fn id(self) -> &'static str {
        match self {
            Self::Buddhist => "buddhist",
            Self::Coptic => "coptic",
            Self::Ethioaa => "ethioaa",
            Self::Ethiopic => "ethiopic",
            Self::Gregory => "gregory",
            Self::Hebrew => "hebrew",
            Self::Indian => "indian",
            Self::IslamicCivil => "islamic-civil",
            Self::IslamicTbla => "islamic-tbla",
            Self::Persian => "persian",
            Self::Roc => "roc",
        }
    }

    /// The offset from ISO years, for the calendars laid over ISO dates.
    const fn iso_year_offset(self) -> Option<i64> {
        match self {
            Self::Gregory => Some(0),
            Self::Buddhist => Some(543),
            Self::Roc => Some(-1911),
            _ => None,
        }
    }

    const fn islamic_epoch(self) -> i64 {
        if matches!(self, Self::IslamicCivil) {
            ISLAMIC_CIVIL_EPOCH
        } else {
            ISLAMIC_TBLA_EPOCH
        }
    }

    #[must_use]
    pub fn months_in_year(self, year: i64) -> u8 {
        match self {
            Self::Coptic | Self::Ethiopic | Self::Ethioaa => 13,
            Self::Hebrew if hebrew_leap(year) => 13,
            _ => 12,
        }
    }

    #[must_use]
    pub fn days_in_month(self, year: i64, month: u8) -> u8 {
        if let Some(offset) = self.iso_year_offset() {
            return iso_days_in_month(year - offset, month);
        }
        match self {
            Self::Coptic | Self::Ethiopic | Self::Ethioaa => match month {
                13 if year.rem_euclid(4) == 3 => 6,
                13 => 5,
                _ => 30,
            },
            Self::Hebrew => hebrew_days_in_month(year, month),
            Self::Persian => persian_days_in_month(year, month),
            Self::Indian => indian_days_in_month(year, month),
            _ => {
                if month % 2 == 1 || (month == 12 && islamic_leap(year)) {
                    30
                } else {
                    29
                }
            }
        }
    }

    #[must_use]
    pub fn in_leap_year(self, year: i64) -> bool {
        if let Some(offset) = self.iso_year_offset() {
            return gregorian_leap(year - offset);
        }
        match self {
            Self::Coptic | Self::Ethiopic | Self::Ethioaa => year.rem_euclid(4) == 3,
            Self::Hebrew => hebrew_leap(year),
            Self::Persian => persian_leap(year),
            Self::Indian => gregorian_leap(year + INDIAN_YEAR_OFFSET),
            _ => islamic_leap(year),
        }
    }

    #[must_use]
    pub fn days_in_year(self, year: i64) -> u16 {
        if self == Self::Hebrew {
            return hebrew_year_length(year) as u16;
        }
        (1..=self.months_in_year(year))
            .map(|month| u16::from(self.days_in_month(year, month)))
            .sum()
    }

    /// Whether any day of `year` is a representable date.
    fn has_representable_days(self, year: i64) -> bool {
        let first = self.epoch_days(year, 1, 1);
        let next = self.epoch_days(year + 1, 1, 1);
        PlainDate::from_epoch_days(first).is_ok() || PlainDate::from_epoch_days(next - 1).is_ok()
    }

    /// Days since the Unix epoch of a calendar date. The date must exist.
    #[must_use]
    pub fn epoch_days(self, year: i64, month: u8, day: u8) -> i64 {
        if let Some(offset) = self.iso_year_offset() {
            return iso_days(year - offset, month, day);
        }
        match self {
            Self::Coptic => coptic_like_days(COPTIC_EPOCH, year, month, day),
            Self::Ethiopic => coptic_like_days(ETHIOPIC_EPOCH, year, month, day),
            Self::Ethioaa => {
                coptic_like_days(ETHIOPIC_EPOCH, year - ETHIOAA_YEAR_OFFSET, month, day)
            }
            Self::Hebrew => hebrew_days(year, month, day),
            Self::Persian => persian_days(year, month, day),
            Self::Indian => indian_days(year, month, day),
            _ => islamic_days(self.islamic_epoch(), year, month, day),
        }
    }

    /// The calendar date of a day count.
    #[must_use]
    pub fn date(self, days: i64) -> CalendarDate {
        let (year, month, day) = if let Some(offset) = self.iso_year_offset() {
            let (year, month, day) = iso_from_days(days);
            (year + offset, month, day)
        } else {
            match self {
                Self::Coptic => coptic_like_date(COPTIC_EPOCH, days),
                Self::Ethiopic => coptic_like_date(ETHIOPIC_EPOCH, days),
                Self::Ethioaa => {
                    let (year, month, day) = coptic_like_date(ETHIOPIC_EPOCH, days);
                    (year + ETHIOAA_YEAR_OFFSET, month, day)
                }
                Self::Hebrew => hebrew_date(days),
                Self::Persian => persian_date(days),
                Self::Indian => indian_date(days),
                _ => islamic_date(self.islamic_epoch(), days),
            }
        };
        CalendarDate { year, month, day }
    }

    /// The code of an ordinal month. Hebrew's sixth month in a leap year is
    /// Adar I, the leap month, and pushes the rest along by one.
    #[must_use]
    pub fn month_code(self, year: i64, month: u8) -> MonthCode {
        if self == Self::Hebrew && hebrew_leap(year) {
            return match month {
                1..=5 => MonthCode {
                    number: month,
                    leap: false,
                },
                6 => MonthCode {
                    number: 5,
                    leap: true,
                },
                _ => MonthCode {
                    number: month - 1,
                    leap: false,
                },
            };
        }
        MonthCode {
            number: month,
            leap: false,
        }
    }

    /// Whether a month code exists in some year of this calendar.
    #[must_use]
    pub fn has_month_code(self, code: MonthCode) -> bool {
        let last = if matches!(self, Self::Coptic | Self::Ethiopic | Self::Ethioaa) {
            13
        } else {
            12
        };
        if code.leap {
            self == Self::Hebrew && code.number == 5
        } else {
            (1..=last).contains(&code.number)
        }
    }

    /// The ordinal month of a code in `year`, if the year has it.
    #[must_use]
    pub fn ordinal_month(self, year: i64, code: MonthCode) -> Option<u8> {
        if !self.has_month_code(code) {
            return None;
        }
        if self == Self::Hebrew {
            let leap = hebrew_leap(year);
            return match (code.leap, leap) {
                (true, true) => Some(6),
                (true, false) => None,
                (false, true) if code.number >= 6 => Some(code.number + 1),
                (false, _) => Some(code.number),
            };
        }
        Some(code.number)
    }

    /// The ordinal month a code lands on in `year`. A leap month a year lacks
    /// falls to the month it stands in for, or is an error.
    fn ordinal_month_or_constrain(
        self,
        year: i64,
        code: MonthCode,
        overflow: Overflow,
    ) -> TemporalResult<u8> {
        match self.ordinal_month(year, code) {
            Some(month) => Ok(month),
            None if overflow == Overflow::Constrain => Ok(self
                .ordinal_month(
                    year,
                    MonthCode {
                        number: code.number + 1,
                        leap: false,
                    },
                )
                .unwrap_or(code.number)),
            None => Err(TemporalError::range(format!(
                "month {} does not exist in year {year}",
                code.render()
            ))),
        }
    }

    /// The era and era year of a date, for the calendars that have eras.
    #[must_use]
    pub fn era(self, date: CalendarDate) -> (&'static str, i64) {
        let CalendarDate { year, .. } = date;
        match self {
            Self::Buddhist => ("be", year),
            Self::Coptic | Self::Hebrew => ("am", year),
            Self::Ethioaa => ("aa", year),
            Self::Ethiopic if year > 0 => ("am", year),
            Self::Ethiopic => ("aa", year + ETHIOAA_YEAR_OFFSET),
            Self::Indian => ("shaka", year),
            Self::Persian => ("ap", year),
            Self::IslamicCivil | Self::IslamicTbla if year > 0 => ("ah", year),
            Self::IslamicCivil | Self::IslamicTbla => ("bh", 1 - year),
            Self::Roc if year > 0 => ("roc", year),
            Self::Roc => ("broc", 1 - year),
            Self::Gregory if year > 0 => ("ce", year),
            Self::Gregory => ("bce", 1 - year),
        }
    }

    /// The arithmetic year of an era year, or `None` for an era the calendar
    /// does not have.
    #[must_use]
    pub fn year_of_era(self, era: &str, era_year: i64) -> Option<i64> {
        let single = |name: &str| (era == name).then_some(era_year);
        match self {
            Self::Buddhist => single("be"),
            Self::Coptic | Self::Hebrew => single("am"),
            Self::Ethioaa => single("aa"),
            Self::Indian => single("shaka"),
            Self::Persian => single("ap"),
            Self::Ethiopic => match era {
                "am" => Some(era_year),
                "aa" => Some(era_year - ETHIOAA_YEAR_OFFSET),
                _ => None,
            },
            Self::IslamicCivil | Self::IslamicTbla => match era {
                "ah" => Some(era_year),
                "bh" => Some(1 - era_year),
                _ => None,
            },
            Self::Roc => match era {
                "roc" | "minguo" => Some(era_year),
                "broc" | "before-roc" | "minguo-qian" => Some(1 - era_year),
                _ => None,
            },
            Self::Gregory => match era {
                "ce" | "ad" => Some(era_year),
                "bce" | "bc" => Some(1 - era_year),
                _ => None,
            },
        }
    }

    /// The day count of `year`, an ordinal month, and a day, kept within the
    /// month as `overflow` says. It may lie past the representable range; only
    /// a finished date has to be inside it.
    fn days_of(self, year: i64, month: u8, day: i64, overflow: Overflow) -> TemporalResult<i64> {
        let last = i64::from(self.days_in_month(year, month));
        if day > last && overflow == Overflow::Reject {
            return Err(TemporalError::range(format!(
                "day {day} does not exist in month {month} of year {year}"
            )));
        }
        Ok(self.epoch_days(year, month, day.clamp(1, last) as u8))
    }

    /// The year and ordinal month `months` after a month.
    fn add_months(self, mut year: i64, mut month: i64, months: i64) -> TemporalResult<(i64, u8)> {
        month += months;
        while month < 1 {
            year -= 1;
            check_year(year)?;
            month += i64::from(self.months_in_year(year));
        }
        while month > i64::from(self.months_in_year(year)) {
            month -= i64::from(self.months_in_year(year));
            year += 1;
            check_year(year)?;
        }
        Ok((year, month as u8))
    }

    /// CalendarDateAdd.
    fn add(
        self,
        iso_date: PlainDate,
        duration: &Duration,
        overflow: Overflow,
    ) -> TemporalResult<PlainDate> {
        let date = self.date(iso_date.epoch_days());
        let year = i64::try_from(duration.years)
            .ok()
            .and_then(|years| date.year.checked_add(years))
            .filter(|year| year.abs() < YEAR_LIMIT)
            .ok_or_else(out_of_range)?;
        let code = self.month_code(date.year, date.month);
        let month = self.ordinal_month_or_constrain(year, code, overflow)?;
        let months = i64::try_from(duration.months).map_err(|_| out_of_range())?;
        if months.abs() > 13 * YEAR_LIMIT {
            return Err(out_of_range());
        }
        let (year, month) = self.add_months(year, i64::from(month), months)?;
        let start = self.days_of(year, month, i64::from(date.day), overflow)?;
        let total = i128::from(start) + duration.weeks * 7 + duration.days;
        PlainDate::from_epoch_days(i64::try_from(total).map_err(|_| out_of_range())?)
    }

    /// Whether a first date moved by `years` lands past `target`. The code is
    /// compared as it stands, before any constraining to the year.
    fn years_surpass(
        self,
        sign: i64,
        first: CalendarDate,
        years: i64,
        target: CalendarDate,
    ) -> TemporalResult<bool> {
        let year = first.year + years;
        let code = self.month_code(first.year, first.month);
        let target_code = self.month_code(target.year, target.month);
        let as_written = (year, (code.number, code.leap), first.day).cmp(&(
            target.year,
            (target_code.number, target_code.leap),
            target.day,
        ));
        if as_written as i64 * sign > 0 {
            return Ok(true);
        }
        let month = self.ordinal_month_or_constrain(year, code, Overflow::Constrain)?;
        Ok(month_surpasses(sign, year, month, first.day, target))
    }

    /// CalendarDateUntil.
    fn until(self, one: PlainDate, two: PlainDate, largest_unit: Unit) -> TemporalResult<Duration> {
        let (one_days, two_days) = (one.epoch_days(), two.epoch_days());
        let sign = (two_days - one_days).signum();
        if sign == 0 {
            return Ok(Duration::default());
        }
        let first = self.date(one_days);
        let target = self.date(two_days);
        let mut years = 0;
        if largest_unit == Unit::Year {
            years = target.year - first.year;
            while self.years_surpass(sign, first, years, target)? {
                years -= sign;
            }
        }
        let code = self.month_code(first.year, first.month);
        let year = first.year + years;
        let month = self.ordinal_month_or_constrain(year, code, Overflow::Constrain)?;
        let mut position = (year, month);
        let mut months = 0;
        if matches!(largest_unit, Unit::Year | Unit::Month) {
            loop {
                let next = self.add_months(position.0, i64::from(position.1), sign)?;
                if month_surpasses(sign, next.0, next.1, first.day, target) {
                    break;
                }
                position = next;
                months += sign;
            }
        }
        let day = first.day.min(self.days_in_month(position.0, position.1));
        let mut days = two_days - self.epoch_days(position.0, position.1, day);
        let mut weeks = 0;
        if largest_unit == Unit::Week {
            weeks = days / 7;
            days %= 7;
        }
        Duration::from_date(years.into(), months.into(), weeks.into(), days.into())
    }

    fn fields(self, iso_date: PlainDate) -> CalendarDateFields {
        let days = iso_date.epoch_days();
        let date = self.date(days);
        let (era, era_year) = self.era(date);
        let start_of_year = self.epoch_days(date.year, 1, 1);
        CalendarDateFields {
            era: Some(Arc::from(era)),
            era_year: Some(era_year as i32),
            year: date.year as i32,
            month: date.month,
            month_code: Arc::from(self.month_code(date.year, date.month).render()),
            day: date.day,
            day_of_week: iso_day_of_week(iso_date.year, iso_date.month, iso_date.day),
            day_of_year: (days - start_of_year + 1) as u16,
            week_of_year: None,
            year_of_week: None,
            days_in_week: 7,
            days_in_month: self.days_in_month(date.year, date.month),
            days_in_year: self.days_in_year(date.year),
            months_in_year: self.months_in_year(date.year),
            in_leap_year: self.in_leap_year(date.year),
        }
    }
}

/// Whether a year, ordinal month, and unconstrained day land past `target`.
fn month_surpasses(sign: i64, year: i64, month: u8, day: u8, target: CalendarDate) -> bool {
    let ordering = (year, month, day).cmp(&(target.year, target.month, target.day));
    ordering as i64 * sign > 0
}

fn out_of_range() -> TemporalError {
    TemporalError::range("date outside the representable range")
}

fn check_year(year: i64) -> TemporalResult<()> {
    if year.abs() < YEAR_LIMIT {
        Ok(())
    } else {
        Err(out_of_range())
    }
}

/// What a fields record says about a month.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum MonthField {
    Ordinal(f64),
    Code(MonthCode),
}

/// The day count of resolved fields: CalendarDateToISO, before the limits.
///
/// # Errors
/// `RangeError` for a month, day, or year that does not exist under `overflow`.
fn days_from_fields(
    calendar: Calendar,
    year: f64,
    month: MonthField,
    day: f64,
    overflow: Overflow,
) -> TemporalResult<i64> {
    if year.abs() >= YEAR_LIMIT as f64 {
        return Err(out_of_range());
    }
    let year = year as i64;
    let month = match month {
        MonthField::Code(code) => calendar.ordinal_month_or_constrain(year, code, overflow)?,
        MonthField::Ordinal(ordinal) => {
            let last = calendar.months_in_year(year);
            if ordinal > f64::from(last) && overflow == Overflow::Reject {
                return Err(TemporalError::range(format!(
                    "month {ordinal} does not exist in year {year}"
                )));
            }
            ordinal.min(f64::from(last)) as u8
        }
    };
    calendar.days_of(year, month, day.min(1000.0) as i64, overflow)
}

/// CalendarDateFromFields.
///
/// # Errors
/// `RangeError` for a date that does not exist under `overflow` or lies past the
/// representable range.
pub fn date_from_fields(
    calendar: Calendar,
    year: f64,
    month: MonthField,
    day: f64,
    overflow: Overflow,
) -> TemporalResult<PlainDate> {
    PlainDate::from_epoch_days(days_from_fields(calendar, year, month, day, overflow)?)
}

/// CalendarYearMonthFromFields: the month's first day is the reference.
///
/// # Errors
/// `RangeError` for a month that does not exist under `overflow` or lies past
/// the representable range.
pub fn year_month_from_fields(
    calendar: Calendar,
    year: f64,
    month: MonthField,
    overflow: Overflow,
) -> TemporalResult<PlainYearMonth> {
    let days = days_from_fields(calendar, year, month, 1.0, overflow)?;
    let (year, month, day) = ymd_from_epoch_days(days);
    PlainYearMonth::with_reference_day(year, month, day)
}

/// CalendarMonthDayFromFields. A year decides only what the month and day
/// constrain to, but it has to be a year some date falls in; without one,
/// `month` alone names nothing.
///
/// # Errors
/// `TypeError` for an ordinal month with no year; `RangeError` for a year past
/// the representable range, or a month or day that does not exist under
/// `overflow`.
pub fn month_day_from_fields(
    calendar: Calendar,
    year: Option<f64>,
    month: MonthField,
    day: f64,
    overflow: Overflow,
) -> TemporalResult<PlainMonthDay> {
    match (year, month) {
        (Some(year), month) => {
            if !calendar.has_representable_days(year as i64) {
                return Err(out_of_range());
            }
            let days = days_from_fields(calendar, year, month, day, overflow)?;
            let date = calendar.date(days);
            month_day_reference(
                calendar,
                calendar.month_code(date.year, date.month),
                f64::from(date.day),
                overflow,
            )
        }
        (None, MonthField::Code(code)) => month_day_reference(calendar, code, day, overflow),
        (None, MonthField::Ordinal(_)) => Err(TemporalError::type_error(
            "month needs a year to name a month",
        )),
    }
}

/// Whether `month` and `code` name the same month of `year`, the check for a
/// fields record that gives both.
#[must_use]
pub fn month_matches(calendar: Calendar, year: f64, month: f64, code: MonthCode) -> bool {
    year.abs() >= YEAR_LIMIT as f64
        || calendar
            .ordinal_month(year as i64, code)
            .is_none_or(|ordinal| f64::from(ordinal) == month)
}

/// CalendarMonthDayToISOReferenceDate: the latest ISO date no later than the end
/// of 1972 that has this month code and day. A day past the longest such month
/// is constrained to it or is an error.
fn month_day_reference(
    calendar: Calendar,
    code: MonthCode,
    day: f64,
    overflow: Overflow,
) -> TemporalResult<PlainMonthDay> {
    let limit = iso_days(1972, 12, 31);
    let start = calendar.date(limit).year;
    let months = (start - REFERENCE_SEARCH_YEARS..=start)
        .rev()
        .filter_map(|year| {
            calendar
                .ordinal_month(year, code)
                .map(|month| (year, month, calendar.days_in_month(year, month)))
        });
    let longest = months.clone().map(|(_, _, length)| length).max();
    let Some(longest) = longest else {
        return Err(TemporalError::range(format!(
            "{} is not a month of the {} calendar",
            code.render(),
            calendar.id()
        )));
    };
    if day > f64::from(longest) && overflow == Overflow::Reject {
        return Err(TemporalError::range(format!(
            "day {day} does not exist in {}",
            code.render()
        )));
    }
    let day = day.min(f64::from(longest)) as u8;
    months
        .filter(|(_, _, length)| *length >= day)
        .map(|(year, month, _)| calendar.epoch_days(year, month, day))
        .find(|days| *days <= limit)
        .ok_or_else(out_of_range)
        .and_then(|days| {
            let (year, month, day) = ymd_from_epoch_days(days);
            PlainMonthDay::with_reference_year(month.into(), day.into(), year, Overflow::Reject)
        })
}

/// The year-month holding an ISO date, as CalendarYearMonthFromFields sees it.
///
/// # Errors
/// `RangeError` when that month is past the representable range.
pub fn year_month_of(calendar: Calendar, iso_date: PlainDate) -> TemporalResult<PlainYearMonth> {
    let date = calendar.date(iso_date.epoch_days());
    let (year, month, day) = ymd_from_epoch_days(calendar.epoch_days(date.year, date.month, 1));
    PlainYearMonth::with_reference_day(year, month, day)
}

/// The month-day of an ISO date, as CalendarMonthDayFromFields sees it.
///
/// # Errors
/// `RangeError` when no reference date exists.
pub fn month_day_of(calendar: Calendar, iso_date: PlainDate) -> TemporalResult<PlainMonthDay> {
    let date = calendar.date(iso_date.epoch_days());
    month_day_reference(
        calendar,
        calendar.month_code(date.year, date.month),
        f64::from(date.day),
        Overflow::Constrain,
    )
}

/// The first day of a year-month's calendar month.
///
/// # Errors
/// `RangeError` when that day is past the representable range.
pub fn first_of_month(calendar: Calendar, value: PlainYearMonth) -> TemporalResult<PlainDate> {
    let date = calendar.date(value.iso_date().epoch_days());
    PlainDate::from_epoch_days(calendar.epoch_days(date.year, date.month, 1))
}

/// AddDurationToYearMonth. Only years and months move a year-month.
///
/// # Errors
/// `RangeError` for a smaller unit, a month that does not exist under
/// `overflow`, or a result past the representable range.
pub fn add_to_year_month(
    calendar: Calendar,
    value: PlainYearMonth,
    duration: &Duration,
    overflow: Overflow,
) -> TemporalResult<PlainYearMonth> {
    if duration.default_largest_unit() > Unit::Month && !duration.is_zero() {
        return Err(TemporalError::range(
            "a year-month can only change by whole years and months",
        ));
    }
    let moved = calendar.add(first_of_month(calendar, value)?, duration, overflow)?;
    year_month_of(calendar, moved)
}

/// The calendars this runtime has, ISO 8601 among them.
#[derive(Debug, Clone, Copy, Default)]
pub struct Calendars;

impl CalendarProvider for Calendars {
    fn fields(
        &self,
        calendar: &CalendarId,
        iso_date: PlainDate,
    ) -> TemporalResult<CalendarDateFields> {
        match Calendar::from_id(calendar) {
            Some(calendar) => Ok(calendar.fields(iso_date)),
            None => IsoCalendarProvider.fields(calendar, iso_date),
        }
    }

    fn date_add(
        &self,
        calendar: &CalendarId,
        iso_date: PlainDate,
        duration: &Duration,
        overflow: Overflow,
    ) -> TemporalResult<PlainDate> {
        match Calendar::from_id(calendar) {
            Some(calendar) => calendar.add(iso_date, duration, overflow),
            None => IsoCalendarProvider.date_add(calendar, iso_date, duration, overflow),
        }
    }

    fn date_until(
        &self,
        calendar: &CalendarId,
        one: PlainDate,
        two: PlainDate,
        largest_unit: Unit,
    ) -> TemporalResult<Duration> {
        match Calendar::from_id(calendar) {
            Some(calendar) => calendar.until(one, two, largest_unit),
            None => iso_date_until(one, two, largest_unit),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALL: [Calendar; 11] = Calendar::ALL;

    #[test]
    fn dates_round_trip_through_day_counts() {
        for calendar in ALL {
            for days in (-1_000_000..1_000_000).step_by(997) {
                let date = calendar.date(days);
                assert_eq!(
                    calendar.epoch_days(date.year, date.month, date.day),
                    days,
                    "{} {date:?}",
                    calendar.id()
                );
                assert!(date.month <= calendar.months_in_year(date.year));
                assert!(date.day >= 1);
                assert!(date.day <= calendar.days_in_month(date.year, date.month));
            }
        }
    }

    #[test]
    fn known_new_years_land_on_known_days() {
        let date = |calendar: Calendar, year, month, day| {
            let (iso_year, iso_month, iso_day) =
                iso_from_days(calendar.epoch_days(year, month, day));
            (iso_year, iso_month, iso_day)
        };
        assert_eq!(date(Calendar::Hebrew, 5784, 1, 1), (2023, 9, 16));
        assert_eq!(date(Calendar::Persian, 1403, 1, 1), (2024, 3, 20));
        assert_eq!(date(Calendar::Indian, 1946, 1, 1), (2024, 3, 21));
        assert_eq!(date(Calendar::Coptic, 1741, 1, 1), (2024, 9, 11));
        assert_eq!(date(Calendar::Ethiopic, 2017, 1, 1), (2024, 9, 11));
        assert_eq!(date(Calendar::IslamicCivil, 1446, 1, 1), (2024, 7, 8));
    }

    #[test]
    fn hebrew_leap_years_shift_the_codes_after_adar_i() {
        let calendar = Calendar::Hebrew;
        assert_eq!(calendar.month_code(5779, 6).render(), "M05L");
        assert_eq!(calendar.month_code(5779, 7).render(), "M06");
        assert_eq!(calendar.month_code(5780, 6).render(), "M06");
        assert_eq!(
            calendar.ordinal_month(
                5780,
                MonthCode {
                    number: 5,
                    leap: true
                }
            ),
            None
        );
    }
}
