//! English date and time data: patterns, names, and calendar dates.

use super::date_time_format::{
    CalendarDateTime, DateTimeComponents, DateTimeFormatDataProvider, DateTimePattern,
    DateTimeRangePattern, DateTimeStyle, HourCycle, HourCyclePreferences, IntegerFormatRequest,
    MonthStyle, NumericStyle, PatternField, PatternItem, PatternRequest, ProviderError,
    RangeDifference, RangePatternItem, RangePatternRequest, RangeSource, TextField,
    TextFormatRequest, TextWidth, TimeZoneNameStyle,
};
use super::locale_data::{IntlData, numbering_system_digits, time_zone};
use crate::temporal::calendar::Calendar;

const NANOSECONDS_PER_MILLISECOND: i128 = 1_000_000;
const MILLISECONDS_PER_DAY: i128 = 86_400_000;

const WEEKDAYS: [&str; 7] = [
    "Monday",
    "Tuesday",
    "Wednesday",
    "Thursday",
    "Friday",
    "Saturday",
    "Sunday",
];
const MONTHS: [&str; 12] = [
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
];
const COPTIC_MONTHS: [&str; 13] = [
    "Tout",
    "Baba",
    "Hator",
    "Kiahk",
    "Toba",
    "Amshir",
    "Baramhat",
    "Baramouda",
    "Bashans",
    "Paona",
    "Epep",
    "Mesra",
    "Nasie",
];
const ETHIOPIC_MONTHS: [&str; 13] = [
    "Meskerem", "Tekemt", "Hedar", "Tahsas", "Ter", "Yekatit", "Megabit", "Miazia", "Genbot",
    "Sene", "Hamle", "Nehasse", "Pagumen",
];
const INDIAN_MONTHS: [&str; 12] = [
    "Chaitra",
    "Vaisakha",
    "Jyaistha",
    "Asadha",
    "Sravana",
    "Bhadra",
    "Asvina",
    "Kartika",
    "Agrahayana",
    "Pausa",
    "Magha",
    "Phalguna",
];
const ISLAMIC_MONTHS: [&str; 12] = [
    "Muharram",
    "Safar",
    "Rabi\u{02BB} I",
    "Rabi\u{02BB} II",
    "Jumada I",
    "Jumada II",
    "Rajab",
    "Sha\u{02BB}ban",
    "Ramadan",
    "Shawwal",
    "Dhu\u{02BB}l-Qi\u{02BB}dah",
    "Dhu\u{02BB}l-Hijjah",
];
const PERSIAN_MONTHS: [&str; 12] = [
    "Farvardin",
    "Ordibehesht",
    "Khordad",
    "Tir",
    "Mordad",
    "Shahrivar",
    "Mehr",
    "Aban",
    "Azar",
    "Dey",
    "Bahman",
    "Esfand",
];
/// Hebrew months by month code, M01 to M12, without the leap month.
const HEBREW_MONTHS: [&str; 12] = [
    "Tishri", "Heshvan", "Kislev", "Tevet", "Shevat", "Adar", "Nisan", "Iyar", "Sivan", "Tamuz",
    "Av", "Elul",
];

fn literal(text: &str) -> PatternItem {
    PatternItem::Literal(text.to_owned())
}

fn field(field: PatternField) -> PatternItem {
    PatternItem::Field(field)
}

/// Appends `items` to `pattern` after `separator`, when both have something.
fn join(pattern: &mut Vec<PatternItem>, separator: &str, items: Vec<PatternItem>) {
    if !pattern.is_empty() && !items.is_empty() {
        pattern.push(literal(separator));
    }
    pattern.extend(items);
}

/// The date half of a pattern, in English order.
fn date_items(components: &DateTimeComponents) -> Vec<PatternItem> {
    let month = components
        .month
        .map(|style| field(PatternField::Month(style)));
    let day = components.day.map(|style| field(PatternField::Day(style)));
    let year = components
        .year
        .map(|style| field(PatternField::Year(style)));
    let textual = matches!(
        components.month,
        Some(MonthStyle::Narrow | MonthStyle::Short | MonthStyle::Long)
    );
    let mut items = Vec::new();
    if let Some(width) = components.weekday {
        items.push(field(PatternField::Weekday(width)));
    }
    let mut body = Vec::new();
    if textual {
        body.extend(month);
        join(&mut body, " ", day.clone().into_iter().collect());
        let separator = if day.is_some() { ", " } else { " " };
        join(&mut body, separator, year.into_iter().collect());
    } else {
        body.extend(month);
        join(&mut body, "/", day.into_iter().collect());
        join(&mut body, "/", year.into_iter().collect());
    }
    join(&mut items, ", ", body);
    if let Some(width) = components.era {
        join(&mut items, " ", vec![field(PatternField::Era(width))]);
    }
    items
}

/// The time half of a pattern. Minutes and seconds following a larger field
/// always take two digits, and a 24-hour hour does too, as English writes them.
fn time_items(components: &DateTimeComponents, cycle: HourCycle) -> Vec<PatternItem> {
    let twelve_hour = cycle.is_twelve_hour();
    let mut items = Vec::new();
    let mut leading = true;
    if let Some(style) = components.hour {
        let style = if twelve_hour {
            style
        } else {
            NumericStyle::TwoDigit
        };
        items.push(field(PatternField::Hour(style)));
        leading = false;
    }
    if let Some(style) = components.minute {
        let style = if leading && components.second.is_none() {
            style
        } else {
            NumericStyle::TwoDigit
        };
        join(&mut items, ":", vec![field(PatternField::Minute(style))]);
        leading = false;
    }
    if let Some(style) = components.second {
        let style = if leading {
            style
        } else {
            NumericStyle::TwoDigit
        };
        join(&mut items, ":", vec![field(PatternField::Second(style))]);
    }
    if let Some(digits) = components.fractional_second_digits {
        join(
            &mut items,
            ".",
            vec![field(PatternField::FractionalSecond(digits))],
        );
    }
    if let Some(width) = components.day_period {
        join(&mut items, " ", vec![field(PatternField::DayPeriod(width))]);
    } else if components.hour.is_some() && twelve_hour {
        items.push(literal(" "));
        items.push(field(PatternField::AmPm));
    }
    items
}

/// What the pattern for `components` resolves each field to, for
/// `resolvedOptions`.
fn resolved_components(components: &DateTimeComponents, cycle: HourCycle) -> DateTimeComponents {
    let mut resolved = components.clone();
    if resolved.hour.is_some() && !cycle.is_twelve_hour() {
        resolved.hour = Some(NumericStyle::TwoDigit);
    }
    if resolved.minute.is_some() && (resolved.hour.is_some() || resolved.second.is_some()) {
        resolved.minute = Some(NumericStyle::TwoDigit);
    }
    if resolved.second.is_some() && resolved.minute.is_some() {
        resolved.second = Some(NumericStyle::TwoDigit);
    }
    resolved
}

fn components_pattern(components: &DateTimeComponents, cycle: HourCycle) -> DateTimePattern {
    let mut items = date_items(components);
    join(&mut items, ", ", time_items(components, cycle));
    if let Some(style) = components.time_zone_name {
        join(
            &mut items,
            " ",
            vec![field(PatternField::TimeZoneName(style))],
        );
    }
    DateTimePattern {
        components: resolved_components(components, cycle),
        items,
    }
}

fn date_style_items(style: DateTimeStyle) -> Vec<PatternItem> {
    let (month, day, year) = (
        match style {
            DateTimeStyle::Full | DateTimeStyle::Long => MonthStyle::Long,
            DateTimeStyle::Medium => MonthStyle::Short,
            DateTimeStyle::Short => MonthStyle::Numeric,
        },
        NumericStyle::Numeric,
        if style == DateTimeStyle::Short {
            NumericStyle::TwoDigit
        } else {
            NumericStyle::Numeric
        },
    );
    date_items(&DateTimeComponents {
        weekday: (style == DateTimeStyle::Full).then_some(TextWidth::Long),
        month: Some(month),
        day: Some(day),
        year: Some(year),
        ..DateTimeComponents::default()
    })
}

fn time_style_items(style: DateTimeStyle, cycle: HourCycle) -> Vec<PatternItem> {
    let mut items = time_items(
        &DateTimeComponents {
            hour: Some(NumericStyle::Numeric),
            minute: Some(NumericStyle::TwoDigit),
            second: (style != DateTimeStyle::Short).then_some(NumericStyle::TwoDigit),
            ..DateTimeComponents::default()
        },
        cycle,
    );
    let name = match style {
        DateTimeStyle::Full => Some(TimeZoneNameStyle::Long),
        DateTimeStyle::Long => Some(TimeZoneNameStyle::Short),
        DateTimeStyle::Medium | DateTimeStyle::Short => None,
    };
    if let Some(name) = name {
        join(
            &mut items,
            " ",
            vec![field(PatternField::TimeZoneName(name))],
        );
    }
    items
}

fn style_pattern(
    date: Option<DateTimeStyle>,
    time: Option<DateTimeStyle>,
    cycle: HourCycle,
) -> DateTimePattern {
    let mut items = date.map_or_else(Vec::new, date_style_items);
    let separator = if matches!(date, Some(DateTimeStyle::Full | DateTimeStyle::Long)) {
        " at "
    } else {
        ", "
    };
    if let Some(style) = time {
        join(&mut items, separator, time_style_items(style, cycle));
    }
    DateTimePattern {
        components: DateTimeComponents::default(),
        items,
    }
}

/// Where a pattern field sits among the differences a range can have.
fn difference_of(item: &PatternItem) -> Option<RangeDifference> {
    let PatternItem::Field(field) = item else {
        return None;
    };
    Some(match field {
        PatternField::Era(_) => RangeDifference::Era,
        PatternField::Year(_) | PatternField::RelatedYear(_) | PatternField::YearName(_) => {
            RangeDifference::Year
        }
        PatternField::Month(_) => RangeDifference::Month,
        PatternField::Day(_) | PatternField::Weekday(_) => RangeDifference::Day,
        PatternField::DayPeriod(_) | PatternField::AmPm => RangeDifference::DayPeriod,
        PatternField::Hour(_) => RangeDifference::Hour,
        PatternField::Minute(_) => RangeDifference::Minute,
        PatternField::Second(_) => RangeDifference::Second,
        PatternField::FractionalSecond(_) => RangeDifference::FractionalSecond,
        PatternField::TimeZoneName(_) => return None,
    })
}

const fn difference_rank(difference: RangeDifference) -> u8 {
    match difference {
        RangeDifference::Era => 0,
        RangeDifference::Year => 1,
        RangeDifference::Month => 2,
        RangeDifference::Day => 3,
        RangeDifference::DayPeriod => 4,
        RangeDifference::Hour => 5,
        RangeDifference::Minute => 6,
        RangeDifference::Second => 7,
        RangeDifference::FractionalSecond => 8,
    }
}

fn is_date_difference(difference: RangeDifference) -> bool {
    difference_rank(difference) <= difference_rank(RangeDifference::Day)
}

const RANGE_SEPARATOR: &str = " \u{2013} ";

fn sourced(items: &[PatternItem], source: RangeSource) -> Vec<RangePatternItem> {
    items
        .iter()
        .map(|item| RangePatternItem {
            source,
            item: item.clone(),
        })
        .collect()
}

/// Both ends written out in full, around the separator.
fn full_range(items: &[PatternItem]) -> DateTimeRangePattern {
    let mut result = sourced(items, RangeSource::StartRange);
    result.push(RangePatternItem {
        source: RangeSource::Shared,
        item: literal(RANGE_SEPARATOR),
    });
    result.extend(sourced(items, RangeSource::EndRange));
    DateTimeRangePattern { items: result }
}

/// A range that shares what cannot differ: every field coarser than
/// `difference`. Numeric dates are always repeated whole, and so is a date
/// next to a time when the dates differ.
fn range_pattern(pattern: &DateTimePattern, difference: RangeDifference) -> DateTimeRangePattern {
    let items = &pattern.items;
    let has_time = items
        .iter()
        .any(|item| difference_of(item).is_some_and(|kind| !is_date_difference(kind)));
    let has_date = items
        .iter()
        .any(|item| difference_of(item).is_some_and(is_date_difference));
    let numeric_month = items.iter().any(|item| {
        matches!(
            item,
            PatternItem::Field(PatternField::Month(
                MonthStyle::Numeric | MonthStyle::TwoDigit
            ))
        )
    });
    let date_differs = is_date_difference(difference);
    if date_differs && (numeric_month || (has_date && has_time)) {
        return full_range(items);
    }
    let rank = difference_rank(difference);
    let varies =
        |item: &PatternItem| difference_of(item).is_some_and(|kind| difference_rank(kind) >= rank);
    let (Some(first), Some(last)) = (
        items.iter().position(varies),
        items.iter().rposition(varies),
    ) else {
        return full_range(items);
    };
    let mut result = sourced(&items[..first], RangeSource::Shared);
    result.extend(sourced(&items[first..=last], RangeSource::StartRange));
    result.push(RangePatternItem {
        source: RangeSource::Shared,
        item: literal(RANGE_SEPARATOR),
    });
    result.extend(sourced(&items[first..=last], RangeSource::EndRange));
    result.extend(sourced(&items[last + 1..], RangeSource::Shared));
    DateTimeRangePattern { items: result }
}

/// Days since the Unix epoch to a proleptic Gregorian date.
fn civil_from_days(days: i64) -> (i64, u8, u8) {
    let shifted = days + 719_468;
    let era = shifted.div_euclid(146_097);
    let day_of_era = shifted.rem_euclid(146_097);
    let year_of_era =
        (day_of_era - day_of_era / 1460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let shifted_month = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * shifted_month + 2) / 5 + 1;
    let month = if shifted_month < 10 {
        shifted_month + 3
    } else {
        shifted_month - 9
    };
    let year = year_of_era + era * 400 + i64::from(month <= 2);
    (year, month as u8, day as u8)
}

fn local_days(local_epoch_nanoseconds: i128) -> i64 {
    local_epoch_nanoseconds
        .div_euclid(NANOSECONDS_PER_MILLISECOND)
        .div_euclid(MILLISECONDS_PER_DAY) as i64
}

fn gregorian_date_time(local_epoch_nanoseconds: i128) -> CalendarDateTime {
    let milliseconds = local_epoch_nanoseconds.div_euclid(NANOSECONDS_PER_MILLISECOND);
    let days = milliseconds.div_euclid(MILLISECONDS_PER_DAY);
    let of_day = milliseconds.rem_euclid(MILLISECONDS_PER_DAY) as u32;
    let (year, month, day) = civil_from_days(days as i64);
    let (era, display_year) = if year <= 0 {
        ("bce", 1 - year)
    } else {
        ("ce", year)
    };
    CalendarDateTime {
        era: Some(era.to_owned()),
        year: display_year as i32,
        related_year: None,
        year_name: None,
        month,
        month_code: format!("M{month:02}"),
        day,
        weekday: ((days + 3).rem_euclid(7) + 1) as u8,
        hour: (of_day / 3_600_000) as u8,
        minute: (of_day / 60_000 % 60) as u8,
        second: (of_day / 1000 % 60) as u8,
        millisecond: (of_day % 1000) as u16,
    }
}

/// A calendar's view of a local time; the weekday and time of day are the same
/// in every calendar.
fn calendar_view(calendar: Calendar, local_epoch_nanoseconds: i128) -> CalendarDateTime {
    let date = calendar.date(local_days(local_epoch_nanoseconds));
    let (era, year) = calendar.era(date);
    CalendarDateTime {
        era: Some(era.to_owned()),
        year: year as i32,
        month: date.month,
        month_code: calendar.month_code(date.year, date.month).render(),
        day: date.day,
        ..gregorian_date_time(local_epoch_nanoseconds)
    }
}

/// The name of a Hebrew month: Adar is Adar II in a year that has Adar I.
fn hebrew_month_name(local: &CalendarDateTime) -> &'static str {
    match local.month_code.as_str() {
        "M05L" => "Adar I",
        "M06" if local.month == 7 => "Adar II",
        code => {
            let number = code[1..].parse::<usize>().unwrap_or(1);
            HEBREW_MONTHS[number - 1]
        }
    }
}

fn month_name(calendar: &str, local: &CalendarDateTime) -> &'static str {
    let names: &[&'static str] = match calendar {
        "coptic" => &COPTIC_MONTHS,
        "ethioaa" | "ethiopic" => &ETHIOPIC_MONTHS,
        "hebrew" => return hebrew_month_name(local),
        "indian" => &INDIAN_MONTHS,
        "islamic-civil" | "islamic-tbla" => &ISLAMIC_MONTHS,
        "persian" => &PERSIAN_MONTHS,
        _ => &MONTHS,
    };
    names[usize::from(local.month) - 1]
}

/// Calendars other than Gregorian show their era wherever they show a year.
fn show_calendar_era(calendar: &str, pattern: &mut DateTimePattern) {
    if matches!(calendar, "gregory" | "iso8601") {
        return;
    }
    let has_era = |item: &PatternItem| matches!(item, PatternItem::Field(PatternField::Era(_)));
    let is_year = |item: &PatternItem| matches!(item, PatternItem::Field(PatternField::Year(_)));
    if pattern.items.iter().any(has_era) {
        return;
    }
    if let Some(year) = pattern.items.iter().position(is_year) {
        pattern.items.insert(year + 1, literal(" "));
        pattern
            .items
            .insert(year + 2, field(PatternField::Era(TextWidth::Short)));
    }
}

fn day_period_text(hour: u8, width: TextWidth) -> &'static str {
    match hour {
        6..=11 => "in the morning",
        12 if width == TextWidth::Narrow => "n",
        12 => "noon",
        13..=17 => "in the afternoon",
        18..=20 => "in the evening",
        _ => "at night",
    }
}

fn era_text(era: &str, width: TextWidth) -> &'static str {
    match (era, width) {
        ("bce", TextWidth::Long) => "Before Christ",
        ("bce", TextWidth::Short) => "BC",
        ("bce", TextWidth::Narrow) => "B",
        ("be", _) => "BE",
        ("am", _) => "AM",
        ("aa", _) => "AA",
        ("shaka", _) => "Saka",
        ("ah", _) => "AH",
        ("bh", _) => "BH",
        ("ap", _) => "AP",
        ("roc", _) => "Minguo",
        ("broc", _) => "Before R.O.C.",
        (_, TextWidth::Long) => "Anno Domini",
        (_, TextWidth::Short) => "AD",
        (_, TextWidth::Narrow) => "A",
    }
}

fn abbreviated(name: &str, width: TextWidth) -> String {
    match width {
        TextWidth::Long => name.to_owned(),
        TextWidth::Short => name.chars().take(3).collect(),
        TextWidth::Narrow => name.chars().take(1).collect(),
    }
}

/// The offset of a time zone identifier, in minutes.
fn zone_offset_minutes(identifier: &str) -> Option<i32> {
    if let Some((_, hours)) = time_zone(identifier) {
        return Some(i32::from(hours) * 60);
    }
    let (sign, body) = match identifier.as_bytes().first()? {
        b'+' => (1, &identifier[1..]),
        b'-' => (-1, &identifier[1..]),
        _ => return None,
    };
    let (hours, minutes) = body.split_once(':')?;
    Some(sign * (hours.parse::<i32>().ok()? * 60 + minutes.parse::<i32>().ok()?))
}

fn time_zone_text(identifier: &str, style: TimeZoneNameStyle) -> String {
    if identifier == "UTC" {
        match style {
            TimeZoneNameStyle::Short => return String::from("UTC"),
            TimeZoneNameStyle::Long => return String::from("Coordinated Universal Time"),
            _ => {}
        }
    }
    let offset = zone_offset_minutes(identifier).unwrap_or(0);
    if offset == 0 {
        return String::from("GMT");
    }
    let sign = if offset < 0 { '-' } else { '+' };
    let (hours, minutes) = (offset.abs() / 60, offset.abs() % 60);
    match style {
        TimeZoneNameStyle::Long
        | TimeZoneNameStyle::LongOffset
        | TimeZoneNameStyle::LongGeneric => format!("GMT{sign}{hours:02}:{minutes:02}"),
        _ if minutes == 0 => format!("GMT{sign}{hours}"),
        _ => format!("GMT{sign}{hours}:{minutes:02}"),
    }
}

impl DateTimeFormatDataProvider for IntlData {
    fn default_time_zone(&self) -> Result<String, ProviderError> {
        Ok(String::from("UTC"))
    }

    fn canonicalize_time_zone(&self, identifier: &str) -> Result<Option<String>, ProviderError> {
        Ok(time_zone(identifier).map(|(name, _)| name.to_owned()))
    }

    fn hour_cycle_preferences(
        &self,
        _data_locale: &str,
    ) -> Result<HourCyclePreferences, ProviderError> {
        Ok(HourCyclePreferences {
            default: HourCycle::H12,
            twelve_hour: HourCycle::H12,
            twenty_four_hour: HourCycle::H23,
        })
    }

    fn select_pattern(
        &self,
        request: &PatternRequest<'_>,
    ) -> Result<DateTimePattern, ProviderError> {
        let mut pattern = if request.date_style.is_some() || request.time_style.is_some() {
            style_pattern(request.date_style, request.time_style, request.hour_cycle)
        } else {
            components_pattern(request.components, request.hour_cycle)
        };
        show_calendar_era(request.calendar, &mut pattern);
        Ok(pattern)
    }

    fn select_range_pattern(
        &self,
        request: &RangePatternRequest<'_>,
    ) -> Result<Option<DateTimeRangePattern>, ProviderError> {
        Ok(Some(match request.largest_difference {
            Some(difference) => range_pattern(request.pattern, difference),
            None => full_range(&request.pattern.items),
        }))
    }

    fn named_time_zone_offset_nanoseconds(
        &self,
        identifier: &str,
        _epoch_nanoseconds: i128,
    ) -> Result<i64, ProviderError> {
        time_zone(identifier)
            .map(|(_, hours)| i64::from(hours) * 3_600_000_000_000)
            .ok_or_else(|| ProviderError::missing("time zone", identifier))
    }

    fn calendar_date_time(
        &self,
        calendar: &str,
        local_epoch_nanoseconds: i128,
    ) -> Result<CalendarDateTime, ProviderError> {
        match calendar {
            "gregory" | "iso8601" => Ok(gregorian_date_time(local_epoch_nanoseconds)),
            other => Calendar::from_name(other)
                .map(|calendar| calendar_view(calendar, local_epoch_nanoseconds))
                .ok_or_else(|| ProviderError::missing("calendar", other)),
        }
    }

    fn format_integer(&self, request: &IntegerFormatRequest<'_>) -> Result<String, ProviderError> {
        let digits = numbering_system_digits(request.numbering_system)
            .ok_or_else(|| ProviderError::missing("numbering system", request.numbering_system))?;
        let text = format!(
            "{:0>width$}",
            request.value,
            width = usize::from(request.minimum_digits)
        );
        Ok(text
            .chars()
            .map(|character| {
                character
                    .to_digit(10)
                    .map_or(character, |digit| digits[digit as usize])
            })
            .collect())
    }

    fn style_components(
        &self,
        date: Option<DateTimeStyle>,
        time: Option<DateTimeStyle>,
    ) -> DateTimeComponents {
        let mut components = DateTimeComponents::default();
        if let Some(style) = date {
            components.weekday = (style == DateTimeStyle::Full).then_some(TextWidth::Long);
            components.month = Some(match style {
                DateTimeStyle::Full | DateTimeStyle::Long => MonthStyle::Long,
                DateTimeStyle::Medium => MonthStyle::Short,
                DateTimeStyle::Short => MonthStyle::Numeric,
            });
            components.day = Some(NumericStyle::Numeric);
            components.year = Some(if style == DateTimeStyle::Short {
                NumericStyle::TwoDigit
            } else {
                NumericStyle::Numeric
            });
        }
        if let Some(style) = time {
            components.hour = Some(NumericStyle::Numeric);
            components.minute = Some(NumericStyle::TwoDigit);
            components.second = (style != DateTimeStyle::Short).then_some(NumericStyle::TwoDigit);
        }
        components
    }

    fn format_text(&self, request: &TextFormatRequest<'_>) -> Result<String, ProviderError> {
        let local = request.local;
        Ok(match request.field {
            TextField::Weekday(width) => {
                abbreviated(WEEKDAYS[usize::from(local.weekday) - 1], width)
            }
            TextField::Era(width) => {
                era_text(local.era.as_deref().unwrap_or("ce"), width).to_owned()
            }
            TextField::YearName(_) => local.year_name.clone().unwrap_or_default(),
            TextField::Month(width) => abbreviated(month_name(request.calendar, local), width),
            TextField::DayPeriod(width) => day_period_text(local.hour, width).to_owned(),
            TextField::AmPm => String::from(if local.hour < 12 { "AM" } else { "PM" }),
            TextField::TimeZoneName(style) => time_zone_text(request.time_zone, style),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const NANOSECONDS_PER_DAY: i128 = 86_400_000_000_000;

    fn view(calendar: Calendar, days: i128) -> CalendarDateTime {
        calendar_view(calendar, days * NANOSECONDS_PER_DAY)
    }

    #[test]
    fn calendar_view_shows_the_era_year_and_keeps_the_weekday() {
        // 2024-03-26, a Tuesday.
        let days = 19_808;
        let gregorian = gregorian_date_time(days * NANOSECONDS_PER_DAY);
        assert_eq!(gregorian.weekday, 2);

        let buddhist = view(Calendar::Buddhist, days);
        assert_eq!((buddhist.year, buddhist.month, buddhist.day), (2567, 3, 26));
        assert_eq!(buddhist.era.as_deref(), Some("be"));
        assert_eq!(buddhist.weekday, gregorian.weekday);

        let islamic = view(Calendar::IslamicCivil, days);
        assert_eq!((islamic.year, islamic.month), (1445, 9));
        assert_eq!(month_name("islamic-civil", &islamic), "Ramadan");

        // Before 1912 the ROC year counts down from the era's start.
        let before_roc = view(Calendar::Roc, -30_000);
        assert_eq!(before_roc.era.as_deref(), Some("broc"));
        assert!(before_roc.year > 0);
    }

    #[test]
    fn hebrew_month_names_follow_the_month_code() {
        let calendar = Calendar::Hebrew;
        let named = |year, month| {
            let days = calendar.epoch_days(year, month, 1);
            let local = view(calendar, i128::from(days));
            month_name("hebrew", &local)
        };
        // 5784 is a leap year, 5783 is not.
        assert_eq!(named(5784, 6), "Adar I");
        assert_eq!(named(5784, 7), "Adar II");
        assert_eq!(named(5784, 8), "Nisan");
        assert_eq!(named(5783, 6), "Adar");
        assert_eq!(named(5783, 7), "Nisan");
        assert_eq!(named(5783, 12), "Elul");
    }

    #[test]
    fn only_calendars_other_than_gregorian_add_an_era() {
        let year_pattern = || DateTimePattern {
            components: DateTimeComponents::default(),
            items: vec![field(PatternField::Year(NumericStyle::Numeric))],
        };
        let mut plain = year_pattern();
        show_calendar_era("gregory", &mut plain);
        assert_eq!(plain.items.len(), 1);
        show_calendar_era("iso8601", &mut plain);
        assert_eq!(plain.items.len(), 1);

        let mut with_era = year_pattern();
        show_calendar_era("buddhist", &mut with_era);
        assert_eq!(
            with_era.items[2],
            field(PatternField::Era(TextWidth::Short))
        );
        show_calendar_era("buddhist", &mut with_era);
        assert_eq!(with_era.items.len(), 3, "an era is added only once");
    }
}
