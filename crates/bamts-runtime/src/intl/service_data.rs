//! English data for PluralRules, RelativeTimeFormat, ListFormat, Segmenter, and
//! DisplayNames.

use std::collections::BTreeMap;
use std::sync::LazyLock;

use super::locale_data::{IntlData, numbering_system_digits};
use super::locale_negotiation::LocaleDataProvider;
use super::number_data::CURRENCY_NAMES;
use super::plural_rules::{
    DisplayNamesStyle, DisplayNamesType, FormattedNumber, IntlServiceDataProvider, LanguageDisplay,
    ListPatternPosition, ListStyle, ListType, NumberInput, NumberPart, NumberPartKind,
    NumberSpecial, PluralCategory, PluralOperands, PluralRuleType, ProviderSegmentBoundary,
    RelativeTimeStyle, RelativeTimeTense, RelativeTimeUnit, SegmenterGranularity,
};
use super::segmentation;

const CARDINAL: [PluralCategory; 2] = [PluralCategory::One, PluralCategory::Other];
const ORDINAL: [PluralCategory; 4] = [
    PluralCategory::One,
    PluralCategory::Two,
    PluralCategory::Few,
    PluralCategory::Other,
];

/// The English ordinal rule, on the integer digits of a whole `n`. The rule reads
/// `n` and not `v`, so `1.00` is whole.
fn ordinal(integer: &str) -> PluralCategory {
    let last = |count: usize| {
        integer
            .get(integer.len().saturating_sub(count)..)
            .unwrap_or(integer)
    };
    match (last(1), last(2)) {
        ("1", tens) if tens != "11" => PluralCategory::One,
        ("2", tens) if tens != "12" => PluralCategory::Two,
        ("3", tens) if tens != "13" => PluralCategory::Few,
        _ => PluralCategory::Other,
    }
}

const fn style_index(style: RelativeTimeStyle) -> usize {
    match style {
        RelativeTimeStyle::Long => 0,
        RelativeTimeStyle::Short => 1,
        RelativeTimeStyle::Narrow => 2,
    }
}

/// Unit names by style: singular and plural, long then short, then the narrow
/// suffix, which attaches to the number.
const RELATIVE_UNITS: [(RelativeTimeUnit, [&str; 5]); 8] = [
    (
        RelativeTimeUnit::Second,
        ["second", "seconds", "sec.", "sec.", "s"],
    ),
    (
        RelativeTimeUnit::Minute,
        ["minute", "minutes", "min.", "min.", "min"],
    ),
    (RelativeTimeUnit::Hour, ["hour", "hours", "hr.", "hr.", "h"]),
    (RelativeTimeUnit::Day, ["day", "days", "day", "days", "d"]),
    (RelativeTimeUnit::Week, ["week", "weeks", "wk.", "wk.", "w"]),
    (
        RelativeTimeUnit::Month,
        ["month", "months", "mo.", "mo.", "mo"],
    ),
    (
        RelativeTimeUnit::Quarter,
        ["quarter", "quarters", "qtr.", "qtrs.", "q"],
    ),
    (RelativeTimeUnit::Year, ["year", "years", "yr.", "yr.", "y"]),
];

/// Patterns by style, unit, tense, and whether the count is singular.
static RELATIVE_PATTERNS: LazyLock<BTreeMap<(usize, usize, bool, bool), String>> =
    LazyLock::new(|| {
        let mut patterns = BTreeMap::new();
        for (unit, (_, names)) in RELATIVE_UNITS.iter().enumerate() {
            for future in [false, true] {
                for one in [false, true] {
                    let long = names[usize::from(!one)];
                    let short = names[2 + usize::from(!one)];
                    let spaced = |name: &str| {
                        if future {
                            format!("in {{0}} {name}")
                        } else {
                            format!("{{0}} {name} ago")
                        }
                    };
                    let narrow = if future {
                        format!("in {{0}}{}", names[4])
                    } else {
                        format!("{{0}}{} ago", names[4])
                    };
                    patterns.insert((0, unit, future, one), spaced(long));
                    patterns.insert((1, unit, future, one), spaced(short));
                    patterns.insert((2, unit, future, one), narrow);
                }
            }
        }
        patterns
    });

/// The words for the current, previous, and next unit. Clock units have only
/// the current one.
fn relative_term(unit: RelativeTimeUnit, offset: i64) -> Option<&'static str> {
    use RelativeTimeUnit as Unit;
    Some(match (unit, offset) {
        (Unit::Second, 0) => "now",
        (Unit::Minute, 0) => "this minute",
        (Unit::Hour, 0) => "this hour",
        (Unit::Day, -1) => "yesterday",
        (Unit::Day, 0) => "today",
        (Unit::Day, 1) => "tomorrow",
        (Unit::Week, -1) => "last week",
        (Unit::Week, 0) => "this week",
        (Unit::Week, 1) => "next week",
        (Unit::Month, -1) => "last month",
        (Unit::Month, 0) => "this month",
        (Unit::Month, 1) => "next month",
        (Unit::Quarter, -1) => "last quarter",
        (Unit::Quarter, 0) => "this quarter",
        (Unit::Quarter, 1) => "next quarter",
        (Unit::Year, -1) => "last year",
        (Unit::Year, 0) => "this year",
        (Unit::Year, 1) => "next year",
        _ => return None,
    })
}

/// English names by code, the small set a display name is commonly asked for.
const LANGUAGE_NAMES: &[(&str, &str)] = &[
    ("ar", "Arabic"),
    ("de", "German"),
    ("en", "English"),
    ("en-GB", "British English"),
    ("en-US", "American English"),
    ("es", "Spanish"),
    ("fr", "French"),
    ("hi", "Hindi"),
    ("it", "Italian"),
    ("ja", "Japanese"),
    ("ko", "Korean"),
    ("nl", "Dutch"),
    ("pt", "Portuguese"),
    ("ru", "Russian"),
    ("zh", "Chinese"),
];
const REGION_NAMES: &[(&str, &str)] = &[
    ("BR", "Brazil"),
    ("CA", "Canada"),
    ("CN", "China"),
    ("DE", "Germany"),
    ("ES", "Spain"),
    ("FR", "France"),
    ("GB", "United Kingdom"),
    ("IN", "India"),
    ("IT", "Italy"),
    ("JP", "Japan"),
    ("KR", "South Korea"),
    ("MX", "Mexico"),
    ("RU", "Russia"),
    ("US", "United States"),
];
const SCRIPT_NAMES: &[(&str, &str)] = &[
    ("Arab", "Arabic"),
    ("Cyrl", "Cyrillic"),
    ("Deva", "Devanagari"),
    ("Grek", "Greek"),
    ("Hans", "Simplified Han"),
    ("Hant", "Traditional Han"),
    ("Hebr", "Hebrew"),
    ("Jpan", "Japanese"),
    ("Kore", "Korean"),
    ("Latn", "Latin"),
];
const CALENDAR_NAMES: &[(&str, &str)] = &[
    ("buddhist", "Buddhist Calendar"),
    ("coptic", "Coptic Calendar"),
    ("ethioaa", "Ethiopic Amete Alem Calendar"),
    ("ethiopic", "Ethiopic Calendar"),
    ("gregory", "Gregorian Calendar"),
    ("hebrew", "Hebrew Calendar"),
    ("indian", "Indian National Calendar"),
    ("islamic-civil", "Hijri Calendar (tabular, civil epoch)"),
    (
        "islamic-tbla",
        "Hijri Calendar (tabular, astronomical epoch)",
    ),
    ("iso8601", "ISO-8601 Calendar"),
    ("japanese", "Japanese Calendar"),
    ("persian", "Persian Calendar"),
    ("roc", "Minguo Calendar"),
];
const DATE_TIME_FIELD_NAMES: &[(&str, &str)] = &[
    ("day", "day"),
    ("dayPeriod", "AM/PM"),
    ("era", "era"),
    ("hour", "hour"),
    ("minute", "minute"),
    ("month", "month"),
    ("quarter", "quarter"),
    ("second", "second"),
    ("timeZoneName", "time zone"),
    ("weekOfYear", "week"),
    ("weekday", "day of the week"),
    ("year", "year"),
];

/// Writes an ASCII decimal with grouping into `parts`, in `numbering_system`.
fn number_parts(input: &NumberInput, digits: &[char; 10]) -> Vec<NumberPart> {
    let transliterate = |ascii: &str| -> String {
        ascii
            .chars()
            .map(|character| {
                character
                    .to_digit(10)
                    .map_or(character, |digit| digits[digit as usize])
            })
            .collect()
    };
    let mut parts = Vec::new();
    let mut push = |kind, value: String| parts.push(NumberPart { kind, value });
    let (integer, fraction) = input
        .ascii
        .split_once('.')
        .map_or((input.ascii.as_str(), None), |(left, right)| {
            (left, Some(right))
        });
    let leading = match integer.len() % 3 {
        0 => 3,
        length => length,
    };
    let mut start = 0;
    let mut end = leading.min(integer.len());
    while start < integer.len() {
        if start > 0 {
            push(NumberPartKind::Group, String::from(","));
        }
        push(NumberPartKind::Integer, transliterate(&integer[start..end]));
        start = end;
        end += 3;
    }
    if let Some(fraction) = fraction {
        push(NumberPartKind::Decimal, String::from("."));
        push(NumberPartKind::Fraction, transliterate(fraction));
    }
    parts
}

impl IntlServiceDataProvider for IntlData {
    fn locale_data(&self) -> &dyn LocaleDataProvider {
        self
    }

    fn plural_categories(&self, _locale: &str, rule_type: PluralRuleType) -> &[PluralCategory] {
        match rule_type {
            PluralRuleType::Cardinal => &CARDINAL,
            PluralRuleType::Ordinal => &ORDINAL,
        }
    }

    fn plural_category(
        &self,
        _locale: &str,
        rule_type: PluralRuleType,
        operands: &PluralOperands,
    ) -> Option<PluralCategory> {
        Some(match rule_type {
            PluralRuleType::Cardinal if operands.i == "1" && operands.v == 0 => PluralCategory::One,
            PluralRuleType::Cardinal => PluralCategory::Other,
            PluralRuleType::Ordinal if operands.w == 0 => ordinal(&operands.i),
            PluralRuleType::Ordinal => PluralCategory::Other,
        })
    }

    /// Every English range is `other`, cardinal or ordinal. CLDR says so for the pairs
    /// that it lists, and `other` is its fallback for the rest.
    fn plural_range(
        &self,
        _locale: &str,
        _start: PluralCategory,
        _end: PluralCategory,
    ) -> Option<PluralCategory> {
        Some(PluralCategory::Other)
    }

    fn format_number(
        &self,
        _locale: &str,
        numbering_system: &str,
        input: &NumberInput,
    ) -> Option<FormattedNumber> {
        let digits = numbering_system_digits(numbering_system)?;
        let parts = match input.special {
            Some(NumberSpecial::Nan) => vec![NumberPart {
                kind: NumberPartKind::Nan,
                value: String::from("NaN"),
            }],
            Some(NumberSpecial::Infinity) => vec![NumberPart {
                kind: NumberPartKind::Infinity,
                value: String::from("\u{221e}"),
            }],
            None => number_parts(input, &digits),
        };
        let value = parts.iter().map(|part| part.value.as_str()).collect();
        Some(FormattedNumber { value, parts })
    }

    fn relative_time_auto(
        &self,
        _locale: &str,
        _style: RelativeTimeStyle,
        unit: RelativeTimeUnit,
        offset: i64,
    ) -> Option<&str> {
        relative_term(unit, offset)
    }

    fn relative_time_pattern(
        &self,
        _locale: &str,
        style: RelativeTimeStyle,
        unit: RelativeTimeUnit,
        tense: RelativeTimeTense,
        category: PluralCategory,
    ) -> Option<&str> {
        let unit = RELATIVE_UNITS.iter().position(|(name, _)| *name == unit)?;
        RELATIVE_PATTERNS
            .get(&(
                style_index(style),
                unit,
                tense == RelativeTimeTense::Future,
                category == PluralCategory::One,
            ))
            .map(String::as_str)
    }

    fn list_pattern(
        &self,
        _locale: &str,
        list_type: ListType,
        style: ListStyle,
        position: ListPatternPosition,
    ) -> Option<&str> {
        use ListPatternPosition as Position;
        Some(match (list_type, style, position) {
            (ListType::Unit, ListStyle::Narrow, _) => "{0} {1}",
            (ListType::Unit, _, _)
            | (_, _, Position::Start | Position::Middle)
            | (ListType::Conjunction, ListStyle::Narrow, _) => "{0}, {1}",
            (ListType::Disjunction, _, Position::Pair) => "{0} or {1}",
            (ListType::Disjunction, _, Position::End) => "{0}, or {1}",
            (ListType::Conjunction, ListStyle::Long, Position::Pair) => "{0} and {1}",
            (ListType::Conjunction, ListStyle::Long, Position::End) => "{0}, and {1}",
            (ListType::Conjunction, ListStyle::Short, Position::Pair) => "{0} & {1}",
            (ListType::Conjunction, ListStyle::Short, Position::End) => "{0}, & {1}",
        })
    }

    fn segment_boundaries(
        &self,
        _locale: &str,
        granularity: SegmenterGranularity,
        input: &[u16],
    ) -> Option<Vec<ProviderSegmentBoundary>> {
        Some(segmentation::boundaries(granularity, input))
    }

    fn display_name(
        &self,
        _locale: &str,
        _style: DisplayNamesStyle,
        name_type: DisplayNamesType,
        _language_display: LanguageDisplay,
        code: &str,
    ) -> Option<&str> {
        let table = match name_type {
            DisplayNamesType::Language => LANGUAGE_NAMES,
            DisplayNamesType::Region => REGION_NAMES,
            DisplayNamesType::Script => SCRIPT_NAMES,
            DisplayNamesType::Calendar => CALENDAR_NAMES,
            DisplayNamesType::DateTimeField => DATE_TIME_FIELD_NAMES,
            DisplayNamesType::Currency => {
                return CURRENCY_NAMES
                    .iter()
                    .find(|entry| entry.0 == code)
                    .map(|entry| entry.1);
            }
        };
        table
            .iter()
            .find(|(name, _)| *name == code)
            .map(|(_, text)| *text)
    }
}
