//! English number data: symbols, patterns, currencies, and units.

use super::locale_data::{IntlData, numbering_system_digits};
use super::number_format::{
    CompactDisplay, CompactPattern, CurrencyDisplay, CurrencySign, GroupingSizes,
    NumberFormatDataProvider, NumberPatternRequest, NumberPatternSet, NumberStyle, NumberSymbols,
    PluralCategory, PluralOperands, RangePatterns, UnitDisplay,
};

/// Currencies with other than two minor units, from ISO 4217.
const CURRENCY_MINOR_UNITS: &[(&str, u8)] = &[
    ("BHD", 3),
    ("BIF", 0),
    ("CLF", 4),
    ("CLP", 0),
    ("DJF", 0),
    ("GNF", 0),
    ("IQD", 3),
    ("ISK", 0),
    ("JOD", 3),
    ("JPY", 0),
    ("KMF", 0),
    ("KRW", 0),
    ("KWD", 3),
    ("LYD", 3),
    ("OMR", 3),
    ("PYG", 0),
    ("RWF", 0),
    ("TND", 3),
    ("UGX", 0),
    ("UYI", 0),
    ("UYW", 4),
    ("VND", 0),
    ("VUV", 0),
    ("XAF", 0),
    ("XOF", 0),
    ("XPF", 0),
];

/// English currency symbols: code, symbol, narrow symbol.
const CURRENCY_SYMBOLS: &[(&str, &str, &str)] = &[
    ("AUD", "A$", "$"),
    ("BRL", "R$", "R$"),
    ("CAD", "CA$", "$"),
    ("CNY", "CN\u{a5}", "\u{a5}"),
    ("EUR", "\u{20ac}", "\u{20ac}"),
    ("GBP", "\u{a3}", "\u{a3}"),
    ("HKD", "HK$", "$"),
    ("ILS", "\u{20aa}", "\u{20aa}"),
    ("INR", "\u{20b9}", "\u{20b9}"),
    ("JPY", "\u{a5}", "\u{a5}"),
    ("KRW", "\u{20a9}", "\u{20a9}"),
    ("MXN", "MX$", "$"),
    ("NZD", "NZ$", "$"),
    ("TWD", "NT$", "$"),
    ("USD", "$", "$"),
    ("VND", "\u{20ab}", "\u{20ab}"),
    ("XAF", "FCFA", "FCFA"),
    ("XCD", "EC$", "$"),
    ("XOF", "F\u{202f}CFA", "F\u{202f}CFA"),
    ("XPF", "CFPF", "CFPF"),
];

/// English currency names: code, singular, plural.
pub(super) const CURRENCY_NAMES: &[(&str, &str, &str)] = &[
    ("AUD", "Australian dollar", "Australian dollars"),
    ("BRL", "Brazilian real", "Brazilian reals"),
    ("CAD", "Canadian dollar", "Canadian dollars"),
    ("CHF", "Swiss franc", "Swiss francs"),
    ("CNY", "Chinese yuan", "Chinese yuan"),
    ("EUR", "euro", "euros"),
    ("GBP", "British pound", "British pounds"),
    ("INR", "Indian rupee", "Indian rupees"),
    ("JPY", "Japanese yen", "Japanese yen"),
    ("KRW", "South Korean won", "South Korean won"),
    ("MXN", "Mexican peso", "Mexican pesos"),
    ("RUB", "Russian ruble", "Russian rubles"),
    ("USD", "US dollar", "US dollars"),
];

/// English simple units: identifier, short, narrow, long singular, long plural.
pub(super) const UNITS: &[(&str, &str, &str, &str, &str)] = &[
    ("acre", "ac", "ac", "acre", "acres"),
    ("bit", "bit", "bit", "bit", "bits"),
    ("byte", "byte", "B", "byte", "bytes"),
    (
        "celsius",
        "\u{b0}C",
        "\u{b0}C",
        "degree Celsius",
        "degrees Celsius",
    ),
    ("centimeter", "cm", "cm", "centimeter", "centimeters"),
    ("day", "day", "d", "day", "days"),
    ("degree", "deg", "\u{b0}", "degree", "degrees"),
    (
        "fahrenheit",
        "\u{b0}F",
        "\u{b0}",
        "degree Fahrenheit",
        "degrees Fahrenheit",
    ),
    (
        "fluid-ounce",
        "fl oz",
        "fl oz",
        "fluid ounce",
        "fluid ounces",
    ),
    ("foot", "ft", "\u{2032}", "foot", "feet"),
    ("gallon", "gal", "gal", "gallon", "gallons"),
    ("gigabit", "Gb", "Gb", "gigabit", "gigabits"),
    ("gigabyte", "GB", "GB", "gigabyte", "gigabytes"),
    ("gram", "g", "g", "gram", "grams"),
    ("hectare", "ha", "ha", "hectare", "hectares"),
    ("hour", "hr", "h", "hour", "hours"),
    ("inch", "in", "\u{2033}", "inch", "inches"),
    ("kilobit", "kb", "kb", "kilobit", "kilobits"),
    ("kilobyte", "kB", "kB", "kilobyte", "kilobytes"),
    ("kilogram", "kg", "kg", "kilogram", "kilograms"),
    ("kilometer", "km", "km", "kilometer", "kilometers"),
    ("liter", "L", "L", "liter", "liters"),
    ("megabit", "Mb", "Mb", "megabit", "megabits"),
    ("megabyte", "MB", "MB", "megabyte", "megabytes"),
    ("meter", "m", "m", "meter", "meters"),
    (
        "microsecond",
        "\u{3bc}s",
        "\u{3bc}s",
        "microsecond",
        "microseconds",
    ),
    ("mile", "mi", "mi", "mile", "miles"),
    (
        "mile-scandinavian",
        "smi",
        "smi",
        "mile-scandinavian",
        "miles-scandinavian",
    ),
    ("milliliter", "mL", "mL", "milliliter", "milliliters"),
    ("millimeter", "mm", "mm", "millimeter", "millimeters"),
    ("millisecond", "ms", "ms", "millisecond", "milliseconds"),
    ("minute", "min", "m", "minute", "minutes"),
    ("month", "mth", "m", "month", "months"),
    ("nanosecond", "ns", "ns", "nanosecond", "nanoseconds"),
    ("ounce", "oz", "oz", "ounce", "ounces"),
    ("percent", "%", "%", "percent", "percent"),
    ("petabyte", "PB", "PB", "petabyte", "petabytes"),
    ("pound", "lb", "#", "pound", "pounds"),
    ("second", "sec", "s", "second", "seconds"),
    ("stone", "st", "st", "stone", "stones"),
    ("terabit", "Tb", "Tb", "terabit", "terabits"),
    ("terabyte", "TB", "TB", "terabyte", "terabytes"),
    ("week", "wk", "w", "week", "weeks"),
    ("yard", "yd", "yd", "yard", "yards"),
    ("year", "yr", "y", "year", "years"),
];

/// Short forms whose plural is not the singular.
const SHORT_PLURALS: &[(&str, &str)] = &[
    ("day", "days"),
    ("month", "mths"),
    ("week", "wks"),
    ("year", "yrs"),
];

/// Abbreviations of time units after a slash, where the short forms give way.
const PER_UNITS: &[(&str, &str)] = &[
    ("day", "d"),
    ("hour", "h"),
    ("month", "m"),
    ("second", "s"),
    ("week", "w"),
    ("year", "y"),
];

/// Compound units English abbreviates as a whole.
const WHOLE_UNITS: &[(&str, &str)] = &[("mile-per-gallon", "mpg"), ("mile-per-hour", "mph")];

/// Units whose abbreviation attaches to the number without a space.
fn attaches(unit: &str, display: UnitDisplay) -> bool {
    matches!(unit, "celsius" | "fahrenheit" | "percent") && display != UnitDisplay::Long
        || display == UnitDisplay::Narrow
}

fn simple_unit(unit: &str, display: UnitDisplay, category: PluralCategory) -> Option<String> {
    let index = UNITS.binary_search_by(|entry| entry.0.cmp(unit)).ok()?;
    let (_, short, narrow, singular, plural) = UNITS[index];
    let one = category == PluralCategory::One;
    Some(
        match display {
            UnitDisplay::Short if one => short,
            UnitDisplay::Short => SHORT_PLURALS
                .iter()
                .find(|(name, _)| *name == unit)
                .map_or(short, |(_, plural)| plural),
            UnitDisplay::Narrow => narrow,
            UnitDisplay::Long if one => singular,
            UnitDisplay::Long => plural,
        }
        .to_owned(),
    )
}

fn unit_text(unit: &str, display: UnitDisplay, category: PluralCategory) -> Option<String> {
    let Some((numerator, denominator)) = unit.split_once("-per-") else {
        return simple_unit(unit, display, category);
    };
    if display != UnitDisplay::Long
        && let Some((_, whole)) = WHOLE_UNITS.iter().find(|(name, _)| *name == unit)
    {
        return Some((*whole).to_owned());
    }
    let top = simple_unit(numerator, display, category)?;
    let bottom = match PER_UNITS.iter().find(|(name, _)| *name == denominator) {
        Some((_, per)) if display != UnitDisplay::Long => (*per).to_owned(),
        _ => simple_unit(denominator, display, PluralCategory::One)?,
    };
    Some(if display == UnitDisplay::Long {
        format!("{top} per {bottom}")
    } else {
        format!("{top}/{bottom}")
    })
}

fn signed(pattern: &str) -> NumberPatternSet {
    NumberPatternSet {
        zero: pattern.to_owned(),
        positive: format!("{{plusSign}}{pattern}"),
        negative: format!("{{minusSign}}{pattern}"),
    }
}

/// A prefix that ends in a letter is set off from the number.
fn currency_prefix_pattern(currency: &str, display: CurrencyDisplay) -> String {
    let known = CURRENCY_SYMBOLS.iter().any(|entry| entry.0 == currency);
    let letters = display == CurrencyDisplay::Code || !known;
    if letters {
        String::from("{currencyPrefix}\u{a0}{number}")
    } else {
        String::from("{currencyPrefix}{number}")
    }
}

impl NumberFormatDataProvider for IntlData {
    fn number_symbols(&self, _data_locale: &str, numbering_system: &str) -> Option<NumberSymbols> {
        Some(NumberSymbols {
            digits: numbering_system_digits(numbering_system)?,
            decimal: String::from("."),
            group: String::from(","),
            plus_sign: String::from("+"),
            minus_sign: String::from("-"),
            percent_sign: String::from("%"),
            infinity: String::from("\u{221e}"),
            nan: String::from("NaN"),
            exponent_separator: String::from("E"),
            approximately_sign: String::from("~"),
        })
    }

    fn grouping_sizes(&self, _data_locale: &str, _numbering_system: &str) -> Option<GroupingSizes> {
        Some(GroupingSizes {
            primary: 3,
            secondary: 3,
            minimum_grouping_digits: 1,
        })
    }

    fn number_patterns(
        &self,
        _data_locale: &str,
        request: NumberPatternRequest<'_>,
    ) -> Option<NumberPatternSet> {
        Some(match request.style {
            NumberStyle::Decimal => signed("{number}"),
            NumberStyle::Percent => signed("{number}{percentSign}"),
            NumberStyle::Currency => {
                let display = request.currency_display?;
                if display == CurrencyDisplay::Name {
                    return Some(signed("{number} {currencySuffix}"));
                }
                let pattern = currency_prefix_pattern(request.currency?, display);
                let mut set = signed(&pattern);
                if request.currency_sign == Some(CurrencySign::Accounting) {
                    set.negative = format!("({pattern})");
                }
                set
            }
            NumberStyle::Unit => {
                let unit = request.unit?;
                let display = request.unit_display?;
                signed(if attaches(unit, display) {
                    "{number}{unitSuffix}"
                } else {
                    "{number} {unitSuffix}"
                })
            }
        })
    }

    fn scientific_pattern(&self, _data_locale: &str) -> Option<String> {
        Some(String::from(
            "{number}{scientificSeparator}{scientificExponent}",
        ))
    }

    fn compact_exponent(
        &self,
        _data_locale: &str,
        _display: CompactDisplay,
        magnitude: i32,
    ) -> Option<i32> {
        Some(if magnitude < 3 {
            0
        } else {
            (magnitude / 3).min(4) * 3
        })
    }

    fn compact_pattern(
        &self,
        _data_locale: &str,
        display: CompactDisplay,
        exponent: i32,
        _category: PluralCategory,
    ) -> Option<CompactPattern> {
        let (short, long) = match exponent {
            3 => ("K", "thousand"),
            6 => ("M", "million"),
            9 => ("B", "billion"),
            12 => ("T", "trillion"),
            _ => return None,
        };
        Some(match display {
            CompactDisplay::Short => CompactPattern {
                pattern: String::from("{number}{compactSymbol}"),
                display: short.to_owned(),
            },
            CompactDisplay::Long => CompactPattern {
                pattern: String::from("{number} {compactName}"),
                display: long.to_owned(),
            },
        })
    }

    fn currency_minor_units(&self, currency: &str) -> Option<u8> {
        CURRENCY_MINOR_UNITS
            .binary_search_by(|(code, _)| (*code).cmp(currency))
            .ok()
            .map(|index| CURRENCY_MINOR_UNITS[index].1)
    }

    fn currency_display(
        &self,
        _data_locale: &str,
        currency: &str,
        display: CurrencyDisplay,
        category: PluralCategory,
    ) -> Option<String> {
        match display {
            CurrencyDisplay::Code => Some(currency.to_owned()),
            CurrencyDisplay::Symbol | CurrencyDisplay::NarrowSymbol => {
                let (_, symbol, narrow) =
                    CURRENCY_SYMBOLS.iter().find(|entry| entry.0 == currency)?;
                Some(
                    if display == CurrencyDisplay::Symbol {
                        symbol
                    } else {
                        narrow
                    }
                    .to_string(),
                )
            }
            CurrencyDisplay::Name => {
                let (_, singular, plural) =
                    CURRENCY_NAMES.iter().find(|entry| entry.0 == currency)?;
                Some(
                    if category == PluralCategory::One {
                        singular
                    } else {
                        plural
                    }
                    .to_string(),
                )
            }
        }
    }

    fn unit_display(
        &self,
        _data_locale: &str,
        unit: &str,
        display: UnitDisplay,
        category: PluralCategory,
    ) -> Option<String> {
        unit_text(unit, display, category)
    }

    fn plural_category(&self, _data_locale: &str, operands: &PluralOperands) -> PluralCategory {
        if operands.integer_digits == "1" && operands.visible_fraction_digits == 0 {
            PluralCategory::One
        } else {
            PluralCategory::Other
        }
    }

    fn range_patterns(&self, _data_locale: &str, _numbering_system: &str) -> Option<RangePatterns> {
        Some(RangePatterns {
            separator: String::from("\u{2013}"),
            approximate: String::from("{approximatelySign}{number}"),
        })
    }
}

/// The host locale hook of this runtime: no preference, so the provider's
/// default stands.
pub struct NoHostLocale;

impl super::locale_negotiation::HostLocaleHook for NoHostLocale {
    fn preferred_locales(&self) -> Vec<String> {
        Vec::new()
    }
}
