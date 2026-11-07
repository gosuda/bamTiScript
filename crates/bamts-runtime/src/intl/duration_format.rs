//! ECMA-402 `Intl.DurationFormat` mechanics.

use super::locale_data::IntlData;
use super::number_data::NoHostLocale;
use super::number_format::{
    IntlMathematicalValue, NumberFormat, NumberFormatError, NumberFormatOptions, NumberPart,
    UseGroupingOption,
};
use super::plural_rules::{IntlError, ListFormat, ListFormatOptions, ListPartKind};

/// The units a duration has, largest first, as their option names.
pub const UNITS: [&str; 10] = [
    "years",
    "months",
    "weeks",
    "days",
    "hours",
    "minutes",
    "seconds",
    "milliseconds",
    "microseconds",
    "nanoseconds",
];

const SECONDS: usize = 6;

/// How one unit appears. `Fractional` joins the unit above it as a fraction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnitStyle {
    Long,
    Short,
    Narrow,
    Numeric,
    TwoDigit,
    Fractional,
}

impl UnitStyle {
    /// The style's option spelling. A fractional unit reports as numeric.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Long => "long",
            Self::Short => "short",
            Self::Narrow => "narrow",
            Self::Numeric | Self::Fractional => "numeric",
            Self::TwoDigit => "2-digit",
        }
    }

    /// Reads an option value.
    #[must_use]
    pub fn parse(value: &str) -> Self {
        match value {
            "long" => Self::Long,
            "short" => Self::Short,
            "narrow" => Self::Narrow,
            "numeric" => Self::Numeric,
            _ => Self::TwoDigit,
        }
    }

    const fn is_numeric(self) -> bool {
        matches!(self, Self::Numeric | Self::TwoDigit | Self::Fractional)
    }
}

/// The resolved style and display of one unit.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnitOptions {
    pub style: UnitStyle,
    pub always: bool,
}

/// The default style and display of a unit that has no option of its own.
#[must_use]
pub fn default_unit_options(
    unit: usize,
    digital: bool,
    base: UnitStyle,
    previous: Option<UnitStyle>,
) -> (UnitStyle, bool) {
    let is_hms = (4..=SECONDS).contains(&unit);
    if digital {
        (
            if is_hms || unit > SECONDS {
                UnitStyle::Numeric
            } else {
                UnitStyle::Short
            },
            is_hms,
        )
    } else if previous.is_some_and(UnitStyle::is_numeric) {
        (UnitStyle::Numeric, unit == 5 || unit == SECONDS)
    } else {
        (base, false)
    }
}

/// ValidateDurationUnitStyle.
#[must_use]
pub fn is_valid_unit_style(style: UnitStyle, always: bool, previous: Option<UnitStyle>) -> bool {
    !(always && style == UnitStyle::Fractional
        || previous == Some(UnitStyle::Fractional) && style != UnitStyle::Fractional
        || matches!(previous, Some(UnitStyle::Numeric | UnitStyle::TwoDigit))
            && !style.is_numeric())
}

/// The numeric style a unit settles on after its neighbours are known.
#[must_use]
pub fn settled_unit_style(unit: usize, style: UnitStyle, previous: Option<UnitStyle>) -> UnitStyle {
    if (unit == 5 || unit == SECONDS)
        && matches!(previous, Some(UnitStyle::Numeric | UnitStyle::TwoDigit))
    {
        UnitStyle::TwoDigit
    } else {
        style
    }
}

/// One part of a formatted duration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DurationPart {
    pub part_type: &'static str,
    pub value: String,
    pub unit: Option<&'static str>,
}

/// A failure inside the number or list formatters a duration leans on.
#[derive(Clone, Debug)]
pub enum DurationFormatError {
    Number(NumberFormatError),
    List(IntlError),
}

impl std::fmt::Display for DurationFormatError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Number(error) => error.fmt(formatter),
            Self::List(error) => error.fmt(formatter),
        }
    }
}

/// Resolved `Intl.DurationFormat` slots.
#[derive(Clone, Debug)]
pub struct DurationFormat {
    pub locale: String,
    pub numbering_system: String,
    pub style: String,
    pub units: [UnitOptions; 10],
    pub fractional_digits: Option<u8>,
}

/// An exact decimal for a value `digits` places below its unit, in the
/// `sign * integer.fraction` form the number formatter parses.
fn scaled_decimal(value: i128, digits: u32) -> String {
    let divisor = 10_i128.pow(digits);
    let magnitude = value.unsigned_abs();
    let integer = magnitude / divisor.unsigned_abs();
    let fraction = magnitude % divisor.unsigned_abs();
    let sign = if value < 0 { "-" } else { "" };
    format!(
        "{sign}{integer}.{fraction:0width$}",
        width = digits as usize
    )
}

impl DurationFormat {
    /// The number formatter of one unit, given the parts of its options that
    /// depend on the position in the output.
    fn number_format(
        &self,
        unit: usize,
        style: UnitStyle,
        fractional: bool,
        sign_hidden: bool,
        data: &'static IntlData,
    ) -> Result<NumberFormat<'static>, DurationFormatError> {
        let mut options = NumberFormatOptions {
            locale_matcher: Some(String::from("best fit")),
            numbering_system: Some(self.numbering_system.clone()),
            ..NumberFormatOptions::default()
        };
        if fractional {
            options.maximum_fraction_digits = Some(self.fractional_digits.map_or(9.0, f64::from));
            options.minimum_fraction_digits = Some(self.fractional_digits.map_or(0.0, f64::from));
            options.rounding_mode = Some(String::from("trunc"));
        }
        if sign_hidden {
            options.sign_display = Some(String::from("never"));
        }
        if style == UnitStyle::TwoDigit {
            options.minimum_integer_digits = Some(2.0);
        }
        if style.is_numeric() {
            options.use_grouping = Some(UseGroupingOption::Boolean(false));
        } else {
            options.style = Some(String::from("unit"));
            options.unit = Some(UNITS[unit].trim_end_matches('s').to_owned());
            options.unit_display = Some(style.as_str().to_owned());
        }
        NumberFormat::new(
            std::slice::from_ref(&self.locale),
            &options,
            data,
            &NoHostLocale,
        )
        .map_err(DurationFormatError::Number)
    }

    /// PartitionDurationFormatPattern over the ten fields of a duration.
    ///
    /// # Errors
    /// Reports a failure of the number or list formatters.
    pub fn partition(
        &self,
        fields: &[i128; 10],
        data: &'static IntlData,
    ) -> Result<Vec<DurationPart>, DurationFormatError> {
        let negative = fields.iter().any(|field| *field < 0);
        let mut groups: Vec<Vec<DurationPart>> = Vec::new();
        let mut need_separator = false;
        let mut sign_shown = false;
        for (unit, options) in self.units.iter().enumerate() {
            let singular = UNITS[unit].trim_end_matches('s');
            let mut value = fields[unit];
            // A numeric seconds or sub-second unit takes in everything below it.
            let next_numeric =
                (SECONDS..9).contains(&unit) && self.units[unit + 1].style == UnitStyle::Fractional;
            let mut exact = None;
            if next_numeric {
                let digits = 3 * (9 - unit as u32);
                let mut total = fields[9];
                for (index, factor) in [(8, 3), (7, 6), (6, 9)] {
                    if index >= unit {
                        total += fields[index] * 10_i128.pow(factor);
                    }
                }
                if fields[unit + 1..].iter().all(|field| *field == 0) {
                    value = fields[unit];
                } else {
                    value = total;
                    exact = Some(scaled_decimal(total, digits));
                }
            }
            let minutes_needed = unit == 5
                && need_separator
                && (self.units[SECONDS].always
                    || fields[SECONDS..].iter().any(|field| *field != 0));
            if value != 0 || options.always || minutes_needed {
                let hide_sign = sign_shown;
                sign_shown = true;
                let number =
                    self.number_format(unit, options.style, next_numeric, hide_sign, data)?;
                let parts =
                    self.unit_parts(&number, value, exact.as_deref(), negative && !hide_sign)?;
                let tagged = parts.into_iter().map(|part| DurationPart {
                    part_type: part.part_type.as_str(),
                    value: part.value,
                    unit: Some(singular),
                });
                if need_separator {
                    let list = groups.last_mut().expect("a separator follows a group");
                    list.push(DurationPart {
                        part_type: "literal",
                        value: String::from(":"),
                        unit: None,
                    });
                    list.extend(tagged);
                } else {
                    groups.push(tagged.collect());
                    need_separator = options.style.is_numeric();
                }
            }
            if next_numeric {
                break;
            }
        }
        self.join_groups(groups, data)
    }

    fn unit_parts(
        &self,
        number: &NumberFormat<'static>,
        value: i128,
        exact: Option<&str>,
        keep_negative_zero: bool,
    ) -> Result<Vec<NumberPart>, DurationFormatError> {
        let mathematical = match exact {
            Some(text) => IntlMathematicalValue::from_decimal_string(text),
            None if value == 0 && keep_negative_zero => Ok(IntlMathematicalValue::from_f64(-0.0)),
            None => IntlMathematicalValue::from_bigint(&value.to_string()),
        }
        .map_err(DurationFormatError::Number)?;
        number
            .format_to_parts(&mathematical)
            .map_err(DurationFormatError::Number)
    }

    fn join_groups(
        &self,
        groups: Vec<Vec<DurationPart>>,
        data: &'static IntlData,
    ) -> Result<Vec<DurationPart>, DurationFormatError> {
        let style = if self.style == "digital" {
            "short"
        } else {
            self.style.as_str()
        };
        let list = ListFormat::try_new(
            std::slice::from_ref(&self.locale),
            &ListFormatOptions {
                locale_matcher: Some(String::from("best fit")),
                list_type: Some(String::from("unit")),
                style: Some(style.to_owned()),
            },
            data,
            &NoHostLocale,
        )
        .map_err(DurationFormatError::List)?;
        let strings: Vec<String> = groups
            .iter()
            .map(|parts| parts.iter().map(|part| part.value.as_str()).collect())
            .collect();
        let formatted = list
            .format_to_parts(&strings)
            .map_err(DurationFormatError::List)?;
        let mut groups = groups.into_iter();
        let mut result = Vec::new();
        for part in formatted {
            match part.kind {
                ListPartKind::Element => result.extend(groups.next().into_iter().flatten()),
                ListPartKind::Literal => result.push(DurationPart {
                    part_type: "literal",
                    value: part.value,
                    unit: None,
                }),
            }
        }
        Ok(result)
    }
}
