//! Deterministic ECMA-402 number formatting.
//!
//! Locale negotiation is shared with [`super::locale_negotiation`]. All
//! symbols, patterns, plural selection, grouping rules, compact notation data,
//! and currency metadata are supplied by [`NumberFormatDataProvider`]; this
//! module never consults the operating system and contains no locale fallback.
//!
//! The rounding pipeline follows ECMA-402 `SetNumberFormatDigitOptions`,
//! `FormatNumericToString`, `ToRawPrecision`, and `ToRawFixed`. A JavaScript
//! Number is first converted through its shortest decimal representation, as
//! required by `ToIntlMathematicalValue`, rather than rounded as its exact
//! binary IEEE-754 value.

use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;

use super::locale_negotiation::{
    HostLocaleHook, LocaleDataProvider, LocaleError, LocaleMatcher, default_locale, resolve_locale,
};

/// The failure category visible to a runtime adapter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NumberFormatErrorKind {
    /// An option or numeric string is outside the ECMA-402 domain.
    RangeError,
    /// Required options are absent or mutually incompatible in a type-invalid way.
    TypeError,
    /// Required provider data is absent.
    MissingData,
    /// Provider data violates the NumberFormat data contract.
    InvalidData,
}

/// A NumberFormat construction or formatting failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NumberFormatError {
    /// Runtime-visible failure category.
    pub kind: NumberFormatErrorKind,
    /// Stable diagnostic text for host reporting.
    pub message: String,
}

impl NumberFormatError {
    fn range(message: impl Into<String>) -> Self {
        Self {
            kind: NumberFormatErrorKind::RangeError,
            message: message.into(),
        }
    }

    fn type_error(message: impl Into<String>) -> Self {
        Self {
            kind: NumberFormatErrorKind::TypeError,
            message: message.into(),
        }
    }

    fn missing(message: impl Into<String>) -> Self {
        Self {
            kind: NumberFormatErrorKind::MissingData,
            message: message.into(),
        }
    }

    fn invalid_data(message: impl Into<String>) -> Self {
        Self {
            kind: NumberFormatErrorKind::InvalidData,
            message: message.into(),
        }
    }
}

impl fmt::Display for NumberFormatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl Error for NumberFormatError {}

impl From<LocaleError> for NumberFormatError {
    fn from(error: LocaleError) -> Self {
        Self::range(error.to_string())
    }
}

/// `style` resolved by `SetNumberFormatUnitOptions`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NumberStyle {
    Decimal,
    Percent,
    Currency,
    Unit,
}

impl NumberStyle {
    /// ECMA-402 option spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Decimal => "decimal",
            Self::Percent => "percent",
            Self::Currency => "currency",
            Self::Unit => "unit",
        }
    }
}

/// `currencyDisplay` resolved option.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CurrencyDisplay {
    Code,
    Symbol,
    NarrowSymbol,
    Name,
}

impl CurrencyDisplay {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Code => "code",
            Self::Symbol => "symbol",
            Self::NarrowSymbol => "narrowSymbol",
            Self::Name => "name",
        }
    }
}

/// `currencySign` resolved option.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CurrencySign {
    Standard,
    Accounting,
}

impl CurrencySign {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Standard => "standard",
            Self::Accounting => "accounting",
        }
    }
}

/// `unitDisplay` resolved option.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnitDisplay {
    Short,
    Narrow,
    Long,
}

impl UnitDisplay {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Short => "short",
            Self::Narrow => "narrow",
            Self::Long => "long",
        }
    }
}

/// Number notation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Notation {
    Standard,
    Scientific,
    Engineering,
    Compact,
}

impl Notation {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Standard => "standard",
            Self::Scientific => "scientific",
            Self::Engineering => "engineering",
            Self::Compact => "compact",
        }
    }
}

/// Compact notation width.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CompactDisplay {
    Short,
    Long,
}

impl CompactDisplay {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Short => "short",
            Self::Long => "long",
        }
    }
}

/// `signDisplay` resolved option.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SignDisplay {
    Auto,
    Never,
    Always,
    ExceptZero,
    Negative,
}

impl SignDisplay {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::Never => "never",
            Self::Always => "always",
            Self::ExceptZero => "exceptZero",
            Self::Negative => "negative",
        }
    }
}

/// ECMA-402 rounding mode.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RoundingMode {
    Ceil,
    Floor,
    Expand,
    Trunc,
    HalfCeil,
    HalfFloor,
    HalfExpand,
    HalfTrunc,
    HalfEven,
}

impl RoundingMode {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Ceil => "ceil",
            Self::Floor => "floor",
            Self::Expand => "expand",
            Self::Trunc => "trunc",
            Self::HalfCeil => "halfCeil",
            Self::HalfFloor => "halfFloor",
            Self::HalfExpand => "halfExpand",
            Self::HalfTrunc => "halfTrunc",
            Self::HalfEven => "halfEven",
        }
    }

    const fn unsigned(self, negative: bool) -> UnsignedRoundingMode {
        match (self, negative) {
            (Self::Ceil, false) | (Self::Floor, true) | (Self::Expand, _) => {
                UnsignedRoundingMode::Infinity
            }
            (Self::Ceil, true) | (Self::Floor, false) | (Self::Trunc, _) => {
                UnsignedRoundingMode::Zero
            }
            (Self::HalfCeil, false) | (Self::HalfFloor, true) | (Self::HalfExpand, _) => {
                UnsignedRoundingMode::HalfInfinity
            }
            (Self::HalfCeil, true) | (Self::HalfFloor, false) | (Self::HalfTrunc, _) => {
                UnsignedRoundingMode::HalfZero
            }
            (Self::HalfEven, _) => UnsignedRoundingMode::HalfEven,
        }
    }
}

/// `roundingPriority` and the computed resolved priority.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RoundingPriority {
    Auto,
    MorePrecision,
    LessPrecision,
}

impl RoundingPriority {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::MorePrecision => "morePrecision",
            Self::LessPrecision => "lessPrecision",
        }
    }
}

/// `trailingZeroDisplay` resolved option.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TrailingZeroDisplay {
    Auto,
    StripIfInteger,
}

impl TrailingZeroDisplay {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::StripIfInteger => "stripIfInteger",
        }
    }
}

/// Input representation for the Boolean-or-string `useGrouping` option.
#[derive(Clone, Debug, PartialEq)]
pub enum UseGroupingOption {
    Boolean(bool),
    String(String),
}

/// Resolved grouping policy.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UseGrouping {
    False,
    Min2,
    Auto,
    Always,
}

/// Constructor options after JavaScript property access and primitive coercion.
///
/// String-valued fields are still validated here. Numeric fields correspond to
/// the result of ECMAScript `ToNumber`; this layer performs finiteness, range,
/// and flooring checks from `DefaultNumberOption`.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct NumberFormatOptions {
    pub locale_matcher: Option<String>,
    pub numbering_system: Option<String>,
    pub style: Option<String>,
    pub currency: Option<String>,
    pub currency_display: Option<String>,
    pub currency_sign: Option<String>,
    pub unit: Option<String>,
    pub unit_display: Option<String>,
    pub notation: Option<String>,
    pub compact_display: Option<String>,
    pub use_grouping: Option<UseGroupingOption>,
    pub sign_display: Option<String>,
    pub minimum_integer_digits: Option<f64>,
    pub minimum_fraction_digits: Option<f64>,
    pub maximum_fraction_digits: Option<f64>,
    pub minimum_significant_digits: Option<f64>,
    pub maximum_significant_digits: Option<f64>,
    pub rounding_increment: Option<f64>,
    pub rounding_mode: Option<String>,
    pub rounding_priority: Option<String>,
    pub trailing_zero_display: Option<String>,
}

/// Number-system symbols for one locale and numbering system.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NumberSymbols {
    /// Simple per-digit numbering-system mapping. Providers must advertise only
    /// numbering systems for which this mapping is correct.
    pub digits: [char; 10],
    pub decimal: String,
    pub group: String,
    pub plus_sign: String,
    pub minus_sign: String,
    pub percent_sign: String,
    pub infinity: String,
    pub nan: String,
    pub exponent_separator: String,
    pub approximately_sign: String,
}

/// Locale grouping geometry derived from CLDR number patterns.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GroupingSizes {
    /// Digits in the rightmost group.
    pub primary: usize,
    /// Digits in each preceding group.
    pub secondary: usize,
    /// Locale default minimum number of leading digits before grouping starts.
    pub minimum_grouping_digits: usize,
}

/// The sign-dependent leaves of ECMA-402 `[[patterns]]`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NumberPatternSet {
    pub zero: String,
    pub positive: String,
    pub negative: String,
}

/// Resolved style information used to query a provider pattern tree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NumberPatternRequest<'a> {
    pub style: NumberStyle,
    pub currency: Option<&'a str>,
    pub currency_display: Option<CurrencyDisplay>,
    pub currency_sign: Option<CurrencySign>,
    pub unit: Option<&'a str>,
    pub unit_display: Option<UnitDisplay>,
}

/// A compact notation pattern and its locale-dependent display text.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompactPattern {
    /// Pattern string containing `{number}` and `{compactSymbol}` or
    /// `{compactName}`.
    pub pattern: String,
    /// The actual suffix/prefix for the selected exponent and plural category.
    pub display: String,
}

/// Range separator and approximate-value pattern.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RangePatterns {
    pub separator: String,
    /// Pattern containing `{number}` and optionally `{approximatelySign}`.
    pub approximate: String,
}

/// CLDR cardinal plural categories.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PluralCategory {
    Zero,
    One,
    Two,
    Few,
    Many,
    Other,
}

/// Visible-number operands supplied to a provider's CLDR plural evaluator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PluralOperands {
    /// Absolute integer digits, normalized to one leading zero when zero.
    pub integer_digits: String,
    /// All visible fraction digits, including leading and trailing zeros.
    pub fraction_digits: String,
    /// Visible fraction digits after removing trailing zeros.
    pub fraction_digits_without_trailing_zeros: String,
    pub visible_fraction_digits: usize,
    pub visible_fraction_digits_without_trailing_zeros: usize,
    /// Compact decimal exponent (`e`/`c` in CLDR operands).
    pub exponent: i32,
}

/// Locale, pattern, and metadata queries needed by NumberFormat.
///
/// A conforming provider supplies complete data for every locale and numbering
/// system it advertises through [`LocaleDataProvider::key_values`]. Returning
/// `None` reports an incomplete provider rather than an unsupported valid
/// ECMA-402 input.
pub trait NumberFormatDataProvider: LocaleDataProvider {
    fn number_symbols(&self, data_locale: &str, numbering_system: &str) -> Option<NumberSymbols>;
    fn grouping_sizes(&self, data_locale: &str, numbering_system: &str) -> Option<GroupingSizes>;
    fn number_patterns(
        &self,
        data_locale: &str,
        request: NumberPatternRequest<'_>,
    ) -> Option<NumberPatternSet>;
    fn scientific_pattern(&self, data_locale: &str) -> Option<String>;
    /// ILD `ComputeExponentForMagnitude` result for compact notation.
    fn compact_exponent(
        &self,
        data_locale: &str,
        display: CompactDisplay,
        magnitude: i32,
    ) -> Option<i32>;
    fn compact_pattern(
        &self,
        data_locale: &str,
        display: CompactDisplay,
        exponent: i32,
        category: PluralCategory,
    ) -> Option<CompactPattern>;
    /// Fraction digits for a known currency. `None` invokes the normative
    /// `CurrencyDigits` fallback of two.
    fn currency_minor_units(&self, currency: &str) -> Option<u8>;
    /// Localized currency text. `None` invokes the normative ISO-code fallback.
    fn currency_display(
        &self,
        data_locale: &str,
        currency: &str,
        display: CurrencyDisplay,
        category: PluralCategory,
    ) -> Option<String>;
    fn unit_display(
        &self,
        data_locale: &str,
        unit: &str,
        display: UnitDisplay,
        category: PluralCategory,
    ) -> Option<String>;
    fn plural_category(&self, data_locale: &str, operands: &PluralOperands) -> PluralCategory;
    fn range_patterns(&self, data_locale: &str, numbering_system: &str) -> Option<RangePatterns>;
}

/// A NumberFormat part type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NumberPartType {
    Integer,
    Group,
    Decimal,
    Fraction,
    PlusSign,
    MinusSign,
    PercentSign,
    Currency,
    Unit,
    Literal,
    Compact,
    ExponentInteger,
    ExponentMinusSign,
    ExponentSeparator,
    Nan,
    Infinity,
    ApproximatelySign,
    Unknown,
}

impl NumberPartType {
    /// JavaScript `formatToParts` type string.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Integer => "integer",
            Self::Group => "group",
            Self::Decimal => "decimal",
            Self::Fraction => "fraction",
            Self::PlusSign => "plusSign",
            Self::MinusSign => "minusSign",
            Self::PercentSign => "percentSign",
            Self::Currency => "currency",
            Self::Unit => "unit",
            Self::Literal => "literal",
            Self::Compact => "compact",
            Self::ExponentInteger => "exponentInteger",
            Self::ExponentMinusSign => "exponentMinusSign",
            Self::ExponentSeparator => "exponentSeparator",
            Self::Nan => "nan",
            Self::Infinity => "infinity",
            Self::ApproximatelySign => "approximatelySign",
            Self::Unknown => "unknown",
        }
    }
}

/// One `formatToParts` result element.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NumberPart {
    pub part_type: NumberPartType,
    pub value: String,
}

/// `formatRangeToParts` source annotation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RangeSource {
    StartRange,
    EndRange,
    Shared,
}

impl RangeSource {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::StartRange => "startRange",
            Self::EndRange => "endRange",
            Self::Shared => "shared",
        }
    }
}

/// One `formatRangeToParts` result element.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NumberRangePart {
    pub part_type: NumberPartType,
    pub value: String,
    pub source: RangeSource,
}

/// Resolved options exposed without JavaScript object-allocation concerns.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedNumberFormatOptions {
    pub locale: String,
    pub numbering_system: String,
    pub style: NumberStyle,
    pub currency: Option<String>,
    pub currency_display: Option<CurrencyDisplay>,
    pub currency_sign: Option<CurrencySign>,
    pub unit: Option<String>,
    pub unit_display: Option<UnitDisplay>,
    pub minimum_integer_digits: u8,
    pub minimum_fraction_digits: Option<u8>,
    pub maximum_fraction_digits: Option<u8>,
    pub minimum_significant_digits: Option<u8>,
    pub maximum_significant_digits: Option<u8>,
    pub use_grouping: UseGrouping,
    pub notation: Notation,
    pub compact_display: Option<CompactDisplay>,
    pub sign_display: SignDisplay,
    pub rounding_increment: u16,
    pub rounding_mode: RoundingMode,
    pub rounding_priority: RoundingPriority,
    pub trailing_zero_display: TrailingZeroDisplay,
}

/// Exact finite decimal magnitude, normalized without leading or trailing zeroes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Decimal {
    digits: Vec<u8>,
    /// Value is `digits × 10^exponent`.
    exponent: i32,
}

impl Decimal {
    fn zero() -> Self {
        Self {
            digits: vec![0],
            exponent: 0,
        }
    }

    fn new(mut digits: Vec<u8>, mut exponent: i32) -> Result<Self, NumberFormatError> {
        let first_nonzero = digits.iter().position(|digit| *digit != 0);
        let Some(first_nonzero) = first_nonzero else {
            return Ok(Self::zero());
        };
        digits.drain(..first_nonzero);
        while digits.len() > 1 && digits.last() == Some(&0) {
            digits.pop();
            exponent = exponent
                .checked_add(1)
                .ok_or_else(|| NumberFormatError::range("decimal exponent is out of range"))?;
        }
        Ok(Self { digits, exponent })
    }

    fn is_zero(&self) -> bool {
        self.digits == [0]
    }

    fn is_integer(&self) -> bool {
        self.is_zero() || self.exponent >= 0
    }

    /// The value, when it is an integer of at most 19 digits.
    fn small_integer(&self) -> Option<i128> {
        let zeros = usize::try_from(self.exponent).ok()?;
        if self.digits.len().saturating_add(zeros) > 19 {
            return None;
        }
        let coefficient = self
            .digits
            .iter()
            .fold(0_i128, |value, digit| value * 10 + i128::from(*digit));
        Some((0..zeros).fold(coefficient, |value, _| value * 10))
    }

    fn magnitude(&self) -> Result<i32, NumberFormatError> {
        if self.is_zero() {
            return Ok(0);
        }
        let length = i32::try_from(self.digits.len())
            .map_err(|_| NumberFormatError::range("decimal coefficient is too long"))?;
        length
            .checked_add(self.exponent)
            .and_then(|value| value.checked_sub(1))
            .ok_or_else(|| NumberFormatError::range("decimal magnitude is out of range"))
    }

    fn shifted(&self, places: i32) -> Result<Self, NumberFormatError> {
        if self.is_zero() {
            return Ok(Self::zero());
        }
        let exponent = self
            .exponent
            .checked_add(places)
            .ok_or_else(|| NumberFormatError::range("decimal exponent is out of range"))?;
        Ok(Self {
            digits: self.digits.clone(),
            exponent,
        })
    }
}

/// Exact value accepted by the formatter after `ToIntlMathematicalValue`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IntlMathematicalValue {
    Finite { negative: bool, magnitude: Decimal },
    NegativeZero,
    PositiveInfinity,
    NegativeInfinity,
    Nan,
}

impl IntlMathematicalValue {
    /// Applies Number-to-shortest-decimal semantics from `ToIntlMathematicalValue`.
    #[must_use]
    pub fn from_f64(value: f64) -> Self {
        if value.is_nan() {
            return Self::Nan;
        }
        if value == f64::INFINITY {
            return Self::PositiveInfinity;
        }
        if value == f64::NEG_INFINITY {
            return Self::NegativeInfinity;
        }
        if value == 0.0 && value.is_sign_negative() {
            return Self::NegativeZero;
        }
        let negative = value.is_sign_negative();
        let text = value.abs().to_string();
        let magnitude =
            parse_decimal_magnitude(&text).expect("finite f64 renders as a decimal literal");
        Self::Finite {
            negative,
            magnitude,
        }
    }

    /// Parses an exact BigInt decimal representation.
    pub fn from_bigint(value: &str) -> Result<Self, NumberFormatError> {
        let (negative, body) = split_sign(value);
        if body.is_empty() || !body.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err(NumberFormatError::range(
                "invalid BigInt decimal representation",
            ));
        }
        let digits = body.bytes().map(|byte| byte - b'0').collect();
        let magnitude = Decimal::new(digits, 0)?;
        Ok(Self::Finite {
            negative: negative && !magnitude.is_zero(),
            magnitude,
        })
    }

    /// Parses an exact decimal literal for a future JavaScript String adapter.
    pub fn from_decimal_string(value: &str) -> Result<Self, NumberFormatError> {
        let (negative, body) = split_sign(value);
        let magnitude = parse_decimal_magnitude(body)?;
        if negative && magnitude.is_zero() {
            return Ok(Self::NegativeZero);
        }
        Ok(Self::Finite {
            negative,
            magnitude,
        })
    }

    fn shifted(&self, places: i32) -> Result<Self, NumberFormatError> {
        match self {
            Self::Finite {
                negative,
                magnitude,
            } => Ok(Self::Finite {
                negative: *negative,
                magnitude: magnitude.shifted(places)?,
            }),
            Self::NegativeZero => Ok(Self::NegativeZero),
            Self::PositiveInfinity => Ok(Self::PositiveInfinity),
            Self::NegativeInfinity => Ok(Self::NegativeInfinity),
            Self::Nan => Ok(Self::Nan),
        }
    }

    fn is_nan(&self) -> bool {
        matches!(self, Self::Nan)
    }

    /// Whether ICU, which compares the ends of a range before it rounds them, holds
    /// both as one value. It holds an integer that fits 64 bits exactly, and any other
    /// value as the nearest Number, so `"1e-400"` and `"2e-400"` are one value there.
    fn same_in_icu(&self, other: &Self) -> bool {
        match (self.as_i64(), other.as_i64()) {
            (Some(left), Some(right)) => left == right,
            (None, None) => self.nearest_number() == other.nearest_number(),
            _ => false,
        }
    }

    fn as_i64(&self) -> Option<i64> {
        match self {
            Self::NegativeZero => Some(0),
            Self::Finite {
                negative,
                magnitude,
            } => {
                let value = magnitude.small_integer()?;
                i64::try_from(if *negative { -value } else { value }).ok()
            }
            _ => None,
        }
    }

    fn nearest_number(&self) -> f64 {
        match self {
            Self::Finite {
                negative,
                magnitude,
            } => {
                let digits: String = magnitude
                    .digits
                    .iter()
                    .map(|digit| char::from(b'0' + digit))
                    .collect();
                let value = format!("{digits}e{}", magnitude.exponent)
                    .parse()
                    .unwrap_or(f64::NAN);
                if *negative { -value } else { value }
            }
            Self::NegativeZero => -0.0,
            Self::PositiveInfinity => f64::INFINITY,
            Self::NegativeInfinity => f64::NEG_INFINITY,
            Self::Nan => f64::NAN,
        }
    }
}

fn split_sign(value: &str) -> (bool, &str) {
    if let Some(rest) = value.strip_prefix('-') {
        (true, rest)
    } else if let Some(rest) = value.strip_prefix('+') {
        (false, rest)
    } else {
        (false, value)
    }
}

fn parse_decimal_magnitude(value: &str) -> Result<Decimal, NumberFormatError> {
    let mut exponent_split = value.split(['e', 'E']);
    let significand = exponent_split.next().unwrap_or_default();
    let exponent_text = exponent_split.next();
    if exponent_split.next().is_some() {
        return Err(NumberFormatError::range("invalid decimal literal"));
    }
    let explicit_exponent = match exponent_text {
        Some(text) if !text.is_empty() => text
            .parse::<i32>()
            .map_err(|_| NumberFormatError::range("decimal exponent is out of range"))?,
        Some(_) => return Err(NumberFormatError::range("invalid decimal exponent")),
        None => 0,
    };
    let mut point_seen = false;
    let mut fractional_digits = 0_i32;
    let mut digits = Vec::with_capacity(significand.len());
    for byte in significand.bytes() {
        if byte == b'.' && !point_seen {
            point_seen = true;
            continue;
        }
        if !byte.is_ascii_digit() {
            return Err(NumberFormatError::range("invalid decimal literal"));
        }
        digits.push(byte - b'0');
        if point_seen {
            fractional_digits = fractional_digits
                .checked_add(1)
                .ok_or_else(|| NumberFormatError::range("decimal literal is too long"))?;
        }
    }
    if digits.is_empty() {
        return Err(NumberFormatError::range("invalid decimal literal"));
    }
    let exponent = explicit_exponent
        .checked_sub(fractional_digits)
        .ok_or_else(|| NumberFormatError::range("decimal exponent is out of range"))?;
    Decimal::new(digits, exponent)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum UnsignedRoundingMode {
    Zero,
    Infinity,
    HalfZero,
    HalfInfinity,
    HalfEven,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RoundingType {
    FractionDigits,
    SignificantDigits,
    MorePrecision,
    LessPrecision,
}

#[derive(Clone, Debug)]
struct RawResult {
    formatted: String,
    rounded: Decimal,
    integer_digits_count: usize,
    rounding_magnitude: i32,
}

#[derive(Clone, Debug)]
struct QuantumRound {
    integer: Vec<u8>,
    rounded: Decimal,
}

fn normalize_integer(mut digits: Vec<u8>) -> Vec<u8> {
    let first = digits
        .iter()
        .position(|digit| *digit != 0)
        .unwrap_or(digits.len());
    if first == digits.len() {
        return vec![0];
    }
    digits.drain(..first);
    digits
}

fn mod_small(digits: &[u8], divisor: u32) -> u32 {
    digits.iter().fold(0, |remainder, digit| {
        (remainder * 10 + u32::from(*digit)) % divisor
    })
}

fn add_small(mut digits: Vec<u8>, mut addend: u32) -> Vec<u8> {
    let mut index = digits.len();
    while addend > 0 && index > 0 {
        index -= 1;
        let value = u32::from(digits[index]) + addend;
        digits[index] = u8::try_from(value % 10).expect("single decimal digit");
        addend = value / 10;
    }
    while addend > 0 {
        digits.insert(0, u8::try_from(addend % 10).expect("single decimal digit"));
        addend /= 10;
    }
    normalize_integer(digits)
}

fn sub_small(mut digits: Vec<u8>, mut subtrahend: u32) -> Vec<u8> {
    let mut index = digits.len();
    let mut borrow = 0_i32;
    while index > 0 {
        index -= 1;
        let subtract_digit = i32::try_from(subtrahend % 10).expect("single decimal digit") + borrow;
        subtrahend /= 10;
        let mut value = i32::from(digits[index]) - subtract_digit;
        if value < 0 {
            value += 10;
            borrow = 1;
        } else {
            borrow = 0;
        }
        digits[index] = u8::try_from(value).expect("single decimal digit");
        if subtrahend == 0 && borrow == 0 {
            break;
        }
    }
    normalize_integer(digits)
}

fn div_small(digits: &[u8], divisor: u32) -> (Vec<u8>, u32) {
    let mut quotient = Vec::with_capacity(digits.len());
    let mut remainder = 0_u32;
    for digit in digits {
        let value = remainder * 10 + u32::from(*digit);
        quotient.push(u8::try_from(value / divisor).expect("single decimal digit"));
        remainder = value % divisor;
    }
    (normalize_integer(quotient), remainder)
}

fn fraction_cmp_half(remainder: &[u8], scale: usize) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    if scale == 0 || scale > remainder.len() {
        return Ordering::Less;
    }
    match remainder[0].cmp(&5) {
        Ordering::Equal => {
            if remainder[1..].iter().any(|digit| *digit != 0) {
                Ordering::Greater
            } else {
                Ordering::Equal
            }
        }
        other => other,
    }
}

fn twice_offset_cmp_increment(
    integer_remainder: u32,
    fractional_remainder: &[u8],
    fractional_scale: usize,
    increment: u32,
) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    let twice_integer = integer_remainder * 2;
    match twice_integer.cmp(&increment) {
        Ordering::Greater => Ordering::Greater,
        Ordering::Equal => {
            if fractional_remainder.iter().any(|digit| *digit != 0) {
                Ordering::Greater
            } else {
                Ordering::Equal
            }
        }
        Ordering::Less => match increment - twice_integer {
            1 => fraction_cmp_half(fractional_remainder, fractional_scale),
            _ => Ordering::Less,
        },
    }
}

fn round_to_quantum(
    value: &Decimal,
    quantum_exponent: i32,
    increment: u32,
    mode: UnsignedRoundingMode,
) -> Result<QuantumRound, NumberFormatError> {
    use std::cmp::Ordering;
    let delta = value
        .exponent
        .checked_sub(quantum_exponent)
        .ok_or_else(|| NumberFormatError::range("rounding magnitude is out of range"))?;
    let (integer_floor, fractional_remainder, fractional_scale) = if delta >= 0 {
        let zeros = usize::try_from(delta)
            .map_err(|_| NumberFormatError::range("rounding magnitude is out of range"))?;
        let mut integer = value.digits.clone();
        integer.resize(integer.len().saturating_add(zeros), 0);
        (normalize_integer(integer), Vec::new(), 0)
    } else {
        let cut = usize::try_from(-delta)
            .map_err(|_| NumberFormatError::range("rounding magnitude is out of range"))?;
        if cut >= value.digits.len() {
            (vec![0], value.digits.clone(), cut)
        } else {
            let split = value.digits.len() - cut;
            (
                normalize_integer(value.digits[..split].to_vec()),
                value.digits[split..].to_vec(),
                cut,
            )
        }
    };

    let integer_remainder = mod_small(&integer_floor, increment);
    let lower = sub_small(integer_floor, integer_remainder);
    let has_fraction = fractional_remainder.iter().any(|digit| *digit != 0);
    let exact_lower = integer_remainder == 0 && !has_fraction;
    let chosen = if exact_lower {
        lower
    } else {
        let upper = add_small(lower.clone(), increment);
        match mode {
            UnsignedRoundingMode::Zero => lower,
            UnsignedRoundingMode::Infinity => upper,
            UnsignedRoundingMode::HalfZero
            | UnsignedRoundingMode::HalfInfinity
            | UnsignedRoundingMode::HalfEven => {
                match twice_offset_cmp_increment(
                    integer_remainder,
                    &fractional_remainder,
                    fractional_scale,
                    increment,
                ) {
                    Ordering::Less => lower,
                    Ordering::Greater => upper,
                    Ordering::Equal => match mode {
                        UnsignedRoundingMode::HalfZero => lower,
                        UnsignedRoundingMode::HalfInfinity => upper,
                        UnsignedRoundingMode::HalfEven => {
                            let (step_index, remainder) = div_small(&lower, increment);
                            debug_assert_eq!(remainder, 0);
                            if step_index.last().copied().unwrap_or(0) % 2 == 0 {
                                lower
                            } else {
                                upper
                            }
                        }
                        UnsignedRoundingMode::Zero | UnsignedRoundingMode::Infinity => {
                            unreachable!()
                        }
                    },
                }
            }
        }
    };
    let rounded = Decimal::new(chosen.clone(), quantum_exponent)?;
    Ok(QuantumRound {
        integer: chosen,
        rounded,
    })
}

fn digits_to_ascii(digits: &[u8]) -> String {
    digits
        .iter()
        .map(|digit| char::from(b'0' + *digit))
        .collect()
}

fn trim_fraction(mut formatted: String, maximum: u8, minimum: u8) -> String {
    let mut cut = maximum - minimum;
    while cut > 0 && formatted.ends_with('0') {
        formatted.pop();
        cut -= 1;
    }
    if formatted.ends_with('.') {
        formatted.pop();
    }
    formatted
}

fn to_raw_fixed(
    value: &Decimal,
    minimum_fraction: u8,
    maximum_fraction: u8,
    rounding_increment: u16,
    mode: UnsignedRoundingMode,
) -> Result<RawResult, NumberFormatError> {
    let fraction = i32::from(maximum_fraction);
    let rounded = round_to_quantum(value, -fraction, u32::from(rounding_increment), mode)?;
    let mut coefficient = if rounded.integer == [0] {
        String::from("0")
    } else {
        digits_to_ascii(&rounded.integer)
    };
    let integer_digits_count;
    if fraction != 0 {
        let fraction = usize::try_from(fraction).expect("fraction digits fit usize");
        if coefficient.len() <= fraction {
            let padding = "0".repeat(fraction + 1 - coefficient.len());
            coefficient.insert_str(0, &padding);
        }
        let split = coefficient.len() - fraction;
        integer_digits_count = split;
        coefficient.insert(split, '.');
    } else {
        integer_digits_count = coefficient.len();
    }
    coefficient = trim_fraction(coefficient, maximum_fraction, minimum_fraction);
    Ok(RawResult {
        formatted: coefficient,
        rounded: rounded.rounded,
        integer_digits_count,
        rounding_magnitude: -fraction,
    })
}

/// The most zeros that a formatted number spells out after its decimal point. A
/// short decimal string can ask for any number of them, and the text exists before
/// the heap limit can refuse it. The default heap of 64 MiB holds no more units.
const MAX_LEADING_ZEROS: usize = 1 << 25;

fn to_raw_precision(
    value: &Decimal,
    minimum_precision: u8,
    maximum_precision: u8,
    mode: UnsignedRoundingMode,
) -> Result<RawResult, NumberFormatError> {
    let precision = usize::from(maximum_precision);
    let (mut coefficient, exponent, rounded_value) = if value.is_zero() {
        (vec![0; precision], 0, Decimal::zero())
    } else {
        let mut exponent = value.magnitude()?;
        let quantum = exponent
            .checked_sub(i32::from(maximum_precision))
            .and_then(|result| result.checked_add(1))
            .ok_or_else(|| NumberFormatError::range("rounding magnitude is out of range"))?;
        let rounded = round_to_quantum(value, quantum, 1, mode)?;
        let mut coefficient = rounded.integer;
        while coefficient.len() > precision {
            if coefficient.last() != Some(&0) {
                return Err(NumberFormatError::invalid_data(
                    "precision carry is not a power of ten",
                ));
            }
            coefficient.pop();
            exponent = exponent
                .checked_add(1)
                .ok_or_else(|| NumberFormatError::range("decimal exponent is out of range"))?;
        }
        while coefficient.len() < precision {
            coefficient.push(0);
        }
        let final_quantum = exponent
            .checked_sub(i32::from(maximum_precision))
            .and_then(|result| result.checked_add(1))
            .ok_or_else(|| NumberFormatError::range("rounding magnitude is out of range"))?;
        (
            coefficient.clone(),
            exponent,
            Decimal::new(coefficient, final_quantum)?,
        )
    };

    let mut formatted = digits_to_ascii(&coefficient);
    let integer_digits_count;
    let precision_i32 = i32::from(maximum_precision);
    if exponent >= precision_i32 - 1 {
        let zeros = usize::try_from(exponent - precision_i32 + 1)
            .map_err(|_| NumberFormatError::range("decimal magnitude is out of range"))?;
        formatted.push_str(&"0".repeat(zeros));
        integer_digits_count = usize::try_from(exponent + 1)
            .map_err(|_| NumberFormatError::range("decimal magnitude is out of range"))?;
    } else if exponent >= 0 {
        let split = usize::try_from(exponent + 1).expect("non-negative exponent");
        formatted.insert(split, '.');
        integer_digits_count = split;
    } else {
        let zeros = usize::try_from(-(exponent + 1))
            .map_err(|_| NumberFormatError::range("decimal magnitude is out of range"))?;
        if zeros > MAX_LEADING_ZEROS {
            return Err(NumberFormatError::range("formatted number is too long"));
        }
        formatted.insert_str(0, &format!("0.{}", "0".repeat(zeros)));
        integer_digits_count = 1;
    }
    if formatted.contains('.') {
        formatted = trim_fraction(formatted, maximum_precision, minimum_precision);
    }
    coefficient.clear();
    let rounding_magnitude = exponent
        .checked_sub(i32::from(maximum_precision))
        .and_then(|result| result.checked_add(1))
        .ok_or_else(|| NumberFormatError::range("rounding magnitude is out of range"))?;
    Ok(RawResult {
        formatted,
        rounded: rounded_value,
        integer_digits_count,
        rounding_magnitude,
    })
}

/// Fully resolved, reusable NumberFormat core.
#[derive(Clone)]
pub struct NumberFormat<'a> {
    provider: &'a dyn NumberFormatDataProvider,
    locale: String,
    data_locale: String,
    numbering_system: String,
    style: NumberStyle,
    currency: Option<String>,
    currency_display: Option<CurrencyDisplay>,
    currency_sign: Option<CurrencySign>,
    unit: Option<String>,
    unit_display: Option<UnitDisplay>,
    minimum_integer_digits: u8,
    minimum_fraction_digits: Option<u8>,
    maximum_fraction_digits: Option<u8>,
    minimum_significant_digits: Option<u8>,
    maximum_significant_digits: Option<u8>,
    rounding_type: RoundingType,
    rounding_increment: u16,
    rounding_mode: RoundingMode,
    rounding_priority: RoundingPriority,
    trailing_zero_display: TrailingZeroDisplay,
    notation: Notation,
    compact_display: Option<CompactDisplay>,
    use_grouping: UseGrouping,
    sign_display: SignDisplay,
    symbols: NumberSymbols,
    grouping: GroupingSizes,
    patterns: NumberPatternSet,
    scientific_pattern: Option<String>,
    range_patterns: RangePatterns,
}

impl<'a> NumberFormat<'a> {
    /// Resolves locales and options and validates all provider data needed by
    /// repeated formatting operations.
    pub fn new(
        locales: &[String],
        options: &NumberFormatOptions,
        provider: &'a dyn NumberFormatDataProvider,
        host: &dyn HostLocaleHook,
    ) -> Result<Self, NumberFormatError> {
        let locale_matcher = match options.locale_matcher.as_deref().unwrap_or("best fit") {
            "lookup" => LocaleMatcher::Lookup,
            "best fit" => LocaleMatcher::BestFit,
            value => {
                return Err(NumberFormatError::range(format!(
                    "invalid localeMatcher: {value}"
                )));
            }
        };
        let numbering_option = match &options.numbering_system {
            Some(value) => {
                if !is_unicode_type(value) {
                    return Err(NumberFormatError::range(format!(
                        "invalid numberingSystem: {value}"
                    )));
                }
                Some(value.to_ascii_lowercase())
            }
            None => None,
        };
        let requested = if locales.is_empty() {
            vec![default_locale(host, provider)?]
        } else {
            locales.to_vec()
        };
        let mut locale_options = BTreeMap::new();
        if let Some(value) = numbering_option {
            locale_options.insert(String::from("nu"), value);
        }
        let resolved = resolve_locale(
            &requested,
            &locale_options,
            &[String::from("nu")],
            locale_matcher,
            provider,
        )?;
        let numbering_system = resolved.values.get("nu").cloned().unwrap_or_default();
        if numbering_system.is_empty() {
            return Err(NumberFormatError::missing(format!(
                "locale {} has no numbering-system data",
                resolved.data_locale
            )));
        }

        let style = parse_style(options.style.as_deref())?;
        let currency = options
            .currency
            .as_deref()
            .map(validate_currency)
            .transpose()?;
        if style == NumberStyle::Currency && currency.is_none() {
            return Err(NumberFormatError::type_error(
                "currency is required when style is currency",
            ));
        }
        let currency_display = parse_currency_display(options.currency_display.as_deref())?;
        let currency_sign = parse_currency_sign(options.currency_sign.as_deref())?;
        let unit = options.unit.as_deref().map(validate_unit).transpose()?;
        if style == NumberStyle::Unit && unit.is_none() {
            return Err(NumberFormatError::type_error(
                "unit is required when style is unit",
            ));
        }
        let unit_display = parse_unit_display(options.unit_display.as_deref())?;
        let notation = parse_notation(options.notation.as_deref())?;

        let (minimum_fraction_default, maximum_fraction_default) =
            if style == NumberStyle::Currency && notation == Notation::Standard {
                let digits = provider
                    .currency_minor_units(currency.as_deref().expect("currency style validated"))
                    .unwrap_or(2);
                if digits > 100 {
                    return Err(NumberFormatError::invalid_data(
                        "currency minor-unit digits exceed 100",
                    ));
                }
                (digits, digits)
            } else if style == NumberStyle::Percent {
                (0, 0)
            } else {
                (0, 3)
            };
        let digits = resolve_digit_options(
            options,
            minimum_fraction_default,
            maximum_fraction_default,
            notation,
        )?;
        let compact_display_value = parse_compact_display(options.compact_display.as_deref())?;
        let compact_display = (notation == Notation::Compact).then_some(compact_display_value);
        let default_grouping = if notation == Notation::Compact {
            UseGrouping::Min2
        } else {
            UseGrouping::Auto
        };
        let use_grouping = resolve_grouping(options.use_grouping.as_ref(), default_grouping)?;
        let sign_display = parse_sign_display(options.sign_display.as_deref())?;

        let symbols = provider
            .number_symbols(&resolved.data_locale, &numbering_system)
            .ok_or_else(|| {
                NumberFormatError::missing(format!(
                    "missing symbols for {}/{}",
                    resolved.data_locale, numbering_system
                ))
            })?;
        let grouping = provider
            .grouping_sizes(&resolved.data_locale, &numbering_system)
            .ok_or_else(|| {
                NumberFormatError::missing(format!(
                    "missing grouping data for {}/{}",
                    resolved.data_locale, numbering_system
                ))
            })?;
        if grouping.primary == 0 || grouping.secondary == 0 || grouping.minimum_grouping_digits == 0
        {
            return Err(NumberFormatError::invalid_data(
                "grouping sizes must be non-zero",
            ));
        }
        let request = NumberPatternRequest {
            style,
            currency: currency.as_deref(),
            currency_display: (style == NumberStyle::Currency).then_some(currency_display),
            currency_sign: (style == NumberStyle::Currency).then_some(currency_sign),
            unit: unit.as_deref(),
            unit_display: (style == NumberStyle::Unit).then_some(unit_display),
        };
        let patterns = provider
            .number_patterns(&resolved.data_locale, request)
            .ok_or_else(|| NumberFormatError::missing("missing number pattern"))?;
        validate_number_patterns(&patterns)?;
        let scientific_pattern = if matches!(notation, Notation::Scientific | Notation::Engineering)
        {
            let pattern = provider
                .scientific_pattern(&resolved.data_locale)
                .ok_or_else(|| NumberFormatError::missing("missing scientific notation pattern"))?;
            validate_pattern(&pattern)?;
            Some(pattern)
        } else {
            None
        };
        let range_patterns = provider
            .range_patterns(&resolved.data_locale, &numbering_system)
            .ok_or_else(|| NumberFormatError::missing("missing number range patterns"))?;
        validate_range_patterns(&range_patterns)?;

        Ok(Self {
            provider,
            locale: resolved.locale,
            data_locale: resolved.data_locale,
            numbering_system,
            style,
            currency: currency.filter(|_| style == NumberStyle::Currency),
            currency_display: (style == NumberStyle::Currency).then_some(currency_display),
            currency_sign: (style == NumberStyle::Currency).then_some(currency_sign),
            unit: unit.filter(|_| style == NumberStyle::Unit),
            unit_display: (style == NumberStyle::Unit).then_some(unit_display),
            minimum_integer_digits: digits.minimum_integer,
            minimum_fraction_digits: digits.minimum_fraction,
            maximum_fraction_digits: digits.maximum_fraction,
            minimum_significant_digits: digits.minimum_significant,
            maximum_significant_digits: digits.maximum_significant,
            rounding_type: digits.rounding_type,
            rounding_increment: digits.rounding_increment,
            rounding_mode: digits.rounding_mode,
            rounding_priority: digits.computed_priority,
            trailing_zero_display: digits.trailing_zero_display,
            notation,
            compact_display,
            use_grouping,
            sign_display,
            symbols,
            grouping,
            patterns,
            scientific_pattern,
            range_patterns,
        })
    }

    /// Returns the constructor's stable resolved configuration.
    #[must_use]
    pub fn resolved_options(&self) -> ResolvedNumberFormatOptions {
        ResolvedNumberFormatOptions {
            locale: self.locale.clone(),
            numbering_system: self.numbering_system.clone(),
            style: self.style,
            currency: self.currency.clone(),
            currency_display: self.currency_display,
            currency_sign: self.currency_sign,
            unit: self.unit.clone(),
            unit_display: self.unit_display,
            minimum_integer_digits: self.minimum_integer_digits,
            minimum_fraction_digits: self.minimum_fraction_digits,
            maximum_fraction_digits: self.maximum_fraction_digits,
            minimum_significant_digits: self.minimum_significant_digits,
            maximum_significant_digits: self.maximum_significant_digits,
            use_grouping: self.use_grouping,
            notation: self.notation,
            compact_display: self.compact_display,
            sign_display: self.sign_display,
            rounding_increment: self.rounding_increment,
            rounding_mode: self.rounding_mode,
            rounding_priority: self.rounding_priority,
            trailing_zero_display: self.trailing_zero_display,
        }
    }

    /// Formats a Number value.
    pub fn format_number(&self, value: f64) -> Result<String, NumberFormatError> {
        self.format(&IntlMathematicalValue::from_f64(value))
    }

    /// Formats an exact BigInt decimal representation.
    pub fn format_bigint(&self, value: &str) -> Result<String, NumberFormatError> {
        self.format(&IntlMathematicalValue::from_bigint(value)?)
    }

    /// Formats a `ToIntlMathematicalValue` result.
    pub fn format(&self, value: &IntlMathematicalValue) -> Result<String, NumberFormatError> {
        Ok(concatenate_parts(&self.format_to_parts(value)?))
    }

    /// Partitions a Number value.
    pub fn format_number_to_parts(&self, value: f64) -> Result<Vec<NumberPart>, NumberFormatError> {
        self.format_to_parts(&IntlMathematicalValue::from_f64(value))
    }

    /// Partitions an exact BigInt decimal representation.
    pub fn format_bigint_to_parts(
        &self,
        value: &str,
    ) -> Result<Vec<NumberPart>, NumberFormatError> {
        self.format_to_parts(&IntlMathematicalValue::from_bigint(value)?)
    }

    /// ECMA-402 `PartitionNumberPattern`.
    pub fn format_to_parts(
        &self,
        value: &IntlMathematicalValue,
    ) -> Result<Vec<NumberPart>, NumberFormatError> {
        let core = self.prepare_format(value)?;
        self.partition_outer_pattern(&core)
    }

    /// Formats a range. Number ranges are not ordered; only NaN endpoints are rejected.
    pub fn format_range(
        &self,
        start: &IntlMathematicalValue,
        end: &IntlMathematicalValue,
    ) -> Result<String, NumberFormatError> {
        Ok(self
            .format_range_to_parts(start, end)?
            .into_iter()
            .map(|part| part.value)
            .collect())
    }

    /// ECMA-402 `PartitionNumberRangePattern`, with the collapse choices of ICU, which
    /// V8 uses. An end has three layers around its digits: an exponent, the sign and
    /// symbols, and a unit or currency name. A name always collapses, in the plural
    /// form of a range. The sign and symbols collapse when both ends share them and
    /// they are longer than one code point, so `+$2.90–3.10` shares its `+$` and
    /// `$3 – $5` repeats its `$`. An exponent or a sign or symbol that the start keeps
    /// spaces out the separator, so `-1 – 1` has spaces and `1–-1` does not.
    pub fn format_range_to_parts(
        &self,
        start: &IntlMathematicalValue,
        end: &IntlMathematicalValue,
    ) -> Result<Vec<NumberRangePart>, NumberFormatError> {
        if start.is_nan() || end.is_nan() {
            return Err(NumberFormatError::range(
                "number range endpoints must not be NaN",
            ));
        }
        let start_prepared = self.prepare_format(start)?;
        let end_prepared = self.prepare_format(end)?;
        let start_parts = self.partition_for_category(&start_prepared, PluralCategory::Other)?;
        let end_parts = self.partition_for_category(&end_prepared, PluralCategory::Other)?;
        if concatenate_parts(&start_parts) == concatenate_parts(&end_parts)
            || (start.same_in_icu(end) && beside_digits(&start_parts).eq(beside_digits(&end_parts)))
        {
            return self.approximate_range(self.partition_outer_pattern(&start_prepared)?);
        }
        let (start_prefix, start_number, start_suffix) = split_number(&start_parts);
        let (end_prefix, end_number, end_suffix) = split_number(&end_parts);
        let (start_suffix, name) = self.split_name(start_suffix);
        let (end_suffix, _) = self.split_name(end_suffix);
        let symbols = code_points(start_prefix) + code_points(start_suffix);
        let shared = symbols > 1 && start_prefix == end_prefix && start_suffix == end_suffix;
        let exponent = start_number
            .iter()
            .any(|part| part.part_type == NumberPartType::ExponentSeparator);
        let separator = if exponent || (!shared && symbols > 0) {
            format!(" {} ", self.range_patterns.separator)
        } else {
            self.range_patterns.separator.clone()
        };
        let mut result = Vec::with_capacity(start_parts.len() + end_parts.len() + 1);
        let mut push = |parts: &[NumberPart], source| {
            result.extend(parts.iter().map(|part| NumberRangePart {
                part_type: part.part_type,
                value: part.value.clone(),
                source,
            }));
        };
        if shared {
            push(start_prefix, RangeSource::Shared);
        } else {
            push(start_prefix, RangeSource::StartRange);
        }
        push(start_number, RangeSource::StartRange);
        if !shared {
            push(start_suffix, RangeSource::StartRange);
        }
        push(
            &[NumberPart {
                part_type: NumberPartType::Literal,
                value: separator,
            }],
            RangeSource::Shared,
        );
        if !shared {
            push(end_prefix, RangeSource::EndRange);
        }
        push(end_number, RangeSource::EndRange);
        if shared {
            push(start_suffix, RangeSource::Shared);
        } else {
            push(end_suffix, RangeSource::EndRange);
        }
        push(name, RangeSource::Shared);
        Ok(result)
    }

    /// Splits what follows a number at its unit or currency name and the space before.
    /// A percent sign is a symbol, unless compact notation or the word makes it a name.
    fn split_name<'p>(&self, suffix: &'p [NumberPart]) -> (&'p [NumberPart], &'p [NumberPart]) {
        let percent_is_name = matches!(self.notation, Notation::Compact)
            || self.unit_display == Some(UnitDisplay::Long);
        let is_name = |part: &NumberPart| match part.part_type {
            NumberPartType::Unit => percent_is_name || self.unit.as_deref() != Some("percent"),
            NumberPartType::Currency => self.currency_display == Some(CurrencyDisplay::Name),
            NumberPartType::PercentSign => percent_is_name,
            _ => false,
        };
        let Some(name) = suffix.iter().position(is_name) else {
            return (suffix, &[]);
        };
        let spaced = name
            .checked_sub(1)
            .filter(|space| suffix[*space].part_type == NumberPartType::Literal);
        suffix.split_at(spaced.unwrap_or(name))
    }

    fn prepare_format(
        &self,
        value: &IntlMathematicalValue,
    ) -> Result<PreparedFormat, NumberFormatError> {
        match value {
            IntlMathematicalValue::Nan => Ok(PreparedFormat {
                rounded: IntlMathematicalValue::Nan,
                ascii: self.symbols.nan.clone(),
                exponent: 0,
            }),
            IntlMathematicalValue::PositiveInfinity => Ok(PreparedFormat {
                rounded: IntlMathematicalValue::PositiveInfinity,
                ascii: self.symbols.infinity.clone(),
                exponent: 0,
            }),
            IntlMathematicalValue::NegativeInfinity => Ok(PreparedFormat {
                rounded: IntlMathematicalValue::NegativeInfinity,
                ascii: self.symbols.infinity.clone(),
                exponent: 0,
            }),
            IntlMathematicalValue::Finite { .. } | IntlMathematicalValue::NegativeZero => {
                let scaled_percent = if self.style == NumberStyle::Percent {
                    value.shifted(2)?
                } else {
                    value.clone()
                };
                let exponent = self.compute_exponent(&scaled_percent)?;
                let scaled = scaled_percent.shifted(-exponent)?;
                let (rounded, ascii) = self.format_numeric_to_string(&scaled)?;
                Ok(PreparedFormat {
                    rounded,
                    ascii,
                    exponent,
                })
            }
        }
    }

    fn format_numeric_to_string(
        &self,
        value: &IntlMathematicalValue,
    ) -> Result<(IntlMathematicalValue, String), NumberFormatError> {
        let (negative, magnitude) = match value {
            IntlMathematicalValue::NegativeZero => (true, Decimal::zero()),
            IntlMathematicalValue::Finite {
                negative,
                magnitude,
            } => (*negative, magnitude.clone()),
            IntlMathematicalValue::PositiveInfinity
            | IntlMathematicalValue::NegativeInfinity
            | IntlMathematicalValue::Nan => {
                return Err(NumberFormatError::invalid_data(
                    "non-finite value reached rounding",
                ));
            }
        };
        let mode = self.rounding_mode.unsigned(negative);
        let result = match self.rounding_type {
            RoundingType::SignificantDigits => to_raw_precision(
                &magnitude,
                self.minimum_significant_digits
                    .expect("significant rounding has minimum"),
                self.maximum_significant_digits
                    .expect("significant rounding has maximum"),
                mode,
            )?,
            RoundingType::FractionDigits => to_raw_fixed(
                &magnitude,
                self.minimum_fraction_digits
                    .expect("fraction rounding has minimum"),
                self.maximum_fraction_digits
                    .expect("fraction rounding has maximum"),
                self.rounding_increment,
                mode,
            )?,
            RoundingType::MorePrecision | RoundingType::LessPrecision => {
                let significant = to_raw_precision(
                    &magnitude,
                    self.minimum_significant_digits
                        .expect("priority rounding has significant minimum"),
                    self.maximum_significant_digits
                        .expect("priority rounding has significant maximum"),
                    mode,
                )?;
                let fraction = to_raw_fixed(
                    &magnitude,
                    self.minimum_fraction_digits
                        .expect("priority rounding has fraction minimum"),
                    self.maximum_fraction_digits
                        .expect("priority rounding has fraction maximum"),
                    self.rounding_increment,
                    mode,
                )?;
                let fixed_is_more_precise =
                    fraction.rounding_magnitude < significant.rounding_magnitude;
                if (self.rounding_type == RoundingType::MorePrecision && fixed_is_more_precise)
                    || (self.rounding_type == RoundingType::LessPrecision && !fixed_is_more_precise)
                {
                    fraction
                } else {
                    significant
                }
            }
        };
        let mut ascii = result.formatted;
        if self.trailing_zero_display == TrailingZeroDisplay::StripIfInteger
            && result.rounded.is_integer()
            && let Some(index) = ascii.find('.')
        {
            ascii.truncate(index);
        }
        if result.integer_digits_count < usize::from(self.minimum_integer_digits) {
            ascii.insert_str(
                0,
                &"0".repeat(usize::from(self.minimum_integer_digits) - result.integer_digits_count),
            );
        }
        let rounded = if negative {
            if result.rounded.is_zero() {
                IntlMathematicalValue::NegativeZero
            } else {
                IntlMathematicalValue::Finite {
                    negative: true,
                    magnitude: result.rounded,
                }
            }
        } else {
            IntlMathematicalValue::Finite {
                negative: false,
                magnitude: result.rounded,
            }
        };
        Ok((rounded, ascii))
    }

    fn compute_exponent(&self, value: &IntlMathematicalValue) -> Result<i32, NumberFormatError> {
        let magnitude = match value {
            IntlMathematicalValue::NegativeZero => return Ok(0),
            IntlMathematicalValue::Finite { magnitude, .. } if magnitude.is_zero() => return Ok(0),
            IntlMathematicalValue::Finite { magnitude, .. } => magnitude,
            _ => return Ok(0),
        };
        let original_magnitude = magnitude.magnitude()?;
        let exponent = self.compute_exponent_for_magnitude(original_magnitude)?;
        let scaled = IntlMathematicalValue::Finite {
            negative: false,
            magnitude: magnitude.shifted(-exponent)?,
        };
        let (rounded, _) = self.format_numeric_to_string(&scaled)?;
        let new_magnitude = match rounded {
            IntlMathematicalValue::Finite { magnitude, .. } if magnitude.is_zero() => {
                return Ok(exponent);
            }
            IntlMathematicalValue::Finite { magnitude, .. } => magnitude.magnitude()?,
            IntlMathematicalValue::NegativeZero => return Ok(exponent),
            _ => return Err(NumberFormatError::invalid_data("non-finite exponent probe")),
        };
        if new_magnitude == original_magnitude - exponent {
            Ok(exponent)
        } else {
            self.compute_exponent_for_magnitude(
                original_magnitude
                    .checked_add(1)
                    .ok_or_else(|| NumberFormatError::range("decimal magnitude is out of range"))?,
            )
        }
    }

    /// The compact form in use. The long form has no place for a currency symbol or
    /// code, which keep the short form, and only a currency name can follow a long word.
    fn compact_form(&self) -> CompactDisplay {
        let currency_symbol = self.style == NumberStyle::Currency
            && self.currency_display != Some(CurrencyDisplay::Name);
        if currency_symbol {
            CompactDisplay::Short
        } else {
            self.compact_display.expect("compact display is resolved")
        }
    }

    fn compute_exponent_for_magnitude(&self, magnitude: i32) -> Result<i32, NumberFormatError> {
        match self.notation {
            Notation::Standard => Ok(0),
            Notation::Scientific => Ok(magnitude),
            Notation::Engineering => Ok(magnitude.div_euclid(3) * 3),
            Notation::Compact => self
                .provider
                .compact_exponent(&self.data_locale, self.compact_form(), magnitude)
                .ok_or_else(|| {
                    NumberFormatError::missing(format!(
                        "missing compact exponent for magnitude {magnitude}"
                    ))
                }),
        }
    }

    fn partition_outer_pattern(
        &self,
        prepared: &PreparedFormat,
    ) -> Result<Vec<NumberPart>, NumberFormatError> {
        let operands = operands_from_ascii(&prepared.ascii, prepared.exponent);
        let category = match prepared.rounded {
            IntlMathematicalValue::Finite { .. } | IntlMathematicalValue::NegativeZero => {
                self.provider.plural_category(&self.data_locale, &operands)
            }
            _ => PluralCategory::Other,
        };
        self.partition_for_category(prepared, category)
    }

    fn partition_for_category(
        &self,
        prepared: &PreparedFormat,
        category: PluralCategory,
    ) -> Result<Vec<NumberPart>, NumberFormatError> {
        let pattern = self.pattern_for_value(&prepared.rounded);
        let tokens = partition_pattern(pattern)?;
        let mut result = Vec::new();
        for token in tokens {
            match token {
                PatternToken::Literal(value) => {
                    push_part(&mut result, NumberPartType::Literal, value)
                }
                PatternToken::Placeholder(name) => match name.as_str() {
                    "number" => result.extend(self.partition_notation(prepared, category)?),
                    "plusSign" => push_part(
                        &mut result,
                        NumberPartType::PlusSign,
                        self.symbols.plus_sign.clone(),
                    ),
                    "minusSign" => push_part(
                        &mut result,
                        NumberPartType::MinusSign,
                        self.symbols.minus_sign.clone(),
                    ),
                    "percentSign" if self.style == NumberStyle::Percent => {
                        push_part(
                            &mut result,
                            NumberPartType::PercentSign,
                            self.symbols.percent_sign.clone(),
                        );
                    }
                    "currencyCode" if self.style == NumberStyle::Currency => {
                        push_part(
                            &mut result,
                            NumberPartType::Currency,
                            self.currency.as_ref().expect("currency style").clone(),
                        );
                    }
                    "currencyPrefix" | "currencySuffix" if self.style == NumberStyle::Currency => {
                        let currency = self.currency.as_ref().expect("currency style");
                        let display = self.currency_display.expect("currency style");
                        let value = self
                            .provider
                            .currency_display(&self.data_locale, currency, display, category)
                            .unwrap_or_else(|| currency.clone());
                        push_part(&mut result, NumberPartType::Currency, value);
                    }
                    "unitPrefix" | "unitSuffix" if self.style == NumberStyle::Unit => {
                        let unit = self.unit.as_ref().expect("unit style");
                        let value = self
                            .provider
                            .unit_display(
                                &self.data_locale,
                                unit,
                                self.unit_display.expect("unit style"),
                                category,
                            )
                            .ok_or_else(|| {
                                NumberFormatError::missing(format!(
                                    "missing display name for unit {unit}"
                                ))
                            })?;
                        push_part(&mut result, NumberPartType::Unit, value);
                    }
                    _ => push_part(&mut result, NumberPartType::Unknown, name),
                },
            }
        }
        Ok(result)
    }

    fn partition_notation(
        &self,
        prepared: &PreparedFormat,
        category: PluralCategory,
    ) -> Result<Vec<NumberPart>, NumberFormatError> {
        match prepared.rounded {
            IntlMathematicalValue::Nan => {
                return Ok(vec![NumberPart {
                    part_type: NumberPartType::Nan,
                    value: prepared.ascii.clone(),
                }]);
            }
            IntlMathematicalValue::PositiveInfinity | IntlMathematicalValue::NegativeInfinity => {
                return Ok(vec![NumberPart {
                    part_type: NumberPartType::Infinity,
                    value: prepared.ascii.clone(),
                }]);
            }
            _ => {}
        }
        let (pattern, compact_display) = match self.notation {
            Notation::Standard => (String::from("{number}"), None),
            Notation::Scientific | Notation::Engineering => (
                self.scientific_pattern
                    .as_ref()
                    .expect("scientific pattern resolved")
                    .clone(),
                None,
            ),
            Notation::Compact if prepared.exponent == 0 => (String::from("{number}"), None),
            Notation::Compact => {
                let compact = self
                    .provider
                    .compact_pattern(
                        &self.data_locale,
                        self.compact_form(),
                        prepared.exponent,
                        category,
                    )
                    .ok_or_else(|| {
                        NumberFormatError::missing(format!(
                            "missing compact pattern for exponent {}",
                            prepared.exponent
                        ))
                    })?;
                validate_pattern(&compact.pattern)?;
                (compact.pattern, Some(compact.display))
            }
        };
        let tokens = partition_pattern(&pattern)?;
        let mut result = Vec::new();
        for token in tokens {
            match token {
                PatternToken::Literal(value) => {
                    push_part(&mut result, NumberPartType::Literal, value)
                }
                PatternToken::Placeholder(name) => match name.as_str() {
                    "number" => result.extend(self.partition_ascii_number(&prepared.ascii)),
                    "compactSymbol" | "compactName" => push_part(
                        &mut result,
                        NumberPartType::Compact,
                        compact_display.clone().ok_or_else(|| {
                            NumberFormatError::invalid_data(
                                "compact placeholder without compact display",
                            )
                        })?,
                    ),
                    "scientificSeparator" => push_part(
                        &mut result,
                        NumberPartType::ExponentSeparator,
                        self.symbols.exponent_separator.clone(),
                    ),
                    "scientificExponent" => {
                        let mut exponent = prepared.exponent;
                        if exponent < 0 {
                            push_part(
                                &mut result,
                                NumberPartType::ExponentMinusSign,
                                self.symbols.minus_sign.clone(),
                            );
                            exponent = -exponent;
                        }
                        let ascii = exponent.to_string();
                        push_part(
                            &mut result,
                            NumberPartType::ExponentInteger,
                            self.transliterate_digits(&ascii),
                        );
                    }
                    _ => push_part(&mut result, NumberPartType::Unknown, name),
                },
            }
        }
        Ok(result)
    }

    fn partition_ascii_number(&self, ascii: &str) -> Vec<NumberPart> {
        let (integer, fraction) = ascii
            .split_once('.')
            .map_or((ascii, None), |(left, right)| (left, Some(right)));
        let groups = grouped_slices(integer, self.use_grouping, self.grouping);
        let mut result = Vec::with_capacity(groups.len() * 2 + usize::from(fraction.is_some()));
        for (index, group) in groups.iter().enumerate() {
            push_part(
                &mut result,
                NumberPartType::Integer,
                self.transliterate_digits(group),
            );
            if index + 1 < groups.len() {
                push_part(
                    &mut result,
                    NumberPartType::Group,
                    self.symbols.group.clone(),
                );
            }
        }
        if let Some(fraction) = fraction {
            push_part(
                &mut result,
                NumberPartType::Decimal,
                self.symbols.decimal.clone(),
            );
            push_part(
                &mut result,
                NumberPartType::Fraction,
                self.transliterate_digits(fraction),
            );
        }
        result
    }

    fn transliterate_digits(&self, ascii: &str) -> String {
        ascii
            .chars()
            .map(|character| {
                character
                    .to_digit(10)
                    .and_then(|digit| {
                        self.symbols
                            .digits
                            .get(usize::try_from(digit).expect("digit index"))
                    })
                    .copied()
                    .unwrap_or(character)
            })
            .collect()
    }

    fn pattern_for_value(&self, value: &IntlMathematicalValue) -> &str {
        let category = value_category(value);
        match self.sign_display {
            SignDisplay::Never => &self.patterns.zero,
            SignDisplay::Auto => match category {
                ValueCategory::Positive | ValueCategory::ZeroPositive => &self.patterns.zero,
                ValueCategory::Negative | ValueCategory::ZeroNegative => &self.patterns.negative,
            },
            SignDisplay::Always => match category {
                ValueCategory::Positive | ValueCategory::ZeroPositive => &self.patterns.positive,
                ValueCategory::Negative | ValueCategory::ZeroNegative => &self.patterns.negative,
            },
            SignDisplay::ExceptZero => match category {
                ValueCategory::ZeroPositive | ValueCategory::ZeroNegative => &self.patterns.zero,
                ValueCategory::Positive => &self.patterns.positive,
                ValueCategory::Negative => &self.patterns.negative,
            },
            SignDisplay::Negative => match category {
                ValueCategory::Negative => &self.patterns.negative,
                ValueCategory::Positive
                | ValueCategory::ZeroPositive
                | ValueCategory::ZeroNegative => &self.patterns.zero,
            },
        }
    }

    fn approximate_range(
        &self,
        number_parts: Vec<NumberPart>,
    ) -> Result<Vec<NumberRangePart>, NumberFormatError> {
        let tokens = partition_pattern(&self.range_patterns.approximate)?;
        let mut result = Vec::new();
        for token in tokens {
            match token {
                PatternToken::Literal(value) => result.push(NumberRangePart {
                    part_type: NumberPartType::Literal,
                    value,
                    source: RangeSource::Shared,
                }),
                PatternToken::Placeholder(name) if name == "number" => {
                    result.extend(number_parts.iter().cloned().map(|part| NumberRangePart {
                        part_type: part.part_type,
                        value: part.value,
                        source: RangeSource::Shared,
                    }));
                }
                PatternToken::Placeholder(name) if name == "approximatelySign" => {
                    if !self.symbols.approximately_sign.is_empty() {
                        result.push(NumberRangePart {
                            part_type: NumberPartType::ApproximatelySign,
                            value: self.symbols.approximately_sign.clone(),
                            source: RangeSource::Shared,
                        });
                    }
                }
                PatternToken::Placeholder(name) => result.push(NumberRangePart {
                    part_type: NumberPartType::Unknown,
                    value: name,
                    source: RangeSource::Shared,
                }),
            }
        }
        Ok(result)
    }
}

#[derive(Clone, Debug)]
struct PreparedFormat {
    rounded: IntlMathematicalValue,
    ascii: String,
    exponent: i32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ValueCategory {
    Positive,
    ZeroPositive,
    Negative,
    ZeroNegative,
}

fn value_category(value: &IntlMathematicalValue) -> ValueCategory {
    match value {
        IntlMathematicalValue::Nan => ValueCategory::ZeroPositive,
        IntlMathematicalValue::PositiveInfinity => ValueCategory::Positive,
        IntlMathematicalValue::NegativeInfinity => ValueCategory::Negative,
        IntlMathematicalValue::NegativeZero => ValueCategory::ZeroNegative,
        IntlMathematicalValue::Finite {
            negative: true,
            magnitude,
        } if !magnitude.is_zero() => ValueCategory::Negative,
        IntlMathematicalValue::Finite { magnitude, .. } if magnitude.is_zero() => {
            ValueCategory::ZeroPositive
        }
        IntlMathematicalValue::Finite { .. } => ValueCategory::Positive,
    }
}

fn push_part(parts: &mut Vec<NumberPart>, part_type: NumberPartType, value: String) {
    if !value.is_empty() {
        parts.push(NumberPart { part_type, value });
    }
}

/// Splits parts into what precedes the number, the number, and what follows.
fn split_number(parts: &[NumberPart]) -> (&[NumberPart], &[NumberPart], &[NumberPart]) {
    let is_number = |part: &NumberPart| {
        matches!(
            part.part_type,
            NumberPartType::Integer
                | NumberPartType::Group
                | NumberPartType::Decimal
                | NumberPartType::Fraction
                | NumberPartType::Nan
                | NumberPartType::Infinity
                | NumberPartType::ExponentInteger
                | NumberPartType::ExponentMinusSign
                | NumberPartType::ExponentSeparator
        )
    };
    let Some(first) = parts.iter().position(is_number) else {
        return (parts, &[], &[]);
    };
    let last = parts.iter().rposition(is_number).unwrap_or(first) + 1;
    (&parts[..first], &parts[first..last], &parts[last..])
}

/// The parts of a number other than the digits of its coefficient.
fn beside_digits(parts: &[NumberPart]) -> impl Iterator<Item = &NumberPart> {
    parts.iter().filter(|part| {
        !matches!(
            part.part_type,
            NumberPartType::Integer
                | NumberPartType::Group
                | NumberPartType::Decimal
                | NumberPartType::Fraction
        )
    })
}

fn code_points(parts: &[NumberPart]) -> usize {
    parts.iter().map(|part| part.value.chars().count()).sum()
}

fn concatenate_parts(parts: &[NumberPart]) -> String {
    parts.iter().map(|part| part.value.as_str()).collect()
}

fn grouped_slices(integer: &str, use_grouping: UseGrouping, grouping: GroupingSizes) -> Vec<&str> {
    let leading_requirement = match use_grouping {
        UseGrouping::False => return vec![integer],
        UseGrouping::Always => 1,
        UseGrouping::Min2 => grouping.minimum_grouping_digits.max(2),
        UseGrouping::Auto => grouping.minimum_grouping_digits,
    };
    if integer.len() < grouping.primary + leading_requirement {
        return vec![integer];
    }
    let mut reversed = Vec::new();
    let mut end = integer.len();
    let mut width = grouping.primary;
    while end > width {
        reversed.push(&integer[end - width..end]);
        end -= width;
        width = grouping.secondary;
    }
    reversed.push(&integer[..end]);
    reversed.reverse();
    reversed
}

fn operands_from_ascii(ascii: &str, exponent: i32) -> PluralOperands {
    let (integer, fraction) = ascii.split_once('.').unwrap_or((ascii, ""));
    let integer = integer.trim_start_matches('0');
    let integer_digits = if integer.is_empty() {
        String::from("0")
    } else {
        integer.to_owned()
    };
    let without_trailing = fraction.trim_end_matches('0').to_owned();
    PluralOperands {
        integer_digits,
        fraction_digits: fraction.to_owned(),
        fraction_digits_without_trailing_zeros: without_trailing.clone(),
        visible_fraction_digits: fraction.len(),
        visible_fraction_digits_without_trailing_zeros: without_trailing.len(),
        exponent,
    }
}

#[derive(Debug)]
struct ResolvedDigits {
    minimum_integer: u8,
    minimum_fraction: Option<u8>,
    maximum_fraction: Option<u8>,
    minimum_significant: Option<u8>,
    maximum_significant: Option<u8>,
    rounding_type: RoundingType,
    rounding_increment: u16,
    rounding_mode: RoundingMode,
    computed_priority: RoundingPriority,
    trailing_zero_display: TrailingZeroDisplay,
}

fn number_option(
    name: &str,
    value: Option<f64>,
    minimum: u16,
    maximum: u16,
    fallback: Option<u16>,
) -> Result<Option<u16>, NumberFormatError> {
    let Some(value) = value else {
        return Ok(fallback);
    };
    if !value.is_finite() || value < f64::from(minimum) || value > f64::from(maximum) {
        return Err(NumberFormatError::range(format!("{name} is out of range")));
    }
    Ok(Some(value.floor() as u16))
}

fn resolve_digit_options(
    options: &NumberFormatOptions,
    minimum_fraction_default: u8,
    mut maximum_fraction_default: u8,
    notation: Notation,
) -> Result<ResolvedDigits, NumberFormatError> {
    let minimum_integer = u8::try_from(
        number_option(
            "minimumIntegerDigits",
            options.minimum_integer_digits,
            1,
            21,
            Some(1),
        )?
        .expect("fallback provided"),
    )
    .expect("minimum integer range fits u8");
    let mut minimum_fraction = options.minimum_fraction_digits;
    let mut maximum_fraction = options.maximum_fraction_digits;
    let minimum_significant = options.minimum_significant_digits;
    let maximum_significant = options.maximum_significant_digits;
    let rounding_increment = number_option(
        "roundingIncrement",
        options.rounding_increment,
        1,
        5000,
        Some(1),
    )?
    .expect("fallback provided");
    const ALLOWED_INCREMENTS: [u16; 15] = [
        1, 2, 5, 10, 20, 25, 50, 100, 200, 250, 500, 1000, 2000, 2500, 5000,
    ];
    if !ALLOWED_INCREMENTS.contains(&rounding_increment) {
        return Err(NumberFormatError::range("invalid roundingIncrement"));
    }
    let rounding_mode = parse_rounding_mode(options.rounding_mode.as_deref())?;
    let requested_priority = parse_rounding_priority(options.rounding_priority.as_deref())?;
    let trailing_zero_display =
        parse_trailing_zero_display(options.trailing_zero_display.as_deref())?;
    if rounding_increment != 1 {
        maximum_fraction_default = minimum_fraction_default;
    }
    let has_significant = minimum_significant.is_some() || maximum_significant.is_some();
    let has_fraction = minimum_fraction.is_some() || maximum_fraction.is_some();
    let mut need_significant = true;
    let mut need_fraction = true;
    if requested_priority == RoundingPriority::Auto {
        need_significant = has_significant;
        if need_significant || (!has_fraction && notation == Notation::Compact) {
            need_fraction = false;
        }
    }

    let (minimum_significant_resolved, maximum_significant_resolved) = if need_significant {
        if has_significant {
            let minimum = u8::try_from(
                number_option(
                    "minimumSignificantDigits",
                    minimum_significant,
                    1,
                    21,
                    Some(1),
                )?
                .expect("fallback provided"),
            )
            .expect("significant digit range fits u8");
            let maximum = u8::try_from(
                number_option(
                    "maximumSignificantDigits",
                    maximum_significant,
                    u16::from(minimum),
                    21,
                    Some(21),
                )?
                .expect("fallback provided"),
            )
            .expect("significant digit range fits u8");
            (Some(minimum), Some(maximum))
        } else {
            (Some(1), Some(21))
        }
    } else {
        (None, None)
    };

    let (minimum_fraction_resolved, maximum_fraction_resolved) = if need_fraction {
        if has_fraction {
            let minimum = number_option(
                "minimumFractionDigits",
                minimum_fraction.take(),
                0,
                100,
                None,
            )?;
            let maximum = number_option(
                "maximumFractionDigits",
                maximum_fraction.take(),
                0,
                100,
                None,
            )?;
            let (minimum, maximum) = match (minimum, maximum) {
                (None, Some(maximum)) => {
                    (u16::from(minimum_fraction_default).min(maximum), maximum)
                }
                (Some(minimum), None) => {
                    (minimum, u16::from(maximum_fraction_default).max(minimum))
                }
                (Some(minimum), Some(maximum)) if minimum <= maximum => (minimum, maximum),
                (Some(_), Some(_)) => {
                    return Err(NumberFormatError::range(
                        "minimumFractionDigits exceeds maximumFractionDigits",
                    ));
                }
                (None, None) => unreachable!("has_fraction was true"),
            };
            (
                Some(u8::try_from(minimum).expect("fraction range fits u8")),
                Some(u8::try_from(maximum).expect("fraction range fits u8")),
            )
        } else {
            (
                Some(minimum_fraction_default),
                Some(maximum_fraction_default),
            )
        }
    } else {
        (None, None)
    };

    let (
        minimum_fraction_resolved,
        maximum_fraction_resolved,
        minimum_significant_resolved,
        maximum_significant_resolved,
        rounding_type,
        computed_priority,
    ) = if !need_significant && !need_fraction {
        (
            Some(0),
            Some(0),
            Some(1),
            Some(2),
            RoundingType::MorePrecision,
            RoundingPriority::MorePrecision,
        )
    } else if requested_priority == RoundingPriority::MorePrecision {
        (
            minimum_fraction_resolved,
            maximum_fraction_resolved,
            minimum_significant_resolved,
            maximum_significant_resolved,
            RoundingType::MorePrecision,
            RoundingPriority::MorePrecision,
        )
    } else if requested_priority == RoundingPriority::LessPrecision {
        (
            minimum_fraction_resolved,
            maximum_fraction_resolved,
            minimum_significant_resolved,
            maximum_significant_resolved,
            RoundingType::LessPrecision,
            RoundingPriority::LessPrecision,
        )
    } else if has_significant {
        (
            minimum_fraction_resolved,
            maximum_fraction_resolved,
            minimum_significant_resolved,
            maximum_significant_resolved,
            RoundingType::SignificantDigits,
            RoundingPriority::Auto,
        )
    } else {
        (
            minimum_fraction_resolved,
            maximum_fraction_resolved,
            minimum_significant_resolved,
            maximum_significant_resolved,
            RoundingType::FractionDigits,
            RoundingPriority::Auto,
        )
    };

    if rounding_increment != 1 {
        if rounding_type != RoundingType::FractionDigits {
            return Err(NumberFormatError::type_error(
                "roundingIncrement requires fraction-digits rounding",
            ));
        }
        if minimum_fraction_resolved != maximum_fraction_resolved {
            return Err(NumberFormatError::range(
                "roundingIncrement requires equal minimum and maximum fraction digits",
            ));
        }
    }

    Ok(ResolvedDigits {
        minimum_integer,
        minimum_fraction: minimum_fraction_resolved,
        maximum_fraction: maximum_fraction_resolved,
        minimum_significant: minimum_significant_resolved,
        maximum_significant: maximum_significant_resolved,
        rounding_type,
        rounding_increment,
        rounding_mode,
        computed_priority,
        trailing_zero_display,
    })
}

fn parse_style(value: Option<&str>) -> Result<NumberStyle, NumberFormatError> {
    match value.unwrap_or("decimal") {
        "decimal" => Ok(NumberStyle::Decimal),
        "percent" => Ok(NumberStyle::Percent),
        "currency" => Ok(NumberStyle::Currency),
        "unit" => Ok(NumberStyle::Unit),
        value => Err(NumberFormatError::range(format!("invalid style: {value}"))),
    }
}

fn parse_currency_display(value: Option<&str>) -> Result<CurrencyDisplay, NumberFormatError> {
    match value.unwrap_or("symbol") {
        "code" => Ok(CurrencyDisplay::Code),
        "symbol" => Ok(CurrencyDisplay::Symbol),
        "narrowSymbol" => Ok(CurrencyDisplay::NarrowSymbol),
        "name" => Ok(CurrencyDisplay::Name),
        value => Err(NumberFormatError::range(format!(
            "invalid currencyDisplay: {value}"
        ))),
    }
}

fn parse_currency_sign(value: Option<&str>) -> Result<CurrencySign, NumberFormatError> {
    match value.unwrap_or("standard") {
        "standard" => Ok(CurrencySign::Standard),
        "accounting" => Ok(CurrencySign::Accounting),
        value => Err(NumberFormatError::range(format!(
            "invalid currencySign: {value}"
        ))),
    }
}

fn parse_unit_display(value: Option<&str>) -> Result<UnitDisplay, NumberFormatError> {
    match value.unwrap_or("short") {
        "short" => Ok(UnitDisplay::Short),
        "narrow" => Ok(UnitDisplay::Narrow),
        "long" => Ok(UnitDisplay::Long),
        value => Err(NumberFormatError::range(format!(
            "invalid unitDisplay: {value}"
        ))),
    }
}

fn parse_notation(value: Option<&str>) -> Result<Notation, NumberFormatError> {
    match value.unwrap_or("standard") {
        "standard" => Ok(Notation::Standard),
        "scientific" => Ok(Notation::Scientific),
        "engineering" => Ok(Notation::Engineering),
        "compact" => Ok(Notation::Compact),
        value => Err(NumberFormatError::range(format!(
            "invalid notation: {value}"
        ))),
    }
}

fn parse_compact_display(value: Option<&str>) -> Result<CompactDisplay, NumberFormatError> {
    match value.unwrap_or("short") {
        "short" => Ok(CompactDisplay::Short),
        "long" => Ok(CompactDisplay::Long),
        value => Err(NumberFormatError::range(format!(
            "invalid compactDisplay: {value}"
        ))),
    }
}

fn parse_sign_display(value: Option<&str>) -> Result<SignDisplay, NumberFormatError> {
    match value.unwrap_or("auto") {
        "auto" => Ok(SignDisplay::Auto),
        "never" => Ok(SignDisplay::Never),
        "always" => Ok(SignDisplay::Always),
        "exceptZero" => Ok(SignDisplay::ExceptZero),
        "negative" => Ok(SignDisplay::Negative),
        value => Err(NumberFormatError::range(format!(
            "invalid signDisplay: {value}"
        ))),
    }
}

fn parse_rounding_mode(value: Option<&str>) -> Result<RoundingMode, NumberFormatError> {
    match value.unwrap_or("halfExpand") {
        "ceil" => Ok(RoundingMode::Ceil),
        "floor" => Ok(RoundingMode::Floor),
        "expand" => Ok(RoundingMode::Expand),
        "trunc" => Ok(RoundingMode::Trunc),
        "halfCeil" => Ok(RoundingMode::HalfCeil),
        "halfFloor" => Ok(RoundingMode::HalfFloor),
        "halfExpand" => Ok(RoundingMode::HalfExpand),
        "halfTrunc" => Ok(RoundingMode::HalfTrunc),
        "halfEven" => Ok(RoundingMode::HalfEven),
        value => Err(NumberFormatError::range(format!(
            "invalid roundingMode: {value}"
        ))),
    }
}

fn parse_rounding_priority(value: Option<&str>) -> Result<RoundingPriority, NumberFormatError> {
    match value.unwrap_or("auto") {
        "auto" => Ok(RoundingPriority::Auto),
        "morePrecision" => Ok(RoundingPriority::MorePrecision),
        "lessPrecision" => Ok(RoundingPriority::LessPrecision),
        value => Err(NumberFormatError::range(format!(
            "invalid roundingPriority: {value}"
        ))),
    }
}

fn parse_trailing_zero_display(
    value: Option<&str>,
) -> Result<TrailingZeroDisplay, NumberFormatError> {
    match value.unwrap_or("auto") {
        "auto" => Ok(TrailingZeroDisplay::Auto),
        "stripIfInteger" => Ok(TrailingZeroDisplay::StripIfInteger),
        value => Err(NumberFormatError::range(format!(
            "invalid trailingZeroDisplay: {value}"
        ))),
    }
}

fn resolve_grouping(
    value: Option<&UseGroupingOption>,
    fallback: UseGrouping,
) -> Result<UseGrouping, NumberFormatError> {
    match value {
        None => Ok(fallback),
        Some(UseGroupingOption::Boolean(true)) => Ok(UseGrouping::Always),
        Some(UseGroupingOption::Boolean(false)) => Ok(UseGrouping::False),
        Some(UseGroupingOption::String(value)) => match value.as_str() {
            "min2" => Ok(UseGrouping::Min2),
            "auto" => Ok(UseGrouping::Auto),
            "always" => Ok(UseGrouping::Always),
            "true" | "false" => Ok(fallback),
            _ => Err(NumberFormatError::range(format!(
                "invalid useGrouping: {value}"
            ))),
        },
    }
}

fn validate_currency(value: &str) -> Result<String, NumberFormatError> {
    if value.len() != 3 || !value.bytes().all(|byte| byte.is_ascii_alphabetic()) {
        return Err(NumberFormatError::range(format!(
            "invalid currency code: {value}"
        )));
    }
    Ok(value.to_ascii_uppercase())
}

pub const SANCTIONED_UNITS: [&str; 45] = [
    "acre",
    "bit",
    "byte",
    "celsius",
    "centimeter",
    "day",
    "degree",
    "fahrenheit",
    "fluid-ounce",
    "foot",
    "gallon",
    "gigabit",
    "gigabyte",
    "gram",
    "hectare",
    "hour",
    "inch",
    "kilobit",
    "kilobyte",
    "kilogram",
    "kilometer",
    "liter",
    "megabit",
    "megabyte",
    "meter",
    "microsecond",
    "mile",
    "mile-scandinavian",
    "milliliter",
    "millimeter",
    "millisecond",
    "minute",
    "month",
    "nanosecond",
    "ounce",
    "percent",
    "petabyte",
    "pound",
    "second",
    "stone",
    "terabit",
    "terabyte",
    "week",
    "yard",
    "year",
];

/// IsWellFormedUnitIdentifier.
#[must_use]
pub fn is_well_formed_unit(value: &str) -> bool {
    SANCTIONED_UNITS.contains(&value)
        || value
            .split_once("-per-")
            .is_some_and(|(numerator, denominator)| {
                SANCTIONED_UNITS.contains(&numerator) && SANCTIONED_UNITS.contains(&denominator)
            })
}

fn validate_unit(value: &str) -> Result<String, NumberFormatError> {
    if !is_well_formed_unit(value) {
        return Err(NumberFormatError::range(format!(
            "invalid unit identifier: {value}"
        )));
    }
    Ok(value.to_owned())
}

fn is_unicode_type(value: &str) -> bool {
    !value.is_empty()
        && value.split('-').all(|subtag| {
            (3..=8).contains(&subtag.len())
                && subtag.bytes().all(|byte| byte.is_ascii_alphanumeric())
        })
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum PatternToken {
    Literal(String),
    Placeholder(String),
}

fn partition_pattern(pattern: &str) -> Result<Vec<PatternToken>, NumberFormatError> {
    let mut result = Vec::new();
    let mut cursor = 0;
    while let Some(relative_start) = pattern[cursor..].find('{') {
        let start = cursor + relative_start;
        if start > cursor {
            result.push(PatternToken::Literal(pattern[cursor..start].to_owned()));
        }
        let end = pattern[start + 1..]
            .find('}')
            .map(|relative| start + 1 + relative)
            .ok_or_else(|| NumberFormatError::invalid_data("unterminated pattern placeholder"))?;
        let name = &pattern[start + 1..end];
        if name.is_empty()
            || !name
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        {
            return Err(NumberFormatError::invalid_data(
                "invalid pattern placeholder",
            ));
        }
        result.push(PatternToken::Placeholder(name.to_owned()));
        cursor = end + 1;
    }
    if cursor < pattern.len() {
        result.push(PatternToken::Literal(pattern[cursor..].to_owned()));
    }
    Ok(result)
}

fn validate_pattern(pattern: &str) -> Result<(), NumberFormatError> {
    partition_pattern(pattern).map(|_| ())
}

fn validate_number_patterns(patterns: &NumberPatternSet) -> Result<(), NumberFormatError> {
    for pattern in [&patterns.zero, &patterns.positive, &patterns.negative] {
        let tokens = partition_pattern(pattern)?;
        if !tokens
            .iter()
            .any(|token| matches!(token, PatternToken::Placeholder(name) if name == "number"))
        {
            return Err(NumberFormatError::invalid_data(
                "number pattern lacks {number}",
            ));
        }
    }
    Ok(())
}

fn validate_range_patterns(patterns: &RangePatterns) -> Result<(), NumberFormatError> {
    if patterns.separator.is_empty() {
        return Err(NumberFormatError::invalid_data("range separator is empty"));
    }
    let tokens = partition_pattern(&patterns.approximate)?;
    if !tokens
        .iter()
        .any(|token| matches!(token, PatternToken::Placeholder(name) if name == "number"))
    {
        return Err(NumberFormatError::invalid_data(
            "approximate pattern lacks {number}",
        ));
    }
    Ok(())
}

/// `Number.prototype.toLocaleString` core.
pub fn number_to_locale_string(
    value: f64,
    locales: &[String],
    options: &NumberFormatOptions,
    provider: &dyn NumberFormatDataProvider,
    host: &dyn HostLocaleHook,
) -> Result<String, NumberFormatError> {
    NumberFormat::new(locales, options, provider, host)?.format_number(value)
}

/// `BigInt.prototype.toLocaleString` core.
pub fn bigint_to_locale_string(
    value: &str,
    locales: &[String],
    options: &NumberFormatOptions,
    provider: &dyn NumberFormatDataProvider,
    host: &dyn HostLocaleHook,
) -> Result<String, NumberFormatError> {
    NumberFormat::new(locales, options, provider, host)?.format_bigint(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Default)]
    struct TestHost;

    impl HostLocaleHook for TestHost {
        fn preferred_locales(&self) -> Vec<String> {
            vec![String::from("en")]
        }
    }

    struct TestProvider {
        available: Vec<String>,
        en_numbering: Vec<String>,
        hi_numbering: Vec<String>,
        decimal: String,
    }

    impl TestProvider {
        fn new() -> Self {
            Self {
                available: vec![String::from("en"), String::from("hi")],
                en_numbering: vec![String::from("latn"), String::from("deva")],
                hi_numbering: vec![String::from("deva"), String::from("latn")],
                decimal: String::from("."),
            }
        }

        fn with_decimal(mut self, decimal: &str) -> Self {
            self.decimal = decimal.to_owned();
            self
        }
    }

    impl LocaleDataProvider for TestProvider {
        fn available_locales(&self) -> &[String] {
            &self.available
        }

        fn key_values(&self, data_locale: &str, key: &str) -> &[String] {
            if key != "nu" {
                return &[];
            }
            match data_locale {
                "en" => &self.en_numbering,
                "hi" => &self.hi_numbering,
                _ => &[],
            }
        }

        fn fallback_locale(&self) -> Option<&str> {
            Some("en")
        }
    }

    impl NumberFormatDataProvider for TestProvider {
        fn number_symbols(
            &self,
            _data_locale: &str,
            numbering_system: &str,
        ) -> Option<NumberSymbols> {
            let digits = match numbering_system {
                "latn" => ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'],
                "deva" => ['०', '१', '२', '३', '४', '५', '६', '७', '८', '९'],
                _ => return None,
            };
            Some(NumberSymbols {
                digits,
                decimal: self.decimal.clone(),
                group: String::from(","),
                plus_sign: String::from("+"),
                minus_sign: String::from("−"),
                percent_sign: String::from("%"),
                infinity: String::from("∞"),
                nan: String::from("NaN"),
                exponent_separator: String::from("E"),
                approximately_sign: String::from("≈"),
            })
        }

        fn grouping_sizes(
            &self,
            data_locale: &str,
            _numbering_system: &str,
        ) -> Option<GroupingSizes> {
            Some(if data_locale == "hi" {
                GroupingSizes {
                    primary: 3,
                    secondary: 2,
                    minimum_grouping_digits: 1,
                }
            } else {
                GroupingSizes {
                    primary: 3,
                    secondary: 3,
                    minimum_grouping_digits: 1,
                }
            })
        }

        fn number_patterns(
            &self,
            _data_locale: &str,
            request: NumberPatternRequest<'_>,
        ) -> Option<NumberPatternSet> {
            let affixes = match request.style {
                NumberStyle::Decimal => ("{number}", "{plusSign}{number}", "{minusSign}{number}"),
                NumberStyle::Percent => (
                    "{number}{percentSign}",
                    "{plusSign}{number}{percentSign}",
                    "{minusSign}{number}{percentSign}",
                ),
                NumberStyle::Currency
                    if request.currency_sign == Some(CurrencySign::Accounting) =>
                {
                    (
                        "{currencyPrefix}{number}",
                        "{plusSign}{currencyPrefix}{number}",
                        "({currencyPrefix}{number})",
                    )
                }
                NumberStyle::Currency => (
                    "{currencyPrefix}{number}",
                    "{plusSign}{currencyPrefix}{number}",
                    "{minusSign}{currencyPrefix}{number}",
                ),
                NumberStyle::Unit => (
                    "{number} {unitSuffix}",
                    "{plusSign}{number} {unitSuffix}",
                    "{minusSign}{number} {unitSuffix}",
                ),
            };
            Some(NumberPatternSet {
                zero: affixes.0.to_owned(),
                positive: affixes.1.to_owned(),
                negative: affixes.2.to_owned(),
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
            let short = match exponent {
                3 => "K",
                6 => "M",
                9 => "B",
                12 => "T",
                _ => return None,
            };
            let long = match exponent {
                3 => "thousand",
                6 => "million",
                9 => "billion",
                12 => "trillion",
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
            match currency {
                "JPY" => Some(0),
                "KWD" => Some(3),
                "CLF" => Some(4),
                "USD" => Some(2),
                _ => None,
            }
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
                CurrencyDisplay::Symbol | CurrencyDisplay::NarrowSymbol => match currency {
                    "USD" => Some(String::from("$")),
                    "JPY" => Some(String::from("¥")),
                    "KWD" => Some(String::from("KD")),
                    "CLF" => Some(String::from("UF")),
                    _ => None,
                },
                CurrencyDisplay::Name if currency == "USD" => {
                    Some(if category == PluralCategory::One {
                        String::from("US dollar")
                    } else {
                        String::from("US dollars")
                    })
                }
                CurrencyDisplay::Name => None,
            }
        }

        fn unit_display(
            &self,
            _data_locale: &str,
            unit: &str,
            display: UnitDisplay,
            category: PluralCategory,
        ) -> Option<String> {
            match (unit, display) {
                ("meter", UnitDisplay::Long) => Some(if category == PluralCategory::One {
                    String::from("meter")
                } else {
                    String::from("meters")
                }),
                ("meter", UnitDisplay::Short | UnitDisplay::Narrow) => Some(String::from("m")),
                ("meter-per-second", _) => Some(String::from("m/s")),
                _ => None,
            }
        }

        fn plural_category(&self, _data_locale: &str, operands: &PluralOperands) -> PluralCategory {
            if operands.integer_digits == "1"
                && operands.visible_fraction_digits == 0
                && operands.exponent == 0
            {
                PluralCategory::One
            } else {
                PluralCategory::Other
            }
        }

        fn range_patterns(
            &self,
            _data_locale: &str,
            _numbering_system: &str,
        ) -> Option<RangePatterns> {
            Some(RangePatterns {
                separator: String::from("–"),
                approximate: String::from("{approximatelySign}{number}"),
            })
        }
    }

    fn formatter(options: NumberFormatOptions) -> Result<NumberFormat<'static>, NumberFormatError> {
        let provider = Box::leak(Box::new(TestProvider::new()));
        let host = Box::leak(Box::new(TestHost));
        NumberFormat::new(&[String::from("en")], &options, provider, host)
    }

    fn fixed_options(digits: f64, mode: &str) -> NumberFormatOptions {
        NumberFormatOptions {
            minimum_fraction_digits: Some(digits),
            maximum_fraction_digits: Some(digits),
            rounding_mode: Some(mode.to_owned()),
            ..NumberFormatOptions::default()
        }
    }

    #[test]
    fn finite_non_finite_percent_and_negative_zero() {
        let decimal = formatter(NumberFormatOptions::default()).expect("formatter");
        assert_eq!(
            decimal.format_number(12_345.678).expect("finite"),
            "12,345.678"
        );
        assert_eq!(decimal.format_number(f64::INFINITY).expect("infinity"), "∞");
        assert_eq!(
            decimal
                .format_number(f64::NEG_INFINITY)
                .expect("negative infinity"),
            "−∞"
        );
        assert_eq!(decimal.format_number(f64::NAN).expect("NaN"), "NaN");
        assert_eq!(decimal.format_number(-0.0).expect("negative zero"), "−0");

        let percent = formatter(NumberFormatOptions {
            style: Some(String::from("percent")),
            ..NumberFormatOptions::default()
        })
        .expect("percent formatter");
        assert_eq!(percent.format_number(0.126).expect("percent"), "13%");
    }

    #[test]
    fn sign_display_distinguishes_negative_zero() {
        let cases = [
            ("auto", "−0", "0", "−1", "1"),
            ("never", "0", "0", "1", "1"),
            ("always", "−0", "+0", "−1", "+1"),
            ("exceptZero", "0", "0", "−1", "+1"),
            ("negative", "0", "0", "−1", "1"),
        ];
        for (mode, negative_zero, positive_zero, negative, positive) in cases {
            let formatter = formatter(NumberFormatOptions {
                sign_display: Some(mode.to_owned()),
                ..NumberFormatOptions::default()
            })
            .expect("sign formatter");
            assert_eq!(
                formatter.format_number(-0.0).expect("-0"),
                negative_zero,
                "{mode}"
            );
            assert_eq!(
                formatter.format_number(0.0).expect("0"),
                positive_zero,
                "{mode}"
            );
            assert_eq!(
                formatter.format_number(-1.0).expect("-1"),
                negative,
                "{mode}"
            );
            assert_eq!(formatter.format_number(1.0).expect("1"), positive, "{mode}");
        }
    }

    #[test]
    fn bigint_is_exact_and_grouped() {
        let formatter = formatter(NumberFormatOptions::default()).expect("formatter");
        assert_eq!(
            formatter
                .format_bigint("123456789012345678901234567890")
                .expect("large bigint"),
            "123,456,789,012,345,678,901,234,567,890"
        );
        assert_eq!(
            formatter
                .format_bigint("-100000000000000000001")
                .expect("negative bigint"),
            "−100,000,000,000,000,000,001"
        );
    }

    #[test]
    fn currency_minor_units_and_accounting_are_provider_driven() {
        for (currency, expected) in [
            ("JPY", "¥1"),
            ("USD", "$1.23"),
            ("KWD", "KD1.235"),
            ("CLF", "UF1.2346"),
            ("XXX", "XXX1.23"),
        ] {
            let formatter = formatter(NumberFormatOptions {
                style: Some(String::from("currency")),
                currency: Some(currency.to_owned()),
                ..NumberFormatOptions::default()
            })
            .expect("currency formatter");
            assert_eq!(
                formatter.format_number(1.23456).expect("currency"),
                expected,
                "{currency}"
            );
        }
        let accounting = formatter(NumberFormatOptions {
            style: Some(String::from("currency")),
            currency: Some(String::from("USD")),
            currency_sign: Some(String::from("accounting")),
            ..NumberFormatOptions::default()
        })
        .expect("accounting formatter");
        assert_eq!(
            accounting.format_number(-2.0).expect("accounting"),
            "($2.00)"
        );
    }

    #[test]
    fn option_validation_and_increment_conflicts_have_spec_error_kinds() {
        let missing_currency = formatter(NumberFormatOptions {
            style: Some(String::from("currency")),
            ..NumberFormatOptions::default()
        })
        .err()
        .expect("missing currency");
        assert_eq!(missing_currency.kind, NumberFormatErrorKind::TypeError);
        let invalid_unit = formatter(NumberFormatOptions {
            style: Some(String::from("unit")),
            unit: Some(String::from("horsepower")),
            ..NumberFormatOptions::default()
        })
        .err()
        .expect("invalid unit");
        assert_eq!(invalid_unit.kind, NumberFormatErrorKind::RangeError);
        let invalid_increment = formatter(NumberFormatOptions {
            rounding_increment: Some(3.0),
            ..NumberFormatOptions::default()
        })
        .err()
        .expect("invalid increment");
        assert_eq!(invalid_increment.kind, NumberFormatErrorKind::RangeError);
        let significant_increment = formatter(NumberFormatOptions {
            rounding_increment: Some(5.0),
            minimum_significant_digits: Some(2.0),
            ..NumberFormatOptions::default()
        })
        .err()
        .expect("significant increment conflict");
        assert_eq!(significant_increment.kind, NumberFormatErrorKind::TypeError);
        let unequal_increment = formatter(NumberFormatOptions {
            rounding_increment: Some(5.0),
            minimum_fraction_digits: Some(1.0),
            maximum_fraction_digits: Some(2.0),
            ..NumberFormatOptions::default()
        })
        .err()
        .expect("unequal increment conflict");
        assert_eq!(unequal_increment.kind, NumberFormatErrorKind::RangeError);
        let inverted_digits = formatter(NumberFormatOptions {
            minimum_fraction_digits: Some(3.0),
            maximum_fraction_digits: Some(2.0),
            ..NumberFormatOptions::default()
        })
        .err()
        .expect("inverted digits");
        assert_eq!(inverted_digits.kind, NumberFormatErrorKind::RangeError);
        let nan_digits = formatter(NumberFormatOptions {
            minimum_fraction_digits: Some(f64::NAN),
            ..NumberFormatOptions::default()
        })
        .err()
        .expect("NaN digits");
        assert_eq!(nan_digits.kind, NumberFormatErrorKind::RangeError);
    }

    #[test]
    fn a_fraction_of_any_length_has_plural_operands() {
        let significant = formatter(NumberFormatOptions {
            maximum_significant_digits: Some(3.0),
            ..NumberFormatOptions::default()
        })
        .expect("significant");
        assert_eq!(
            significant.format_number(1e-300).expect("a Number"),
            format!("0.{}1", "0".repeat(299))
        );
    }

    #[test]
    fn a_value_below_the_range_of_a_number_is_formatted_exactly() {
        let tiny = IntlMathematicalValue::from_decimal_string("1e-400").expect("a decimal");
        let scientific = formatter(NumberFormatOptions {
            notation: Some("scientific".to_owned()),
            ..NumberFormatOptions::default()
        })
        .expect("scientific");
        assert_eq!(scientific.format(&tiny).expect("scientific"), "1E−400");
        let plain = formatter(NumberFormatOptions::default()).expect("plain");
        assert_eq!(plain.format(&tiny).expect("plain"), "0");
        let significant = formatter(NumberFormatOptions {
            maximum_significant_digits: Some(3.0),
            ..NumberFormatOptions::default()
        })
        .expect("significant");
        assert_eq!(
            significant.format(&tiny).expect("significant"),
            format!("0.{}1", "0".repeat(399))
        );

        // The text of this value would not fit in the heap, and only that form needs it.
        let far = IntlMathematicalValue::from_decimal_string("1e-2000000000").expect("a decimal");
        let refused = significant.format(&far).expect_err("too many zeros");
        assert_eq!(refused.kind, NumberFormatErrorKind::RangeError);
        assert_eq!(plain.format(&far).expect("plain"), "0");
        assert_eq!(
            scientific.format(&far).expect("scientific"),
            "1E−2000000000"
        );
    }

    #[test]
    fn rounding_ties_cover_all_direction_families() {
        let half_even = formatter(fixed_options(0.0, "halfEven")).expect("half even");
        assert_eq!(half_even.format_number(0.5).expect("0.5"), "0");
        assert_eq!(half_even.format_number(1.5).expect("1.5"), "2");
        assert_eq!(half_even.format_number(2.5).expect("2.5"), "2");
        assert_eq!(half_even.format_number(-1.5).expect("-1.5"), "−2");

        let half_trunc = formatter(fixed_options(0.0, "halfTrunc")).expect("half trunc");
        assert_eq!(half_trunc.format_number(1.5).expect("positive tie"), "1");
        assert_eq!(half_trunc.format_number(-1.5).expect("negative tie"), "−1");
        let half_ceil = formatter(fixed_options(0.0, "halfCeil")).expect("half ceil");
        assert_eq!(half_ceil.format_number(-1.5).expect("negative tie"), "−1");
        let half_floor = formatter(fixed_options(0.0, "halfFloor")).expect("half floor");
        assert_eq!(half_floor.format_number(1.5).expect("positive tie"), "1");

        let increment = formatter(NumberFormatOptions {
            minimum_fraction_digits: Some(0.0),
            maximum_fraction_digits: Some(0.0),
            rounding_increment: Some(50.0),
            rounding_mode: Some(String::from("halfEven")),
            ..NumberFormatOptions::default()
        })
        .expect("increment formatter");
        assert_eq!(increment.format_number(25.0).expect("lower tie"), "0");
        assert_eq!(increment.format_number(75.0).expect("upper tie"), "100");
    }

    #[test]
    fn number_shortest_decimal_not_binary_expansion_is_rounded() {
        let formatter = formatter(fixed_options(2.0, "halfExpand")).expect("fixed formatter");
        assert_eq!(
            formatter.format_number(1.005).expect("shortest decimal"),
            "1.01"
        );
        assert_eq!(formatter.format_number(0.1 + 0.2).expect("sum"), "0.30");
    }

    #[test]
    fn rounding_priorities_and_trailing_zero_display() {
        let more = formatter(NumberFormatOptions {
            minimum_fraction_digits: Some(2.0),
            maximum_fraction_digits: Some(2.0),
            minimum_significant_digits: Some(2.0),
            maximum_significant_digits: Some(2.0),
            rounding_priority: Some(String::from("morePrecision")),
            ..NumberFormatOptions::default()
        })
        .expect("more precision");
        let less = formatter(NumberFormatOptions {
            rounding_priority: Some(String::from("lessPrecision")),
            ..more.resolved_options().into_test_options()
        })
        .expect("less precision");
        assert_eq!(more.format_number(1.234).expect("more"), "1.23");
        assert_eq!(less.format_number(1.234).expect("less"), "1.2");

        let stripped = formatter(NumberFormatOptions {
            minimum_fraction_digits: Some(2.0),
            maximum_fraction_digits: Some(2.0),
            trailing_zero_display: Some(String::from("stripIfInteger")),
            ..NumberFormatOptions::default()
        })
        .expect("strip formatter");
        assert_eq!(stripped.format_number(2.0).expect("integer"), "2");
        assert_eq!(stripped.format_number(2.5).expect("fraction"), "2.50");
    }

    impl ResolvedNumberFormatOptions {
        fn into_test_options(self) -> NumberFormatOptions {
            NumberFormatOptions {
                minimum_fraction_digits: self.minimum_fraction_digits.map(f64::from),
                maximum_fraction_digits: self.maximum_fraction_digits.map(f64::from),
                minimum_significant_digits: self.minimum_significant_digits.map(f64::from),
                maximum_significant_digits: self.maximum_significant_digits.map(f64::from),
                ..NumberFormatOptions::default()
            }
        }
    }

    #[test]
    fn scientific_engineering_and_compact_notation_have_exact_parts() {
        let scientific = formatter(NumberFormatOptions {
            notation: Some(String::from("scientific")),
            ..NumberFormatOptions::default()
        })
        .expect("scientific");
        assert_eq!(
            scientific.format_number(12_345.0).expect("scientific"),
            "1.235E4"
        );
        let scientific_parts = scientific.format_number_to_parts(0.0123).expect("parts");
        assert!(
            scientific_parts
                .iter()
                .any(|part| part.part_type == NumberPartType::ExponentSeparator)
        );
        assert!(
            scientific_parts
                .iter()
                .any(|part| part.part_type == NumberPartType::ExponentMinusSign)
        );
        assert!(
            scientific_parts
                .iter()
                .any(|part| part.part_type == NumberPartType::ExponentInteger)
        );

        let engineering = formatter(NumberFormatOptions {
            notation: Some(String::from("engineering")),
            ..NumberFormatOptions::default()
        })
        .expect("engineering");
        assert_eq!(
            engineering.format_number(12_345.0).expect("engineering"),
            "12.345E3"
        );

        let compact = formatter(NumberFormatOptions {
            notation: Some(String::from("compact")),
            ..NumberFormatOptions::default()
        })
        .expect("compact");
        assert_eq!(compact.format_number(1_234_567.0).expect("compact"), "1.2M");
        assert_eq!(
            compact.format_number(999_500.0).expect("compact carry"),
            "1M"
        );
        assert!(
            compact
                .format_number_to_parts(1_200.0)
                .expect("compact parts")
                .iter()
                .any(|part| part.part_type == NumberPartType::Compact && part.value == "K")
        );
    }

    #[test]
    fn parts_cover_currency_unit_group_fraction_and_percent() {
        let currency = formatter(NumberFormatOptions {
            style: Some(String::from("currency")),
            currency: Some(String::from("USD")),
            ..NumberFormatOptions::default()
        })
        .expect("currency");
        let parts = currency
            .format_number_to_parts(-1_234.5)
            .expect("currency parts");
        assert_eq!(
            parts.iter().map(|part| part.part_type).collect::<Vec<_>>(),
            vec![
                NumberPartType::MinusSign,
                NumberPartType::Currency,
                NumberPartType::Integer,
                NumberPartType::Group,
                NumberPartType::Integer,
                NumberPartType::Decimal,
                NumberPartType::Fraction,
            ]
        );
        assert_eq!(concatenate_parts(&parts), "−$1,234.50");

        let unit = formatter(NumberFormatOptions {
            style: Some(String::from("unit")),
            unit: Some(String::from("meter")),
            unit_display: Some(String::from("long")),
            ..NumberFormatOptions::default()
        })
        .expect("unit");
        assert_eq!(unit.format_number(1.0).expect("singular"), "1 meter");
        assert_eq!(unit.format_number(2.0).expect("plural"), "2 meters");
    }

    #[test]
    fn range_parts_annotate_sources_and_equal_results_are_approximate() {
        let formatter = formatter(NumberFormatOptions {
            maximum_fraction_digits: Some(1.0),
            ..NumberFormatOptions::default()
        })
        .expect("formatter");
        let start = IntlMathematicalValue::from_f64(1.2);
        let end = IntlMathematicalValue::from_f64(2.3);
        let parts = formatter
            .format_range_to_parts(&start, &end)
            .expect("range parts");
        assert!(
            parts
                .iter()
                .any(|part| part.source == RangeSource::StartRange)
        );
        assert!(
            parts
                .iter()
                .any(|part| part.source == RangeSource::EndRange)
        );
        assert!(
            parts
                .iter()
                .any(|part| part.source == RangeSource::Shared && part.value == "–")
        );
        assert_eq!(
            formatter.format_range(&start, &end).expect("range"),
            "1.2–2.3"
        );
        assert_eq!(
            formatter
                .format_range(&end, &start)
                .expect("reversed range"),
            "2.3–1.2"
        );

        let equal = formatter
            .format_range_to_parts(
                &IntlMathematicalValue::from_f64(1.21),
                &IntlMathematicalValue::from_f64(1.24),
            )
            .expect("approximately equal");
        assert!(equal.iter().all(|part| part.source == RangeSource::Shared));
        assert_eq!(
            equal.first().map(|part| part.part_type),
            Some(NumberPartType::ApproximatelySign)
        );
        assert_eq!(
            equal
                .iter()
                .map(|part| part.value.as_str())
                .collect::<String>(),
            "≈1.2"
        );

        let nan_error = formatter
            .format_range(
                &IntlMathematicalValue::Nan,
                &IntlMathematicalValue::from_f64(1.0),
            )
            .expect_err("NaN endpoint");
        assert_eq!(nan_error.kind, NumberFormatErrorKind::RangeError);
    }

    #[test]
    fn locale_numbering_system_and_grouping_resolution_are_provider_driven() {
        let provider = TestProvider::new();
        let formatter = NumberFormat::new(
            &[String::from("hi-u-nu-latn")],
            &NumberFormatOptions {
                numbering_system: Some(String::from("deva")),
                ..NumberFormatOptions::default()
            },
            &provider,
            &TestHost,
        )
        .expect("resolved formatter");
        assert_eq!(formatter.resolved_options().locale, "hi");
        assert_eq!(formatter.resolved_options().numbering_system, "deva");
        assert_eq!(
            formatter
                .format_number(12_345_678.0)
                .expect("Indian grouping"),
            "१,२३,४५,६७८"
        );

        let no_group = NumberFormat::new(
            &[String::from("en")],
            &NumberFormatOptions {
                use_grouping: Some(UseGroupingOption::Boolean(false)),
                ..NumberFormatOptions::default()
            },
            &provider,
            &TestHost,
        )
        .expect("no grouping");
        assert_eq!(
            no_group.format_number(12_345.0).expect("ungrouped"),
            "12345"
        );
    }

    #[test]
    fn provider_determinism_and_no_hidden_english_fallback() {
        let options = NumberFormatOptions {
            maximum_fraction_digits: Some(1.0),
            ..NumberFormatOptions::default()
        };
        let first_provider = TestProvider::new().with_decimal("·");
        let second_provider = TestProvider::new().with_decimal("·");
        let first = NumberFormat::new(&[String::from("en")], &options, &first_provider, &TestHost)
            .expect("first formatter")
            .format_number(12.5)
            .expect("first output");
        let second =
            NumberFormat::new(&[String::from("en")], &options, &second_provider, &TestHost)
                .expect("second formatter")
                .format_number(12.5)
                .expect("second output");
        assert_eq!(first, "12·5");
        assert_eq!(first, second);
    }

    #[test]
    fn free_to_locale_string_entry_points_share_the_core() {
        let provider = TestProvider::new();
        assert_eq!(
            number_to_locale_string(
                1_234.5,
                &[],
                &NumberFormatOptions::default(),
                &provider,
                &TestHost
            )
            .expect("Number toLocaleString"),
            "1,234.5"
        );
        assert_eq!(
            bigint_to_locale_string(
                "12345678901234567890",
                &[],
                &NumberFormatOptions::default(),
                &provider,
                &TestHost,
            )
            .expect("BigInt toLocaleString"),
            "12,345,678,901,234,567,890"
        );
    }
}
