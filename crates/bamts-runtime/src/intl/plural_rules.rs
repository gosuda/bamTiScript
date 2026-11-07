//! Deterministic ECMA-402 service cores for plural rules, relative time,
//! list formatting, text segmentation, and display names.
//!
//! Locale, CLDR, Unicode segmentation, and number-symbol data are injected
//! through [`IntlServiceDataProvider`]. This module never reads ambient host
//! state and contains no guessed locale tables.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::sync::Arc;

use super::locale_negotiation::{
    HostLocaleHook, LanguageTag, LocaleDataProvider, LocaleError, LocaleMatcher,
    canonicalize_unicode_locale_id, default_locale, resolve_locale,
};

/// The JavaScript or host error class associated with an Intl failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IntlErrorKind {
    /// A required option is absent.
    TypeError,
    /// An identifier, option, or numeric input is outside its permitted range.
    RangeError,
    /// Required provider data is absent or internally inconsistent.
    DataError,
}

/// A deterministic service-core failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IntlError {
    /// Locale parsing or negotiation failed.
    Locale(LocaleError),
    /// A required option is absent.
    MissingOption(&'static str),
    /// An option string is not one of the sanctioned values.
    InvalidOption {
        /// Option property name.
        name: &'static str,
        /// Rejected value.
        value: String,
    },
    /// A numeric option is outside its permitted inclusive bounds.
    InvalidNumberOption {
        /// Option property name.
        name: &'static str,
        /// Rejected value.
        value: u32,
    },
    /// A service identifier is structurally invalid.
    InvalidIdentifier {
        /// Identifier family.
        kind: &'static str,
        /// Rejected identifier.
        value: String,
    },
    /// A numeric argument is not permitted by the operation.
    InvalidNumber(&'static str),
    /// The provider has no data for a resolved service request.
    MissingData {
        /// Service or data family.
        service: &'static str,
        /// Resolved provider locale.
        locale: String,
    },
    /// The provider returned malformed data.
    InvalidData(&'static str),
}

impl IntlError {
    /// Returns the error class a runtime adapter should expose.
    #[must_use]
    pub const fn kind(&self) -> IntlErrorKind {
        match self {
            Self::MissingOption(_) => IntlErrorKind::TypeError,
            Self::Locale(_)
            | Self::InvalidOption { .. }
            | Self::InvalidNumberOption { .. }
            | Self::InvalidIdentifier { .. }
            | Self::InvalidNumber(_) => IntlErrorKind::RangeError,
            Self::MissingData { .. } | Self::InvalidData(_) => IntlErrorKind::DataError,
        }
    }
}

impl fmt::Display for IntlError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Locale(error) => error.fmt(formatter),
            Self::MissingOption(name) => write!(formatter, "missing required option: {name}"),
            Self::InvalidOption { name, value } => {
                write!(formatter, "invalid {name} option: {value}")
            }
            Self::InvalidNumberOption { name, value } => {
                write!(formatter, "invalid {name} option: {value}")
            }
            Self::InvalidIdentifier { kind, value } => {
                write!(formatter, "invalid {kind} identifier: {value}")
            }
            Self::InvalidNumber(operation) => {
                write!(formatter, "invalid numeric argument to {operation}")
            }
            Self::MissingData { service, locale } => {
                write!(formatter, "missing {service} data for locale {locale}")
            }
            Self::InvalidData(message) => write!(formatter, "invalid provider data: {message}"),
        }
    }
}

impl Error for IntlError {}

impl From<LocaleError> for IntlError {
    fn from(value: LocaleError) -> Self {
        Self::Locale(value)
    }
}

/// CLDR plural-rule categories.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PluralCategory {
    /// `zero`.
    Zero,
    /// `one`.
    One,
    /// `two`.
    Two,
    /// `few`.
    Few,
    /// `many`.
    Many,
    /// `other`.
    Other,
}

impl PluralCategory {
    /// Returns the ECMA-402 string value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Zero => "zero",
            Self::One => "one",
            Self::Two => "two",
            Self::Few => "few",
            Self::Many => "many",
            Self::Other => "other",
        }
    }
}

/// The plural rule set selected by the `type` option.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PluralRuleType {
    /// Cardinal-number rules.
    Cardinal,
    /// Ordinal-number rules.
    Ordinal,
}

impl PluralRuleType {
    fn parse(value: Option<&str>) -> Result<Self, IntlError> {
        match value.unwrap_or("cardinal") {
            "cardinal" => Ok(Self::Cardinal),
            "ordinal" => Ok(Self::Ordinal),
            value => Err(invalid_option("type", value)),
        }
    }

    /// Returns the ECMA-402 string value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Cardinal => "cardinal",
            Self::Ordinal => "ordinal",
        }
    }
}

/// Decimal operands defined by Unicode TR35 plural rules.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PluralOperands {
    /// Absolute rounded number in non-exponential ASCII decimal notation.
    pub n: String,
    /// Integer digits without a sign or leading zero padding.
    pub i: String,
    /// Number of visible fraction digits, including trailing zeros.
    pub v: u32,
    /// Number of visible fraction digits after removing trailing zeros.
    pub w: u32,
    /// Visible fractional digits, retaining their width.
    pub f: String,
    /// Visible fractional digits after removing trailing zeros.
    pub t: String,
    /// Compact-decimal exponent operand. PluralRules always supplies zero.
    pub c: i32,
    /// Exponent operand. PluralRules always supplies zero.
    pub e: i32,
}

/// A non-finite value passed to the injected number formatter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NumberSpecial {
    /// Not-a-number.
    Nan,
    /// Positive or negative infinity; sign is carried by [`NumberInput::negative`].
    Infinity,
}

/// A locale-independent numeric value ready for symbol substitution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NumberInput {
    /// Absolute, rounded ASCII decimal for finite values.
    pub ascii: String,
    /// Whether the original value has a negative sign, including negative zero.
    pub negative: bool,
    /// Non-finite classification, when applicable.
    pub special: Option<NumberSpecial>,
}

/// Number-format part kinds used by RelativeTimeFormat.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NumberPartKind {
    /// Integer digits.
    Integer,
    /// Group separator.
    Group,
    /// Decimal separator.
    Decimal,
    /// Fraction digits.
    Fraction,
    /// Leading plus sign.
    PlusSign,
    /// Leading minus sign.
    MinusSign,
    /// NaN symbol.
    Nan,
    /// Infinity symbol.
    Infinity,
    /// Exponent separator.
    ExponentSeparator,
    /// Exponent minus sign.
    ExponentMinusSign,
    /// Exponent integer digits.
    ExponentInteger,
    /// Compact-notation affix.
    Compact,
    /// Percent sign.
    PercentSign,
    /// Currency token.
    Currency,
    /// Unit token.
    Unit,
    /// Other literal emitted by number formatting.
    Literal,
}

/// One provider-produced number-format part.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NumberPart {
    /// Semantic part kind.
    pub kind: NumberPartKind,
    /// Rendered text.
    pub value: String,
}

/// A formatted number and its lossless semantic partition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FormattedNumber {
    /// Complete rendered value.
    pub value: String,
    /// Parts whose values must concatenate to [`Self::value`].
    pub parts: Vec<NumberPart>,
}

/// Relative-time formatting widths.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RelativeTimeStyle {
    /// Long unit names.
    Long,
    /// Short unit names.
    Short,
    /// Narrow unit names.
    Narrow,
}

impl RelativeTimeStyle {
    fn parse(value: Option<&str>) -> Result<Self, IntlError> {
        match value.unwrap_or("long") {
            "long" => Ok(Self::Long),
            "short" => Ok(Self::Short),
            "narrow" => Ok(Self::Narrow),
            value => Err(invalid_option("style", value)),
        }
    }

    /// Returns the ECMA-402 string value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Long => "long",
            Self::Short => "short",
            Self::Narrow => "narrow",
        }
    }
}

/// Relative-time numeric substitution behavior.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RelativeTimeNumeric {
    /// Always format a numeric value.
    Always,
    /// Prefer locale terms such as “yesterday” when available.
    Auto,
}

impl RelativeTimeNumeric {
    fn parse(value: Option<&str>) -> Result<Self, IntlError> {
        match value.unwrap_or("always") {
            "always" => Ok(Self::Always),
            "auto" => Ok(Self::Auto),
            value => Err(invalid_option("numeric", value)),
        }
    }

    /// Returns the ECMA-402 string value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Always => "always",
            Self::Auto => "auto",
        }
    }
}

/// Canonical RelativeTimeFormat units.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RelativeTimeUnit {
    /// Second.
    Second,
    /// Minute.
    Minute,
    /// Hour.
    Hour,
    /// Day.
    Day,
    /// Week.
    Week,
    /// Month.
    Month,
    /// Quarter.
    Quarter,
    /// Year.
    Year,
}

impl RelativeTimeUnit {
    fn parse(value: &str) -> Result<Self, IntlError> {
        match value {
            "second" | "seconds" => Ok(Self::Second),
            "minute" | "minutes" => Ok(Self::Minute),
            "hour" | "hours" => Ok(Self::Hour),
            "day" | "days" => Ok(Self::Day),
            "week" | "weeks" => Ok(Self::Week),
            "month" | "months" => Ok(Self::Month),
            "quarter" | "quarters" => Ok(Self::Quarter),
            "year" | "years" => Ok(Self::Year),
            value => Err(IntlError::InvalidIdentifier {
                kind: "relative-time unit",
                value: value.to_owned(),
            }),
        }
    }

    /// Returns the singular ECMA-402 unit string.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Second => "second",
            Self::Minute => "minute",
            Self::Hour => "hour",
            Self::Day => "day",
            Self::Week => "week",
            Self::Month => "month",
            Self::Quarter => "quarter",
            Self::Year => "year",
        }
    }
}

/// Whether a numeric relative-time pattern describes the past or future.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RelativeTimeTense {
    /// Past, including negative zero.
    Past,
    /// Present or future.
    Future,
}

/// List semantic type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ListType {
    /// Conjunctive list.
    Conjunction,
    /// Disjunctive list.
    Disjunction,
    /// Unit sequence.
    Unit,
}

impl ListType {
    fn parse(value: Option<&str>) -> Result<Self, IntlError> {
        match value.unwrap_or("conjunction") {
            "conjunction" => Ok(Self::Conjunction),
            "disjunction" => Ok(Self::Disjunction),
            "unit" => Ok(Self::Unit),
            value => Err(invalid_option("type", value)),
        }
    }

    /// Returns the ECMA-402 string value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Conjunction => "conjunction",
            Self::Disjunction => "disjunction",
            Self::Unit => "unit",
        }
    }
}

/// List pattern width.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ListStyle {
    /// Long pattern.
    Long,
    /// Short pattern.
    Short,
    /// Narrow pattern.
    Narrow,
}

impl ListStyle {
    fn parse(value: Option<&str>) -> Result<Self, IntlError> {
        match value.unwrap_or("long") {
            "long" => Ok(Self::Long),
            "short" => Ok(Self::Short),
            "narrow" => Ok(Self::Narrow),
            value => Err(invalid_option("style", value)),
        }
    }

    /// Returns the ECMA-402 string value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Long => "long",
            Self::Short => "short",
            Self::Narrow => "narrow",
        }
    }
}

/// Which list pattern is requested from the provider.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ListPatternPosition {
    /// Exactly two elements.
    Pair,
    /// First two elements of a longer list.
    Start,
    /// Interior join in a longer list.
    Middle,
    /// Final join in a longer list.
    End,
}

/// Segmenter granularity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SegmenterGranularity {
    /// Extended grapheme clusters.
    Grapheme,
    /// Locale-sensitive words.
    Word,
    /// Locale-sensitive sentences.
    Sentence,
}

impl SegmenterGranularity {
    fn parse(value: Option<&str>) -> Result<Self, IntlError> {
        match value.unwrap_or("grapheme") {
            "grapheme" => Ok(Self::Grapheme),
            "word" => Ok(Self::Word),
            "sentence" => Ok(Self::Sentence),
            value => Err(invalid_option("granularity", value)),
        }
    }

    /// Returns the ECMA-402 string value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Grapheme => "grapheme",
            Self::Word => "word",
            Self::Sentence => "sentence",
        }
    }
}

/// One end boundary supplied by a Unicode segmentation provider.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProviderSegmentBoundary {
    /// Exclusive UTF-16 code-unit boundary.
    pub end: usize,
    /// Word-likeness status. Ignored for non-word granularities.
    pub is_word_like: bool,
}

/// DisplayNames semantic type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DisplayNamesType {
    /// Unicode language identifier.
    Language,
    /// Unicode region subtag.
    Region,
    /// Unicode script subtag.
    Script,
    /// ISO 4217 currency code.
    Currency,
    /// Unicode calendar type.
    Calendar,
    /// ECMA-402 date-time field identifier.
    DateTimeField,
}

impl DisplayNamesType {
    fn parse(value: Option<&str>) -> Result<Self, IntlError> {
        match value {
            Some("language") => Ok(Self::Language),
            Some("region") => Ok(Self::Region),
            Some("script") => Ok(Self::Script),
            Some("currency") => Ok(Self::Currency),
            Some("calendar") => Ok(Self::Calendar),
            Some("dateTimeField") => Ok(Self::DateTimeField),
            Some(value) => Err(invalid_option("type", value)),
            None => Err(IntlError::MissingOption("type")),
        }
    }

    /// Returns the ECMA-402 string value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Language => "language",
            Self::Region => "region",
            Self::Script => "script",
            Self::Currency => "currency",
            Self::Calendar => "calendar",
            Self::DateTimeField => "dateTimeField",
        }
    }
}

/// DisplayNames width.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DisplayNamesStyle {
    /// Long name.
    Long,
    /// Short name.
    Short,
    /// Narrow name.
    Narrow,
}

impl DisplayNamesStyle {
    fn parse(value: Option<&str>) -> Result<Self, IntlError> {
        match value.unwrap_or("long") {
            "long" => Ok(Self::Long),
            "short" => Ok(Self::Short),
            "narrow" => Ok(Self::Narrow),
            value => Err(invalid_option("style", value)),
        }
    }

    /// Returns the ECMA-402 string value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Long => "long",
            Self::Short => "short",
            Self::Narrow => "narrow",
        }
    }
}

/// DisplayNames missing-name behavior.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DisplayNamesFallback {
    /// Return the canonical input code.
    Code,
    /// Return no value.
    None,
}

impl DisplayNamesFallback {
    fn parse(value: Option<&str>) -> Result<Self, IntlError> {
        match value.unwrap_or("code") {
            "code" => Ok(Self::Code),
            "none" => Ok(Self::None),
            value => Err(invalid_option("fallback", value)),
        }
    }

    /// Returns the ECMA-402 string value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Code => "code",
            Self::None => "none",
        }
    }
}

/// Language-name presentation behavior.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LanguageDisplay {
    /// Prefer dialect names.
    Dialect,
    /// Prefer standard language names.
    Standard,
}

impl LanguageDisplay {
    fn parse(value: Option<&str>) -> Result<Self, IntlError> {
        match value.unwrap_or("dialect") {
            "dialect" => Ok(Self::Dialect),
            "standard" => Ok(Self::Standard),
            value => Err(invalid_option("languageDisplay", value)),
        }
    }

    /// Returns the ECMA-402 string value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Dialect => "dialect",
            Self::Standard => "standard",
        }
    }
}

/// All locale-dependent contracts required by the five service cores.
///
/// Implementations are expected to adapt maintained CLDR/ICU data. Returning
/// `None` means data is unavailable; the service reports a typed data failure
/// instead of guessing a locale fallback.
pub trait IntlServiceDataProvider {
    /// Locale negotiation and canonicalization data for this service bundle.
    fn locale_data(&self) -> &dyn LocaleDataProvider;

    /// Ordered plural categories exposed by `resolvedOptions()`.
    fn plural_categories(&self, _locale: &str, _rule_type: PluralRuleType) -> &[PluralCategory] {
        &[]
    }

    /// Evaluates one CLDR plural rule set.
    fn plural_category(
        &self,
        _locale: &str,
        _rule_type: PluralRuleType,
        _operands: &PluralOperands,
    ) -> Option<PluralCategory> {
        None
    }

    /// Resolves a CLDR plural-range category pair.
    fn plural_range(
        &self,
        _locale: &str,
        _start: PluralCategory,
        _end: PluralCategory,
    ) -> Option<PluralCategory> {
        None
    }

    /// Formats a pre-rounded numeric value using locale number symbols.
    fn format_number(
        &self,
        _locale: &str,
        _numbering_system: &str,
        _input: &NumberInput,
    ) -> Option<FormattedNumber> {
        None
    }

    /// Returns an exact numeric-auto relative-time term for an integral offset.
    fn relative_time_auto(
        &self,
        _locale: &str,
        _style: RelativeTimeStyle,
        _unit: RelativeTimeUnit,
        _offset: i64,
    ) -> Option<&str> {
        None
    }

    /// Returns a relative-time pattern containing exactly one `{0}` placeholder.
    fn relative_time_pattern(
        &self,
        _locale: &str,
        _style: RelativeTimeStyle,
        _unit: RelativeTimeUnit,
        _tense: RelativeTimeTense,
        _category: PluralCategory,
    ) -> Option<&str> {
        None
    }

    /// Returns a list pattern containing one `{0}` and one `{1}` placeholder.
    fn list_pattern(
        &self,
        _locale: &str,
        _list_type: ListType,
        _style: ListStyle,
        _position: ListPatternPosition,
    ) -> Option<&str> {
        None
    }

    /// Runs a maintained UAX #29/locale segmentation implementation over UTF-16.
    fn segment_boundaries(
        &self,
        _locale: &str,
        _granularity: SegmenterGranularity,
        _input: &[u16],
    ) -> Option<Vec<ProviderSegmentBoundary>> {
        None
    }

    /// Looks up a canonical display-name code.
    fn display_name(
        &self,
        _locale: &str,
        _style: DisplayNamesStyle,
        _name_type: DisplayNamesType,
        _language_display: LanguageDisplay,
        _code: &str,
    ) -> Option<&str> {
        None
    }
}

/// Raw PluralRules options after JavaScript property coercion.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PluralRulesOptions {
    /// `localeMatcher`.
    pub locale_matcher: Option<String>,
    /// `type`.
    pub plural_type: Option<String>,
    /// `minimumIntegerDigits`.
    pub minimum_integer_digits: Option<u8>,
    /// `minimumFractionDigits`.
    pub minimum_fraction_digits: Option<u8>,
    /// `maximumFractionDigits`.
    pub maximum_fraction_digits: Option<u8>,
    /// `minimumSignificantDigits`.
    pub minimum_significant_digits: Option<u8>,
    /// `maximumSignificantDigits`.
    pub maximum_significant_digits: Option<u8>,
    /// `roundingPriority`.
    pub rounding_priority: Option<String>,
    /// `roundingIncrement`.
    pub rounding_increment: Option<u16>,
    /// `roundingMode`.
    pub rounding_mode: Option<String>,
    /// `trailingZeroDisplay`.
    pub trailing_zero_display: Option<String>,
    /// `notation`.
    pub notation: Option<String>,
    /// `compactDisplay`.
    pub compact_display: Option<String>,
}

/// PluralRules rounding-priority mode.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RoundingPriority {
    /// Significant digits win when present; otherwise fraction digits are used.
    Auto,
    /// Select the result with the finer rounding magnitude.
    MorePrecision,
    /// Select the result with the coarser rounding magnitude.
    LessPrecision,
}

impl RoundingPriority {
    fn parse(value: Option<&str>) -> Result<Self, IntlError> {
        match value.unwrap_or("auto") {
            "auto" => Ok(Self::Auto),
            "morePrecision" => Ok(Self::MorePrecision),
            "lessPrecision" => Ok(Self::LessPrecision),
            value => Err(invalid_option("roundingPriority", value)),
        }
    }

    /// Returns the ECMA-402 string value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::MorePrecision => "morePrecision",
            Self::LessPrecision => "lessPrecision",
        }
    }
}

/// ECMA-402 unsigned rounding mode.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RoundingMode {
    /// Toward positive infinity.
    Ceil,
    /// Toward negative infinity.
    Floor,
    /// Away from zero.
    Expand,
    /// Toward zero.
    Trunc,
    /// Half toward positive infinity.
    HalfCeil,
    /// Half toward negative infinity.
    HalfFloor,
    /// Half away from zero.
    HalfExpand,
    /// Half toward zero.
    HalfTrunc,
    /// Half to even.
    HalfEven,
}

impl RoundingMode {
    fn parse(value: Option<&str>) -> Result<Self, IntlError> {
        match value.unwrap_or("halfExpand") {
            "ceil" => Ok(Self::Ceil),
            "floor" => Ok(Self::Floor),
            "expand" => Ok(Self::Expand),
            "trunc" => Ok(Self::Trunc),
            "halfCeil" => Ok(Self::HalfCeil),
            "halfFloor" => Ok(Self::HalfFloor),
            "halfExpand" => Ok(Self::HalfExpand),
            "halfTrunc" => Ok(Self::HalfTrunc),
            "halfEven" => Ok(Self::HalfEven),
            value => Err(invalid_option("roundingMode", value)),
        }
    }

    /// Returns the ECMA-402 string value.
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
}

/// ECMA-402 trailing-zero behavior.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TrailingZeroDisplay {
    /// Preserve zeros required by minimum digit options.
    Auto,
    /// Remove all fraction zeros when the rounded value is an integer.
    StripIfInteger,
}

impl TrailingZeroDisplay {
    fn parse(value: Option<&str>) -> Result<Self, IntlError> {
        match value.unwrap_or("auto") {
            "auto" => Ok(Self::Auto),
            "stripIfInteger" => Ok(Self::StripIfInteger),
            value => Err(invalid_option("trailingZeroDisplay", value)),
        }
    }

    /// Returns the ECMA-402 string value.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::StripIfInteger => "stripIfInteger",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RoundingType {
    FractionDigits,
    SignificantDigits,
    MorePrecision,
    LessPrecision,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DigitOptions {
    minimum_integer_digits: u8,
    minimum_fraction_digits: u8,
    maximum_fraction_digits: u8,
    minimum_significant_digits: u8,
    maximum_significant_digits: u8,
    has_significant_digits: bool,
    rounding_increment: u16,
    rounding_mode: RoundingMode,
    rounding_priority: RoundingPriority,
    rounding_type: RoundingType,
    trailing_zero_display: TrailingZeroDisplay,
}

impl DigitOptions {
    fn plural(options: &PluralRulesOptions) -> Result<Self, IntlError> {
        let minimum_integer_digits = option_in_range(
            "minimumIntegerDigits",
            u32::from(options.minimum_integer_digits.unwrap_or(1)),
            1,
            21,
        )? as u8;
        let priority = RoundingPriority::parse(options.rounding_priority.as_deref())?;
        let rounding_mode = RoundingMode::parse(options.rounding_mode.as_deref())?;
        let trailing_zero_display =
            TrailingZeroDisplay::parse(options.trailing_zero_display.as_deref())?;
        let has_significant = options.minimum_significant_digits.is_some()
            || options.maximum_significant_digits.is_some();
        let has_fraction =
            options.minimum_fraction_digits.is_some() || options.maximum_fraction_digits.is_some();
        let compact = options.notation.as_deref() == Some("compact");
        let need_significant = priority != RoundingPriority::Auto || has_significant;
        let need_fraction =
            priority != RoundingPriority::Auto || !(has_significant || (compact && !has_fraction));

        let (minimum_fraction_digits, maximum_fraction_digits) = if need_fraction {
            fraction_digit_bounds(options)?
        } else {
            (0, 0)
        };
        let (minimum_significant_digits, maximum_significant_digits) = if need_significant {
            significant_digit_bounds(options)?
        } else {
            (0, 0)
        };
        let rounding_increment = options.rounding_increment.unwrap_or(1);
        if !VALID_ROUNDING_INCREMENTS.contains(&rounding_increment) {
            return Err(IntlError::InvalidNumberOption {
                name: "roundingIncrement",
                value: u32::from(rounding_increment),
            });
        }
        if rounding_increment != 1
            && (priority != RoundingPriority::Auto
                || has_significant
                || minimum_fraction_digits != maximum_fraction_digits)
        {
            return Err(IntlError::InvalidOption {
                name: "roundingIncrement",
                value: rounding_increment.to_string(),
            });
        }
        if !need_significant && !need_fraction {
            return Ok(Self {
                minimum_integer_digits,
                minimum_fraction_digits: 0,
                maximum_fraction_digits: 0,
                minimum_significant_digits: 1,
                maximum_significant_digits: 2,
                has_significant_digits: true,
                rounding_increment,
                rounding_mode,
                rounding_priority: RoundingPriority::MorePrecision,
                rounding_type: RoundingType::MorePrecision,
                trailing_zero_display,
            });
        }
        let rounding_type = match priority {
            RoundingPriority::MorePrecision => RoundingType::MorePrecision,
            RoundingPriority::LessPrecision => RoundingType::LessPrecision,
            RoundingPriority::Auto if has_significant => RoundingType::SignificantDigits,
            RoundingPriority::Auto => RoundingType::FractionDigits,
        };
        Ok(Self {
            minimum_integer_digits,
            minimum_fraction_digits,
            maximum_fraction_digits,
            minimum_significant_digits,
            maximum_significant_digits,
            has_significant_digits: need_significant,
            rounding_increment,
            rounding_mode,
            rounding_priority: priority,
            rounding_type,
            trailing_zero_display,
        })
    }

    const fn relative_time_default() -> Self {
        Self {
            minimum_integer_digits: 1,
            minimum_fraction_digits: 0,
            maximum_fraction_digits: 3,
            minimum_significant_digits: 0,
            maximum_significant_digits: 0,
            has_significant_digits: false,
            rounding_increment: 1,
            rounding_mode: RoundingMode::HalfExpand,
            rounding_priority: RoundingPriority::Auto,
            rounding_type: RoundingType::FractionDigits,
            trailing_zero_display: TrailingZeroDisplay::Auto,
        }
    }
}

const VALID_ROUNDING_INCREMENTS: &[u16] = &[
    1, 2, 5, 10, 20, 25, 50, 100, 200, 250, 500, 1_000, 2_000, 2_500, 5_000,
];

fn fraction_digit_bounds(options: &PluralRulesOptions) -> Result<(u8, u8), IntlError> {
    let minimum = match options.minimum_fraction_digits {
        Some(value) => option_in_range("minimumFractionDigits", u32::from(value), 0, 100)? as u8,
        None => 0,
    };
    let maximum = match options.maximum_fraction_digits {
        Some(value) => option_in_range("maximumFractionDigits", u32::from(value), 0, 100)? as u8,
        None => minimum.max(3),
    };
    if minimum > maximum {
        return Err(IntlError::InvalidOption {
            name: "maximumFractionDigits",
            value: maximum.to_string(),
        });
    }
    Ok((minimum, maximum))
}

fn significant_digit_bounds(options: &PluralRulesOptions) -> Result<(u8, u8), IntlError> {
    let minimum = match options.minimum_significant_digits {
        Some(value) => option_in_range("minimumSignificantDigits", u32::from(value), 1, 21)? as u8,
        None => 1,
    };
    let maximum = match options.maximum_significant_digits {
        Some(value) => option_in_range("maximumSignificantDigits", u32::from(value), 1, 21)? as u8,
        None => 21,
    };
    if minimum > maximum {
        return Err(IntlError::InvalidOption {
            name: "maximumSignificantDigits",
            value: maximum.to_string(),
        });
    }
    Ok((minimum, maximum))
}

fn option_in_range(
    name: &'static str,
    value: u32,
    minimum: u32,
    maximum: u32,
) -> Result<u32, IntlError> {
    if (minimum..=maximum).contains(&value) {
        Ok(value)
    } else {
        Err(IntlError::InvalidNumberOption { name, value })
    }
}

fn invalid_option(name: &'static str, value: &str) -> IntlError {
    IntlError::InvalidOption {
        name,
        value: value.to_owned(),
    }
}

fn parse_locale_matcher(value: Option<&str>) -> Result<LocaleMatcher, IntlError> {
    match value.unwrap_or("best fit") {
        "lookup" => Ok(LocaleMatcher::Lookup),
        "best fit" | "bestFit" => Ok(LocaleMatcher::BestFit),
        value => Err(invalid_option("localeMatcher", value)),
    }
}

fn requested_with_default(
    requested: &[String],
    host: &dyn HostLocaleHook,
    provider: &dyn LocaleDataProvider,
) -> Result<Vec<String>, IntlError> {
    if requested.is_empty() {
        Ok(vec![default_locale(host, provider)?])
    } else {
        Ok(requested.to_vec())
    }
}

fn resolve_service_locale(
    requested: &[String],
    host: &dyn HostLocaleHook,
    provider: &dyn LocaleDataProvider,
    matcher: LocaleMatcher,
    options: &BTreeMap<String, String>,
    keys: &[String],
) -> Result<super::locale_negotiation::ResolvedLocale, IntlError> {
    let requested = requested_with_default(requested, host, provider)?;
    Ok(resolve_locale(
        &requested, options, keys, matcher, provider,
    )?)
}

/// The exact values reported by `PluralRules.prototype.resolvedOptions`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PluralRulesResolvedOptions {
    /// Resolved locale.
    pub locale: String,
    /// Rule type.
    pub plural_type: PluralRuleType,
    /// Minimum integer digits.
    pub minimum_integer_digits: u8,
    /// Minimum fraction digits when fraction rounding is active.
    pub minimum_fraction_digits: Option<u8>,
    /// Maximum fraction digits when fraction rounding is active.
    pub maximum_fraction_digits: Option<u8>,
    /// Minimum significant digits when significant rounding is active.
    pub minimum_significant_digits: Option<u8>,
    /// Maximum significant digits when significant rounding is active.
    pub maximum_significant_digits: Option<u8>,
    /// Rounding increment.
    pub rounding_increment: u16,
    /// Rounding mode.
    pub rounding_mode: RoundingMode,
    /// Rounding priority.
    pub rounding_priority: RoundingPriority,
    /// Trailing-zero behavior.
    pub trailing_zero_display: TrailingZeroDisplay,
    /// Provider-defined observable category order.
    pub plural_categories: Vec<PluralCategory>,
    /// Resolved notation.
    pub notation: String,
    /// Resolved compact display, for compact notation.
    pub compact_display: Option<String>,
}

/// ECMA-402 PluralRules service core.
#[derive(Clone)]
pub struct PluralRules<'a> {
    provider: &'a dyn IntlServiceDataProvider,
    locale: String,
    data_locale: String,
    rule_type: PluralRuleType,
    digits: DigitOptions,
    categories: Vec<PluralCategory>,
    notation: String,
    compact_display: Option<String>,
}

impl<'a> PluralRules<'a> {
    /// Constructs a plural-rule service from explicit locale and host inputs.
    ///
    /// # Errors
    /// Returns a typed error for invalid options, locale negotiation failure, or
    /// missing/inconsistent provider data.
    pub fn try_new(
        requested_locales: &[String],
        options: &PluralRulesOptions,
        provider: &'a dyn IntlServiceDataProvider,
        host: &dyn HostLocaleHook,
    ) -> Result<Self, IntlError> {
        let matcher = parse_locale_matcher(options.locale_matcher.as_deref())?;
        let rule_type = PluralRuleType::parse(options.plural_type.as_deref())?;
        let digits = DigitOptions::plural(options)?;
        let resolved = resolve_service_locale(
            requested_locales,
            host,
            provider.locale_data(),
            matcher,
            &BTreeMap::new(),
            &[],
        )?;
        let categories = provider
            .plural_categories(&resolved.data_locale, rule_type)
            .to_vec();
        validate_plural_categories(&categories)?;
        Ok(Self {
            provider,
            locale: resolved.locale,
            data_locale: resolved.data_locale,
            rule_type,
            digits,
            categories,
            notation: options
                .notation
                .clone()
                .unwrap_or_else(|| String::from("standard")),
            compact_display: (options.notation.as_deref() == Some("compact")).then(|| {
                options
                    .compact_display
                    .clone()
                    .unwrap_or_else(|| String::from("short"))
            }),
        })
    }

    /// Returns the category for one number.
    ///
    /// Non-finite values always select `other`, as required by ECMA-402.
    ///
    /// # Errors
    /// Returns a data error when the provider has no category for finite input.
    pub fn select(&self, value: f64) -> Result<PluralCategory, IntlError> {
        if !value.is_finite() {
            return Ok(PluralCategory::Other);
        }
        self.select_finite(value)
    }

    /// Returns the locale-defined plural range category.
    ///
    /// # Errors
    /// Returns a range error for NaN and a data error when the provider lacks
    /// the selected category or range mapping.
    pub fn select_range(&self, start: f64, end: f64) -> Result<PluralCategory, IntlError> {
        if start.is_nan() || end.is_nan() {
            return Err(IntlError::InvalidNumber("PluralRules.selectRange"));
        }
        let start_category = self.select(start)?;
        let end_category = self.select(end)?;
        self.provider
            .plural_range(&self.data_locale, start_category, end_category)
            .ok_or_else(|| IntlError::MissingData {
                service: "plural range",
                locale: self.data_locale.clone(),
            })
    }

    /// Returns all resolved options without consulting the provider again.
    #[must_use]
    pub fn resolved_options(&self) -> PluralRulesResolvedOptions {
        let fraction_active = matches!(
            self.digits.rounding_type,
            RoundingType::FractionDigits
                | RoundingType::MorePrecision
                | RoundingType::LessPrecision
        );
        PluralRulesResolvedOptions {
            locale: self.locale.clone(),
            plural_type: self.rule_type,
            minimum_integer_digits: self.digits.minimum_integer_digits,
            minimum_fraction_digits: fraction_active.then_some(self.digits.minimum_fraction_digits),
            maximum_fraction_digits: fraction_active.then_some(self.digits.maximum_fraction_digits),
            minimum_significant_digits: self
                .digits
                .has_significant_digits
                .then_some(self.digits.minimum_significant_digits),
            maximum_significant_digits: self
                .digits
                .has_significant_digits
                .then_some(self.digits.maximum_significant_digits),
            rounding_increment: self.digits.rounding_increment,
            rounding_mode: self.digits.rounding_mode,
            rounding_priority: self.digits.rounding_priority,
            trailing_zero_display: self.digits.trailing_zero_display,
            plural_categories: self.categories.clone(),
            notation: self.notation.clone(),
            compact_display: self.compact_display.clone(),
        }
    }

    fn select_finite(&self, value: f64) -> Result<PluralCategory, IntlError> {
        let rounded = round_finite(value, self.digits);
        let operands = plural_operands(&rounded.formatted);
        let category = self
            .provider
            .plural_category(&self.data_locale, self.rule_type, &operands)
            .ok_or_else(|| IntlError::MissingData {
                service: "plural rules",
                locale: self.data_locale.clone(),
            })?;
        if self.categories.contains(&category) {
            Ok(category)
        } else {
            Err(IntlError::InvalidData(
                "plural rule returned an unadvertised category",
            ))
        }
    }
}

fn validate_plural_categories(categories: &[PluralCategory]) -> Result<(), IntlError> {
    let unique = categories.iter().copied().collect::<BTreeSet<_>>();
    if categories.is_empty()
        || unique.len() != categories.len()
        || !categories.contains(&PluralCategory::Other)
    {
        return Err(IntlError::InvalidData(
            "plural categories must be unique and contain other",
        ));
    }
    Ok(())
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RoundedDecimal {
    formatted: String,
    rounding_magnitude: i32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ExactDecimal {
    digits: Vec<u8>,
    decimal_position: i32,
}

impl ExactDecimal {
    fn from_f64(value: f64) -> Self {
        let rendered = format!("{:.1074}", value.abs());
        let (integer, fraction) = rendered
            .split_once('.')
            .expect("fixed float formatting always contains a decimal point");
        let mut digits = Vec::with_capacity(integer.len() + fraction.len());
        digits.extend(integer.bytes().map(|byte| byte - b'0'));
        digits.extend(fraction.bytes().map(|byte| byte - b'0'));
        while digits.len() > 1 && digits.last() == Some(&0) {
            digits.pop();
        }
        Self {
            digits,
            decimal_position: i32::try_from(integer.len()).expect("float text length fits i32"),
        }
    }

    fn magnitude(&self) -> i32 {
        self.digits
            .iter()
            .position(|digit| *digit != 0)
            .map_or(0, |position| {
                self.decimal_position
                    - i32::try_from(position).expect("float digit count fits i32")
                    - 1
            })
    }
}

fn round_finite(value: f64, options: DigitOptions) -> RoundedDecimal {
    let exact = ExactDecimal::from_f64(value);
    match options.rounding_type {
        RoundingType::FractionDigits => round_fraction(&exact, value.is_sign_negative(), options),
        RoundingType::SignificantDigits => {
            round_significant(&exact, value.is_sign_negative(), options)
        }
        RoundingType::MorePrecision | RoundingType::LessPrecision => {
            let fraction = round_fraction(&exact, value.is_sign_negative(), options);
            let significant = round_significant(&exact, value.is_sign_negative(), options);
            match options.rounding_type {
                RoundingType::MorePrecision
                    if significant.rounding_magnitude < fraction.rounding_magnitude =>
                {
                    significant
                }
                RoundingType::LessPrecision
                    if significant.rounding_magnitude > fraction.rounding_magnitude =>
                {
                    significant
                }
                _ => fraction,
            }
        }
    }
}

fn round_fraction(exact: &ExactDecimal, negative: bool, options: DigitOptions) -> RoundedDecimal {
    let magnitude = -i32::from(options.maximum_fraction_digits);
    let coefficient = quantize(
        exact,
        magnitude,
        options.rounding_increment,
        negative,
        options.rounding_mode,
    );
    let formatted = format_fraction_result(
        &coefficient,
        magnitude,
        options.minimum_fraction_digits,
        options.trailing_zero_display,
    );
    RoundedDecimal {
        formatted,
        rounding_magnitude: magnitude,
    }
}

fn round_significant(
    exact: &ExactDecimal,
    negative: bool,
    options: DigitOptions,
) -> RoundedDecimal {
    let magnitude = exact.magnitude() - i32::from(options.maximum_significant_digits) + 1;
    let coefficient = quantize(exact, magnitude, 1, negative, options.rounding_mode);
    let formatted = format_significant_result(
        &coefficient,
        magnitude,
        options.minimum_significant_digits,
        options.trailing_zero_display,
    );
    RoundedDecimal {
        formatted,
        rounding_magnitude: magnitude,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum HalfRelation {
    Below,
    Equal,
    Above,
}

fn quantize(
    exact: &ExactDecimal,
    magnitude: i32,
    increment: u16,
    negative: bool,
    mode: RoundingMode,
) -> Vec<u8> {
    let cut = exact.decimal_position - magnitude;
    let integer = scaled_integer_digits(&exact.digits, cut);
    let fraction = scaled_fraction_digits(&exact.digits, cut);
    let (mut quotient, integer_remainder) = divide_small(&integer, increment);
    let has_fraction = fraction.iter().any(|digit| *digit != 0);
    let has_remainder = integer_remainder != 0 || has_fraction;
    let relation = compare_half(integer_remainder, &fraction, increment);
    let quotient_is_odd = quotient.last().is_some_and(|digit| digit % 2 == 1);
    if should_increment(mode, negative, has_remainder, relation, quotient_is_odd) {
        add_one(&mut quotient);
    }
    multiply_small(&quotient, increment)
}

fn scaled_integer_digits(digits: &[u8], cut: i32) -> Vec<u8> {
    if cut <= 0 {
        return vec![0];
    }
    let cut = usize::try_from(cut).expect("positive cut fits usize");
    let mut result = if cut <= digits.len() {
        digits[..cut].to_vec()
    } else {
        let mut value = digits.to_vec();
        value.resize(cut, 0);
        value
    };
    trim_leading_zeros(&mut result);
    result
}

fn scaled_fraction_digits(digits: &[u8], cut: i32) -> Vec<u8> {
    if cut < 0 {
        let zeros = usize::try_from(-cut).expect("negative cut magnitude fits usize");
        let mut result = vec![0; zeros];
        result.extend_from_slice(digits);
        result
    } else {
        let cut = usize::try_from(cut).expect("non-negative cut fits usize");
        digits.get(cut..).unwrap_or(&[]).to_vec()
    }
}

fn divide_small(digits: &[u8], divisor: u16) -> (Vec<u8>, u16) {
    let mut quotient = Vec::with_capacity(digits.len());
    let mut remainder = 0_u16;
    for digit in digits {
        let current = remainder * 10 + u16::from(*digit);
        quotient.push(u8::try_from(current / divisor).expect("single quotient digit"));
        remainder = current % divisor;
    }
    trim_leading_zeros(&mut quotient);
    (quotient, remainder)
}

fn compare_half(remainder: u16, fraction: &[u8], divisor: u16) -> HalfRelation {
    let doubled = remainder * 2;
    if doubled > divisor {
        return HalfRelation::Above;
    }
    if doubled == divisor {
        return if fraction.iter().any(|digit| *digit != 0) {
            HalfRelation::Above
        } else {
            HalfRelation::Equal
        };
    }
    if divisor - doubled > 1 {
        return HalfRelation::Below;
    }
    match fraction.first().copied().unwrap_or(0).cmp(&5) {
        std::cmp::Ordering::Less => HalfRelation::Below,
        std::cmp::Ordering::Greater => HalfRelation::Above,
        std::cmp::Ordering::Equal => {
            if fraction.iter().skip(1).any(|digit| *digit != 0) {
                HalfRelation::Above
            } else {
                HalfRelation::Equal
            }
        }
    }
}

fn should_increment(
    mode: RoundingMode,
    negative: bool,
    has_remainder: bool,
    relation: HalfRelation,
    quotient_is_odd: bool,
) -> bool {
    if !has_remainder {
        return false;
    }
    match mode {
        RoundingMode::Ceil => !negative,
        RoundingMode::Floor => negative,
        RoundingMode::Expand => true,
        RoundingMode::Trunc => false,
        RoundingMode::HalfCeil => {
            relation == HalfRelation::Above || (relation == HalfRelation::Equal && !negative)
        }
        RoundingMode::HalfFloor => {
            relation == HalfRelation::Above || (relation == HalfRelation::Equal && negative)
        }
        RoundingMode::HalfExpand => relation != HalfRelation::Below,
        RoundingMode::HalfTrunc => relation == HalfRelation::Above,
        RoundingMode::HalfEven => {
            relation == HalfRelation::Above || (relation == HalfRelation::Equal && quotient_is_odd)
        }
    }
}

fn add_one(digits: &mut Vec<u8>) {
    for digit in digits.iter_mut().rev() {
        if *digit < 9 {
            *digit += 1;
            return;
        }
        *digit = 0;
    }
    digits.insert(0, 1);
}

fn multiply_small(digits: &[u8], multiplier: u16) -> Vec<u8> {
    let mut reversed = Vec::with_capacity(digits.len() + 4);
    let mut carry = 0_u32;
    for digit in digits.iter().rev() {
        let current = u32::from(*digit) * u32::from(multiplier) + carry;
        reversed.push(u8::try_from(current % 10).expect("single product digit"));
        carry = current / 10;
    }
    while carry != 0 {
        reversed.push(u8::try_from(carry % 10).expect("single carry digit"));
        carry /= 10;
    }
    reversed.reverse();
    trim_leading_zeros(&mut reversed);
    reversed
}

fn trim_leading_zeros(digits: &mut Vec<u8>) {
    let first_nonzero = digits
        .iter()
        .position(|digit| *digit != 0)
        .unwrap_or(digits.len().saturating_sub(1));
    if first_nonzero != 0 {
        digits.drain(..first_nonzero);
    }
    if digits.is_empty() {
        digits.push(0);
    }
}

fn decimal_parts(coefficient: &[u8], magnitude: i32) -> (String, String) {
    let digits: String = coefficient
        .iter()
        .map(|digit| char::from(b'0' + *digit))
        .collect();
    if magnitude >= 0 {
        let mut integer = digits;
        integer.extend(std::iter::repeat_n(
            '0',
            usize::try_from(magnitude).expect("non-negative magnitude fits usize"),
        ));
        return (integer, String::new());
    }
    let fraction_width = usize::try_from(-magnitude).expect("fraction width fits usize");
    if digits.len() > fraction_width {
        let split = digits.len() - fraction_width;
        (digits[..split].to_owned(), digits[split..].to_owned())
    } else {
        let mut fraction = "0".repeat(fraction_width - digits.len());
        fraction.push_str(&digits);
        ("0".to_owned(), fraction)
    }
}

fn format_fraction_result(
    coefficient: &[u8],
    magnitude: i32,
    minimum_fraction_digits: u8,
    trailing_zero_display: TrailingZeroDisplay,
) -> String {
    let (integer, mut fraction) = decimal_parts(coefficient, magnitude);
    let minimum = usize::from(minimum_fraction_digits);
    while fraction.len() > minimum && fraction.ends_with('0') {
        fraction.pop();
    }
    if fraction.len() < minimum {
        fraction.extend(std::iter::repeat_n('0', minimum - fraction.len()));
    }
    finish_decimal(integer, fraction, trailing_zero_display)
}

fn format_significant_result(
    coefficient: &[u8],
    magnitude: i32,
    minimum_significant_digits: u8,
    trailing_zero_display: TrailingZeroDisplay,
) -> String {
    let (integer, mut fraction) = decimal_parts(coefficient, magnitude);
    let minimum = usize::from(minimum_significant_digits);
    while fraction.ends_with('0') && significant_digit_count(&integer, &fraction) > minimum {
        fraction.pop();
    }
    while significant_digit_count(&integer, &fraction) < minimum {
        fraction.push('0');
    }
    finish_decimal(integer, fraction, trailing_zero_display)
}

/// The significant digits of a plain decimal. Every digit of a zero counts, so
/// `0.00` has three.
fn significant_digit_count(integer: &str, fraction: &str) -> usize {
    let combined = integer.bytes().chain(fraction.bytes());
    let mut seen_nonzero = false;
    let mut count = 0;
    for digit in combined {
        if digit != b'0' {
            seen_nonzero = true;
        }
        if seen_nonzero {
            count += 1;
        }
    }
    if seen_nonzero {
        count
    } else {
        fraction.len() + 1
    }
}

fn finish_decimal(
    integer: String,
    mut fraction: String,
    trailing_zero_display: TrailingZeroDisplay,
) -> String {
    if trailing_zero_display == TrailingZeroDisplay::StripIfInteger
        && fraction.bytes().all(|digit| digit == b'0')
    {
        fraction.clear();
    }
    if fraction.is_empty() {
        integer
    } else {
        format!("{integer}.{fraction}")
    }
}

fn plural_operands(formatted: &str) -> PluralOperands {
    let (integer, fraction) = formatted.split_once('.').unwrap_or((formatted, ""));
    let integer = integer.trim_start_matches('0');
    let integer = if integer.is_empty() { "0" } else { integer };
    let trimmed_fraction = fraction.trim_end_matches('0');
    let n = if fraction.is_empty() {
        integer.to_owned()
    } else {
        format!("{integer}.{fraction}")
    };
    PluralOperands {
        n,
        i: integer.to_owned(),
        v: u32::try_from(fraction.len()).expect("fraction digit count fits u32"),
        w: u32::try_from(trimmed_fraction.len()).expect("fraction digit count fits u32"),
        f: fraction.to_owned(),
        t: trimmed_fraction.to_owned(),
        c: 0,
        e: 0,
    }
}

/// Raw RelativeTimeFormat options after JavaScript property coercion.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RelativeTimeFormatOptions {
    /// `localeMatcher`.
    pub locale_matcher: Option<String>,
    /// `numeric`.
    pub numeric: Option<String>,
    /// `style`.
    pub style: Option<String>,
    /// `numberingSystem`.
    pub numbering_system: Option<String>,
}

/// RelativeTimeFormat resolved options.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelativeTimeFormatResolvedOptions {
    /// Resolved locale.
    pub locale: String,
    /// Resolved numbering system.
    pub numbering_system: String,
    /// Resolved style.
    pub style: RelativeTimeStyle,
    /// Resolved numeric behavior.
    pub numeric: RelativeTimeNumeric,
}

/// RelativeTimeFormat output-part type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RelativeTimePartKind {
    /// Locale pattern literal.
    Literal,
    /// A semantic number-format part.
    Number(NumberPartKind),
}

/// One RelativeTimeFormat part with a UTF-16 code-unit index.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelativeTimePart {
    /// Part kind.
    pub kind: RelativeTimePartKind,
    /// Rendered text.
    pub value: String,
    /// Canonical unit for number parts; absent for literals.
    pub unit: Option<RelativeTimeUnit>,
    /// Start index in UTF-16 code units.
    pub index: usize,
}

/// ECMA-402 RelativeTimeFormat service core.
#[derive(Clone)]
pub struct RelativeTimeFormat<'a> {
    provider: &'a dyn IntlServiceDataProvider,
    locale: String,
    data_locale: String,
    numbering_system: String,
    style: RelativeTimeStyle,
    numeric: RelativeTimeNumeric,
}

impl<'a> RelativeTimeFormat<'a> {
    /// Constructs a relative-time formatter.
    ///
    /// # Errors
    /// Returns a typed error for invalid options, locale failure, or missing
    /// numbering-system data.
    pub fn try_new(
        requested_locales: &[String],
        options: &RelativeTimeFormatOptions,
        provider: &'a dyn IntlServiceDataProvider,
        host: &dyn HostLocaleHook,
    ) -> Result<Self, IntlError> {
        let matcher = parse_locale_matcher(options.locale_matcher.as_deref())?;
        let numeric = RelativeTimeNumeric::parse(options.numeric.as_deref())?;
        let style = RelativeTimeStyle::parse(options.style.as_deref())?;
        let mut locale_options = BTreeMap::new();
        if let Some(numbering_system) = &options.numbering_system {
            if !is_unicode_type(numbering_system) {
                return Err(IntlError::InvalidIdentifier {
                    kind: "numbering system",
                    value: numbering_system.clone(),
                });
            }
            locale_options.insert("nu".to_owned(), numbering_system.to_ascii_lowercase());
        }
        let resolved = resolve_service_locale(
            requested_locales,
            host,
            provider.locale_data(),
            matcher,
            &locale_options,
            &["nu".to_owned()],
        )?;
        let numbering_system = resolved.values.get("nu").cloned().unwrap_or_default();
        if numbering_system.is_empty() {
            return Err(IntlError::MissingData {
                service: "numbering system",
                locale: resolved.data_locale,
            });
        }
        Ok(Self {
            provider,
            locale: resolved.locale,
            data_locale: resolved.data_locale,
            numbering_system,
            style,
            numeric,
        })
    }

    /// Formats a relative-time value.
    ///
    /// # Errors
    /// Returns a range error for non-finite values or invalid units and a data
    /// error for missing/malformed locale data.
    pub fn format(&self, value: f64, unit: &str) -> Result<String, IntlError> {
        Ok(self
            .format_to_parts(value, unit)?
            .into_iter()
            .map(|part| part.value)
            .collect())
    }

    /// Partitions a relative-time value and records UTF-16 start indices.
    ///
    /// # Errors
    /// Returns the same failures as [`Self::format`].
    pub fn format_to_parts(
        &self,
        value: f64,
        unit: &str,
    ) -> Result<Vec<RelativeTimePart>, IntlError> {
        if !value.is_finite() {
            return Err(IntlError::InvalidNumber("RelativeTimeFormat.format"));
        }
        let unit = RelativeTimeUnit::parse(unit)?;
        if self.numeric == RelativeTimeNumeric::Auto
            && value.fract() == 0.0
            && value >= i64::MIN as f64
            && value <= i64::MAX as f64
            && let Some(term) =
                self.provider
                    .relative_time_auto(&self.data_locale, self.style, unit, value as i64)
        {
            return Ok(vec![RelativeTimePart {
                kind: RelativeTimePartKind::Literal,
                value: term.to_owned(),
                unit: None,
                index: 0,
            }]);
        }

        let rounded = round_finite(value, DigitOptions::relative_time_default());
        let operands = plural_operands(&rounded.formatted);
        let category = self
            .provider
            .plural_category(&self.data_locale, PluralRuleType::Cardinal, &operands)
            .ok_or_else(|| IntlError::MissingData {
                service: "plural rules",
                locale: self.data_locale.clone(),
            })?;
        let tense = if value.is_sign_negative() {
            RelativeTimeTense::Past
        } else {
            RelativeTimeTense::Future
        };
        let pattern = self
            .provider
            .relative_time_pattern(&self.data_locale, self.style, unit, tense, category)
            .ok_or_else(|| IntlError::MissingData {
                service: "relative time",
                locale: self.data_locale.clone(),
            })?;
        let (prefix, suffix) = one_placeholder(pattern, "{0}")?;
        let number_input = NumberInput {
            ascii: rounded.formatted,
            negative: value.is_sign_negative(),
            special: None,
        };
        let number = self
            .provider
            .format_number(&self.data_locale, &self.numbering_system, &number_input)
            .ok_or_else(|| IntlError::MissingData {
                service: "number formatting",
                locale: self.data_locale.clone(),
            })?;
        validate_formatted_number(&number)?;

        let mut parts = Vec::with_capacity(number.parts.len() + 2);
        let mut index = 0;
        push_relative_literal(&mut parts, prefix, &mut index);
        for part in number.parts {
            let value = part.value;
            let start = index;
            index += utf16_len(&value);
            parts.push(RelativeTimePart {
                kind: RelativeTimePartKind::Number(part.kind),
                value,
                unit: Some(unit),
                index: start,
            });
        }
        push_relative_literal(&mut parts, suffix, &mut index);
        Ok(parts)
    }

    /// Returns all resolved options.
    #[must_use]
    pub fn resolved_options(&self) -> RelativeTimeFormatResolvedOptions {
        RelativeTimeFormatResolvedOptions {
            locale: self.locale.clone(),
            numbering_system: self.numbering_system.clone(),
            style: self.style,
            numeric: self.numeric,
        }
    }
}

fn validate_formatted_number(number: &FormattedNumber) -> Result<(), IntlError> {
    if number.parts.is_empty()
        || number
            .parts
            .iter()
            .map(|part| part.value.as_str())
            .collect::<String>()
            != number.value
    {
        return Err(IntlError::InvalidData(
            "number parts do not concatenate to the formatted number",
        ));
    }
    Ok(())
}

fn push_relative_literal(parts: &mut Vec<RelativeTimePart>, literal: &str, index: &mut usize) {
    if literal.is_empty() {
        return;
    }
    parts.push(RelativeTimePart {
        kind: RelativeTimePartKind::Literal,
        value: literal.to_owned(),
        unit: None,
        index: *index,
    });
    *index += utf16_len(literal);
}

fn one_placeholder<'a>(
    pattern: &'a str,
    placeholder: &str,
) -> Result<(&'a str, &'a str), IntlError> {
    let (prefix, suffix) = pattern
        .split_once(placeholder)
        .ok_or(IntlError::InvalidData("pattern is missing a placeholder"))?;
    if suffix.contains(placeholder) {
        return Err(IntlError::InvalidData("pattern repeats a placeholder"));
    }
    Ok((prefix, suffix))
}

/// Raw ListFormat options after JavaScript property coercion.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ListFormatOptions {
    /// `localeMatcher`.
    pub locale_matcher: Option<String>,
    /// `type`.
    pub list_type: Option<String>,
    /// `style`.
    pub style: Option<String>,
}

/// ListFormat resolved options.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ListFormatResolvedOptions {
    /// Resolved locale.
    pub locale: String,
    /// Resolved list type.
    pub list_type: ListType,
    /// Resolved style.
    pub style: ListStyle,
}

/// ListFormat output-part type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ListPartKind {
    /// Original list element.
    Element,
    /// Locale pattern literal.
    Literal,
}

/// One ListFormat part with a UTF-16 code-unit index.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ListPart {
    /// Part kind.
    pub kind: ListPartKind,
    /// Rendered value.
    pub value: String,
    /// Start index in UTF-16 code units.
    pub index: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RawListPart {
    kind: ListPartKind,
    value: String,
}

/// ECMA-402 ListFormat service core.
#[derive(Clone)]
pub struct ListFormat<'a> {
    provider: &'a dyn IntlServiceDataProvider,
    locale: String,
    data_locale: String,
    list_type: ListType,
    style: ListStyle,
}

impl<'a> ListFormat<'a> {
    /// Constructs a list formatter.
    ///
    /// # Errors
    /// Returns a typed error for invalid options or locale negotiation failure.
    pub fn try_new(
        requested_locales: &[String],
        options: &ListFormatOptions,
        provider: &'a dyn IntlServiceDataProvider,
        host: &dyn HostLocaleHook,
    ) -> Result<Self, IntlError> {
        let matcher = parse_locale_matcher(options.locale_matcher.as_deref())?;
        let list_type = ListType::parse(options.list_type.as_deref())?;
        let style = ListStyle::parse(options.style.as_deref())?;
        let resolved = resolve_service_locale(
            requested_locales,
            host,
            provider.locale_data(),
            matcher,
            &BTreeMap::new(),
            &[],
        )?;
        Ok(Self {
            provider,
            locale: resolved.locale,
            data_locale: resolved.data_locale,
            list_type,
            style,
        })
    }

    /// Formats a list of already-string-coerced elements.
    ///
    /// # Errors
    /// Returns a data error for missing or malformed locale patterns.
    pub fn format(&self, elements: &[String]) -> Result<String, IntlError> {
        Ok(self
            .format_to_parts(elements)?
            .into_iter()
            .map(|part| part.value)
            .collect())
    }

    /// Partitions a list and records UTF-16 start indices.
    ///
    /// # Errors
    /// Returns a data error for missing or malformed locale patterns.
    pub fn format_to_parts(&self, elements: &[String]) -> Result<Vec<ListPart>, IntlError> {
        let mut raw = self.partition(elements)?;
        let mut index = 0;
        let mut parts = Vec::with_capacity(raw.len());
        for part in raw.drain(..) {
            let start = index;
            index += utf16_len(&part.value);
            parts.push(ListPart {
                kind: part.kind,
                value: part.value,
                index: start,
            });
        }
        Ok(parts)
    }

    /// Returns all resolved options.
    #[must_use]
    pub fn resolved_options(&self) -> ListFormatResolvedOptions {
        ListFormatResolvedOptions {
            locale: self.locale.clone(),
            list_type: self.list_type,
            style: self.style,
        }
    }

    fn partition(&self, elements: &[String]) -> Result<Vec<RawListPart>, IntlError> {
        let element = |value: &String| {
            vec![RawListPart {
                kind: ListPartKind::Element,
                value: value.clone(),
            }]
        };
        match elements.len() {
            0 => Ok(Vec::new()),
            1 => Ok(element(&elements[0])),
            2 => self.apply_list_pattern(
                ListPatternPosition::Pair,
                element(&elements[0]),
                element(&elements[1]),
            ),
            length => {
                let mut result = self.apply_list_pattern(
                    ListPatternPosition::Start,
                    element(&elements[0]),
                    element(&elements[1]),
                )?;
                for item in &elements[2..length - 1] {
                    result = self.apply_list_pattern(
                        ListPatternPosition::Middle,
                        result,
                        element(item),
                    )?;
                }
                self.apply_list_pattern(
                    ListPatternPosition::End,
                    result,
                    element(&elements[length - 1]),
                )
            }
        }
    }

    fn apply_list_pattern(
        &self,
        position: ListPatternPosition,
        left: Vec<RawListPart>,
        right: Vec<RawListPart>,
    ) -> Result<Vec<RawListPart>, IntlError> {
        let pattern = self
            .provider
            .list_pattern(&self.data_locale, self.list_type, self.style, position)
            .ok_or_else(|| IntlError::MissingData {
                service: "list pattern",
                locale: self.data_locale.clone(),
            })?;
        apply_two_placeholder_pattern(pattern, left, right)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum PatternPiece {
    Literal(String),
    Left,
    Right,
}

fn apply_two_placeholder_pattern(
    pattern: &str,
    left: Vec<RawListPart>,
    right: Vec<RawListPart>,
) -> Result<Vec<RawListPart>, IntlError> {
    let pieces = parse_two_placeholder_pattern(pattern)?;
    let mut left = Some(left);
    let mut right = Some(right);
    let mut result = Vec::new();
    for piece in pieces {
        match piece {
            PatternPiece::Literal(value) if !value.is_empty() => result.push(RawListPart {
                kind: ListPartKind::Literal,
                value,
            }),
            PatternPiece::Literal(_) => {}
            PatternPiece::Left => result.extend(left.take().expect("validated unique left slot")),
            PatternPiece::Right => {
                result.extend(right.take().expect("validated unique right slot"));
            }
        }
    }
    Ok(result)
}

fn parse_two_placeholder_pattern(pattern: &str) -> Result<Vec<PatternPiece>, IntlError> {
    let mut pieces = Vec::new();
    let mut cursor = 0;
    let mut saw_left = false;
    let mut saw_right = false;
    while cursor < pattern.len() {
        let tail = &pattern[cursor..];
        let left = tail.find("{0}").map(|index| (index, PatternPiece::Left));
        let right = tail.find("{1}").map(|index| (index, PatternPiece::Right));
        let next = match (left, right) {
            (Some(left), Some(right)) => Some(if left.0 <= right.0 { left } else { right }),
            (Some(left), None) => Some(left),
            (None, Some(right)) => Some(right),
            (None, None) => None,
        };
        let Some((offset, piece)) = next else {
            pieces.push(PatternPiece::Literal(tail.to_owned()));
            cursor = pattern.len();
            continue;
        };
        if offset != 0 {
            pieces.push(PatternPiece::Literal(tail[..offset].to_owned()));
        }
        match piece {
            PatternPiece::Left if saw_left => {
                return Err(IntlError::InvalidData("list pattern repeats {0}"));
            }
            PatternPiece::Right if saw_right => {
                return Err(IntlError::InvalidData("list pattern repeats {1}"));
            }
            PatternPiece::Left => saw_left = true,
            PatternPiece::Right => saw_right = true,
            PatternPiece::Literal(_) => unreachable!(),
        }
        pieces.push(piece);
        cursor += offset + 3;
    }
    if !saw_left || !saw_right {
        return Err(IntlError::InvalidData(
            "list pattern must contain {0} and {1}",
        ));
    }
    Ok(pieces)
}

/// Raw Segmenter options after JavaScript property coercion.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SegmenterOptions {
    /// `localeMatcher`.
    pub locale_matcher: Option<String>,
    /// `granularity`.
    pub granularity: Option<String>,
}

/// Segmenter resolved options.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SegmenterResolvedOptions {
    /// Resolved locale.
    pub locale: String,
    /// Resolved granularity.
    pub granularity: SegmenterGranularity,
}

/// One validated segment record over a shared UTF-16 input.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SegmentRecord {
    /// Inclusive start in UTF-16 code units.
    pub start: usize,
    /// Exclusive end in UTF-16 code units.
    pub end: usize,
    /// Word-likeness for word granularity; absent otherwise.
    pub is_word_like: Option<bool>,
}

/// A segmented UTF-16 string. A `Segments` object and each iterator over it share
/// one copy of the input and of the records, so a clone costs nothing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SegmentedText {
    input: Arc<[u16]>,
    records: Arc<[SegmentRecord]>,
}

impl SegmentedText {
    /// Returns the original JavaScript UTF-16 string.
    #[must_use]
    pub fn input(&self) -> &[u16] {
        &self.input
    }

    /// Returns ordered segment records.
    #[must_use]
    pub fn records(&self) -> &[SegmentRecord] {
        &self.records
    }

    /// Returns one segment's UTF-16 code units.
    #[must_use]
    pub fn segment(&self, record: &SegmentRecord) -> &[u16] {
        &self.input[record.start..record.end]
    }

    /// Implements `Segments.prototype.containing` with a UTF-16 code-unit index.
    #[must_use]
    pub fn containing(&self, index: usize) -> Option<&SegmentRecord> {
        let position = self.records.partition_point(|record| record.end <= index);
        self.records.get(position)
    }
}

/// ECMA-402 Segmenter service core.
#[derive(Clone)]
pub struct Segmenter<'a> {
    provider: &'a dyn IntlServiceDataProvider,
    locale: String,
    data_locale: String,
    granularity: SegmenterGranularity,
}

impl<'a> Segmenter<'a> {
    /// Constructs a segmenter.
    ///
    /// # Errors
    /// Returns a typed error for invalid options or locale negotiation failure.
    pub fn try_new(
        requested_locales: &[String],
        options: &SegmenterOptions,
        provider: &'a dyn IntlServiceDataProvider,
        host: &dyn HostLocaleHook,
    ) -> Result<Self, IntlError> {
        let matcher = parse_locale_matcher(options.locale_matcher.as_deref())?;
        let granularity = SegmenterGranularity::parse(options.granularity.as_deref())?;
        let resolved = resolve_service_locale(
            requested_locales,
            host,
            provider.locale_data(),
            matcher,
            &BTreeMap::new(),
            &[],
        )?;
        Ok(Self {
            provider,
            locale: resolved.locale,
            data_locale: resolved.data_locale,
            granularity,
        })
    }

    /// Segments an exact JavaScript UTF-16 string.
    ///
    /// # Errors
    /// Returns a data error if provider boundaries are absent, unordered,
    /// incomplete, or split a surrogate pair.
    pub fn segment_utf16(&self, input: &[u16]) -> Result<SegmentedText, IntlError> {
        if input.is_empty() {
            return Ok(SegmentedText {
                input: Arc::from([]),
                records: Arc::from([]),
            });
        }
        let boundaries = self
            .provider
            .segment_boundaries(&self.data_locale, self.granularity, input)
            .ok_or_else(|| IntlError::MissingData {
                service: "Unicode segmentation",
                locale: self.data_locale.clone(),
            })?;
        let mut start = 0;
        let mut records = Vec::with_capacity(boundaries.len());
        for boundary in boundaries {
            if boundary.end <= start
                || boundary.end > input.len()
                || splits_surrogate_pair(input, boundary.end)
            {
                return Err(IntlError::InvalidData(
                    "segment boundaries must increase, cover valid UTF-16 boundaries, and stay in range",
                ));
            }
            records.push(SegmentRecord {
                start,
                end: boundary.end,
                is_word_like: (self.granularity == SegmenterGranularity::Word)
                    .then_some(boundary.is_word_like),
            });
            start = boundary.end;
        }
        if start != input.len() {
            return Err(IntlError::InvalidData(
                "segment boundaries do not cover the complete input",
            ));
        }
        Ok(SegmentedText {
            input: Arc::from(input),
            records: Arc::from(records),
        })
    }

    /// UTF-8 convenience entry point that preserves UTF-16 result indices.
    ///
    /// # Errors
    /// Returns the same failures as [`Self::segment_utf16`].
    pub fn segment_str(&self, input: &str) -> Result<SegmentedText, IntlError> {
        self.segment_utf16(&input.encode_utf16().collect::<Vec<_>>())
    }

    /// Returns all resolved options.
    #[must_use]
    pub fn resolved_options(&self) -> SegmenterResolvedOptions {
        SegmenterResolvedOptions {
            locale: self.locale.clone(),
            granularity: self.granularity,
        }
    }
}

fn splits_surrogate_pair(input: &[u16], index: usize) -> bool {
    index != 0
        && index < input.len()
        && (0xD800..=0xDBFF).contains(&input[index - 1])
        && (0xDC00..=0xDFFF).contains(&input[index])
}

/// Raw DisplayNames options after JavaScript property coercion.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DisplayNamesOptions {
    /// `localeMatcher`.
    pub locale_matcher: Option<String>,
    /// Required `type`.
    pub name_type: Option<String>,
    /// `style`.
    pub style: Option<String>,
    /// `fallback`.
    pub fallback: Option<String>,
    /// `languageDisplay`.
    pub language_display: Option<String>,
}

/// DisplayNames resolved options.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DisplayNamesResolvedOptions {
    /// Resolved locale.
    pub locale: String,
    /// Resolved style.
    pub style: DisplayNamesStyle,
    /// Resolved type.
    pub name_type: DisplayNamesType,
    /// Missing-name behavior.
    pub fallback: DisplayNamesFallback,
    /// Language-name presentation behavior.
    pub language_display: LanguageDisplay,
}

/// ECMA-402 DisplayNames service core.
#[derive(Clone)]
pub struct DisplayNames<'a> {
    provider: &'a dyn IntlServiceDataProvider,
    locale_provider: &'a dyn LocaleDataProvider,
    locale: String,
    data_locale: String,
    style: DisplayNamesStyle,
    name_type: DisplayNamesType,
    fallback: DisplayNamesFallback,
    language_display: LanguageDisplay,
}

impl<'a> DisplayNames<'a> {
    /// Constructs a display-name service.
    ///
    /// # Errors
    /// Returns TypeError when `type` is absent and RangeError-equivalent errors
    /// for invalid option values or locales.
    pub fn try_new(
        requested_locales: &[String],
        options: &DisplayNamesOptions,
        provider: &'a dyn IntlServiceDataProvider,
        host: &dyn HostLocaleHook,
    ) -> Result<Self, IntlError> {
        let matcher = parse_locale_matcher(options.locale_matcher.as_deref())?;
        let name_type = DisplayNamesType::parse(options.name_type.as_deref())?;
        let style = DisplayNamesStyle::parse(options.style.as_deref())?;
        let fallback = DisplayNamesFallback::parse(options.fallback.as_deref())?;
        let language_display = LanguageDisplay::parse(options.language_display.as_deref())?;
        let locale_provider = provider.locale_data();
        let resolved = resolve_service_locale(
            requested_locales,
            host,
            locale_provider,
            matcher,
            &BTreeMap::new(),
            &[],
        )?;
        Ok(Self {
            provider,
            locale_provider,
            locale: resolved.locale,
            data_locale: resolved.data_locale,
            style,
            name_type,
            fallback,
            language_display,
        })
    }

    /// Returns a localized name, its canonical code fallback, or no value.
    ///
    /// # Errors
    /// Returns a range error for a structurally invalid identifier.
    pub fn of(&self, code: &str) -> Result<Option<String>, IntlError> {
        let canonical = canonical_display_code(self.name_type, code, self.locale_provider)?;
        if let Some(name) = self.provider.display_name(
            &self.data_locale,
            self.style,
            self.name_type,
            self.language_display,
            &canonical,
        ) {
            return Ok(Some(name.to_owned()));
        }
        Ok(match self.fallback {
            DisplayNamesFallback::Code => Some(canonical),
            DisplayNamesFallback::None => None,
        })
    }

    /// Returns all resolved options.
    #[must_use]
    pub fn resolved_options(&self) -> DisplayNamesResolvedOptions {
        DisplayNamesResolvedOptions {
            locale: self.locale.clone(),
            style: self.style,
            name_type: self.name_type,
            fallback: self.fallback,
            language_display: self.language_display,
        }
    }
}

fn canonical_display_code(
    name_type: DisplayNamesType,
    code: &str,
    provider: &dyn LocaleDataProvider,
) -> Result<String, IntlError> {
    match name_type {
        DisplayNamesType::Language => canonical_language_code(code, provider),
        DisplayNamesType::Region => canonical_region_code(code, provider),
        DisplayNamesType::Script => canonical_script_code(code, provider),
        DisplayNamesType::Currency => canonical_currency_code(code),
        DisplayNamesType::Calendar => canonical_calendar_code(code, provider),
        DisplayNamesType::DateTimeField => canonical_date_time_field(code),
    }
}

fn canonical_language_code(
    code: &str,
    provider: &dyn LocaleDataProvider,
) -> Result<String, IntlError> {
    if !is_unicode_language_id(code) {
        return Err(invalid_identifier("language", code));
    }
    canonicalize_unicode_locale_id(code, provider).map_err(|_| invalid_identifier("language", code))
}

fn canonical_region_code(
    code: &str,
    provider: &dyn LocaleDataProvider,
) -> Result<String, IntlError> {
    if !is_region_subtag(code) {
        return Err(invalid_identifier("region", code));
    }
    let canonical = canonicalize_unicode_locale_id(&format!("und-{code}"), provider)
        .map_err(|_| invalid_identifier("region", code))?;
    LanguageTag::parse(&canonical)
        .ok()
        .and_then(|tag| tag.id.region)
        .ok_or_else(|| invalid_identifier("region", code))
}

fn canonical_script_code(
    code: &str,
    provider: &dyn LocaleDataProvider,
) -> Result<String, IntlError> {
    if code.len() != 4 || !code.bytes().all(|byte| byte.is_ascii_alphabetic()) {
        return Err(invalid_identifier("script", code));
    }
    let canonical = canonicalize_unicode_locale_id(&format!("und-{code}"), provider)
        .map_err(|_| invalid_identifier("script", code))?;
    LanguageTag::parse(&canonical)
        .ok()
        .and_then(|tag| tag.id.script)
        .ok_or_else(|| invalid_identifier("script", code))
}

fn canonical_currency_code(code: &str) -> Result<String, IntlError> {
    if code.len() == 3 && code.bytes().all(|byte| byte.is_ascii_alphabetic()) {
        Ok(code.to_ascii_uppercase())
    } else {
        Err(invalid_identifier("currency", code))
    }
}

fn canonical_calendar_code(
    code: &str,
    provider: &dyn LocaleDataProvider,
) -> Result<String, IntlError> {
    if !is_unicode_type(code) {
        return Err(invalid_identifier("calendar", code));
    }
    let canonical = canonicalize_unicode_locale_id(
        &format!("und-u-ca-{}", code.to_ascii_lowercase()),
        provider,
    )
    .map_err(|_| invalid_identifier("calendar", code))?;
    LanguageTag::parse(&canonical)
        .ok()
        .and_then(|tag| tag.unicode)
        .and_then(|extension| extension.keywords.get("ca").cloned())
        .filter(|value| !value.is_empty())
        .ok_or_else(|| invalid_identifier("calendar", code))
}

fn canonical_date_time_field(code: &str) -> Result<String, IntlError> {
    const FIELDS: &[&str] = &[
        "era",
        "year",
        "quarter",
        "month",
        "weekOfYear",
        "weekday",
        "day",
        "dayPeriod",
        "hour",
        "minute",
        "second",
        "timeZoneName",
    ];
    if FIELDS.contains(&code) {
        Ok(code.to_owned())
    } else {
        Err(invalid_identifier("dateTimeField", code))
    }
}

fn invalid_identifier(kind: &'static str, value: &str) -> IntlError {
    IntlError::InvalidIdentifier {
        kind,
        value: value.to_owned(),
    }
}

fn is_unicode_language_id(value: &str) -> bool {
    let mut parts = value.split('-');
    let Some(language) = parts.next() else {
        return false;
    };
    if !(((2..=3).contains(&language.len()) || (5..=8).contains(&language.len()))
        && language.bytes().all(|byte| byte.is_ascii_alphabetic()))
    {
        return false;
    }
    let rest: Vec<&str> = parts.collect();
    if rest.iter().any(|part| part.is_empty()) {
        return false;
    }
    let mut index = 0;
    if rest
        .get(index)
        .is_some_and(|part| part.len() == 4 && part.bytes().all(|byte| byte.is_ascii_alphabetic()))
    {
        index += 1;
    }
    if rest.get(index).is_some_and(|part| is_region_subtag(part)) {
        index += 1;
    }
    let mut variants = BTreeSet::new();
    for variant in &rest[index..] {
        let bytes = variant.as_bytes();
        let structurally_valid = ((5..=8).contains(&bytes.len())
            && bytes.iter().all(u8::is_ascii_alphanumeric))
            || (bytes.len() == 4
                && bytes[0].is_ascii_digit()
                && bytes[1..].iter().all(u8::is_ascii_alphanumeric));
        if !structurally_valid || !variants.insert(variant.to_ascii_lowercase()) {
            return false;
        }
    }
    true
}

fn is_region_subtag(value: &str) -> bool {
    (value.len() == 2 && value.bytes().all(|byte| byte.is_ascii_alphabetic()))
        || (value.len() == 3 && value.bytes().all(|byte| byte.is_ascii_digit()))
}

fn is_unicode_type(value: &str) -> bool {
    !value.is_empty()
        && value.split('-').all(|part| {
            (3..=8).contains(&part.len()) && part.bytes().all(|byte| byte.is_ascii_alphanumeric())
        })
}

fn utf16_len(value: &str) -> usize {
    value.encode_utf16().count()
}

#[cfg(test)]
mod tests {
    use super::super::locale_data::DATA;
    use super::super::number_data::NoHostLocale;
    use super::{PluralCategory, PluralRules, PluralRulesOptions};

    fn rules(options: &PluralRulesOptions) -> PluralRules<'static> {
        PluralRules::try_new(&["en".to_owned()], options, &*DATA, &NoHostLocale).expect("rules")
    }

    #[test]
    fn a_zero_has_as_many_significant_digits_as_it_shows() {
        let minimum = rules(&PluralRulesOptions {
            minimum_significant_digits: Some(3),
            ..PluralRulesOptions::default()
        });
        assert_eq!(minimum.select(0.0).expect("zero"), PluralCategory::Other);
        assert_eq!(minimum.select(-0.0).expect("zero"), PluralCategory::Other);
        assert_eq!(minimum.select(1.0).expect("one"), PluralCategory::Other);
    }
}
