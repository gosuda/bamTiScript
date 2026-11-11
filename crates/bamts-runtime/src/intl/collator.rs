//! Deterministic ECMA-402 `Intl.Collator` mechanics.
//!
//! Locale negotiation is shared with [`super::locale_negotiation`]. Actual
//! collation and locale defaults are supplied by [`CollatorDataProvider`]; this
//! module never reads process locale, environment, time, randomness, or OS data.
//!
//! Specification sources:
//! - <https://tc39.es/ecma402/#sec-intl-collator-constructor>
//! - <https://tc39.es/ecma402/#sec-intl.collator.prototype.resolvedoptions>
//! - <https://tc39.es/ecma402/#sec-collator-comparestrings>

use super::locale_negotiation::{
    LocaleDataProvider, LocaleError, LocaleMatcher, canonicalize_locale_list, resolve_locale,
    supported_locales,
};
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;
use std::sync::LazyLock;

static RELEVANT_EXTENSION_KEYS: LazyLock<[String; 3]> =
    LazyLock::new(|| ["co".to_owned(), "kn".to_owned(), "kf".to_owned()]);

/// The JavaScript error class appropriate for a Collator operation failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CollatorErrorKind {
    /// A JavaScript conversion or adapter boundary failed.
    TypeError,
    /// A locale or option value is outside the permitted range.
    RangeError,
}

/// A typed Collator initialization or option-access failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CollatorError {
    /// ECMAScript exception class to construct.
    pub kind: CollatorErrorKind,
    /// Stable diagnostic text for the runtime adapter.
    pub message: String,
}

impl CollatorError {
    /// Creates a JavaScript `TypeError` result.
    #[must_use]
    pub fn type_error(message: impl Into<String>) -> Self {
        Self {
            kind: CollatorErrorKind::TypeError,
            message: message.into(),
        }
    }

    /// Creates a JavaScript `RangeError` result.
    #[must_use]
    pub fn range_error(message: impl Into<String>) -> Self {
        Self {
            kind: CollatorErrorKind::RangeError,
            message: message.into(),
        }
    }
}

impl From<LocaleError> for CollatorError {
    fn from(error: LocaleError) -> Self {
        Self::range_error(error.to_string())
    }
}

impl fmt::Display for CollatorError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self.message)
    }
}

impl Error for CollatorError {}

/// Collator operation selected by the `usage` option.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum CollatorUsage {
    /// Produce a stable linguistic sort order.
    Sort,
    /// Find matching strings; no useful sort order is implied.
    Search,
}

impl CollatorUsage {
    /// Returns the ECMA-402 option spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Sort => "sort",
            Self::Search => "search",
        }
    }
}

/// Differences that make two strings unequal.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum CollatorSensitivity {
    /// Ignore case and accents.
    Base,
    /// Distinguish accents but ignore case.
    Accent,
    /// Distinguish case but ignore accents.
    Case,
    /// Distinguish case, accents, and other variant differences.
    Variant,
}

impl CollatorSensitivity {
    /// Returns the ECMA-402 option spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Base => "base",
            Self::Accent => "accent",
            Self::Case => "case",
            Self::Variant => "variant",
        }
    }
}

/// Relative ordering of uppercase and lowercase variants.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum CollatorCaseFirst {
    /// Uppercase variants sort first.
    Upper,
    /// Lowercase variants sort first.
    Lower,
    /// Locale data chooses the case ordering.
    False,
}

impl CollatorCaseFirst {
    /// Returns the ECMA-402 option spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Upper => "upper",
            Self::Lower => "lower",
            Self::False => "false",
        }
    }
}

/// Already-coerced value returned by a JavaScript options adapter.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CoercedCollatorOption {
    /// Result of ECMA-262 `ToBoolean`.
    Boolean(bool),
    /// Result of ECMA-262 `ToString`.
    String(String),
}

/// Coercion required by ECMA-402 `GetOption`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CollatorOptionType {
    /// Apply ECMA-262 `ToBoolean`.
    Boolean,
    /// Apply ECMA-262 `ToString`.
    String,
}

/// Observable options-object operations delegated to the JavaScript adapter.
///
/// `None` at the constructor boundary represents an omitted/`undefined`
/// options value. A supplied source represents every other JavaScript value:
/// [`Self::coerce_options_to_object`] must perform `ToObject` and therefore
/// reject `null` with `TypeError`. Each property is then read exactly once, in
/// specification order. `get_option` must perform the requested JavaScript
/// coercion and return `Ok(None)` only for an absent or `undefined` property.
pub trait CollatorOptionsSource {
    /// Applies ECMA-402 `CoerceOptionsToObject` to the adapter's input.
    ///
    /// # Errors
    /// Propagates the JavaScript abrupt completion, including `TypeError` for
    /// `null`.
    fn coerce_options_to_object(&mut self) -> Result<(), CollatorError>;

    /// Reads and coerces one options property.
    ///
    /// # Errors
    /// Propagates property-access and coercion abrupt completions.
    fn get_option(
        &mut self,
        property: &'static str,
        option_type: CollatorOptionType,
    ) -> Result<Option<CoercedCollatorOption>, CollatorError>;
}

/// Locale-data defaults selected before explicit options are applied.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CollatorLocaleDefaults {
    /// Search-collator sensitivity from `[[SearchLocaleData]]`.
    /// Sort collators use the specification default `variant` instead.
    pub sensitivity: CollatorSensitivity,
    /// Locale- and usage-specific punctuation default.
    pub ignore_punctuation: bool,
}

/// Borrowed, allocation-free options supplied to a collation engine.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CollatorCompareOptions<'a> {
    /// Provider locale selected by locale negotiation, without requested
    /// Unicode extension keywords.
    pub data_locale: &'a str,
    /// Sort or search tailoring.
    pub usage: CollatorUsage,
    /// Effective collation strength/case level.
    pub sensitivity: CollatorSensitivity,
    /// Whether punctuation contributes collation elements.
    pub ignore_punctuation: bool,
    /// Whether digit sequences compare numerically.
    pub numeric: bool,
    /// Effective case-first behavior.
    pub case_first: CollatorCaseFirst,
    /// Effective Unicode collation identifier, or `"default"`.
    pub collation: &'a str,
}

/// One provider comparison request over exact JavaScript UTF-16 strings.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CollatorCompareRequest<'a> {
    /// Resolved options and provider data locale.
    pub options: CollatorCompareOptions<'a>,
    /// Left JavaScript string as UTF-16 code units. Lone surrogates are valid.
    pub left: &'a [u16],
    /// Right JavaScript string as UTF-16 code units. Lone surrogates are valid.
    pub right: &'a [u16],
}

/// Supplies every implementation- and locale-dependent Collator fact.
///
/// Implementations should use CLDR/ICU collation data. They must be pure and
/// deterministic: repeated identical requests must return identical orderings,
/// and returned orderings must form a consistent comparator. Canonically
/// equivalent strings must return [`Ordering::Equal`]. Returning `None` selects
/// the deterministic UTF-16 code-unit fallback; this keeps the runtime total
/// when an injected provider deliberately has no tailoring for a request.
pub trait CollatorDataProvider: LocaleDataProvider {
    /// Returns defaults from the resolved sort/search locale-data record.
    fn locale_defaults(&self, data_locale: &str, usage: CollatorUsage) -> CollatorLocaleDefaults;

    /// Compares two exact JavaScript strings, or selects the UTF-16 fallback.
    fn compare(&self, request: CollatorCompareRequest<'_>) -> Option<Ordering>;
}

/// Borrowed `resolvedOptions()` fields in specification property order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ResolvedCollatorOptions<'a> {
    /// Resolved canonical locale, including retained supported keywords.
    pub locale: &'a str,
    /// Sort or search usage.
    pub usage: CollatorUsage,
    /// Effective sensitivity.
    pub sensitivity: CollatorSensitivity,
    /// Effective punctuation behavior.
    pub ignore_punctuation: bool,
    /// Effective collation identifier, or `"default"`.
    pub collation: &'a str,
    /// Effective numeric behavior.
    pub numeric: bool,
    /// Effective case-first behavior.
    pub case_first: CollatorCaseFirst,
}

/// Resolved ECMA-402 Collator internal slots.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Collator {
    locale: String,
    data_locale: String,
    usage: CollatorUsage,
    sensitivity: CollatorSensitivity,
    ignore_punctuation: bool,
    collation: String,
    numeric: bool,
    case_first: CollatorCaseFirst,
}

impl Collator {
    /// Canonicalizes locales, reads options in ECMA-402 order, and resolves
    /// Collator internal slots solely from the injected provider.
    ///
    /// `options == None` represents an omitted or `undefined` options value.
    /// Every other JavaScript value must be represented by a source so its
    /// `ToObject` behavior remains observable.
    ///
    /// # Errors
    /// Returns `RangeError` for malformed locales and out-of-range options, or
    /// propagates typed adapter failures such as `TypeError` from `ToObject` and
    /// `ToString`.
    pub fn new(
        locales: &[String],
        options: Option<&mut dyn CollatorOptionsSource>,
        provider: &dyn CollatorDataProvider,
    ) -> Result<Self, CollatorError> {
        let requested = canonicalize_locale_list(locales, provider)?;
        let mut options = options;
        coerce_options(&mut options)?;

        let usage = parse_usage(read_string_option(
            &mut options,
            "usage",
            &["sort", "search"],
        )?)?;
        let matcher = parse_locale_matcher(read_string_option(
            &mut options,
            "localeMatcher",
            &["lookup", "best fit"],
        )?)?;

        let collation = read_string_option(&mut options, "collation", &[])?;
        if let Some(value) = &collation
            && !is_unicode_type(value)
        {
            return Err(CollatorError::range_error(format!(
                "invalid value for option collation: {value}"
            )));
        }
        let numeric = read_boolean_option(&mut options, "numeric")?;
        let case_first =
            read_string_option(&mut options, "caseFirst", &["upper", "lower", "false"])?;

        let mut resolution_options = BTreeMap::new();
        if let Some(value) = collation {
            resolution_options.insert("co".to_owned(), canonicalize_uvalue(provider, "co", &value));
        }
        if let Some(value) = numeric {
            resolution_options.insert(
                "kn".to_owned(),
                if value { "true" } else { "false" }.to_owned(),
            );
        }
        if let Some(value) = case_first {
            resolution_options.insert("kf".to_owned(), value);
        }

        let resolved = resolve_locale(
            &requested,
            &resolution_options,
            &*RELEVANT_EXTENSION_KEYS,
            matcher,
            provider,
        )?;
        let defaults = provider.locale_defaults(&resolved.data_locale, usage);

        let sensitivity = match read_string_option(
            &mut options,
            "sensitivity",
            &["base", "accent", "case", "variant"],
        )? {
            Some(value) => parse_sensitivity(&value),
            None if usage == CollatorUsage::Sort => CollatorSensitivity::Variant,
            None => defaults.sensitivity,
        };
        let ignore_punctuation = read_boolean_option(&mut options, "ignorePunctuation")?
            .unwrap_or(defaults.ignore_punctuation);

        let mut values = resolved.values;
        let collation_value = values.remove("co");
        let collation = match collation_value.as_deref() {
            Some("") | Some("standard") | Some("search") | None => "default".to_owned(),
            Some(value) => value.to_owned(),
        };
        let numeric = values.remove("kn").as_deref() == Some("true");
        let case_first_value = values.remove("kf");
        let case_first = match case_first_value.as_deref() {
            Some("upper") => CollatorCaseFirst::Upper,
            Some("lower") => CollatorCaseFirst::Lower,
            _ => CollatorCaseFirst::False,
        };

        Ok(Self {
            locale: resolved.locale,
            data_locale: resolved.data_locale,
            usage,
            sensitivity,
            ignore_punctuation,
            collation,
            numeric,
            case_first,
        })
    }

    /// Returns the ECMA-402 resolved options in property-table order.
    #[must_use]
    pub fn resolved_options(&self) -> ResolvedCollatorOptions<'_> {
        ResolvedCollatorOptions {
            locale: &self.locale,
            usage: self.usage,
            sensitivity: self.sensitivity,
            ignore_punctuation: self.ignore_punctuation,
            collation: &self.collation,
            numeric: self.numeric,
            case_first: self.case_first,
        }
    }

    /// Compares exact JavaScript UTF-16 strings and normalizes the provider's
    /// implementation-defined number to `-1`, `0`, or `1`.
    #[must_use]
    pub fn compare(&self, provider: &dyn CollatorDataProvider, left: &[u16], right: &[u16]) -> i8 {
        let request = CollatorCompareRequest {
            options: CollatorCompareOptions {
                data_locale: &self.data_locale,
                usage: self.usage,
                sensitivity: self.sensitivity,
                ignore_punctuation: self.ignore_punctuation,
                numeric: self.numeric,
                case_first: self.case_first,
                collation: &self.collation,
            },
            left,
            right,
        };
        ordering_number(provider.compare(request).unwrap_or_else(|| left.cmp(right)))
    }
}

/// Implements `Intl.Collator.supportedLocalesOf` without ambient locale data.
///
/// # Errors
/// Returns `RangeError` for malformed locale identifiers and invalid
/// `localeMatcher`, or propagates typed options-adapter failures.
pub fn supported_locales_of(
    locales: &[String],
    options: Option<&mut dyn CollatorOptionsSource>,
    provider: &dyn CollatorDataProvider,
) -> Result<Vec<String>, CollatorError> {
    let requested = canonicalize_locale_list(locales, provider)?;
    let mut options = options;
    coerce_options(&mut options)?;
    let matcher = parse_locale_matcher(read_string_option(
        &mut options,
        "localeMatcher",
        &["lookup", "best fit"],
    )?)?;
    supported_locales(&requested, matcher, provider).map_err(Into::into)
}

fn coerce_options(
    options: &mut Option<&mut dyn CollatorOptionsSource>,
) -> Result<(), CollatorError> {
    if let Some(source) = options.as_deref_mut() {
        source.coerce_options_to_object()?;
    }
    Ok(())
}

fn read_string_option(
    options: &mut Option<&mut dyn CollatorOptionsSource>,
    property: &'static str,
    allowed: &[&str],
) -> Result<Option<String>, CollatorError> {
    let Some(source) = options.as_deref_mut() else {
        return Ok(None);
    };
    let Some(value) = source.get_option(property, CollatorOptionType::String)? else {
        return Ok(None);
    };
    let CoercedCollatorOption::String(value) = value else {
        return Err(CollatorError::type_error(format!(
            "options adapter returned a non-string value for {property}"
        )));
    };
    if !allowed.is_empty() && !allowed.contains(&value.as_str()) {
        return Err(CollatorError::range_error(format!(
            "invalid value for option {property}: {value}"
        )));
    }
    Ok(Some(value))
}

fn read_boolean_option(
    options: &mut Option<&mut dyn CollatorOptionsSource>,
    property: &'static str,
) -> Result<Option<bool>, CollatorError> {
    let Some(source) = options.as_deref_mut() else {
        return Ok(None);
    };
    let Some(value) = source.get_option(property, CollatorOptionType::Boolean)? else {
        return Ok(None);
    };
    let CoercedCollatorOption::Boolean(value) = value else {
        return Err(CollatorError::type_error(format!(
            "options adapter returned a non-boolean value for {property}"
        )));
    };
    Ok(Some(value))
}

fn parse_usage(value: Option<String>) -> Result<CollatorUsage, CollatorError> {
    match value.as_deref() {
        None | Some("sort") => Ok(CollatorUsage::Sort),
        Some("search") => Ok(CollatorUsage::Search),
        Some(value) => Err(CollatorError::range_error(format!(
            "invalid value for option usage: {value}"
        ))),
    }
}

fn parse_locale_matcher(value: Option<String>) -> Result<LocaleMatcher, CollatorError> {
    match value.as_deref() {
        None | Some("best fit") => Ok(LocaleMatcher::BestFit),
        Some("lookup") => Ok(LocaleMatcher::Lookup),
        Some(value) => Err(CollatorError::range_error(format!(
            "invalid value for option localeMatcher: {value}"
        ))),
    }
}

fn parse_sensitivity(value: &str) -> CollatorSensitivity {
    match value {
        "base" => CollatorSensitivity::Base,
        "accent" => CollatorSensitivity::Accent,
        "case" => CollatorSensitivity::Case,
        _ => CollatorSensitivity::Variant,
    }
}

fn canonicalize_uvalue(provider: &dyn LocaleDataProvider, key: &str, value: &str) -> String {
    let lower = value.to_ascii_lowercase();
    provider
        .unicode_type_alias(key, &lower)
        .unwrap_or(&lower)
        .to_ascii_lowercase()
}

fn is_unicode_type(value: &str) -> bool {
    !value.is_empty()
        && value.split('-').all(|subtag| {
            (3..=8).contains(&subtag.len())
                && subtag.bytes().all(|byte| byte.is_ascii_alphanumeric())
        })
}

const fn ordering_number(ordering: Ordering) -> i8 {
    match ordering {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    }
}

#[cfg(test)]
mod tests {
    use super::super::locale_negotiation::LanguageId;
    use super::*;
    use std::cell::{Cell, RefCell};

    #[derive(Clone, Debug, Eq, PartialEq)]
    enum OptionEvent {
        Coerce,
        Get(&'static str, CollatorOptionType),
    }

    #[derive(Default)]
    struct Options {
        values: BTreeMap<&'static str, CoercedCollatorOption>,
        events: Vec<OptionEvent>,
        fail_coercion: bool,
        fail_property: Option<&'static str>,
    }

    impl Options {
        fn string(mut self, key: &'static str, value: &str) -> Self {
            self.values
                .insert(key, CoercedCollatorOption::String(value.to_owned()));
            self
        }

        fn boolean(mut self, key: &'static str, value: bool) -> Self {
            self.values
                .insert(key, CoercedCollatorOption::Boolean(value));
            self
        }
    }

    impl CollatorOptionsSource for Options {
        fn coerce_options_to_object(&mut self) -> Result<(), CollatorError> {
            self.events.push(OptionEvent::Coerce);
            if self.fail_coercion {
                return Err(CollatorError::type_error("cannot convert null to object"));
            }
            Ok(())
        }

        fn get_option(
            &mut self,
            property: &'static str,
            option_type: CollatorOptionType,
        ) -> Result<Option<CoercedCollatorOption>, CollatorError> {
            self.events.push(OptionEvent::Get(property, option_type));
            if self.fail_property == Some(property) {
                return Err(CollatorError::type_error(format!(
                    "hostile getter for {property}"
                )));
            }
            Ok(self.values.get(property).cloned())
        }
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct OwnedCompareCall {
        data_locale: String,
        usage: CollatorUsage,
        sensitivity: CollatorSensitivity,
        ignore_punctuation: bool,
        numeric: bool,
        case_first: CollatorCaseFirst,
        collation: String,
        left: Vec<u16>,
        right: Vec<u16>,
    }

    struct TestProvider {
        available: Vec<String>,
        fallback: Option<String>,
        key_values: BTreeMap<(String, String), Vec<String>>,
        type_aliases: BTreeMap<(String, String), String>,
        defer_compare: Cell<bool>,
        defaults_calls: RefCell<Vec<(String, CollatorUsage)>>,
        compare_calls: RefCell<Vec<OwnedCompareCall>>,
    }

    impl TestProvider {
        fn populated() -> Self {
            let available = vec![
                "de".to_owned(),
                "en".to_owned(),
                "sv".to_owned(),
                "zh-Hant-TW".to_owned(),
            ];
            let mut key_values = BTreeMap::new();
            for locale in &available {
                key_values.insert(
                    (locale.clone(), "co".to_owned()),
                    vec!["".to_owned(), "phonebk".to_owned(), "emoji".to_owned()],
                );
                key_values.insert(
                    (locale.clone(), "kn".to_owned()),
                    vec!["false".to_owned(), "true".to_owned()],
                );
                key_values.insert(
                    (locale.clone(), "kf".to_owned()),
                    vec!["false".to_owned(), "upper".to_owned(), "lower".to_owned()],
                );
            }
            let mut type_aliases = BTreeMap::new();
            type_aliases.insert(
                ("co".to_owned(), "dictionary".to_owned()),
                "dict".to_owned(),
            );
            Self {
                available,
                fallback: Some("en".to_owned()),
                key_values,
                type_aliases,
                defer_compare: Cell::new(false),
                defaults_calls: RefCell::new(Vec::new()),
                compare_calls: RefCell::new(Vec::new()),
            }
        }

        fn empty() -> Self {
            Self {
                available: Vec::new(),
                fallback: None,
                key_values: BTreeMap::new(),
                type_aliases: BTreeMap::new(),
                defer_compare: Cell::new(false),
                defaults_calls: RefCell::new(Vec::new()),
                compare_calls: RefCell::new(Vec::new()),
            }
        }
    }

    impl LocaleDataProvider for TestProvider {
        fn available_locales(&self) -> &[String] {
            &self.available
        }

        fn unicode_type_alias(&self, key: &str, value: &str) -> Option<&str> {
            self.type_aliases
                .get(&(key.to_owned(), value.to_owned()))
                .map(String::as_str)
        }

        fn key_values(&self, data_locale: &str, key: &str) -> &[String] {
            self.key_values
                .get(&(data_locale.to_owned(), key.to_owned()))
                .map_or(&[], Vec::as_slice)
        }

        fn add_likely_subtags(&self, locale: &LanguageId) -> Option<LanguageId> {
            if locale.language != "zh" {
                return None;
            }
            Some(LanguageId {
                language: "zh".to_owned(),
                script: Some(locale.script.clone().unwrap_or_else(|| "Hant".to_owned())),
                region: Some(locale.region.clone().unwrap_or_else(|| "TW".to_owned())),
                variants: locale.variants.clone(),
            })
        }

        fn fallback_locale(&self) -> Option<&str> {
            self.fallback.as_deref()
        }
    }

    impl CollatorDataProvider for TestProvider {
        fn locale_defaults(
            &self,
            data_locale: &str,
            usage: CollatorUsage,
        ) -> CollatorLocaleDefaults {
            self.defaults_calls
                .borrow_mut()
                .push((data_locale.to_owned(), usage));
            CollatorLocaleDefaults {
                sensitivity: CollatorSensitivity::Base,
                ignore_punctuation: usage == CollatorUsage::Search,
            }
        }

        fn compare(&self, request: CollatorCompareRequest<'_>) -> Option<Ordering> {
            self.compare_calls.borrow_mut().push(OwnedCompareCall {
                data_locale: request.options.data_locale.to_owned(),
                usage: request.options.usage,
                sensitivity: request.options.sensitivity,
                ignore_punctuation: request.options.ignore_punctuation,
                numeric: request.options.numeric,
                case_first: request.options.case_first,
                collation: request.options.collation.to_owned(),
                left: request.left.to_vec(),
                right: request.right.to_vec(),
            });
            if self.defer_compare.get() {
                return None;
            }
            Some(fixture_collation(request))
        }
    }

    fn fixture_collation(request: CollatorCompareRequest<'_>) -> Ordering {
        let mut left = normalize_fixture(request.left, request.options.sensitivity);
        let mut right = normalize_fixture(request.right, request.options.sensitivity);
        if request.options.ignore_punctuation {
            left.retain(|unit| !is_ascii_punctuation(*unit));
            right.retain(|unit| !is_ascii_punctuation(*unit));
        }
        if matches!(
            request.options.sensitivity,
            CollatorSensitivity::Case | CollatorSensitivity::Variant
        ) && request.options.case_first != CollatorCaseFirst::False
            && let Some(ordering) = compare_case_variants(&left, &right, request.options.case_first)
        {
            return ordering;
        }
        if request.options.numeric {
            return compare_numeric_runs(&left, &right);
        }
        left.cmp(&right)
    }

    fn normalize_fixture(input: &[u16], sensitivity: CollatorSensitivity) -> Vec<u16> {
        let mut decomposed = Vec::with_capacity(input.len() + 1);
        for unit in input {
            match unit {
                0x00e9 => decomposed.extend(['e' as u16, 0x0301]),
                0x00c9 => decomposed.extend(['E' as u16, 0x0301]),
                _ => decomposed.push(*unit),
            }
        }
        match sensitivity {
            CollatorSensitivity::Base => decomposed
                .into_iter()
                .filter(|unit| *unit != 0x0301)
                .map(ascii_lower)
                .collect(),
            CollatorSensitivity::Accent => decomposed.into_iter().map(ascii_lower).collect(),
            CollatorSensitivity::Case => decomposed
                .into_iter()
                .filter(|unit| *unit != 0x0301)
                .collect(),
            CollatorSensitivity::Variant => decomposed,
        }
    }

    const fn ascii_lower(unit: u16) -> u16 {
        if unit >= b'A' as u16 && unit <= b'Z' as u16 {
            unit + (b'a' - b'A') as u16
        } else {
            unit
        }
    }

    const fn is_ascii_punctuation(unit: u16) -> bool {
        (unit >= 0x20 && unit <= 0x2f)
            || (unit >= 0x3a && unit <= 0x40)
            || (unit >= 0x5b && unit <= 0x60)
            || (unit >= 0x7b && unit <= 0x7e)
    }

    fn compare_case_variants(
        left: &[u16],
        right: &[u16],
        case_first: CollatorCaseFirst,
    ) -> Option<Ordering> {
        for (left_unit, right_unit) in left.iter().zip(right) {
            if left_unit == right_unit {
                continue;
            }
            if ascii_lower(*left_unit) != ascii_lower(*right_unit) {
                return None;
            }
            let left_upper = (*left_unit >= b'A' as u16) && (*left_unit <= b'Z' as u16);
            let right_upper = (*right_unit >= b'A' as u16) && (*right_unit <= b'Z' as u16);
            if left_upper == right_upper {
                return None;
            }
            let upper_first = case_first == CollatorCaseFirst::Upper;
            return Some(if left_upper == upper_first {
                Ordering::Less
            } else {
                Ordering::Greater
            });
        }
        None
    }

    fn compare_numeric_runs(left: &[u16], right: &[u16]) -> Ordering {
        let (mut left_index, mut right_index) = (0, 0);
        while left_index < left.len() && right_index < right.len() {
            let left_digit = is_ascii_digit_unit(left[left_index]);
            let right_digit = is_ascii_digit_unit(right[right_index]);
            if left_digit && right_digit {
                let left_end = digit_run_end(left, left_index);
                let right_end = digit_run_end(right, right_index);
                let left_significant = significant_digits(&left[left_index..left_end]);
                let right_significant = significant_digits(&right[right_index..right_end]);
                let ordering = left_significant
                    .len()
                    .cmp(&right_significant.len())
                    .then_with(|| left_significant.cmp(right_significant));
                if ordering != Ordering::Equal {
                    return ordering;
                }
                left_index = left_end;
                right_index = right_end;
                continue;
            }
            let ordering = left[left_index].cmp(&right[right_index]);
            if ordering != Ordering::Equal {
                return ordering;
            }
            left_index += 1;
            right_index += 1;
        }
        (left.len() - left_index).cmp(&(right.len() - right_index))
    }

    const fn is_ascii_digit_unit(unit: u16) -> bool {
        unit >= b'0' as u16 && unit <= b'9' as u16
    }

    fn digit_run_end(units: &[u16], start: usize) -> usize {
        let mut end = start;
        while end < units.len() && is_ascii_digit_unit(units[end]) {
            end += 1;
        }
        end
    }

    fn significant_digits(units: &[u16]) -> &[u16] {
        let first_nonzero = units.iter().position(|unit| *unit != b'0' as u16);
        first_nonzero.map_or(&units[units.len()..], |index| &units[index..])
    }

    fn utf16(value: &str) -> Vec<u16> {
        value.encode_utf16().collect()
    }

    #[test]
    fn constructor_reads_hostile_options_in_specification_order_once() {
        let provider = TestProvider::populated();
        let mut options = Options::default()
            .string("usage", "search")
            .string("localeMatcher", "lookup")
            .string("collation", "phonebk")
            .boolean("numeric", true)
            .string("caseFirst", "upper")
            .string("sensitivity", "case")
            .boolean("ignorePunctuation", true);

        let collator = Collator::new(&["de".to_owned()], Some(&mut options), &provider)
            .expect("all options are valid");

        assert_eq!(
            options.events,
            vec![
                OptionEvent::Coerce,
                OptionEvent::Get("usage", CollatorOptionType::String),
                OptionEvent::Get("localeMatcher", CollatorOptionType::String),
                OptionEvent::Get("collation", CollatorOptionType::String),
                OptionEvent::Get("numeric", CollatorOptionType::Boolean),
                OptionEvent::Get("caseFirst", CollatorOptionType::String),
                OptionEvent::Get("sensitivity", CollatorOptionType::String),
                OptionEvent::Get("ignorePunctuation", CollatorOptionType::Boolean),
            ]
        );
        assert_eq!(
            collator.resolved_options(),
            ResolvedCollatorOptions {
                locale: "de",
                usage: CollatorUsage::Search,
                sensitivity: CollatorSensitivity::Case,
                ignore_punctuation: true,
                collation: "phonebk",
                numeric: true,
                case_first: CollatorCaseFirst::Upper,
            }
        );
    }

    #[test]
    fn explicit_options_override_unicode_keywords_and_strip_superseded_keys() {
        let provider = TestProvider::populated();
        let mut options = Options::default()
            .string("collation", "emoji")
            .boolean("numeric", false)
            .string("caseFirst", "lower");

        let collator = Collator::new(
            &["de-u-co-phonebk-kf-upper-kn".to_owned()],
            Some(&mut options),
            &provider,
        )
        .expect("provider supports every explicit value");
        let resolved = collator.resolved_options();

        assert_eq!(resolved.locale, "de");
        assert_eq!(resolved.collation, "emoji");
        assert!(!resolved.numeric);
        assert_eq!(resolved.case_first, CollatorCaseFirst::Lower);
    }

    #[test]
    fn supported_unicode_keywords_survive_and_provider_defaults_fill_absent_keys() {
        let provider = TestProvider::populated();
        let collator = Collator::new(&["de-u-kn-kf-upper-co-phonebk".to_owned()], None, &provider)
            .expect("locale extension is supported");
        let resolved = collator.resolved_options();

        assert_eq!(resolved.locale, "de-u-co-phonebk-kf-upper-kn");
        assert_eq!(resolved.collation, "phonebk");
        assert!(resolved.numeric);
        assert_eq!(resolved.case_first, CollatorCaseFirst::Upper);

        let collator = Collator::new(&["de".to_owned()], None, &provider)
            .expect("provider has a default locale record");
        let default = collator.resolved_options();
        assert_eq!(default.collation, "default");
        assert!(!default.numeric);
        assert_eq!(default.case_first, CollatorCaseFirst::False);
    }

    #[test]
    fn sort_and_search_use_their_required_default_sources() {
        let provider = TestProvider::populated();
        let sort =
            Collator::new(&["en".to_owned()], None, &provider).expect("sort defaults resolve");
        let mut search_options = Options::default().string("usage", "search");
        let search = Collator::new(&["en".to_owned()], Some(&mut search_options), &provider)
            .expect("search defaults resolve");

        assert_eq!(
            sort.resolved_options().sensitivity,
            CollatorSensitivity::Variant
        );
        assert!(!sort.resolved_options().ignore_punctuation);
        assert_eq!(
            search.resolved_options().sensitivity,
            CollatorSensitivity::Base
        );
        assert!(search.resolved_options().ignore_punctuation);
        assert_eq!(
            *provider.defaults_calls.borrow(),
            vec![
                ("en".to_owned(), CollatorUsage::Sort),
                ("en".to_owned(), CollatorUsage::Search),
            ]
        );
    }

    #[test]
    fn locale_and_option_failures_keep_error_classes_and_short_circuit_getters() {
        let provider = TestProvider::populated();
        let mut untouched = Options::default();
        let invalid_locale = Collator::new(&["en--US".to_owned()], Some(&mut untouched), &provider)
            .expect_err("ill-formed locales are rejected");
        assert_eq!(invalid_locale.kind, CollatorErrorKind::RangeError);
        assert!(untouched.events.is_empty());

        let mut null_options = Options {
            fail_coercion: true,
            ..Options::default()
        };
        let null_error = Collator::new(&["en".to_owned()], Some(&mut null_options), &provider)
            .expect_err("null ToObject is a TypeError");
        assert_eq!(null_error.kind, CollatorErrorKind::TypeError);
        assert_eq!(null_options.events, vec![OptionEvent::Coerce]);

        let mut invalid_collation = Options::default().string("collation", "ab");
        let range_error =
            Collator::new(&["en".to_owned()], Some(&mut invalid_collation), &provider)
                .expect_err("a Unicode type subtag needs at least three characters");
        assert_eq!(range_error.kind, CollatorErrorKind::RangeError);
        assert!(range_error.message.contains("collation"));
        assert_eq!(
            invalid_collation.events,
            vec![
                OptionEvent::Coerce,
                OptionEvent::Get("usage", CollatorOptionType::String),
                OptionEvent::Get("localeMatcher", CollatorOptionType::String),
                OptionEvent::Get("collation", CollatorOptionType::String),
            ]
        );

        let mut hostile = Options {
            fail_property: Some("caseFirst"),
            ..Options::default()
        };
        let hostile_error = Collator::new(&["en".to_owned()], Some(&mut hostile), &provider)
            .expect_err("getter failure propagates");
        assert_eq!(hostile_error.kind, CollatorErrorKind::TypeError);
        assert_eq!(
            hostile.events.last(),
            Some(&OptionEvent::Get("caseFirst", CollatorOptionType::String))
        );
        assert!(!hostile.events.iter().any(|event| matches!(
            event,
            OptionEvent::Get("sensitivity" | "ignorePunctuation", _)
        )));
    }

    #[test]
    fn supported_locales_preserve_order_and_matcher_behavior() {
        let provider = TestProvider::populated();
        let locales = vec![
            "SV-se".to_owned(),
            "zh-HK".to_owned(),
            "en-US".to_owned(),
            "sv-SE".to_owned(),
            "xx".to_owned(),
        ];
        let mut lookup = Options::default().string("localeMatcher", "lookup");
        let lookup_result = supported_locales_of(&locales, Some(&mut lookup), &provider)
            .expect("lookup filtering succeeds");
        assert_eq!(lookup_result, vec!["sv-SE", "en-US"]);
        assert_eq!(
            lookup.events,
            vec![
                OptionEvent::Coerce,
                OptionEvent::Get("localeMatcher", CollatorOptionType::String),
            ]
        );

        let best_fit =
            supported_locales_of(&locales, None, &provider).expect("best-fit filtering succeeds");
        assert_eq!(best_fit, vec!["sv-SE", "zh-HK", "en-US"]);
    }

    #[test]
    fn supported_locales_validate_locales_before_touching_options() {
        let provider = TestProvider::populated();
        let mut options = Options {
            fail_coercion: true,
            ..Options::default()
        };
        let error =
            supported_locales_of(&["not_a_locale".to_owned()], Some(&mut options), &provider)
                .expect_err("locale failure precedes options coercion");
        assert_eq!(error.kind, CollatorErrorKind::RangeError);
        assert!(options.events.is_empty());
    }

    #[test]
    fn numeric_case_and_punctuation_options_reach_collation() {
        let provider = TestProvider::populated();
        let mut options = Options::default()
            .boolean("numeric", true)
            .string("caseFirst", "lower")
            .boolean("ignorePunctuation", true);
        let collator = Collator::new(&["en".to_owned()], Some(&mut options), &provider)
            .expect("comparison options resolve");

        assert_eq!(
            collator.compare(&provider, &utf16("item-2"), &utf16("item 10")),
            -1
        );
        assert_eq!(collator.compare(&provider, &utf16("a"), &utf16("A")), -1);
        assert_eq!(collator.compare(&provider, &utf16("a-b"), &utf16("ab")), 0);

        let calls = provider.compare_calls.borrow();
        assert_eq!(calls.len(), 3);
        assert!(calls.iter().all(|call| call.numeric));
        assert!(calls.iter().all(|call| call.ignore_punctuation));
        assert!(
            calls
                .iter()
                .all(|call| call.case_first == CollatorCaseFirst::Lower)
        );
    }

    #[test]
    fn canonical_equivalence_remains_equal_without_a_code_unit_tiebreak() {
        let provider = TestProvider::populated();
        let collator =
            Collator::new(&["en".to_owned()], None, &provider).expect("default collator resolves");
        let composed = vec![0x00e9];
        let decomposed = vec!['e' as u16, 0x0301];

        assert_eq!(collator.compare(&provider, &composed, &decomposed), 0);
        let calls = provider.compare_calls.borrow();
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].left, composed);
        assert_eq!(calls[0].right, decomposed);
    }

    #[test]
    fn utf16_fallback_is_total_and_preserves_lone_surrogates() {
        let provider = TestProvider::populated();
        provider.defer_compare.set(true);
        let collator =
            Collator::new(&["en".to_owned()], None, &provider).expect("default collator resolves");

        assert_eq!(collator.compare(&provider, &[0xd800], &[0xdc00]), -1);
        assert_eq!(collator.compare(&provider, &[0xd800], &[0xd800]), 0);
        assert_eq!(
            collator.compare(&provider, &[0xd800, 0xdc00], &[0xd800, 0xdc01]),
            -1
        );
        assert_eq!(collator.compare(&provider, &[0xe000], &[0xd800, 0xdc00]), 1);
    }

    #[test]
    fn provider_calls_are_stable_complete_and_allocation_free_at_the_boundary() {
        let provider = TestProvider::populated();
        let mut options = Options::default()
            .string("usage", "search")
            .string("collation", "phonebk")
            .boolean("numeric", true)
            .string("caseFirst", "upper")
            .string("sensitivity", "accent")
            .boolean("ignorePunctuation", false);
        let collator = Collator::new(&["de".to_owned()], Some(&mut options), &provider)
            .expect("collator resolves");
        let left = utf16("A2");
        let right = utf16("a10");

        let first = collator.compare(&provider, &left, &right);
        let second = collator.compare(&provider, &left, &right);
        assert_eq!(first, second);
        let calls = provider.compare_calls.borrow();
        assert_eq!(calls.len(), 2);
        assert_eq!(calls[0], calls[1]);
        assert_eq!(calls[0].data_locale, "de");
        assert_eq!(calls[0].usage, CollatorUsage::Search);
        assert_eq!(calls[0].sensitivity, CollatorSensitivity::Accent);
        assert_eq!(calls[0].collation, "phonebk");
        assert_eq!(calls[0].left, left);
        assert_eq!(calls[0].right, right);
    }

    #[test]
    fn absent_provider_data_fails_instead_of_reading_an_ambient_locale() {
        let provider = TestProvider::empty();
        let error =
            Collator::new(&[], None, &provider).expect_err("no provider locale means no Collator");

        assert_eq!(error.kind, CollatorErrorKind::RangeError);
        assert_eq!(error.message, "no available locale");
        assert!(provider.defaults_calls.borrow().is_empty());
        assert!(provider.compare_calls.borrow().is_empty());
    }
}
