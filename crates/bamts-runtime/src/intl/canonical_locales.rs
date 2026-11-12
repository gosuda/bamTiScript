//! Cross-service ECMA-402 adapter contracts.
//!
//! Implements `Intl.getCanonicalLocales`, `Intl.supportedValuesOf`, and the
//! shared constructor/call contracts every Intl service constructor uses.
//! Options are not read here: the JavaScript binding reads them from live
//! values, in the order the specification makes observable. All locale parsing and canonicalization delegate to the C10.1
//! negotiation module through [`LocaleDataProvider`]; all
//! implementation-defined value inventories (calendar, collation, currency,
//! numberingSystem, timeZone, unit) arrive through the injected
//! [`SupportedValuesInventory`] trait. This module reads no environment,
//! filesystem, clock, or other ambient host state and embeds no CLDR guesses.
//!
//! UTF-16 boundary: JavaScript strings are sequences of UTF-16 code units.
//! The runtime adapter decodes them to Rust `String` values and performs any
//! observable `Get`/`ToString` side effects before calling this module, which
//! then applies only the ECMA-402 validation layer to the decoded text.
//!
//! Specification sources:
//! - <https://tc39.es/ecma402/#sec-canonicalizelocalelist>
//! - <https://tc39.es/ecma402/#sec-supported-values-of>

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use super::locale_negotiation::{
    JsErrorKind, LocaleDataProvider, LocaleError, canonicalize_unicode_locale_id,
};

/// The ECMAScript error class surfaced by a cross-service adapter failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IntlErrorKind {
    /// Wrong invocation form, wrong argument type, or a type-checked failure.
    TypeError,
    /// An input string or option value is outside the permitted range.
    RangeError,
}

/// An adapter failure carrying its ECMAScript error class and message text.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IntlError {
    /// ECMAScript error class of the thrown value.
    pub kind: IntlErrorKind,
    /// Human-readable `Error.prototype.message` text.
    pub message: String,
}

impl IntlError {
    /// Builds a `TypeError` failure.
    #[must_use]
    pub fn type_error(message: impl Into<String>) -> Self {
        Self {
            kind: IntlErrorKind::TypeError,
            message: message.into(),
        }
    }

    /// Builds a `RangeError` failure.
    #[must_use]
    pub fn range_error(message: impl Into<String>) -> Self {
        Self {
            kind: IntlErrorKind::RangeError,
            message: message.into(),
        }
    }

    /// Converts a C10.1 locale failure, preserving its JS error class.
    #[must_use]
    pub fn from_locale_error(error: LocaleError) -> Self {
        let message = error.to_string();
        match error.js_error_kind() {
            JsErrorKind::RangeError => Self::range_error(message),
        }
    }
}

impl fmt::Display for IntlError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl Error for IntlError {}

/// A JavaScript value at the Intl adapter boundary, carrying its ECMAScript
/// type tag and, for objects, the text the host obtained by coercion.
///
/// The host performs observable coercions before constructing this enum:
/// `ToString` on plain object values, and the internal-slot string of
/// `Intl.Locale` instances (whose user-defined `toString` must NOT be called
/// per `CanonicalizeLocaleList`). This module applies only validation.
#[derive(Clone, Debug, PartialEq)]
pub enum IntlValue {
    /// `undefined`.
    Undefined,
    /// `null`.
    Null,
    /// A boolean primitive.
    Boolean(bool),
    /// A number primitive.
    Number(f64),
    /// A string primitive, decoded to scalar text by the host.
    String(String),
    /// An object value, carried as the host-provided `ToString` result.
    Object(String),
}

/// Invocation form of a JavaScript call crossing the adapter boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IntlCallForm {
    /// Called with `new` (`NewTarget` is defined).
    Construct,
    /// Called as a plain function (`NewTarget` is undefined).
    Apply,
}

/// Enforces the constructor-only contract shared by every Intl service
/// constructor (`Intl.Collator`, `Intl.NumberFormat`, `Intl.DateTimeFormat`,
/// and peers): a call with an undefined `NewTarget` throws `TypeError`.
///
/// # Errors
/// Returns `TypeError` when the constructor was invoked as a plain function.
pub fn require_constructor_call(name: &str, form: IntlCallForm) -> Result<(), IntlError> {
    match form {
        IntlCallForm::Construct => Ok(()),
        IntlCallForm::Apply => Err(IntlError::type_error(format!(
            "Constructor {name} requires 'new'"
        ))),
    }
}

/// Enforces the not-a-constructor contract of plain Intl functions such as
/// `Intl.getCanonicalLocales` and `Intl.supportedValuesOf`: using them with
/// `new` throws `TypeError`.
///
/// # Errors
/// Returns `TypeError` when the function was invoked with `new`.
pub fn require_ordinary_call(name: &str, form: IntlCallForm) -> Result<(), IntlError> {
    match form {
        IntlCallForm::Apply => Ok(()),
        IntlCallForm::Construct => Err(IntlError::type_error(format!(
            "{name} is not a constructor"
        ))),
    }
}

/// The typed `locales` argument of `Intl.getCanonicalLocales` and of every
/// Intl service constructor.
#[derive(Clone, Debug, PartialEq)]
pub enum LocaleListArgument {
    /// The argument is `undefined`; the canonical list is empty.
    Undefined,
    /// A string argument, or a single `Intl.Locale` instance: per
    /// `CanonicalizeLocaleList` step 3 it is wrapped as a single-element list,
    /// using the internal slot text without calling `toString`.
    Text(String),
    /// An object argument materialized by the host into its indexed elements
    /// in ascending index order, after `Get(O, "length")` and each `Get(O, Pk)`.
    Elements(Vec<IntlValue>),
    /// The argument is `null`; the `ToObject` in `CanonicalizeLocaleList`
    /// step 3b throws `TypeError`.
    Null,
    /// A boolean, number, bigint, or symbol primitive argument: `ToObject`
    /// wraps it into an object without a `length` own property, so the
    /// canonical list is empty.
    Primitive,
}

/// Applies ECMA-402 `Intl.getCanonicalLocales`. Structural validation and
/// canonicalization delegate to C10.1 using the provider's alias data; the
/// result is order-preserving and deduplicated on first occurrence.
///
/// # Errors
/// Returns `TypeError` for a `null` locales argument or a non-string,
/// non-object list element; returns `RangeError` for a structurally invalid
/// language tag.
pub fn get_canonical_locales(
    argument: &LocaleListArgument,
    provider: &dyn LocaleDataProvider,
) -> Result<Vec<String>, IntlError> {
    match argument {
        LocaleListArgument::Undefined | LocaleListArgument::Primitive => Ok(Vec::new()),
        LocaleListArgument::Null => Err(IntlError::type_error("invalid locales argument: null")),
        LocaleListArgument::Text(text) => Ok(vec![canonicalize_single_tag(text, provider)?]),
        LocaleListArgument::Elements(elements) => {
            let mut seen = BTreeSet::new();
            let mut canonical = Vec::new();
            for element in elements {
                let text = match element {
                    IntlValue::Undefined => continue,
                    IntlValue::String(text) | IntlValue::Object(text) => text,
                    IntlValue::Null | IntlValue::Boolean(_) | IntlValue::Number(_) => {
                        return Err(IntlError::type_error(
                            "locale list element must be a string or an object",
                        ));
                    }
                };
                let tag = canonicalize_single_tag(text, provider)?;
                if seen.insert(tag.clone()) {
                    canonical.push(tag);
                }
            }
            Ok(canonical)
        }
    }
}

fn canonicalize_single_tag(
    tag: &str,
    provider: &dyn LocaleDataProvider,
) -> Result<String, IntlError> {
    canonicalize_unicode_locale_id(tag, provider).map_err(IntlError::from_locale_error)
}

/// The six keys accepted by `Intl.supportedValuesOf`.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SupportedValuesKey {
    /// `"calendar"`.
    Calendar,
    /// `"collation"`.
    Collation,
    /// `"currency"`.
    Currency,
    /// `"numberingSystem"`.
    NumberingSystem,
    /// `"timeZone"`.
    TimeZone,
    /// `"unit"`.
    Unit,
}

impl SupportedValuesKey {
    /// The exact ECMA-402 spelling of this key.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Calendar => "calendar",
            Self::Collation => "collation",
            Self::Currency => "currency",
            Self::NumberingSystem => "numberingSystem",
            Self::TimeZone => "timeZone",
            Self::Unit => "unit",
        }
    }
}

impl TryFrom<&str> for SupportedValuesKey {
    type Error = IntlError;

    /// Exact, case-sensitive key match; every other spelling is `RangeError`.
    fn try_from(key: &str) -> Result<Self, IntlError> {
        for candidate in [
            Self::Calendar,
            Self::Collation,
            Self::Currency,
            Self::NumberingSystem,
            Self::TimeZone,
            Self::Unit,
        ] {
            if key == candidate.name() {
                return Ok(candidate);
            }
        }
        Err(IntlError::range_error("Invalid key"))
    }
}

/// Supplies the implementation-defined canonical value inventories backing
/// `Intl.supportedValuesOf`. An ICU4X/CLDR adapter sources these from
/// formatter provider data; implementers must not consult ambient host state.
pub trait SupportedValuesInventory {
    /// Canonical calendar identifiers available to date formatting.
    fn supported_calendars(&self) -> &[String];
    /// Canonical collation type identifiers available to collation.
    fn supported_collations(&self) -> &[String];
    /// Currency identifiers available to currency-aware number formatting.
    fn supported_currencies(&self) -> &[String];
    /// Canonical numbering system identifiers available to number formatting.
    fn supported_numbering_systems(&self) -> &[String];
    /// Case-sensitive IANA time zone names available to date formatting.
    fn supported_time_zones(&self) -> &[String];
    /// Simple and compound unit identifiers available to unit formatting.
    fn supported_units(&self) -> &[String];
}

/// Caller-populated, deterministic value inventory useful for embedding and
/// tests. Contains no CLDR guesses of its own.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MapSupportedValues {
    values: BTreeMap<SupportedValuesKey, Vec<String>>,
}

impl MapSupportedValues {
    /// Creates an empty inventory.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Replaces the inventory for one key. Entries may be unsorted and
    /// duplicate; normalization happens per query.
    #[must_use]
    pub fn with_values(mut self, key: SupportedValuesKey, values: Vec<String>) -> Self {
        self.values.insert(key, values);
        self
    }

    fn raw(&self, key: SupportedValuesKey) -> &[String] {
        self.values.get(&key).map_or(&[], Vec::as_slice)
    }
}

impl SupportedValuesInventory for MapSupportedValues {
    fn supported_calendars(&self) -> &[String] {
        self.raw(SupportedValuesKey::Calendar)
    }
    fn supported_collations(&self) -> &[String] {
        self.raw(SupportedValuesKey::Collation)
    }
    fn supported_currencies(&self) -> &[String] {
        self.raw(SupportedValuesKey::Currency)
    }
    fn supported_numbering_systems(&self) -> &[String] {
        self.raw(SupportedValuesKey::NumberingSystem)
    }
    fn supported_time_zones(&self) -> &[String] {
        self.raw(SupportedValuesKey::TimeZone)
    }
    fn supported_units(&self) -> &[String] {
        self.raw(SupportedValuesKey::Unit)
    }
}

/// Applies ECMA-402 `Intl.supportedValuesOf`. `key` is the host-coerced
/// `ToString` of the property-key argument. The result carries the canonical
/// casing for the key, is ASCII-byte-order sorted (equal to the UTF-16
/// code-unit order of the JavaScript default sort for these identifiers), and
/// is deduplicated.
///
/// # Errors
/// Returns `RangeError` for an invalid key or a provider inventory entry that
/// violates the structural validity rule for its key.
pub fn supported_values_of(
    key: &str,
    inventory: &dyn SupportedValuesInventory,
) -> Result<Vec<String>, IntlError> {
    let key = SupportedValuesKey::try_from(key)?;
    let raw = match key {
        SupportedValuesKey::Calendar => inventory.supported_calendars(),
        SupportedValuesKey::Collation => inventory.supported_collations(),
        SupportedValuesKey::Currency => inventory.supported_currencies(),
        SupportedValuesKey::NumberingSystem => inventory.supported_numbering_systems(),
        SupportedValuesKey::TimeZone => inventory.supported_time_zones(),
        SupportedValuesKey::Unit => inventory.supported_units(),
    };
    normalize_supported_values(key, raw)
}

fn normalize_supported_values(
    key: SupportedValuesKey,
    raw: &[String],
) -> Result<Vec<String>, IntlError> {
    let mut values = Vec::with_capacity(raw.len());
    for entry in raw {
        let canonical = match key {
            // Currency codes are canonical uppercase; Unicode type values are
            // canonical lowercase; time zone names and unit identifiers are
            // case-sensitive and pass through unchanged.
            SupportedValuesKey::Currency => entry.to_ascii_uppercase(),
            SupportedValuesKey::Calendar
            | SupportedValuesKey::Collation
            | SupportedValuesKey::NumberingSystem => entry.to_ascii_lowercase(),
            SupportedValuesKey::TimeZone | SupportedValuesKey::Unit => entry.clone(),
        };
        let valid = match key {
            SupportedValuesKey::Calendar
            | SupportedValuesKey::Collation
            | SupportedValuesKey::NumberingSystem => is_unicode_type_value(&canonical),
            SupportedValuesKey::Currency => is_currency_code(&canonical),
            SupportedValuesKey::TimeZone => is_time_zone_name(&canonical),
            SupportedValuesKey::Unit => is_unit_identifier(&canonical),
        };
        if !valid {
            return Err(IntlError::range_error(format!(
                "Invalid {} inventory value: {canonical}",
                key.name()
            )));
        }
        values.push(canonical);
    }
    if key == SupportedValuesKey::Collation {
        // ECMA-402 AvailableCollations: "search" and "standard" do not
        // represent collations and must never surface in the result.
        values.retain(|value| value != "search" && value != "standard");
    }
    values.sort();
    values.dedup();
    Ok(values)
}

/// Unicode `unicode_type`: one or more `-`-separated 3-to-8-character ASCII
/// alphanumeric sequences (the calendar/collation/numberingSystem shape).
fn is_unicode_type_value(value: &str) -> bool {
    !value.is_empty()
        && value.split('-').all(|part| {
            (3..=8).contains(&part.len()) && part.bytes().all(|byte| byte.is_ascii_alphanumeric())
        })
}

/// Three uppercase ASCII letters (the ISO 4217 alpha-code shape).
fn is_currency_code(value: &str) -> bool {
    value.len() == 3 && value.bytes().all(|byte| byte.is_ascii_uppercase())
}

/// A case-sensitive IANA time zone name: nonempty ASCII letters, digits,
/// `_`, `-`, `+`, and `/`. IANA zone names contain no `.` runs.
fn is_time_zone_name(value: &str) -> bool {
    !value.is_empty()
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-' | b'+' | b'/'))
}

/// A well-formed simple or compound Unicode unit identifier: `-`-separated
/// nonempty ASCII alphanumeric segments containing at most one inner `-per-`
/// denominator separator.
fn is_unit_identifier(value: &str) -> bool {
    !value.is_empty()
        && value
            .split('-')
            .all(|part| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_alphanumeric()))
        && value.matches("-per-").count() <= 1
        && !value.starts_with("per-")
        && !value.ends_with("-per")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intl::locale_negotiation::MapLocaleData;

    fn tag_list(argument: &LocaleListArgument, data: &dyn LocaleDataProvider) -> Vec<String> {
        get_canonical_locales(argument, data).unwrap_or_else(|error| panic!("{error}"))
    }

    fn inventory() -> MapSupportedValues {
        MapSupportedValues::new()
            .with_values(
                SupportedValuesKey::Calendar,
                vec![
                    "gregory".into(),
                    "ROC".into(),
                    "Buddhist".into(),
                    "gregory".into(),
                ],
            )
            .with_values(
                SupportedValuesKey::Collation,
                vec![
                    "search".into(),
                    "emoji".into(),
                    "standard".into(),
                    "EMOJI".into(),
                    "big5han".into(),
                ],
            )
            .with_values(
                SupportedValuesKey::Currency,
                vec!["thb".into(), "usd".into(), "EUR".into(), "USD".into()],
            )
            .with_values(
                SupportedValuesKey::NumberingSystem,
                vec!["thai".into(), "Latn".into(), "thai".into()],
            )
            .with_values(
                SupportedValuesKey::TimeZone,
                vec![
                    "Europe/Paris".into(),
                    "UTC".into(),
                    "America/New_York".into(),
                    "Europe/Paris".into(),
                ],
            )
            .with_values(
                SupportedValuesKey::Unit,
                vec![
                    "square-meter".into(),
                    "celsius".into(),
                    "liter-per-100kilometer".into(),
                    "celsius".into(),
                ],
            )
    }

    #[test]
    fn canonical_locales_argument_forms() {
        let data = MapLocaleData::new();
        assert_eq!(
            tag_list(&LocaleListArgument::Undefined, &data),
            Vec::<String>::new()
        );
        assert_eq!(
            tag_list(&LocaleListArgument::Primitive, &data),
            Vec::<String>::new()
        );
        assert_eq!(
            get_canonical_locales(&LocaleListArgument::Null, &data).map_err(|error| error.kind),
            Err(IntlErrorKind::TypeError),
        );
        // A single string argument is wrapped, not iterated character-wise.
        assert_eq!(
            tag_list(&LocaleListArgument::Text("EN-gb".into()), &data),
            vec!["en-GB".to_owned()],
        );
    }

    #[test]
    fn canonical_list_applies_element_rules_dedup_and_order() {
        let data = MapLocaleData::new().with_language_alias("iw", "he");
        let elements = vec![
            IntlValue::String("EN-gb".into()),
            IntlValue::Undefined,
            IntlValue::Object("he-IL".into()),
            IntlValue::String("iw-IL".into()),
            IntlValue::String("fr".into()),
        ];
        assert_eq!(
            tag_list(&LocaleListArgument::Elements(elements), &data),
            vec!["en-GB".to_owned(), "he-IL".to_owned(), "fr".to_owned()],
        );
    }

    #[test]
    fn canonical_list_rejects_non_string_elements() {
        let data = MapLocaleData::new();
        for element in [
            IntlValue::Null,
            IntlValue::Boolean(true),
            IntlValue::Number(3.0),
        ] {
            let error = get_canonical_locales(&LocaleListArgument::Elements(vec![element]), &data)
                .expect_err("accepted a non-string element");
            assert_eq!(error.kind, IntlErrorKind::TypeError);
        }
    }

    #[test]
    fn malformed_tags_are_range_errors() {
        let data = MapLocaleData::new();
        for tag in ["", "en_US", "en--US", "en-u", "-en"] {
            let error = get_canonical_locales(&LocaleListArgument::Text(tag.to_owned()), &data)
                .expect_err("accepted a malformed tag");
            assert_eq!(
                error.kind,
                IntlErrorKind::RangeError,
                "wrong class for {tag}"
            );
        }
    }

    #[test]
    fn canonical_list_is_deterministic_across_calls() {
        let data = MapLocaleData::new().with_language_alias("sh", "sr-Latn");
        let elements = vec![
            IntlValue::String("SH".into()),
            IntlValue::String("sh".into()),
        ];
        let argument = LocaleListArgument::Elements(elements);
        assert_eq!(tag_list(&argument, &data), tag_list(&argument, &data),);
        assert_eq!(tag_list(&argument, &data), vec!["sr-Latn".to_owned()]);
    }

    #[test]
    fn supported_values_returns_each_key_sorted_unique_canonical() {
        let data = inventory();
        assert_eq!(
            supported_values_of("calendar", &data).unwrap_or_else(|error| panic!("{error}")),
            vec![
                "buddhist".to_owned(),
                "gregory".to_owned(),
                "roc".to_owned()
            ],
        );
        assert_eq!(
            supported_values_of("collation", &data).unwrap_or_else(|error| panic!("{error}")),
            vec!["big5han".to_owned(), "emoji".to_owned()],
        );
        assert_eq!(
            supported_values_of("currency", &data).unwrap_or_else(|error| panic!("{error}")),
            vec!["EUR".to_owned(), "THB".to_owned(), "USD".to_owned()],
        );
        assert_eq!(
            supported_values_of("numberingSystem", &data).unwrap_or_else(|error| panic!("{error}")),
            vec!["latn".to_owned(), "thai".to_owned()],
        );
        assert_eq!(
            supported_values_of("timeZone", &data).unwrap_or_else(|error| panic!("{error}")),
            vec![
                "America/New_York".to_owned(),
                "Europe/Paris".to_owned(),
                "UTC".to_owned(),
            ],
        );
        assert_eq!(
            supported_values_of("unit", &data).unwrap_or_else(|error| panic!("{error}")),
            vec![
                "celsius".to_owned(),
                "liter-per-100kilometer".to_owned(),
                "square-meter".to_owned(),
            ],
        );
    }

    #[test]
    fn supported_values_rejects_invalid_keys() {
        let data = MapSupportedValues::new();
        for key in ["", "Calendar", "calendars", "ca", "timezone", "units"] {
            let error = supported_values_of(key, &data).expect_err("accepted an invalid key");
            assert_eq!(
                error.kind,
                IntlErrorKind::RangeError,
                "wrong class for {key}"
            );
            assert_eq!(error.message, "Invalid key", "wrong message for {key}");
        }
    }

    #[test]
    fn supported_values_rejects_malformed_inventory_entries() {
        let cases: [(SupportedValuesKey, &str); 7] = [
            (SupportedValuesKey::Currency, "US"),
            (SupportedValuesKey::Currency, "U2D"),
            (SupportedValuesKey::Calendar, "ab"),
            (SupportedValuesKey::NumberingSystem, "abcdefghi"),
            (SupportedValuesKey::TimeZone, ""),
            (SupportedValuesKey::Unit, "per-second"),
            (SupportedValuesKey::Unit, "meter--second"),
        ];
        for (key, entry) in cases {
            let data = MapSupportedValues::new().with_values(key, vec![entry.to_owned()]);
            let error = supported_values_of(key.name(), &data)
                .expect_err("accepted a malformed inventory entry");
            assert_eq!(
                error.kind,
                IntlErrorKind::RangeError,
                "wrong class for {entry}"
            );
            assert!(
                error.message.contains(key.name()) && error.message.contains(entry),
                "message {error:?} names neither key nor value",
            );
        }
    }

    #[test]
    fn collation_exclusions_apply_before_sort_and_dedup() {
        let data = MapSupportedValues::new().with_values(
            SupportedValuesKey::Collation,
            vec!["standard".into(), "search".into(), "EMO".into()],
        );
        assert_eq!(
            supported_values_of("collation", &data).unwrap_or_else(|error| panic!("{error}")),
            vec!["emo".to_owned()],
        );
    }

    #[test]
    fn supported_values_is_deterministic_across_calls() {
        let data = inventory();
        for key in [
            "calendar",
            "collation",
            "currency",
            "numberingSystem",
            "timeZone",
            "unit",
        ] {
            assert_eq!(
                supported_values_of(key, &data),
                supported_values_of(key, &data),
            );
        }
    }

    #[test]
    fn constructor_and_plain_call_contracts() {
        assert!(require_constructor_call("Collator", IntlCallForm::Construct).is_ok());
        let error = require_constructor_call("Collator", IntlCallForm::Apply)
            .expect_err("accepted a plain constructor call");
        assert_eq!(error.kind, IntlErrorKind::TypeError);
        assert!(error.message.contains("Collator"));
        assert!(require_ordinary_call("Intl.getCanonicalLocales", IntlCallForm::Apply).is_ok());
        let error = require_ordinary_call("Intl.getCanonicalLocales", IntlCallForm::Construct)
            .expect_err("accepted constructing a plain function");
        assert_eq!(error.kind, IntlErrorKind::TypeError);
    }
}
