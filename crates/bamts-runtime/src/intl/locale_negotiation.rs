//! Deterministic ECMA-402 locale parsing, canonicalization, and negotiation.
//!
//! Locale-dependent facts are supplied by [`LocaleDataProvider`]. This module
//! never reads the process environment and contains no built-in CLDR aliases.
//!
//! Specification sources:
//! - <https://tc39.es/ecma402/#sec-language-tags>
//! - <https://tc39.es/ecma402/#sec-locale-and-parameter-negotiation>
//! - <https://unicode.org/reports/tr35/#Unicode_Language_and_Locale_Identifiers>

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

/// The JavaScript error class appropriate for a locale operation failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum JsErrorKind {
    /// An input string or option value is outside the permitted range.
    RangeError,
}

/// A failure while parsing or negotiating locales.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LocaleError {
    /// The supplied string is not a structurally valid Unicode BCP 47 locale ID.
    InvalidLanguageTag(String),
    /// A locale has a duplicate variant, extension singleton, attribute, or key.
    DuplicateSubtag(String),
    /// No provider locale can serve the request and no valid fallback exists.
    NoAvailableLocale,
}

impl LocaleError {
    /// Returns the ECMAScript error class for this failure.
    #[must_use]
    pub const fn js_error_kind(&self) -> JsErrorKind {
        JsErrorKind::RangeError
    }
}

impl fmt::Display for LocaleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidLanguageTag(tag) => write!(f, "invalid language tag: {tag}"),
            Self::DuplicateSubtag(subtag) => write!(f, "duplicate locale subtag: {subtag}"),
            Self::NoAvailableLocale => f.write_str("no available locale"),
        }
    }
}

impl Error for LocaleError {}

/// The language/script/region/variant portion of a locale identifier.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LanguageId {
    /// Lowercase primary language subtag.
    pub language: String,
    /// Title-case script subtag, when present.
    pub script: Option<String>,
    /// Uppercase region subtag, when present.
    pub region: Option<String>,
    /// Lowercase, lexicographically ordered variant subtags.
    pub variants: Vec<String>,
}

impl LanguageId {
    fn render(&self) -> String {
        let mut out = self.language.clone();
        if let Some(script) = &self.script {
            out.push('-');
            out.push_str(script);
        }
        if let Some(region) = &self.region {
            out.push('-');
            out.push_str(region);
        }
        for variant in &self.variants {
            out.push('-');
            out.push_str(variant);
        }
        out
    }

    fn normalize(&mut self) {
        self.language.make_ascii_lowercase();
        self.script = self.script.take().map(|value| titlecase(&value));
        self.region = self.region.take().map(|value| value.to_ascii_uppercase());
        for variant in &mut self.variants {
            variant.make_ascii_lowercase();
        }
        self.variants.sort();
    }
}

/// A parsed Unicode `u` extension.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct UnicodeExtension {
    /// Sorted, unique Unicode extension attributes.
    pub attributes: Vec<String>,
    /// Sorted Unicode keyword keys and their hyphen-joined types.
    /// An empty type represents the boolean value `true`.
    pub keywords: BTreeMap<String, String>,
}

/// A structurally parsed Unicode BCP 47 locale identifier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LanguageTag {
    /// Base language identifier.
    pub id: LanguageId,
    /// Unicode locale extension, when present.
    pub unicode: Option<UnicodeExtension>,
    extensions: BTreeMap<char, Vec<String>>,
    private_use: Vec<String>,
}

impl LanguageTag {
    /// Parses a Unicode BCP 47 locale identifier and applies canonical casing
    /// and ordering, without consulting locale data.
    ///
    /// # Errors
    /// Returns [`LocaleError`] for malformed grammar or duplicate subtags.
    pub fn parse(input: &str) -> Result<Self, LocaleError> {
        if input.is_empty() || !input.is_ascii() || input.starts_with('-') || input.ends_with('-') {
            return Err(LocaleError::InvalidLanguageTag(input.to_owned()));
        }
        let parts: Vec<&str> = input.split('-').collect();
        if parts.iter().any(|part| part.is_empty()) {
            return Err(LocaleError::InvalidLanguageTag(input.to_owned()));
        }
        let (mut id, mut index) = parse_language_id(&parts, 0, input)?;
        let mut unicode = None;
        let mut extensions = BTreeMap::new();
        let mut private_use = Vec::new();
        let mut seen_singletons = BTreeSet::new();

        while index < parts.len() {
            let singleton = parts[index];
            if singleton.len() != 1 || !is_alnum(singleton) {
                return Err(LocaleError::InvalidLanguageTag(input.to_owned()));
            }
            let singleton = singleton.as_bytes()[0].to_ascii_lowercase() as char;
            if singleton == 'x' {
                index += 1;
                if index == parts.len() {
                    return Err(LocaleError::InvalidLanguageTag(input.to_owned()));
                }
                for part in &parts[index..] {
                    if !(1..=8).contains(&part.len()) || !is_alnum(part) {
                        return Err(LocaleError::InvalidLanguageTag(input.to_owned()));
                    }
                    private_use.push(part.to_ascii_lowercase());
                }
                index = parts.len();
                continue;
            }
            if !seen_singletons.insert(singleton) {
                return Err(LocaleError::DuplicateSubtag(singleton.to_string()));
            }
            index += 1;
            let start = index;
            while index < parts.len() && parts[index].len() != 1 {
                index += 1;
            }
            if start == index {
                return Err(LocaleError::InvalidLanguageTag(input.to_owned()));
            }
            let body = &parts[start..index];
            if singleton == 'u' {
                unicode = Some(parse_unicode_extension(body, input)?);
            } else if singleton == 't' {
                extensions.insert(singleton, parse_transformed_extension(body, input)?);
            } else {
                if body
                    .iter()
                    .any(|part| !(2..=8).contains(&part.len()) || !is_alnum(part))
                {
                    return Err(LocaleError::InvalidLanguageTag(input.to_owned()));
                }
                extensions.insert(
                    singleton,
                    body.iter().map(|part| part.to_ascii_lowercase()).collect(),
                );
            }
        }
        id.normalize();
        let mut tag = Self {
            id,
            unicode,
            extensions,
            private_use,
        };
        tag.normalize();
        Ok(tag)
    }

    fn normalize(&mut self) {
        self.id.normalize();
        if let Some(unicode) = &mut self.unicode {
            for attribute in &mut unicode.attributes {
                attribute.make_ascii_lowercase();
            }
            unicode.attributes.sort();
            let old = std::mem::take(&mut unicode.keywords);
            for (mut key, mut value) in old {
                key.make_ascii_lowercase();
                value.make_ascii_lowercase();
                if value == "true" {
                    value.clear();
                }
                unicode.keywords.insert(key, value);
            }
        }
    }

    fn without_unicode(&self) -> Self {
        let mut result = self.clone();
        result.unicode = None;
        result
    }

    fn render(&self) -> String {
        let mut out = self.id.render();
        let mut all_extensions: Vec<(char, Vec<String>)> = self
            .extensions
            .iter()
            .map(|(key, value)| (*key, value.clone()))
            .collect();
        if let Some(unicode) = &self.unicode {
            let mut body = unicode.attributes.clone();
            for (key, value) in &unicode.keywords {
                body.push(key.clone());
                if !value.is_empty() {
                    body.extend(value.split('-').map(str::to_owned));
                }
            }
            if !body.is_empty() {
                all_extensions.push(('u', body));
            }
        }
        all_extensions.sort_by_key(|(singleton, _)| *singleton);
        for (singleton, body) in all_extensions {
            out.push('-');
            out.push(singleton);
            for subtag in body {
                out.push('-');
                out.push_str(&subtag);
            }
        }
        if !self.private_use.is_empty() {
            out.push_str("-x");
            for subtag in &self.private_use {
                out.push('-');
                out.push_str(subtag);
            }
        }
        out
    }
}

impl fmt::Display for LanguageTag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.render())
    }
}

fn parse_language_id(
    parts: &[&str],
    start: usize,
    original: &str,
) -> Result<(LanguageId, usize), LocaleError> {
    let Some(language) = parts.get(start) else {
        return Err(LocaleError::InvalidLanguageTag(original.to_owned()));
    };
    if !is_language(language) {
        return Err(LocaleError::InvalidLanguageTag(original.to_owned()));
    }
    let mut index = start + 1;
    let script = parts
        .get(index)
        .filter(|value| is_script(value))
        .map(|value| {
            index += 1;
            titlecase(value)
        });
    let region = parts
        .get(index)
        .filter(|value| is_region(value))
        .map(|value| {
            index += 1;
            value.to_ascii_uppercase()
        });
    let mut variants = Vec::new();
    let mut seen = BTreeSet::new();
    while let Some(part) = parts.get(index) {
        if !is_variant(part) {
            break;
        }
        let variant = part.to_ascii_lowercase();
        if !seen.insert(variant.clone()) {
            return Err(LocaleError::DuplicateSubtag(variant));
        }
        variants.push(variant);
        index += 1;
    }
    Ok((
        LanguageId {
            language: language.to_ascii_lowercase(),
            script,
            region,
            variants,
        },
        index,
    ))
}

fn parse_unicode_extension(
    parts: &[&str],
    original: &str,
) -> Result<UnicodeExtension, LocaleError> {
    let mut extension = UnicodeExtension::default();
    let mut seen_attributes = BTreeSet::new();
    let mut index = 0;
    while let Some(part) = parts.get(index) {
        if !(3..=8).contains(&part.len()) || !is_alnum(part) {
            break;
        }
        let attribute = part.to_ascii_lowercase();
        if !seen_attributes.insert(attribute.clone()) {
            return Err(LocaleError::DuplicateSubtag(attribute));
        }
        extension.attributes.push(attribute);
        index += 1;
    }
    while index < parts.len() {
        let key = parts[index].to_ascii_lowercase();
        if !is_unicode_key(&key) {
            return Err(LocaleError::InvalidLanguageTag(original.to_owned()));
        }
        if extension.keywords.contains_key(&key) {
            return Err(LocaleError::DuplicateSubtag(key));
        }
        index += 1;
        let start = index;
        while let Some(part) = parts.get(index) {
            if !(3..=8).contains(&part.len()) || !is_alnum(part) {
                break;
            }
            index += 1;
        }
        extension.keywords.insert(
            key,
            parts[start..index]
                .iter()
                .map(|part| part.to_ascii_lowercase())
                .collect::<Vec<_>>()
                .join("-"),
        );
    }
    extension.attributes.sort();
    if extension.attributes.is_empty() && extension.keywords.is_empty() {
        return Err(LocaleError::InvalidLanguageTag(original.to_owned()));
    }
    Ok(extension)
}

fn parse_transformed_extension(parts: &[&str], original: &str) -> Result<Vec<String>, LocaleError> {
    let mut index = 0;
    let mut language = None;
    if parts.first().is_some_and(|part| is_language(part)) {
        let (id, next) = parse_language_id(parts, 0, original)?;
        language = Some(id);
        index = next;
    }
    let mut fields = BTreeMap::new();
    while index < parts.len() {
        let key = parts[index].to_ascii_lowercase();
        if key.len() != 2
            || !key.as_bytes()[0].is_ascii_alphabetic()
            || !key.as_bytes()[1].is_ascii_digit()
        {
            return Err(LocaleError::InvalidLanguageTag(original.to_owned()));
        }
        if fields.contains_key(&key) {
            return Err(LocaleError::DuplicateSubtag(key));
        }
        index += 1;
        let start = index;
        while let Some(value) = parts.get(index) {
            if !(3..=8).contains(&value.len()) || !is_alnum(value) {
                break;
            }
            index += 1;
        }
        if start == index {
            return Err(LocaleError::InvalidLanguageTag(original.to_owned()));
        }
        fields.insert(
            key,
            parts[start..index]
                .iter()
                .map(|part| part.to_ascii_lowercase())
                .collect::<Vec<_>>(),
        );
    }
    if language.is_none() && fields.is_empty() {
        return Err(LocaleError::InvalidLanguageTag(original.to_owned()));
    }
    let mut body = Vec::new();
    if let Some(mut id) = language {
        id.normalize();
        body.extend(id.render().split('-').map(str::to_owned));
    }
    for (key, values) in fields {
        body.push(key);
        body.extend(values);
    }
    Ok(body)
}

fn is_language(value: &str) -> bool {
    ((2..=3).contains(&value.len()) || (5..=8).contains(&value.len())) && is_alpha(value)
}
fn is_script(value: &&str) -> bool {
    value.len() == 4 && is_alpha(value)
}
fn is_region(value: &&str) -> bool {
    (value.len() == 2 && is_alpha(value))
        || (value.len() == 3 && value.bytes().all(|byte| byte.is_ascii_digit()))
}
fn is_variant(value: &str) -> bool {
    ((5..=8).contains(&value.len()) && is_alnum(value))
        || (value.len() == 4 && value.as_bytes()[0].is_ascii_digit() && is_alnum(value))
}
fn is_unicode_key(value: &str) -> bool {
    value.len() == 2
        && value.as_bytes()[0].is_ascii_alphanumeric()
        && value.as_bytes()[1].is_ascii_alphabetic()
}
fn is_alpha(value: &str) -> bool {
    value.bytes().all(|byte| byte.is_ascii_alphabetic())
}
fn is_alnum(value: &str) -> bool {
    value.bytes().all(|byte| byte.is_ascii_alphanumeric())
}
fn titlecase(value: &str) -> String {
    let mut result = value.to_ascii_lowercase();
    result[0..1].make_ascii_uppercase();
    result
}

/// Supplies all implementation- and locale-dependent data.
///
/// An ICU4X adapter should source aliases from locale canonicalizer data,
/// likely subtags from the locale expander, and service-specific keyword data
/// from the formatter provider. Implementations must not consult ambient host
/// state from these methods.
pub trait LocaleDataProvider {
    /// Canonical, deduplicated locales supported by the active Intl service.
    fn available_locales(&self) -> &[String];
    /// Preferred replacement for a language subtag or language identifier.
    fn language_alias(&self, _language: &str) -> Option<&str> {
        None
    }
    /// Preferred replacement for a script subtag.
    fn script_alias(&self, _script: &str) -> Option<&str> {
        None
    }
    /// Preferred replacement for a region subtag.
    fn region_alias(&self, _region: &str) -> Option<&str> {
        None
    }
    /// Preferred replacement for a variant subtag.
    fn variant_alias(&self, _variant: &str) -> Option<&str> {
        None
    }
    /// Preferred replacement for a Unicode extension key.
    fn unicode_key_alias(&self, _key: &str) -> Option<&str> {
        None
    }
    /// Preferred replacement for a Unicode extension type.
    fn unicode_type_alias(&self, _key: &str, _value: &str) -> Option<&str> {
        None
    }
    /// Supported values for a relevant extension key. The first value is the default.
    fn key_values(&self, _data_locale: &str, _key: &str) -> &[String] {
        &[]
    }
    /// Maximizes a language identifier with provider likely-subtags data.
    fn add_likely_subtags(&self, _locale: &LanguageId) -> Option<LanguageId> {
        None
    }
    /// Canonical last-resort locale, which must be in [`Self::available_locales`].
    fn fallback_locale(&self) -> Option<&str> {
        None
    }
}

/// Supplies a host-preferred default locale without granting environment access
/// to the locale implementation.
pub trait HostLocaleHook {
    /// Returns the host's preferred locale IDs in priority order.
    fn preferred_locales(&self) -> Vec<String>;
}

/// Caller-populated, deterministic locale data useful for embedding and tests.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MapLocaleData {
    available: Vec<String>,
    language_aliases: BTreeMap<String, String>,
    script_aliases: BTreeMap<String, String>,
    region_aliases: BTreeMap<String, String>,
    variant_aliases: BTreeMap<String, String>,
    key_aliases: BTreeMap<String, String>,
    type_aliases: BTreeMap<(String, String), String>,
    key_values: BTreeMap<(String, String), Vec<String>>,
    likely_subtags: BTreeMap<String, LanguageId>,
    fallback: Option<String>,
}

impl MapLocaleData {
    /// Creates an empty provider. It intentionally contains no CLDR guesses.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
    /// Replaces the supported locale set, sorting and deduplicating it.
    #[must_use]
    pub fn with_available(mut self, mut locales: Vec<String>) -> Self {
        locales.sort();
        locales.dedup();
        self.available = locales;
        self
    }
    /// Adds a language or compound-language alias.
    #[must_use]
    pub fn with_language_alias(mut self, from: &str, to: &str) -> Self {
        self.language_aliases
            .insert(from.to_ascii_lowercase(), to.to_owned());
        self
    }
    /// Adds a script alias.
    #[must_use]
    pub fn with_script_alias(mut self, from: &str, to: &str) -> Self {
        self.script_aliases.insert(titlecase(from), to.to_owned());
        self
    }
    /// Adds a region alias.
    #[must_use]
    pub fn with_region_alias(mut self, from: &str, to: &str) -> Self {
        self.region_aliases
            .insert(from.to_ascii_uppercase(), to.to_owned());
        self
    }
    /// Adds a variant alias.
    #[must_use]
    pub fn with_variant_alias(mut self, from: &str, to: &str) -> Self {
        self.variant_aliases
            .insert(from.to_ascii_lowercase(), to.to_owned());
        self
    }
    /// Adds a Unicode extension key alias.
    #[must_use]
    pub fn with_key_alias(mut self, from: &str, to: &str) -> Self {
        self.key_aliases
            .insert(from.to_ascii_lowercase(), to.to_ascii_lowercase());
        self
    }
    /// Adds a Unicode extension type alias.
    #[must_use]
    pub fn with_type_alias(mut self, key: &str, from: &str, to: &str) -> Self {
        self.type_aliases.insert(
            (key.to_ascii_lowercase(), from.to_ascii_lowercase()),
            to.to_ascii_lowercase(),
        );
        self
    }
    /// Defines supported key values; the first value is the locale-data default.
    #[must_use]
    pub fn with_key_values(mut self, locale: &str, key: &str, values: Vec<String>) -> Self {
        self.key_values
            .insert((locale.to_owned(), key.to_ascii_lowercase()), values);
        self
    }
    /// Adds one likely-subtags expansion.
    ///
    /// # Errors
    /// Returns an error if either identifier is malformed or contains extensions.
    pub fn with_likely_subtag(mut self, from: &str, to: &str) -> Result<Self, LocaleError> {
        let from_tag = LanguageTag::parse(from)?;
        let to_tag = LanguageTag::parse(to)?;
        if from_tag.unicode.is_some() || to_tag.unicode.is_some() {
            return Err(LocaleError::InvalidLanguageTag(format!("{from} -> {to}")));
        }
        self.likely_subtags.insert(from_tag.id.render(), to_tag.id);
        Ok(self)
    }
    /// Defines the provider's canonical last-resort locale.
    #[must_use]
    pub fn with_fallback(mut self, locale: &str) -> Self {
        self.fallback = Some(locale.to_owned());
        self
    }
}

impl LocaleDataProvider for MapLocaleData {
    fn available_locales(&self) -> &[String] {
        &self.available
    }
    fn language_alias(&self, value: &str) -> Option<&str> {
        self.language_aliases.get(value).map(String::as_str)
    }
    fn script_alias(&self, value: &str) -> Option<&str> {
        self.script_aliases.get(value).map(String::as_str)
    }
    fn region_alias(&self, value: &str) -> Option<&str> {
        self.region_aliases.get(value).map(String::as_str)
    }
    fn variant_alias(&self, value: &str) -> Option<&str> {
        self.variant_aliases.get(value).map(String::as_str)
    }
    fn unicode_key_alias(&self, value: &str) -> Option<&str> {
        self.key_aliases.get(value).map(String::as_str)
    }
    fn unicode_type_alias(&self, key: &str, value: &str) -> Option<&str> {
        self.type_aliases
            .get(&(key.to_owned(), value.to_owned()))
            .map(String::as_str)
    }
    fn key_values(&self, locale: &str, key: &str) -> &[String] {
        self.key_values
            .get(&(locale.to_owned(), key.to_owned()))
            .map_or(&[], Vec::as_slice)
    }
    fn add_likely_subtags(&self, locale: &LanguageId) -> Option<LanguageId> {
        let candidates = [
            locale.render(),
            LanguageId {
                language: locale.language.clone(),
                script: None,
                region: locale.region.clone(),
                variants: Vec::new(),
            }
            .render(),
            LanguageId {
                language: locale.language.clone(),
                script: locale.script.clone(),
                region: None,
                variants: Vec::new(),
            }
            .render(),
            locale.language.clone(),
        ];
        for candidate in candidates {
            if let Some(expanded) = self.likely_subtags.get(&candidate) {
                let mut result = expanded.clone();
                if locale.script.is_some() {
                    result.script.clone_from(&locale.script);
                }
                if locale.region.is_some() {
                    result.region.clone_from(&locale.region);
                }
                result.variants.clone_from(&locale.variants);
                return Some(result);
            }
        }
        None
    }
    fn fallback_locale(&self) -> Option<&str> {
        self.fallback.as_deref()
    }
}

/// Canonicalizes a Unicode locale identifier using provider alias data.
///
/// # Errors
/// Returns an error for an invalid identifier or invalid provider alias.
pub fn canonicalize_unicode_locale_id(
    locale: &str,
    provider: &dyn LocaleDataProvider,
) -> Result<String, LocaleError> {
    let mut tag = LanguageTag::parse(locale)?;
    if let Some(alias) = provider.language_alias(&tag.id.language) {
        let replacement = LanguageTag::parse(alias)?;
        tag.id.language = replacement.id.language;
        if tag.id.script.is_none() {
            tag.id.script = replacement.id.script;
        }
        if tag.id.region.is_none() {
            tag.id.region = replacement.id.region;
        }
        tag.id.variants.extend(replacement.id.variants);
    }
    if let Some(script) = tag.id.script.clone()
        && let Some(alias) = provider.script_alias(&script)
    {
        tag.id.script = Some(titlecase(alias));
    }
    if let Some(region) = tag.id.region.clone()
        && let Some(alias) = provider.region_alias(&region)
    {
        tag.id.region = alias
            .split_ascii_whitespace()
            .next()
            .map(str::to_ascii_uppercase);
    }
    for variant in &mut tag.id.variants {
        if let Some(alias) = provider.variant_alias(variant) {
            *variant = alias.to_ascii_lowercase();
        }
    }
    if let Some(extension) = &mut tag.unicode {
        let old = std::mem::take(&mut extension.keywords);
        for (key, value) in old {
            let canonical_key = provider
                .unicode_key_alias(&key)
                .unwrap_or(&key)
                .to_ascii_lowercase();
            let canonical_value = provider
                .unicode_type_alias(&canonical_key, &value)
                .unwrap_or(&value)
                .to_ascii_lowercase();
            if extension
                .keywords
                .insert(canonical_key.clone(), canonical_value)
                .is_some()
            {
                return Err(LocaleError::DuplicateSubtag(canonical_key));
            }
        }
    }
    tag.normalize();
    LanguageTag::parse(&tag.render()).map(|validated| validated.render())
}

/// Canonicalizes and order-preservingly deduplicates a requested locale list.
///
/// # Errors
/// Returns an error if any requested locale is invalid.
pub fn canonicalize_locale_list(
    locales: &[String],
    provider: &dyn LocaleDataProvider,
) -> Result<Vec<String>, LocaleError> {
    let mut seen = BTreeSet::new();
    let mut result = Vec::new();
    for locale in locales {
        let canonical = canonicalize_unicode_locale_id(locale, provider)?;
        if seen.insert(canonical.clone()) {
            result.push(canonical);
        }
    }
    Ok(result)
}

/// Locale matching strategy selected by `localeMatcher`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LocaleMatcher {
    /// RFC 4647 lookup matching.
    Lookup,
    /// Provider-driven best-fit matching.
    BestFit,
}

/// The locale and requested Unicode extension selected by a matcher.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MatchResult {
    /// Canonical provider locale.
    pub locale: String,
    /// Requested Unicode extension, removed from the matched base name.
    pub extension: Option<UnicodeExtension>,
}

fn best_available_locale(available: &[String], candidate: &str) -> Option<String> {
    let mut candidate = candidate.to_owned();
    loop {
        if available.binary_search(&candidate).is_ok()
            || available.iter().any(|item| item == &candidate)
        {
            return Some(candidate);
        }
        let position = candidate.rfind('-')?;
        let truncate = if position >= 2 && candidate.as_bytes()[position - 2] == b'-' {
            position - 2
        } else {
            position
        };
        candidate.truncate(truncate);
    }
}

/// Applies ECMA-402 `LookupMatcher`.
///
/// # Errors
/// Returns an error if a request is invalid or the provider has no fallback.
pub fn lookup_matcher(
    requested: &[String],
    provider: &dyn LocaleDataProvider,
) -> Result<MatchResult, LocaleError> {
    for requested_locale in canonicalize_locale_list(requested, provider)? {
        let tag = LanguageTag::parse(&requested_locale)?;
        if let Some(locale) = best_available_locale(
            provider.available_locales(),
            &tag.without_unicode().render(),
        ) {
            return Ok(MatchResult {
                locale,
                extension: tag.unicode,
            });
        }
    }
    fallback_match(provider)
}

fn fallback_match(provider: &dyn LocaleDataProvider) -> Result<MatchResult, LocaleError> {
    if let Some(locale) = provider.fallback_locale() {
        let locale = canonicalize_unicode_locale_id(locale, provider)?;
        if provider
            .available_locales()
            .iter()
            .any(|available| available == &locale)
        {
            return Ok(MatchResult {
                locale,
                extension: None,
            });
        }
    }
    provider
        .available_locales()
        .first()
        .cloned()
        .map(|locale| MatchResult {
            locale,
            extension: None,
        })
        .ok_or(LocaleError::NoAvailableLocale)
}

/// Applies provider-driven best-fit matching. If likely-subtags data is absent,
/// this operation is exactly [`lookup_matcher`].
///
/// # Errors
/// Returns an error if a request is invalid or the provider has no fallback.
pub fn best_fit_matcher(
    requested: &[String],
    provider: &dyn LocaleDataProvider,
) -> Result<MatchResult, LocaleError> {
    let canonical = canonicalize_locale_list(requested, provider)?;
    for requested_locale in &canonical {
        if let Some(matched) = best_fit_available(requested_locale, provider)? {
            return Ok(matched);
        }
    }
    fallback_match(provider)
}

fn best_fit_available(
    requested_locale: &str,
    provider: &dyn LocaleDataProvider,
) -> Result<Option<MatchResult>, LocaleError> {
    let requested_tag = LanguageTag::parse(requested_locale)?;
    if let Some(max_requested) = provider.add_likely_subtags(&requested_tag.id) {
        let mut best: Option<(u8, String)> = None;
        for available in provider.available_locales() {
            let available_tag = LanguageTag::parse(available)?;
            let Some(max_available) = provider.add_likely_subtags(&available_tag.id) else {
                continue;
            };
            if max_requested.language != max_available.language {
                continue;
            }
            let score = 4
                + u8::from(max_requested.script == max_available.script) * 2
                + u8::from(max_requested.region == max_available.region);
            if best.as_ref().is_none_or(|(best_score, best_name)| {
                score > *best_score || (score == *best_score && available < best_name)
            }) {
                best = Some((score, available.clone()));
            }
        }
        if let Some((_, locale)) = best {
            return Ok(Some(MatchResult {
                locale,
                extension: requested_tag.unicode,
            }));
        }
    }
    Ok(best_available_locale(
        provider.available_locales(),
        &requested_tag.without_unicode().render(),
    )
    .map(|locale| MatchResult {
        locale,
        extension: requested_tag.unicode,
    }))
}

/// Returns the requested locales supported by a service, preserving requested
/// spelling after canonicalization and preserving list order.
///
/// # Errors
/// Returns an error if any requested locale is invalid.
pub fn supported_locales(
    requested: &[String],
    matcher: LocaleMatcher,
    provider: &dyn LocaleDataProvider,
) -> Result<Vec<String>, LocaleError> {
    let canonical = canonicalize_locale_list(requested, provider)?;
    let mut result = Vec::new();
    for locale in canonical {
        let matched = match matcher {
            LocaleMatcher::Lookup => {
                let tag = LanguageTag::parse(&locale)?;
                best_available_locale(
                    provider.available_locales(),
                    &tag.without_unicode().render(),
                )
                .is_some()
            }
            LocaleMatcher::BestFit => best_fit_available(&locale, provider)?.is_some(),
        };
        if matched {
            result.push(locale);
        }
    }
    Ok(result)
}

/// Output of ECMA-402 `ResolveLocale`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedLocale {
    /// Resolved locale including supported requested Unicode keywords.
    pub locale: String,
    /// Provider locale used to retrieve service data.
    pub data_locale: String,
    /// Resolved value for every relevant extension key.
    pub values: BTreeMap<String, String>,
}

/// Applies ECMA-402 `ResolveLocale` option precedence: locale-data default,
/// requested Unicode keyword, then explicit options.
///
/// # Errors
/// Returns an error for malformed requests or missing available locales.
pub fn resolve_locale(
    requested: &[String],
    options: &BTreeMap<String, String>,
    relevant_extension_keys: &[String],
    matcher: LocaleMatcher,
    provider: &dyn LocaleDataProvider,
) -> Result<ResolvedLocale, LocaleError> {
    let matched = match matcher {
        LocaleMatcher::Lookup => lookup_matcher(requested, provider)?,
        LocaleMatcher::BestFit => best_fit_matcher(requested, provider)?,
    };
    let mut result_tag = LanguageTag::parse(&matched.locale)?;
    let mut supported_keywords = BTreeMap::new();
    let mut values = BTreeMap::new();
    for key in relevant_extension_keys {
        let key = key.to_ascii_lowercase();
        let supported = provider.key_values(&matched.locale, &key);
        let mut value = supported.first().cloned().unwrap_or_default();
        let mut requested_supported = false;
        if let Some(requested) = matched
            .extension
            .as_ref()
            .and_then(|extension| extension.keywords.get(&key))
        {
            let requested = if requested.is_empty() {
                "true"
            } else {
                requested
            };
            if supported
                .iter()
                .any(|supported_value| supported_value == requested)
            {
                value = requested.to_owned();
                requested_supported = true;
            }
        }
        if let Some(option) = options.get(&key)
            && supported
                .iter()
                .any(|supported_value| supported_value == option)
        {
            if option != &value {
                requested_supported = false;
            }
            value.clone_from(option);
        }
        if requested_supported {
            supported_keywords.insert(
                key.clone(),
                if value == "true" {
                    String::new()
                } else {
                    value.clone()
                },
            );
        }
        values.insert(key, value);
    }
    if !supported_keywords.is_empty() {
        result_tag.unicode = Some(UnicodeExtension {
            attributes: Vec::new(),
            keywords: supported_keywords,
        });
    }
    Ok(ResolvedLocale {
        locale: result_tag.render(),
        data_locale: matched.locale,
        values,
    })
}

/// Resolves the injected host preference against provider locales, then uses
/// the provider fallback. No environment or OS API is read.
///
/// # Errors
/// Returns an error when neither host preferences nor provider fallback resolve.
pub fn default_locale(
    hook: &dyn HostLocaleHook,
    provider: &dyn LocaleDataProvider,
) -> Result<String, LocaleError> {
    let preferred = hook.preferred_locales();
    if !preferred.is_empty() {
        for locale in canonicalize_locale_list(&preferred, provider)? {
            let tag = LanguageTag::parse(&locale)?;
            if let Some(found) = best_available_locale(
                provider.available_locales(),
                &tag.without_unicode().render(),
            ) {
                return Ok(found);
            }
        }
    }
    fallback_match(provider).map(|matched| matched.locale)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn provider() -> MapLocaleData {
        MapLocaleData::new()
            .with_available(vec![
                "en".into(),
                "en-GB".into(),
                "he-IL".into(),
                "sr-Cyrl".into(),
                "sr-Latn".into(),
                "zh-Hans".into(),
                "zh-Hant".into(),
            ])
            .with_language_alias("iw", "he")
            .with_language_alias("sh", "sr-Latn")
            .with_region_alias("BU", "MM")
            .with_variant_alias("heploc", "alalc97")
            .with_type_alias("ca", "islamicc", "islamic-civil")
            .with_key_values("en", "ca", vec!["gregory".into(), "buddhist".into()])
            .with_key_values("en", "kn", vec!["false".into(), "true".into()])
            .with_fallback("en")
    }

    #[test]
    fn canonical_aliases_come_only_from_provider() {
        assert_eq!(
            canonicalize_unicode_locale_id("IW-il-u-ca-islamicc", &provider()),
            Ok("he-IL-u-ca-islamic-civil".into())
        );
        assert_eq!(
            canonicalize_unicode_locale_id("iw-IL", &MapLocaleData::new()),
            Ok("iw-IL".into())
        );
        assert_eq!(
            canonicalize_unicode_locale_id("sh-Cyrl", &provider()),
            Ok("sr-Cyrl".into())
        );
    }

    #[test]
    fn structural_ordering_and_true_are_canonical() {
        let value = canonicalize_unicode_locale_id(
            "EN-latn-us-1996-u-FOO-kn-true-ca-buddhist-a-ZZZ",
            &MapLocaleData::new(),
        );
        assert_eq!(
            value,
            Ok("en-Latn-US-1996-a-zzz-u-foo-ca-buddhist-kn".into())
        );
        let once = value.unwrap_or_default();
        assert_eq!(
            canonicalize_unicode_locale_id(&once, &MapLocaleData::new()),
            Ok(once)
        );
    }

    #[test]
    fn invalid_tags_are_rejected() {
        for invalid in [
            "",
            "e",
            "en--US",
            "en-US-",
            "en-u",
            "en-x",
            "en-abcdefghi",
            "i-klingon",
            "en-GB-oed",
            "en-t-a0",
        ] {
            assert!(LanguageTag::parse(invalid).is_err(), "accepted {invalid}");
        }
    }

    #[test]
    fn duplicate_variants_extensions_attributes_and_keys_are_rejected() {
        for invalid in [
            "de-1996-1996",
            "en-a-foo-a-bar",
            "en-u-foo-foo",
            "en-u-ca-gregory-ca-buddhist",
            "en-t-es-1996-1996-h0-hybrid",
            "en-t-h0-hybrid-h0-ascii",
        ] {
            assert!(
                matches!(
                    LanguageTag::parse(invalid),
                    Err(LocaleError::DuplicateSubtag(_))
                ),
                "wrong result for {invalid}"
            );
        }
    }

    #[test]
    fn lookup_truncates_and_drops_singleton_sequences() {
        let data = MapLocaleData::new()
            .with_available(vec!["de".into()])
            .with_fallback("de");
        assert_eq!(
            lookup_matcher(&["de-DE-x-goethe".into()], &data).map(|result| result.locale),
            Ok("de".into())
        );
        assert_eq!(
            lookup_matcher(&["de-a-foo".into()], &data).map(|result| result.locale),
            Ok("de".into())
        );
    }

    #[test]
    fn resolve_locale_honours_extension_then_option_precedence() {
        let data = provider();
        let requested = vec!["en-u-ca-buddhist-kn".into()];
        let keys = vec!["ca".into(), "kn".into()];
        let extension = resolve_locale(
            &requested,
            &BTreeMap::new(),
            &keys,
            LocaleMatcher::Lookup,
            &data,
        )
        .unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(extension.locale, "en-u-ca-buddhist-kn");
        assert_eq!(
            extension.values.get("ca").map(String::as_str),
            Some("buddhist")
        );
        assert_eq!(extension.values.get("kn").map(String::as_str), Some("true"));
        let options = BTreeMap::from([("ca".into(), "gregory".into())]);
        let overridden = resolve_locale(&requested, &options, &keys, LocaleMatcher::Lookup, &data)
            .unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(overridden.locale, "en-u-kn");
        assert_eq!(
            overridden.values.get("ca").map(String::as_str),
            Some("gregory")
        );
    }

    struct Hook(Vec<String>);
    impl HostLocaleHook for Hook {
        fn preferred_locales(&self) -> Vec<String> {
            self.0.clone()
        }
    }

    #[test]
    fn default_locale_uses_hook_then_provider_fallback() {
        let data = provider();
        assert_eq!(
            default_locale(&Hook(vec!["en-GB-u-ca-buddhist".into()]), &data),
            Ok("en-GB".into())
        );
        assert_eq!(default_locale(&Hook(Vec::new()), &data), Ok("en".into()));
    }

    #[test]
    fn supported_locales_are_canonical_ordered_and_deterministic() {
        let requested = vec!["EN-gb-u-ca-gregory".into(), "fr-FR".into(), "en".into()];
        let first = supported_locales(&requested, LocaleMatcher::Lookup, &provider());
        assert_eq!(first, Ok(vec!["en-GB-u-ca-gregory".into(), "en".into()]));
        assert_eq!(
            first,
            supported_locales(&requested, LocaleMatcher::Lookup, &provider())
        );
        assert_eq!(
            supported_locales(&requested, LocaleMatcher::BestFit, &provider()),
            Ok(vec!["en-GB-u-ca-gregory".into(), "en".into()]),
        );
    }

    #[test]
    fn best_fit_uses_provider_likely_subtags_and_otherwise_lookup() {
        let data = MapLocaleData::new()
            .with_available(vec!["zh-Hans".into(), "zh-Hant".into()])
            .with_fallback("zh-Hans")
            .with_likely_subtag("zh-TW", "zh-Hant-TW")
            .unwrap_or_else(|error| panic!("{error}"))
            .with_likely_subtag("zh-Hant", "zh-Hant-TW")
            .unwrap_or_else(|error| panic!("{error}"))
            .with_likely_subtag("zh-Hans", "zh-Hans-CN")
            .unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(
            best_fit_matcher(&["zh-TW".into()], &data).map(|result| result.locale),
            Ok("zh-Hant".into())
        );
        let no_likely = MapLocaleData::new()
            .with_available(vec!["en".into()])
            .with_fallback("en");
        assert_eq!(
            best_fit_matcher(&["en-US".into()], &no_likely),
            lookup_matcher(&["en-US".into()], &no_likely)
        );
    }
}
