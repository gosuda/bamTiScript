//! The locale data this runtime ships.
//!
//! There is no CLDR here. Identifier aliases are complete (see
//! [`super::locale_aliases`]); everything else is a small table of well-known
//! facts about languages and regions, and only `en` and `en-US` are available
//! locales. A locale outside that set is reported as unsupported through the
//! ordinary `supportedLocalesOf` and fallback paths.

use std::cmp::Ordering;
use std::sync::LazyLock;

use super::canonical_locales::SupportedValuesInventory;
use super::collation;
use super::collator::{
    CollatorCompareRequest, CollatorDataProvider, CollatorLocaleDefaults, CollatorSensitivity,
    CollatorUsage,
};
use super::locale_aliases::{
    COMPLEX_REGION_ALIASES, LANGUAGE_ALIASES, REGION_ALIASES, TAG_ALIASES, TRANSFORM_TYPE_ALIASES,
    UNICODE_TYPE_ALIASES, VARIANT_ALIASES, VariantAlias,
};
use super::locale_negotiation::{LanguageId, LanguageTag, LocaleDataProvider};
use super::number_format::SANCTIONED_UNITS;

/// The locale used when a request matches nothing available.
pub const DEFAULT_LOCALE: &str = "en-US";

/// `language[-Script][-REGION]` to the full identifier it most likely means.
const LIKELY_SUBTAGS: &[(&str, &str)] = &[
    ("aa", "aa-Latn-ET"),
    ("aae", "aae-Latn-IT"),
    ("af", "af-Latn-ZA"),
    ("am", "am-Ethi-ET"),
    ("ar", "ar-Arab-EG"),
    ("as", "as-Beng-IN"),
    ("ast", "ast-Latn-ES"),
    ("az", "az-Latn-AZ"),
    ("az-Arab", "az-Arab-IR"),
    ("az-IQ", "az-Arab-IQ"),
    ("az-IR", "az-Arab-IR"),
    ("az-RU", "az-Cyrl-RU"),
    ("be", "be-Cyrl-BY"),
    ("bg", "bg-Cyrl-BG"),
    ("bn", "bn-Beng-BD"),
    ("bo", "bo-Tibt-CN"),
    ("br", "br-Latn-FR"),
    ("bs", "bs-Latn-BA"),
    ("ca", "ca-Latn-ES"),
    ("ceb", "ceb-Latn-PH"),
    ("cs", "cs-Latn-CZ"),
    ("cy", "cy-Latn-GB"),
    ("da", "da-Latn-DK"),
    ("de", "de-Latn-DE"),
    ("dv", "dv-Thaa-MV"),
    ("el", "el-Grek-GR"),
    ("en", "en-Latn-US"),
    ("en-Shaw", "en-Shaw-GB"),
    ("eo", "eo-Latn-001"),
    ("es", "es-Latn-ES"),
    ("et", "et-Latn-EE"),
    ("eu", "eu-Latn-ES"),
    ("fa", "fa-Arab-IR"),
    ("fi", "fi-Latn-FI"),
    ("fil", "fil-Latn-PH"),
    ("fo", "fo-Latn-FO"),
    ("fr", "fr-Latn-FR"),
    ("fy", "fy-Latn-NL"),
    ("ga", "ga-Latn-IE"),
    ("gd", "gd-Latn-GB"),
    ("gl", "gl-Latn-ES"),
    ("gsw", "gsw-Latn-CH"),
    ("gu", "gu-Gujr-IN"),
    ("ha", "ha-Latn-NG"),
    ("hak", "hak-Hans-CN"),
    ("he", "he-Hebr-IL"),
    ("hi", "hi-Deva-IN"),
    ("hr", "hr-Latn-HR"),
    ("hsn", "hsn-Hans-CN"),
    ("hu", "hu-Latn-HU"),
    ("hy", "hy-Armn-AM"),
    ("hyw", "hyw-Armn-AM"),
    ("id", "id-Latn-ID"),
    ("ig", "ig-Latn-NG"),
    ("is", "is-Latn-IS"),
    ("it", "it-Latn-IT"),
    ("ja", "ja-Jpan-JP"),
    ("jbo", "jbo-Latn-001"),
    ("jv", "jv-Latn-ID"),
    ("ka", "ka-Geor-GE"),
    ("kk", "kk-Cyrl-KZ"),
    ("km", "km-Khmr-KH"),
    ("kn", "kn-Knda-IN"),
    ("ko", "ko-Kore-KR"),
    ("ku", "ku-Latn-TR"),
    ("ku-Arab", "ku-Arab-IQ"),
    ("ky", "ky-Cyrl-KG"),
    ("la", "la-Latn-VA"),
    ("lb", "lb-Latn-LU"),
    ("lo", "lo-Laoo-LA"),
    ("lt", "lt-Latn-LT"),
    ("lv", "lv-Latn-LV"),
    ("mg", "mg-Latn-MG"),
    ("mi", "mi-Latn-NZ"),
    ("mk", "mk-Cyrl-MK"),
    ("ml", "ml-Mlym-IN"),
    ("mn", "mn-Cyrl-MN"),
    ("mn-CN", "mn-Mong-CN"),
    ("mn-Mong", "mn-Mong-CN"),
    ("mr", "mr-Deva-IN"),
    ("ms", "ms-Latn-MY"),
    ("ms-Arab", "ms-Arab-MY"),
    ("mt", "mt-Latn-MT"),
    ("my", "my-Mymr-MM"),
    ("nan", "nan-Hans-CN"),
    ("nb", "nb-Latn-NO"),
    ("ne", "ne-Deva-NP"),
    ("nl", "nl-Latn-NL"),
    ("nn", "nn-Latn-NO"),
    ("no", "no-Latn-NO"),
    ("nv", "nv-Latn-US"),
    ("or", "or-Orya-IN"),
    ("pa", "pa-Guru-IN"),
    ("pa-Arab", "pa-Arab-PK"),
    ("pa-PK", "pa-Arab-PK"),
    ("pap", "pap-Latn-CW"),
    ("pl", "pl-Latn-PL"),
    ("ps", "ps-Arab-AF"),
    ("pt", "pt-Latn-BR"),
    ("rm", "rm-Latn-CH"),
    ("ro", "ro-Latn-RO"),
    ("ru", "ru-Cyrl-RU"),
    ("rw", "rw-Latn-RW"),
    ("sa", "sa-Deva-IN"),
    ("sco", "sco-Latn-GB"),
    ("sd", "sd-Arab-PK"),
    ("sd-Deva", "sd-Deva-IN"),
    ("sd-IN", "sd-Deva-IN"),
    ("si", "si-Sinh-LK"),
    ("sk", "sk-Latn-SK"),
    ("sl", "sl-Latn-SI"),
    ("so", "so-Latn-SO"),
    ("sq", "sq-Latn-AL"),
    ("sr", "sr-Cyrl-RS"),
    ("sr-Latn", "sr-Latn-RS"),
    ("sr-ME", "sr-Latn-ME"),
    ("sr-RO", "sr-Latn-RO"),
    ("sr-TR", "sr-Latn-TR"),
    ("sv", "sv-Latn-SE"),
    ("sw", "sw-Latn-TZ"),
    ("ta", "ta-Taml-IN"),
    ("te", "te-Telu-IN"),
    ("tg", "tg-Cyrl-TJ"),
    ("th", "th-Thai-TH"),
    ("ti", "ti-Ethi-ET"),
    ("tk", "tk-Latn-TM"),
    ("tl", "tl-Latn-PH"),
    ("tr", "tr-Latn-TR"),
    ("tt", "tt-Cyrl-RU"),
    ("ug", "ug-Arab-CN"),
    ("uk", "uk-Cyrl-UA"),
    ("und", "en-Latn-US"),
    ("und-001", "en-Latn-001"),
    ("und-150", "en-Latn-150"),
    ("und-419", "es-Latn-419"),
    ("und-AE", "ar-Arab-AE"),
    ("und-AF", "fa-Arab-AF"),
    ("und-AM", "hy-Armn-AM"),
    ("und-AR", "es-Latn-AR"),
    ("und-AT", "de-Latn-AT"),
    ("und-AU", "en-Latn-AU"),
    ("und-AW", "nl-Latn-AW"),
    ("und-AZ", "az-Latn-AZ"),
    ("und-Arab", "ar-Arab-EG"),
    ("und-Armn", "hy-Armn-AM"),
    ("und-BD", "bn-Beng-BD"),
    ("und-BE", "nl-Latn-BE"),
    ("und-BG", "bg-Cyrl-BG"),
    ("und-BR", "pt-Latn-BR"),
    ("und-BY", "be-Cyrl-BY"),
    ("und-Beng", "bn-Beng-BD"),
    ("und-CA", "en-Latn-CA"),
    ("und-CH", "de-Latn-CH"),
    ("und-CL", "es-Latn-CL"),
    ("und-CN", "zh-Hans-CN"),
    ("und-CO", "es-Latn-CO"),
    ("und-CW", "pap-Latn-CW"),
    ("und-CZ", "cs-Latn-CZ"),
    ("und-Cyrl", "ru-Cyrl-RU"),
    ("und-Cyrl-RO", "bg-Cyrl-RO"),
    ("und-DE", "de-Latn-DE"),
    ("und-DK", "da-Latn-DK"),
    ("und-Deva", "hi-Deva-IN"),
    ("und-EG", "ar-Arab-EG"),
    ("und-ES", "es-Latn-ES"),
    ("und-ET", "am-Ethi-ET"),
    ("und-Ethi", "am-Ethi-ET"),
    ("und-FI", "fi-Latn-FI"),
    ("und-FR", "fr-Latn-FR"),
    ("und-GB", "en-Latn-GB"),
    ("und-GE", "ka-Geor-GE"),
    ("und-GR", "el-Grek-GR"),
    ("und-Geor", "ka-Geor-GE"),
    ("und-Grek", "el-Grek-GR"),
    ("und-Gujr", "gu-Gujr-IN"),
    ("und-Guru", "pa-Guru-IN"),
    ("und-HK", "zh-Hant-HK"),
    ("und-HU", "hu-Latn-HU"),
    ("und-Hans", "zh-Hans-CN"),
    ("und-Hant", "zh-Hant-TW"),
    ("und-Hebr", "he-Hebr-IL"),
    ("und-Hira", "ja-Hira-JP"),
    ("und-ID", "id-Latn-ID"),
    ("und-IE", "en-Latn-IE"),
    ("und-IL", "he-Hebr-IL"),
    ("und-IN", "hi-Deva-IN"),
    ("und-IQ", "ar-Arab-IQ"),
    ("und-IR", "fa-Arab-IR"),
    ("und-IT", "it-Latn-IT"),
    ("und-JP", "ja-Jpan-JP"),
    ("und-Jpan", "ja-Jpan-JP"),
    ("und-KE", "sw-Latn-KE"),
    ("und-KH", "km-Khmr-KH"),
    ("und-KR", "ko-Kore-KR"),
    ("und-KZ", "ru-Cyrl-KZ"),
    ("und-Kana", "ja-Kana-JP"),
    ("und-Khmr", "km-Khmr-KH"),
    ("und-Knda", "kn-Knda-IN"),
    ("und-Kore", "ko-Kore-KR"),
    ("und-LA", "lo-Laoo-LA"),
    ("und-Laoo", "lo-Laoo-LA"),
    ("und-Latn", "en-Latn-US"),
    ("und-MM", "my-Mymr-MM"),
    ("und-MN", "mn-Cyrl-MN"),
    ("und-MX", "es-Latn-MX"),
    ("und-MY", "ms-Latn-MY"),
    ("und-Mlym", "ml-Mlym-IN"),
    ("und-Mong", "mn-Mong-CN"),
    ("und-Mymr", "my-Mymr-MM"),
    ("und-NG", "en-Latn-NG"),
    ("und-NL", "nl-Latn-NL"),
    ("und-NO", "nb-Latn-NO"),
    ("und-NP", "ne-Deva-NP"),
    ("und-NZ", "en-Latn-NZ"),
    ("und-Orya", "or-Orya-IN"),
    ("und-PE", "es-Latn-PE"),
    ("und-PH", "fil-Latn-PH"),
    ("und-PK", "ur-Arab-PK"),
    ("und-PL", "pl-Latn-PL"),
    ("und-PT", "pt-Latn-PT"),
    ("und-RO", "ro-Latn-RO"),
    ("und-RS", "sr-Cyrl-RS"),
    ("und-RU", "ru-Cyrl-RU"),
    ("und-SA", "ar-Arab-SA"),
    ("und-SE", "sv-Latn-SE"),
    ("und-SG", "en-Latn-SG"),
    ("und-SK", "sk-Latn-SK"),
    ("und-Shaw", "en-Shaw-GB"),
    ("und-Sinh", "si-Sinh-LK"),
    ("und-TH", "th-Thai-TH"),
    ("und-TR", "tr-Latn-TR"),
    ("und-TW", "zh-Hant-TW"),
    ("und-TZ", "sw-Latn-TZ"),
    ("und-Taml", "ta-Taml-IN"),
    ("und-Telu", "te-Telu-IN"),
    ("und-Thaa", "dv-Thaa-MV"),
    ("und-Thai", "th-Thai-TH"),
    ("und-Tibt", "bo-Tibt-CN"),
    ("und-UA", "uk-Cyrl-UA"),
    ("und-US", "en-Latn-US"),
    ("und-VE", "es-Latn-VE"),
    ("und-VN", "vi-Latn-VN"),
    ("und-ZA", "en-Latn-ZA"),
    ("ur", "ur-Arab-PK"),
    ("ur-IN", "ur-Arab-IN"),
    ("uz", "uz-Latn-UZ"),
    ("uz-AF", "uz-Arab-AF"),
    ("uz-Arab", "uz-Arab-AF"),
    ("uz-CN", "uz-Cyrl-CN"),
    ("vi", "vi-Latn-VN"),
    ("wuu", "wuu-Hans-CN"),
    ("xh", "xh-Latn-ZA"),
    ("yi", "yi-Hebr-UA"),
    ("yo", "yo-Latn-NG"),
    ("yue", "yue-Hant-HK"),
    ("zh", "zh-Hans-CN"),
    ("zh-AU", "zh-Hant-AU"),
    ("zh-BN", "zh-Hant-BN"),
    ("zh-GB", "zh-Hant-GB"),
    ("zh-GF", "zh-Hant-GF"),
    ("zh-HK", "zh-Hant-HK"),
    ("zh-Hant", "zh-Hant-TW"),
    ("zh-ID", "zh-Hant-ID"),
    ("zh-MO", "zh-Hant-MO"),
    ("zh-PA", "zh-Hant-PA"),
    ("zh-PF", "zh-Hant-PF"),
    ("zh-PH", "zh-Hant-PH"),
    ("zh-SR", "zh-Hant-SR"),
    ("zh-TH", "zh-Hant-TH"),
    ("zh-TW", "zh-Hant-TW"),
    ("zh-US", "zh-Hant-US"),
    ("zh-VN", "zh-Hant-VN"),
    ("zu", "zu-Latn-ZA"),
];

/// Numbering systems whose ten digits are consecutive code points, with their
/// zero. `hanidec`, the one other system with a simple mapping, is not.
const CONTIGUOUS_NUMBERING_SYSTEMS: &[(&str, char)] = &[
    ("adlm", '\u{1E950}'),
    ("ahom", '\u{11730}'),
    ("arab", '\u{660}'),
    ("arabext", '\u{6F0}'),
    ("bali", '\u{1B50}'),
    ("beng", '\u{9E6}'),
    ("bhks", '\u{11C50}'),
    ("brah", '\u{11066}'),
    ("cakm", '\u{11136}'),
    ("cham", '\u{AA50}'),
    ("deva", '\u{966}'),
    ("diak", '\u{11950}'),
    ("fullwide", '\u{FF10}'),
    ("gara", '\u{10D40}'),
    ("gong", '\u{11DA0}'),
    ("gonm", '\u{11D50}'),
    ("gujr", '\u{AE6}'),
    ("gukh", '\u{16130}'),
    ("guru", '\u{A66}'),
    ("hmng", '\u{16B50}'),
    ("hmnp", '\u{1E140}'),
    ("java", '\u{A9D0}'),
    ("kali", '\u{A900}'),
    ("kawi", '\u{11F50}'),
    ("khmr", '\u{17E0}'),
    ("knda", '\u{CE6}'),
    ("krai", '\u{16D70}'),
    ("lana", '\u{1A80}'),
    ("lanatham", '\u{1A90}'),
    ("laoo", '\u{ED0}'),
    ("latn", '\u{30}'),
    ("lepc", '\u{1C40}'),
    ("limb", '\u{1946}'),
    ("mathbold", '\u{1D7CE}'),
    ("mathdbl", '\u{1D7D8}'),
    ("mathmono", '\u{1D7F6}'),
    ("mathsanb", '\u{1D7EC}'),
    ("mathsans", '\u{1D7E2}'),
    ("mlym", '\u{D66}'),
    ("modi", '\u{11650}'),
    ("mong", '\u{1810}'),
    ("mroo", '\u{16A60}'),
    ("mtei", '\u{ABF0}'),
    ("mymr", '\u{1040}'),
    ("mymrepka", '\u{116DA}'),
    ("mymrpao", '\u{116D0}'),
    ("mymrshan", '\u{1090}'),
    ("mymrtlng", '\u{A9F0}'),
    ("nagm", '\u{1E4F0}'),
    ("newa", '\u{11450}'),
    ("nkoo", '\u{7C0}'),
    ("olck", '\u{1C50}'),
    ("onao", '\u{1E5F1}'),
    ("orya", '\u{B66}'),
    ("osma", '\u{104A0}'),
    ("outlined", '\u{1CCF0}'),
    ("rohg", '\u{10D30}'),
    ("saur", '\u{A8D0}'),
    ("segment", '\u{1FBF0}'),
    ("shrd", '\u{111D0}'),
    ("sind", '\u{112F0}'),
    ("sinh", '\u{DE6}'),
    ("sora", '\u{110F0}'),
    ("sund", '\u{1BB0}'),
    ("sunu", '\u{11BF0}'),
    ("takr", '\u{116C0}'),
    ("talu", '\u{19D0}'),
    ("tamldec", '\u{BE6}'),
    ("telu", '\u{C66}'),
    ("thai", '\u{E50}'),
    ("tibt", '\u{F20}'),
    ("tirh", '\u{114D0}'),
    ("tnsa", '\u{16AC0}'),
    ("tols", '\u{11DE0}'),
    ("vaii", '\u{A620}'),
    ("wara", '\u{118E0}'),
    ("wcho", '\u{1E2F0}'),
];

/// The digits of `hanidec`.
const HANIDEC_DIGITS: [char; 10] = [
    '\u{3007}', '\u{4E00}', '\u{4E8C}', '\u{4E09}', '\u{56DB}', '\u{4E94}', '\u{516D}', '\u{4E03}',
    '\u{516B}', '\u{4E5D}',
];

/// The ten digits of a numbering system with a simple digit mapping.
#[must_use]
pub fn numbering_system_digits(name: &str) -> Option<[char; 10]> {
    if name == "hanidec" {
        return Some(HANIDEC_DIGITS);
    }
    let zero = lookup(CONTIGUOUS_NUMBERING_SYSTEMS, name)?;
    Some(std::array::from_fn(|digit| {
        char::from_u32(u32::from(zero) + digit as u32).expect("digits are assigned code points")
    }))
}

/// The value of a decimal digit of any numbering system this runtime knows.
#[must_use]
pub fn decimal_digit_value(character: char) -> Option<u32> {
    if let Some(digit) = character.to_digit(10) {
        return Some(digit);
    }
    let code = u32::from(character);
    CONTIGUOUS_NUMBERING_SYSTEMS.iter().find_map(|(_, zero)| {
        code.checked_sub(u32::from(*zero))
            .filter(|digit| *digit < 10)
    })
}

/// ISO 4217 codes.
const CURRENCIES: &[&str] = &[
    "AED", "AFN", "ALL", "AMD", "ANG", "AOA", "ARS", "AUD", "AWG", "AZN", "BAM", "BBD", "BDT",
    "BGN", "BHD", "BIF", "BMD", "BND", "BOB", "BOV", "BRL", "BSD", "BTN", "BWP", "BYN", "BZD",
    "CAD", "CDF", "CHE", "CHF", "CHW", "CLF", "CLP", "CNY", "COP", "COU", "CRC", "CUC", "CUP",
    "CVE", "CZK", "DJF", "DKK", "DOP", "DZD", "EGP", "ERN", "ETB", "EUR", "FJD", "FKP", "GBP",
    "GEL", "GHS", "GIP", "GMD", "GNF", "GTQ", "GYD", "HKD", "HNL", "HTG", "HUF", "IDR", "ILS",
    "INR", "IQD", "IRR", "ISK", "JMD", "JOD", "JPY", "KES", "KGS", "KHR", "KMF", "KPW", "KRW",
    "KWD", "KYD", "KZT", "LAK", "LBP", "LKR", "LRD", "LSL", "LYD", "MAD", "MDL", "MGA", "MKD",
    "MMK", "MNT", "MOP", "MRU", "MUR", "MVR", "MWK", "MXN", "MXV", "MYR", "MZN", "NAD", "NGN",
    "NIO", "NOK", "NPR", "NZD", "OMR", "PAB", "PEN", "PGK", "PHP", "PKR", "PLN", "PYG", "QAR",
    "RON", "RSD", "RUB", "RWF", "SAR", "SBD", "SCR", "SDG", "SEK", "SGD", "SHP", "SLE", "SLL",
    "SOS", "SRD", "SSP", "STN", "SVC", "SYP", "SZL", "THB", "TJS", "TMT", "TND", "TOP", "TRY",
    "TTD", "TWD", "TZS", "UAH", "UGX", "USD", "USN", "UYI", "UYU", "UYW", "UZS", "VED", "VES",
    "VND", "VUV", "WST", "XAF", "XAG", "XAU", "XBA", "XBB", "XBC", "XBD", "XCD", "XCG", "XDR",
    "XOF", "XPD", "XPF", "XPT", "XSU", "XTS", "XUA", "XXX", "YER", "ZAR", "ZMW", "ZWG", "ZWL",
];

/// Time zones this runtime can compute offsets for: UTC and the fixed `Etc`
/// zones. There is no time zone database, so no zone with transitions.
const TIME_ZONES: [(&str, i8); 27] = [
    ("Etc/GMT+1", -1),
    ("Etc/GMT+10", -10),
    ("Etc/GMT+11", -11),
    ("Etc/GMT+12", -12),
    ("Etc/GMT+2", -2),
    ("Etc/GMT+3", -3),
    ("Etc/GMT+4", -4),
    ("Etc/GMT+5", -5),
    ("Etc/GMT+6", -6),
    ("Etc/GMT+7", -7),
    ("Etc/GMT+8", -8),
    ("Etc/GMT+9", -9),
    ("Etc/GMT-1", 1),
    ("Etc/GMT-10", 10),
    ("Etc/GMT-11", 11),
    ("Etc/GMT-12", 12),
    ("Etc/GMT-13", 13),
    ("Etc/GMT-14", 14),
    ("Etc/GMT-2", 2),
    ("Etc/GMT-3", 3),
    ("Etc/GMT-4", 4),
    ("Etc/GMT-5", 5),
    ("Etc/GMT-6", 6),
    ("Etc/GMT-7", 7),
    ("Etc/GMT-8", 8),
    ("Etc/GMT-9", 9),
    ("UTC", 0),
];

/// The links to UTC, which keep their own names: an identifier is reported as
/// written, in its canonical case, rather than replaced by its target.
const UTC_LINKS: [&str; 10] = [
    "Etc/GMT",
    "Etc/Greenwich",
    "Etc/UCT",
    "Etc/UTC",
    "Etc/Universal",
    "Etc/Zulu",
    "GMT",
    "UCT",
    "Universal",
    "Zulu",
];

/// The time zone a case-insensitive identifier names and its offset in hours.
#[must_use]
pub fn time_zone(identifier: &str) -> Option<(&'static str, i8)> {
    if let Some(link) = UTC_LINKS
        .iter()
        .find(|link| link.eq_ignore_ascii_case(identifier))
    {
        return Some((link, 0));
    }
    TIME_ZONES
        .iter()
        .find(|(name, _)| name.eq_ignore_ascii_case(identifier))
        .copied()
}

fn likely_entry(key: &str) -> Option<LanguageId> {
    let index = LIKELY_SUBTAGS
        .binary_search_by(|(entry, _)| (*entry).cmp(key))
        .ok()?;
    LanguageTag::parse(LIKELY_SUBTAGS[index].1)
        .ok()
        .map(|tag| tag.id)
}

fn join_id(language: &str, script: Option<&str>, region: Option<&str>) -> String {
    let mut key = language.to_owned();
    for part in [script, region].into_iter().flatten() {
        key.push('-');
        key.push_str(part);
    }
    key
}

/// The UTS #35 Add Likely Subtags lookup. Subtags the input already has win.
#[must_use]
pub fn add_likely_subtags(locale: &LanguageId) -> Option<LanguageId> {
    let language = locale.language.as_str();
    let script = locale.script.as_deref();
    let region = locale.region.as_deref();
    let candidates = [
        Some(join_id(language, script, region)),
        Some(join_id(language, None, region)),
        Some(join_id(language, script, None)),
        Some(join_id(language, None, None)),
        script.map(|script| join_id("und", Some(script), None)),
    ];
    let found = candidates
        .iter()
        .flatten()
        .find_map(|key| likely_entry(key))?;
    Some(LanguageId {
        language: if language == "und" {
            found.language
        } else {
            locale.language.clone()
        },
        script: locale.script.clone().or(found.script),
        region: locale.region.clone().or(found.region),
        variants: locale.variants.clone(),
    })
}

/// The UTS #35 Remove Likely Subtags algorithm, favouring the region.
#[must_use]
pub fn remove_likely_subtags(locale: &LanguageId) -> Option<LanguageId> {
    let maximal = add_likely_subtags(locale)?;
    let trial = |script: Option<&String>, region: Option<&String>| LanguageId {
        language: maximal.language.clone(),
        script: script.cloned(),
        region: region.cloned(),
        variants: Vec::new(),
    };
    let target = (&maximal.language, &maximal.script, &maximal.region);
    for candidate in [
        trial(None, None),
        trial(None, maximal.region.as_ref()),
        trial(maximal.script.as_ref(), None),
    ] {
        if add_likely_subtags(&candidate).is_some_and(|expanded| {
            (&expanded.language, &expanded.script, &expanded.region) == target
        }) {
            return Some(LanguageId {
                variants: locale.variants.clone(),
                ..candidate
            });
        }
    }
    Some(maximal)
}

/// `-u-rg` and `-u-sd` values start with the region they belong to.
fn keyword_region(tag: &LanguageTag, key: &str) -> Option<String> {
    let value = tag.unicode.as_ref()?.keywords.get(key)?;
    let region = value.get(..2)?;
    region
        .bytes()
        .all(|byte| byte.is_ascii_alphabetic())
        .then(|| region.to_ascii_uppercase())
}

/// RegionPreference: the region that speaks for a locale. Every table below
/// covers all regions by way of a default, so the first signal present decides.
fn preferred_region(tag: &LanguageTag) -> String {
    keyword_region(tag, "rg")
        .or_else(|| tag.id.region.clone())
        .or_else(|| keyword_region(tag, "sd"))
        .or_else(|| add_likely_subtags(&tag.id).and_then(|maximal| maximal.region))
        .unwrap_or_else(|| String::from("001"))
}

/// Hour cycles for language-region pairs and regions, preferred first. Regions
/// outside the table use the 24-hour clock first, as the world does.
const HOUR_CYCLES: &[(&str, &[&str])] = &[
    ("AE", TWELVE_HOUR),
    ("AU", TWELVE_HOUR),
    ("BD", TWELVE_HOUR),
    ("CA", TWELVE_HOUR),
    ("CO", TWELVE_HOUR),
    ("DO", TWELVE_HOUR),
    ("EG", TWELVE_HOUR),
    ("ET", TWELVE_HOUR),
    ("GR", TWELVE_HOUR),
    ("IN", TWELVE_HOUR),
    ("IQ", TWELVE_HOUR),
    ("JO", TWELVE_HOUR),
    ("KR", TWELVE_HOUR),
    ("KW", TWELVE_HOUR),
    ("LB", TWELVE_HOUR),
    ("MX", TWELVE_HOUR),
    ("MY", TWELVE_HOUR),
    ("NZ", TWELVE_HOUR),
    ("OM", TWELVE_HOUR),
    ("PA", TWELVE_HOUR),
    ("PH", TWELVE_HOUR),
    ("PK", TWELVE_HOUR),
    ("PR", TWELVE_HOUR),
    ("QA", TWELVE_HOUR),
    ("SA", TWELVE_HOUR),
    ("SG", TWELVE_HOUR),
    ("SY", TWELVE_HOUR),
    ("US", TWELVE_HOUR),
    ("VE", TWELVE_HOUR),
    ("YE", TWELVE_HOUR),
    ("ZA", TWELVE_HOUR),
    ("fr-CA", TWENTY_FOUR_HOUR),
];
const TWELVE_HOUR: &[&str] = &["h12", "h23"];
const TWENTY_FOUR_HOUR: &[&str] = &["h23", "h12"];

/// HourCyclesOfLocale without its keyword step.
#[must_use]
pub fn hour_cycles(tag: &LanguageTag) -> &'static [&'static str] {
    let region = preferred_region(tag);
    let paired = format!("{}-{region}", tag.id.language);
    lookup(HOUR_CYCLES, &paired)
        .or_else(|| lookup(HOUR_CYCLES, &region))
        .unwrap_or(TWENTY_FOUR_HOUR)
}

/// Calendars in use by region, preferred first. Only calendars this runtime
/// implements are named; other regions use `gregory`.
const CALENDARS_BY_REGION: &[(&str, &[&str])] = &[
    (
        "AF",
        &["persian", "gregory", "islamic-civil", "islamic-tbla"],
    ),
    (
        "EG",
        &["gregory", "coptic", "islamic-civil", "islamic-tbla"],
    ),
    ("ET", &["gregory", "ethiopic"]),
    (
        "IL",
        &["gregory", "hebrew", "islamic-civil", "islamic-tbla"],
    ),
    ("IN", &["gregory", "indian"]),
    (
        "IR",
        &["persian", "gregory", "islamic-civil", "islamic-tbla"],
    ),
    ("JP", &["gregory", "japanese"]),
    ("SA", &["gregory", "islamic-civil", "islamic-tbla"]),
    ("TH", &["buddhist", "gregory"]),
    ("TW", &["gregory", "roc"]),
];

/// CalendarsOfLocale without its keyword step.
#[must_use]
pub fn calendars_of(tag: &LanguageTag) -> &'static [&'static str] {
    lookup(CALENDARS_BY_REGION, &preferred_region(tag)).unwrap_or(&["gregory"])
}

/// Regions whose week starts on Sunday, Saturday, or Friday. Every other region
/// starts on Monday.
const SUNDAY_FIRST: &[&str] = &[
    "AG", "AS", "AU", "BD", "BR", "BS", "BT", "BW", "BZ", "CA", "CN", "CO", "DM", "DO", "ET", "GT",
    "GU", "HK", "HN", "ID", "IL", "IN", "JM", "JP", "KE", "KH", "KR", "LA", "MH", "MM", "MO", "MT",
    "MX", "MZ", "NI", "NP", "PA", "PE", "PH", "PK", "PR", "PT", "PY", "SA", "SG", "SV", "TH", "TT",
    "TW", "UM", "US", "VE", "VI", "WS", "YE", "ZA", "ZW",
];
const SATURDAY_FIRST: &[&str] = &[
    "AE", "AF", "BH", "DJ", "DZ", "EG", "IQ", "IR", "JO", "KW", "LY", "OM", "QA", "SD", "SY",
];

/// Weekends that are not Saturday and Sunday, as ISO weekday numbers.
const WEEKENDS: &[(&str, &[u8])] = &[
    ("AE", FRIDAY_SATURDAY),
    ("AF", &[4, 5]),
    ("BH", FRIDAY_SATURDAY),
    ("DZ", FRIDAY_SATURDAY),
    ("EG", FRIDAY_SATURDAY),
    ("IL", FRIDAY_SATURDAY),
    ("IN", &[7]),
    ("IQ", FRIDAY_SATURDAY),
    ("IR", &[5]),
    ("JO", FRIDAY_SATURDAY),
    ("KW", FRIDAY_SATURDAY),
    ("LY", FRIDAY_SATURDAY),
    ("OM", FRIDAY_SATURDAY),
    ("QA", FRIDAY_SATURDAY),
    ("SA", FRIDAY_SATURDAY),
    ("SD", FRIDAY_SATURDAY),
    ("SY", FRIDAY_SATURDAY),
    ("UG", &[7]),
    ("YE", FRIDAY_SATURDAY),
];
const FRIDAY_SATURDAY: &[u8] = &[5, 6];

/// WeekInfoOfLocale: the first day and weekend, as ISO weekday numbers.
#[must_use]
pub fn week_info(tag: &LanguageTag) -> (u8, &'static [u8]) {
    let region = preferred_region(tag);
    let region = region.as_str();
    let first_day = if SUNDAY_FIRST.contains(&region) {
        7
    } else if SATURDAY_FIRST.contains(&region) {
        6
    } else if region == "MV" {
        5
    } else {
        1
    };
    (first_day, lookup(WEEKENDS, region).unwrap_or(&[6, 7]))
}

/// Time zones in use by region, sorted. Regions outside the table report none.
const TIME_ZONES_BY_REGION: &[(&str, &[&str])] = &[
    ("AR", &["America/Argentina/Buenos_Aires"]),
    ("AT", &["Europe/Vienna"]),
    ("BE", &["Europe/Brussels"]),
    ("CH", &["Europe/Zurich"]),
    ("CN", &["Asia/Shanghai", "Asia/Urumqi"]),
    ("DE", &["Europe/Berlin", "Europe/Busingen"]),
    ("ES", &["Africa/Ceuta", "Atlantic/Canary", "Europe/Madrid"]),
    ("FR", &["Europe/Paris"]),
    ("GB", &["Europe/London"]),
    ("IE", &["Europe/Dublin"]),
    ("IL", &["Asia/Jerusalem"]),
    ("IN", &["Asia/Kolkata"]),
    ("IT", &["Europe/Rome"]),
    ("JP", &["Asia/Tokyo"]),
    ("KR", &["Asia/Seoul"]),
    ("NL", &["Europe/Amsterdam"]),
    ("NO", &["Europe/Oslo"]),
    ("SE", &["Europe/Stockholm"]),
    ("TH", &["Asia/Bangkok"]),
    ("TW", &["Asia/Taipei"]),
    (
        "US",
        &[
            "America/Adak",
            "America/Anchorage",
            "America/Boise",
            "America/Chicago",
            "America/Denver",
            "America/Detroit",
            "America/Indiana/Indianapolis",
            "America/Juneau",
            "America/Kentucky/Louisville",
            "America/Los_Angeles",
            "America/New_York",
            "America/Phoenix",
            "Pacific/Honolulu",
        ],
    ),
];

/// TimeZonesOfLocale, `None` without a region subtag.
#[must_use]
pub fn time_zones_of(tag: &LanguageTag) -> Option<&'static [&'static str]> {
    let region = tag.id.region.as_deref()?;
    Some(lookup(TIME_ZONES_BY_REGION, region).unwrap_or(&[]))
}

/// TextDirectionOfLocale: whether the locale's script runs right to left.
#[must_use]
pub fn is_right_to_left(tag: &LanguageTag) -> bool {
    const RIGHT_TO_LEFT: &[&str] = &[
        "Adlm", "Arab", "Hebr", "Mand", "Nkoo", "Rohg", "Samr", "Syrc", "Thaa", "Yezi",
    ];
    let script = tag
        .id
        .script
        .clone()
        .or_else(|| add_likely_subtags(&tag.id).and_then(|maximal| maximal.script));
    script.is_some_and(|script| RIGHT_TO_LEFT.contains(&script.as_str()))
}

/// NumberingSystemsOfLocale without its keyword step.
#[must_use]
pub fn numbering_systems_of(tag: &LanguageTag) -> &'static [&'static str] {
    match tag.id.language.as_str() {
        "as" | "bn" => &["beng"],
        "fa" | "ps" => &["arabext"],
        "mr" | "ne" => &["deva"],
        _ => &["latn"],
    }
}

/// Reads a sorted `(key, value)` table.
fn lookup<T: Copy>(table: &[(&str, T)], key: &str) -> Option<T> {
    table
        .binary_search_by(|(entry, _)| (*entry).cmp(key))
        .ok()
        .map(|index| table[index].1)
}

fn triple<'a>(table: &'a [(&str, &str, &'a str)], key: &str, value: &str) -> Option<&'a str> {
    table
        .binary_search_by(|(entry_key, entry_value, _)| {
            (*entry_key, *entry_value).cmp(&(key, value))
        })
        .ok()
        .map(|index| table[index].2)
}

/// The collations available everywhere: those of the root locale.
pub const COLLATIONS: &[&str] = &["emoji", "eor"];

/// The locale data behind every Intl service.
pub struct IntlData {
    available: Vec<String>,
    calendars: Vec<String>,
    collations: Vec<String>,
    currencies: Vec<String>,
    numbering_systems: Vec<String>,
    time_zones: Vec<String>,
    units: Vec<String>,
    collation_keywords: Vec<String>,
    case_first_keywords: Vec<String>,
    numeric_keywords: Vec<String>,
    numbering_keywords: Vec<String>,
    calendar_keywords: Vec<String>,
    hour_cycle_keywords: Vec<String>,
}

/// The one instance services hold a reference to.
pub static DATA: LazyLock<IntlData> = LazyLock::new(|| {
    let owned = |values: &[&str]| values.iter().map(|value| (*value).to_owned()).collect();
    let mut numbering_systems: Vec<String> = CONTIGUOUS_NUMBERING_SYSTEMS
        .iter()
        .map(|(name, _)| (*name).to_owned())
        .collect();
    numbering_systems.push(String::from("hanidec"));
    numbering_systems.sort();
    let mut numbering_keywords = vec![String::from("latn")];
    numbering_keywords.extend(
        numbering_systems
            .iter()
            .filter(|name| *name != "latn")
            .cloned(),
    );
    IntlData {
        available: owned(&["en", "en-US"]),
        calendars: owned(&[
            "buddhist",
            "coptic",
            "ethioaa",
            "ethiopic",
            "gregory",
            "hebrew",
            "indian",
            "islamic-civil",
            "islamic-tbla",
            "iso8601",
            "persian",
            "roc",
        ]),
        collations: owned(COLLATIONS),
        currencies: owned(CURRENCIES),
        numbering_systems,
        time_zones: TIME_ZONES
            .iter()
            .map(|(name, _)| (*name).to_owned())
            .collect(),
        units: owned(&SANCTIONED_UNITS),
        collation_keywords: std::iter::once(String::new())
            .chain(COLLATIONS.iter().map(|value| (*value).to_owned()))
            .collect(),
        case_first_keywords: owned(&["false", "lower", "upper"]),
        numeric_keywords: owned(&["false", "true"]),
        numbering_keywords,
        calendar_keywords: owned(&[
            "gregory",
            "buddhist",
            "coptic",
            "ethioaa",
            "ethiopic",
            "hebrew",
            "indian",
            "islamic-civil",
            "islamic-tbla",
            "iso8601",
            "persian",
            "roc",
        ]),
        hour_cycle_keywords: owned(&["h12", "h11", "h23", "h24"]),
    }
});

impl SupportedValuesInventory for IntlData {
    fn supported_calendars(&self) -> &[String] {
        &self.calendars
    }
    fn supported_collations(&self) -> &[String] {
        &self.collations
    }
    fn supported_currencies(&self) -> &[String] {
        &self.currencies
    }
    fn supported_numbering_systems(&self) -> &[String] {
        &self.numbering_systems
    }
    fn supported_time_zones(&self) -> &[String] {
        &self.time_zones
    }
    fn supported_units(&self) -> &[String] {
        &self.units
    }
}

impl CollatorDataProvider for IntlData {
    fn locale_defaults(&self, _data_locale: &str, _usage: CollatorUsage) -> CollatorLocaleDefaults {
        CollatorLocaleDefaults {
            sensitivity: CollatorSensitivity::Variant,
            ignore_punctuation: false,
        }
    }
    fn compare(&self, request: CollatorCompareRequest<'_>) -> Option<Ordering> {
        Some(collation::compare(&request))
    }
}

impl LocaleDataProvider for IntlData {
    fn available_locales(&self) -> &[String] {
        &self.available
    }
    fn language_alias(&self, language: &str) -> Option<&str> {
        lookup(TAG_ALIASES, language).or_else(|| lookup(LANGUAGE_ALIASES, language))
    }
    fn region_alias(&self, region: &str) -> Option<&str> {
        lookup(REGION_ALIASES, region)
    }
    fn complex_region_alias(
        &self,
        region: &str,
        language: &str,
        script: Option<&str>,
    ) -> Option<&str> {
        let index = COMPLEX_REGION_ALIASES
            .binary_search_by(|(entry, _, _)| (*entry).cmp(region))
            .ok()?;
        let (_, default, choices) = COMPLEX_REGION_ALIASES[index];
        let scripted = script.and_then(|script| {
            lookup(choices, &join_id(language, Some(script), None))
                .or_else(|| lookup(choices, &join_id("und", Some(script), None)))
        });
        Some(
            scripted
                .or_else(|| lookup(choices, language))
                .unwrap_or(default),
        )
    }
    fn variant_alias(&self, variant: &str) -> Option<&str> {
        match lookup(VARIANT_ALIASES, variant)? {
            VariantAlias::Variant(replacement) => Some(replacement),
            VariantAlias::Language(_) | VariantAlias::Region(_) => None,
        }
    }
    fn variant_language_alias(&self, variant: &str) -> Option<&str> {
        match lookup(VARIANT_ALIASES, variant)? {
            VariantAlias::Language(replacement) => Some(replacement),
            VariantAlias::Region(_) | VariantAlias::Variant(_) => None,
        }
    }
    fn variant_region_alias(&self, variant: &str) -> Option<&str> {
        match lookup(VARIANT_ALIASES, variant)? {
            VariantAlias::Region(replacement) => Some(replacement),
            VariantAlias::Language(_) | VariantAlias::Variant(_) => None,
        }
    }
    fn unicode_type_alias(&self, key: &str, value: &str) -> Option<&str> {
        triple(UNICODE_TYPE_ALIASES, key, value)
    }
    fn transform_type_alias(&self, key: &str, value: &str) -> Option<&str> {
        triple(TRANSFORM_TYPE_ALIASES, key, value)
    }
    fn key_values(&self, _data_locale: &str, key: &str) -> &[String] {
        match key {
            "ca" => &self.calendar_keywords,
            "co" => &self.collation_keywords,
            "hc" => &self.hour_cycle_keywords,
            "kf" => &self.case_first_keywords,
            "kn" => &self.numeric_keywords,
            "nu" => &self.numbering_keywords,
            _ => &[],
        }
    }
    fn add_likely_subtags(&self, locale: &LanguageId) -> Option<LanguageId> {
        add_likely_subtags(locale)
    }
    fn fallback_locale(&self) -> Option<&str> {
        Some(DEFAULT_LOCALE)
    }
}

/// Whether a table in this file is sorted the way its lookups assume.
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lookup_tables_are_sorted_by_their_keys() {
        for table in [
            TAG_ALIASES,
            LANGUAGE_ALIASES,
            REGION_ALIASES,
            LIKELY_SUBTAGS,
        ] {
            assert!(table.windows(2).all(|pair| pair[0].0 < pair[1].0));
        }
        assert!(
            COMPLEX_REGION_ALIASES
                .windows(2)
                .all(|pair| pair[0].0 < pair[1].0)
        );
        for (_, _, choices) in COMPLEX_REGION_ALIASES {
            assert!(choices.windows(2).all(|pair| pair[0].0 < pair[1].0));
        }
        assert!(VARIANT_ALIASES.windows(2).all(|pair| pair[0].0 < pair[1].0));
        for table in [UNICODE_TYPE_ALIASES, TRANSFORM_TYPE_ALIASES] {
            assert!(
                table
                    .windows(2)
                    .all(|pair| (pair[0].0, pair[0].1) < (pair[1].0, pair[1].1))
            );
        }
    }

    #[test]
    fn likely_subtags_keep_what_the_input_already_has() {
        let maximize = |tag: &str| {
            let id = LanguageTag::parse(tag).unwrap().id;
            add_likely_subtags(&id).unwrap().render()
        };
        assert_eq!(maximize("en"), "en-Latn-US");
        assert_eq!(maximize("en-Arab"), "en-Arab-US");
        assert_eq!(maximize("und-419"), "es-Latn-419");
        assert_eq!(maximize("und-Cyrl-RO"), "bg-Cyrl-RO");
        assert_eq!(maximize("und-AQ"), "en-Latn-AQ");
    }
}
