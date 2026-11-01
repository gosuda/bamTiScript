//! ECMA-402 internationalization primitives.

use std::fmt;

pub mod canonical_locales;
pub mod collator;
pub mod date_time_format;
pub mod locale_negotiation;
pub mod number_format;
pub mod plural_rules;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum IntlKind {
    Collator,
    NumberFormat,
    DateTimeFormat,
    PluralRules,
    RelativeTimeFormat,
    ListFormat,
    Segmenter,
    DisplayNames,
    Locale,
}

impl IntlKind {
    pub const COUNT: usize = 9;

    pub const fn index(self) -> usize {
        self as usize
    }
}

#[derive(Clone)]
pub enum IntlObject {
    Collator(collator::Collator),
    NumberFormat(Box<number_format::NumberFormat<'static>>),
    DateTimeFormat(date_time_format::DateTimeFormat),
    PluralRules(plural_rules::PluralRules<'static>),
    RelativeTimeFormat(plural_rules::RelativeTimeFormat<'static>),
    ListFormat(plural_rules::ListFormat<'static>),
    Segmenter(plural_rules::Segmenter<'static>),
    DisplayNames(plural_rules::DisplayNames<'static>),
    Locale(locale_negotiation::LanguageTag),
}

impl IntlObject {
    pub const fn kind(&self) -> IntlKind {
        match self {
            Self::Collator(_) => IntlKind::Collator,
            Self::NumberFormat(_) => IntlKind::NumberFormat,
            Self::DateTimeFormat(_) => IntlKind::DateTimeFormat,
            Self::PluralRules(_) => IntlKind::PluralRules,
            Self::RelativeTimeFormat(_) => IntlKind::RelativeTimeFormat,
            Self::ListFormat(_) => IntlKind::ListFormat,
            Self::Segmenter(_) => IntlKind::Segmenter,
            Self::DisplayNames(_) => IntlKind::DisplayNames,
            Self::Locale(_) => IntlKind::Locale,
        }
    }
}

impl fmt::Debug for IntlObject {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_tuple("IntlObject")
            .field(&self.kind())
            .finish()
    }
}
