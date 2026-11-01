//! ECMA-402 internationalization primitives.

use std::fmt;

pub mod canonical_locales;
mod collation;
pub mod collator;
mod date_data;
pub mod date_time_format;
mod locale_aliases;
pub mod locale_data;
pub mod locale_negotiation;
pub mod number_data;
pub mod number_format;
pub mod plural_rules;
mod segmentation;
pub mod service_data;

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
    DurationFormat,
    Segments,
    SegmentIterator,
}

impl IntlKind {
    pub const COUNT: usize = 12;
    pub const ALL: [Self; Self::COUNT] = [
        Self::Collator,
        Self::NumberFormat,
        Self::DateTimeFormat,
        Self::PluralRules,
        Self::RelativeTimeFormat,
        Self::ListFormat,
        Self::Segmenter,
        Self::DisplayNames,
        Self::Locale,
        Self::DurationFormat,
        Self::Segments,
        Self::SegmentIterator,
    ];

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
    Segments(Box<SegmentsRecord>),
    SegmentIterator(Box<SegmentIteratorRecord>),
}

/// The state of a `Segments` object: the text and how it broke up.
#[derive(Clone, Debug)]
pub struct SegmentsRecord {
    pub text: plural_rules::SegmentedText,
    pub granularity: plural_rules::SegmenterGranularity,
}

/// The state of a Segment Iterator: what it walks and where it is.
#[derive(Clone, Debug)]
pub struct SegmentIteratorRecord {
    pub text: plural_rules::SegmentedText,
    pub granularity: plural_rules::SegmenterGranularity,
    pub next_record: usize,
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
            Self::Segments(_) => IntlKind::Segments,
            Self::SegmentIterator(_) => IntlKind::SegmentIterator,
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
