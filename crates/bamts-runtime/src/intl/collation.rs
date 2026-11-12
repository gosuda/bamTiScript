//! A root-locale collation built on Unicode properties.
//!
//! There are no DUCET tables here, so this approximates the Unicode Collation
//! Algorithm rather than implementing it: strings compare on the NFD of their
//! text, by the four levels and class order the algorithm prescribes, with
//! letters of one case-folded base ordered by code point. Canonically
//! equivalent strings are therefore equal, and ASCII orders as it should.

use std::cmp::Ordering;

use icu_properties::CodePointMapData;
use icu_properties::props::GeneralCategory;
use unicode_normalization::UnicodeNormalization;

use super::collator::{CollatorCaseFirst, CollatorCompareRequest, CollatorSensitivity};
use super::locale_data::decimal_digit_value;

/// Primary classes, in the order the collation orders them.
const WHITESPACE: u32 = 0;
const PUNCTUATION: u32 = 1;
const SYMBOL: u32 = 2;
const DIGIT: u32 = 3;
const LETTER: u32 = 4;

/// Numbers of different lengths sort by length when `numeric` is on. Lengths
/// are shifted past the digit values so the two weights cannot be confused.
const NUMERIC_LENGTH_BASE: u32 = 10;

#[derive(Default)]
struct SortKey {
    primary: Vec<(u32, u32)>,
    secondary: Vec<u32>,
    tertiary: Vec<u8>,
}

fn scalars(units: &[u16]) -> String {
    char::decode_utf16(units.iter().copied())
        .map(|unit| unit.unwrap_or(char::REPLACEMENT_CHARACTER))
        .collect()
}

fn folded(character: char) -> char {
    character.to_lowercase().next().unwrap_or(character)
}

fn primary_class(character: char, category: GeneralCategory) -> Option<u32> {
    use GeneralCategory as Gc;
    if character.is_whitespace() {
        return Some(WHITESPACE);
    }
    match category {
        Gc::Control | Gc::Format | Gc::Unassigned | Gc::Surrogate => None,
        Gc::ConnectorPunctuation
        | Gc::DashPunctuation
        | Gc::OpenPunctuation
        | Gc::ClosePunctuation
        | Gc::InitialPunctuation
        | Gc::FinalPunctuation
        | Gc::OtherPunctuation => Some(PUNCTUATION),
        Gc::MathSymbol | Gc::CurrencySymbol | Gc::ModifierSymbol | Gc::OtherSymbol => Some(SYMBOL),
        Gc::DecimalNumber => Some(DIGIT),
        _ => Some(LETTER),
    }
}

fn sort_key(units: &[u16], ignore_punctuation: bool, numeric: bool) -> SortKey {
    let categories = CodePointMapData::<GeneralCategory>::new();
    let text = scalars(units);
    let mut key = SortKey::default();
    let characters: Vec<char> = text.nfd().collect();
    let mut index = 0;
    while let Some(&character) = characters.get(index) {
        let category = categories.get(character);
        index += 1;
        if matches!(
            category,
            GeneralCategory::NonspacingMark | GeneralCategory::EnclosingMark
        ) {
            key.secondary.push(u32::from(character) + 1);
            continue;
        }
        let Some(class) = primary_class(character, category) else {
            continue;
        };
        if ignore_punctuation && matches!(class, WHITESPACE | PUNCTUATION) {
            continue;
        }
        if class == DIGIT
            && numeric
            && let Some(first) = decimal_digit_value(character)
        {
            let mut digits = vec![first];
            while let Some(digit) = characters.get(index).copied().and_then(decimal_digit_value) {
                digits.push(digit);
                index += 1;
            }
            let leading = digits.iter().take_while(|digit| **digit == 0).count();
            let significant = &digits[leading.min(digits.len() - 1)..];
            let length = u32::try_from(significant.len()).unwrap_or(u32::MAX);
            key.primary
                .push((DIGIT, NUMERIC_LENGTH_BASE.saturating_add(length)));
            key.primary
                .extend(significant.iter().map(|digit| (DIGIT, *digit)));
            key.secondary.push(0);
            key.tertiary.push(0);
            continue;
        }
        let weight = match decimal_digit_value(character) {
            Some(digit) if class == DIGIT => digit,
            _ => u32::from(folded(character)),
        };
        key.primary.push((class, weight));
        key.secondary.push(0);
        key.tertiary.push(u8::from(character.is_uppercase()));
    }
    key
}

/// Compares two exact JavaScript strings under the requested options.
pub(super) fn compare(request: &CollatorCompareRequest<'_>) -> Ordering {
    let options = request.options;
    let left = sort_key(request.left, options.ignore_punctuation, options.numeric);
    let right = sort_key(request.right, options.ignore_punctuation, options.numeric);
    let primary = left.primary.cmp(&right.primary);
    if primary != Ordering::Equal {
        return primary;
    }
    let accents = left.secondary.cmp(&right.secondary);
    let case = || {
        let ordering = left.tertiary.cmp(&right.tertiary);
        if options.case_first == CollatorCaseFirst::Upper {
            ordering.reverse()
        } else {
            ordering
        }
    };
    match options.sensitivity {
        CollatorSensitivity::Base => Ordering::Equal,
        CollatorSensitivity::Accent => accents,
        CollatorSensitivity::Case => case(),
        CollatorSensitivity::Variant => accents.then_with(case),
    }
}
