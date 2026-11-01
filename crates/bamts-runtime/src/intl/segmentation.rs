//! UAX #29 text segmentation over UTF-16, from Unicode property data.

use icu_properties::props::{
    ExtendedPictographic, GeneralCategory, GraphemeClusterBreak, SentenceBreak, WordBreak,
};
use icu_properties::{CodePointMapData, CodePointSetData};

use super::plural_rules::{ProviderSegmentBoundary, SegmenterGranularity};

/// One code point and where it ends. A lone surrogate is a code point here.
struct Scalar {
    character: char,
    end: usize,
}

fn scalars(input: &[u16]) -> Vec<Scalar> {
    let mut result = Vec::with_capacity(input.len());
    let mut end = 0;
    for unit in char::decode_utf16(input.iter().copied()) {
        let (character, width) = match unit {
            Ok(character) => (character, character.len_utf16()),
            Err(_) => ('\u{fffd}', 1),
        };
        end += width;
        result.push(Scalar { character, end });
    }
    result
}

/// The grapheme cluster boundaries after each code point that ends a cluster.
fn grapheme_breaks(text: &[Scalar]) -> Vec<usize> {
    use GraphemeClusterBreak as Gcb;
    let classes = CodePointMapData::<Gcb>::new();
    let pictographic = CodePointSetData::new::<ExtendedPictographic>();
    let mut breaks = Vec::new();
    let mut pictographic_run = false;
    let mut indicators = 0_usize;
    for (index, scalar) in text.iter().enumerate() {
        let class = classes.get(scalar.character);
        if pictographic.contains(scalar.character) {
            pictographic_run = true;
        } else if class != Gcb::Extend && class != Gcb::ZWJ {
            pictographic_run = false;
        }
        indicators = if class == Gcb::RegionalIndicator {
            indicators + 1
        } else {
            0
        };
        let Some(next) = text.get(index + 1) else {
            breaks.push(index);
            break;
        };
        let after = classes.get(next.character);
        let joined = match (class, after) {
            (Gcb::CR, Gcb::LF) => true,
            (Gcb::Control | Gcb::CR | Gcb::LF, _) | (_, Gcb::Control | Gcb::CR | Gcb::LF) => false,
            (Gcb::L, Gcb::L | Gcb::V | Gcb::LV | Gcb::LVT)
            | (Gcb::LV | Gcb::V, Gcb::V | Gcb::T)
            | (Gcb::LVT | Gcb::T, Gcb::T) => true,
            (_, Gcb::Extend | Gcb::ZWJ | Gcb::SpacingMark) | (Gcb::Prepend, _) => true,
            (Gcb::ZWJ, _) if pictographic_run && pictographic.contains(next.character) => true,
            (Gcb::RegionalIndicator, Gcb::RegionalIndicator) => indicators % 2 == 1,
            _ => false,
        };
        if !joined {
            breaks.push(index);
        }
    }
    breaks
}

fn ignorable_word(class: WordBreak) -> bool {
    matches!(
        class,
        WordBreak::Extend | WordBreak::Format | WordBreak::ZWJ
    )
}

fn hard_word(class: WordBreak) -> bool {
    matches!(class, WordBreak::CR | WordBreak::LF | WordBreak::Newline)
}

fn letter(class: WordBreak) -> bool {
    matches!(class, WordBreak::ALetter | WordBreak::HebrewLetter)
}

/// Whether the word rules keep positions `index` and `index + 1` together.
fn word_joined(classes: &[WordBreak], pictographic: &[bool], index: usize) -> bool {
    use WordBreak as Wb;
    let (here, next) = (classes[index], classes[index + 1]);
    if here == Wb::CR && next == Wb::LF {
        return true;
    }
    if hard_word(here) || hard_word(next) {
        return false;
    }
    if here == Wb::ZWJ && pictographic[index + 1] {
        return true;
    }
    if here == Wb::WSegSpace && next == Wb::WSegSpace {
        return true;
    }
    if ignorable_word(next) {
        return true;
    }
    // Later rules see through Extend, Format and ZWJ.
    let significant = |mut position: usize| {
        while ignorable_word(classes[position]) && position > 0 {
            position -= 1;
        }
        position
    };
    let before = significant(index);
    let left = classes[before];
    let previous = (before > 0).then(|| classes[significant(before - 1)]);
    let mut following = index + 2;
    while following < classes.len() && ignorable_word(classes[following]) {
        following += 1;
    }
    let after = classes.get(following).copied();
    match (left, next) {
        (l, r) if letter(l) && letter(r) => true,
        (l, Wb::MidLetter | Wb::MidNumLet | Wb::SingleQuote)
            if letter(l) && after.is_some_and(letter) =>
        {
            true
        }
        (Wb::MidLetter | Wb::MidNumLet | Wb::SingleQuote, r)
            if letter(r) && previous.is_some_and(letter) =>
        {
            true
        }
        (Wb::HebrewLetter, Wb::SingleQuote) => true,
        (Wb::HebrewLetter, Wb::DoubleQuote) if after == Some(Wb::HebrewLetter) => true,
        (Wb::DoubleQuote, Wb::HebrewLetter) if previous == Some(Wb::HebrewLetter) => true,
        (Wb::Numeric, Wb::Numeric) => true,
        (l, Wb::Numeric) if letter(l) => true,
        (Wb::Numeric, r) if letter(r) => true,
        (Wb::MidNum | Wb::MidNumLet | Wb::SingleQuote, Wb::Numeric)
            if previous == Some(Wb::Numeric) =>
        {
            true
        }
        (Wb::Numeric, Wb::MidNum | Wb::MidNumLet | Wb::SingleQuote)
            if after == Some(Wb::Numeric) =>
        {
            true
        }
        (Wb::Katakana, Wb::Katakana) => true,
        (l, Wb::ExtendNumLet)
            if letter(l) || matches!(l, Wb::Numeric | Wb::Katakana | Wb::ExtendNumLet) =>
        {
            true
        }
        (Wb::ExtendNumLet, r) if letter(r) || matches!(r, Wb::Numeric | Wb::Katakana) => true,
        (Wb::RegionalIndicator, Wb::RegionalIndicator) => {
            let mut count = 0;
            let mut position = before;
            loop {
                if classes[position] == Wb::RegionalIndicator {
                    count += 1;
                } else if !ignorable_word(classes[position]) {
                    break;
                }
                if position == 0 {
                    break;
                }
                position -= 1;
            }
            count % 2 == 1
        }
        _ => false,
    }
}

fn word_breaks(text: &[Scalar]) -> Vec<usize> {
    let map = CodePointMapData::<WordBreak>::new();
    let extended = CodePointSetData::new::<ExtendedPictographic>();
    let classes: Vec<WordBreak> = text.iter().map(|s| map.get(s.character)).collect();
    let pictographic: Vec<bool> = text
        .iter()
        .map(|s| extended.contains(s.character))
        .collect();
    (0..text.len())
        .filter(|index| index + 1 == text.len() || !word_joined(&classes, &pictographic, *index))
        .collect()
}

fn ignorable_sentence(class: SentenceBreak) -> bool {
    matches!(class, SentenceBreak::Extend | SentenceBreak::Format)
}

fn paragraph_separator(class: SentenceBreak) -> bool {
    matches!(
        class,
        SentenceBreak::Sep | SentenceBreak::CR | SentenceBreak::LF
    )
}

/// The rules SB6 to SB11, for a boundary before position `next`. `significant`
/// lists the code points before it that are not Extend or Format, nearest last.
fn sentence_joined(significant: &[SentenceBreak], classes: &[SentenceBreak], next: usize) -> bool {
    use SentenceBreak as Sb;
    let mut position = significant.len();
    let mut take_while = |test: &dyn Fn(Sb) -> bool| {
        let start = position;
        while position > 0 && test(significant[position - 1]) {
            position -= 1;
        }
        start - position
    };
    let spaces = take_while(&|class| class == Sb::Sp);
    let closes = take_while(&|class| class == Sb::Close);
    let Some(&terminator) = position
        .checked_sub(1)
        .and_then(|last| significant.get(last))
    else {
        return true;
    };
    if !matches!(terminator, Sb::ATerm | Sb::STerm) {
        return true;
    }
    let before_terminator = position.checked_sub(2).map(|index| significant[index]);
    let upcoming: Vec<Sb> = classes[next..]
        .iter()
        .copied()
        .filter(|class| !ignorable_sentence(*class))
        .collect();
    let first = upcoming.first().copied();
    if terminator == Sb::ATerm {
        if spaces == 0 && closes == 0 && first == Some(Sb::Numeric) {
            return true;
        }
        if spaces == 0
            && closes == 0
            && first == Some(Sb::Upper)
            && matches!(before_terminator, Some(Sb::Upper | Sb::Lower))
        {
            return true;
        }
        let lower_ahead = upcoming.iter().copied().find(|class| {
            matches!(
                *class,
                Sb::OLetter
                    | Sb::Upper
                    | Sb::Lower
                    | Sb::Sep
                    | Sb::CR
                    | Sb::LF
                    | Sb::ATerm
                    | Sb::STerm
            )
        }) == Some(Sb::Lower);
        if lower_ahead {
            return true;
        }
    }
    if matches!(first, Some(Sb::SContinue | Sb::ATerm | Sb::STerm)) {
        return true;
    }
    if spaces == 0 && matches!(first, Some(Sb::Close | Sb::Sp)) {
        return true;
    }
    if spaces > 0 && matches!(first, Some(Sb::Sp)) {
        return true;
    }
    spaces > 0 && first.is_some_and(paragraph_separator)
        || closes > 0 && first.is_some_and(paragraph_separator)
}

fn sentence_breaks(text: &[Scalar]) -> Vec<usize> {
    use SentenceBreak as Sb;
    let map = CodePointMapData::<Sb>::new();
    let classes: Vec<Sb> = text.iter().map(|s| map.get(s.character)).collect();
    let mut breaks = Vec::new();
    let mut significant: Vec<Sb> = Vec::new();
    for index in 0..text.len() {
        let class = classes[index];
        if !ignorable_sentence(class) || significant.is_empty() {
            significant.push(class);
        }
        if index + 1 == text.len() {
            breaks.push(index);
            break;
        }
        let next = classes[index + 1];
        if class == Sb::CR && next == Sb::LF {
            continue;
        }
        if paragraph_separator(class) {
            breaks.push(index);
            significant.clear();
            continue;
        }
        if ignorable_sentence(next) {
            continue;
        }
        if !sentence_joined(&significant, &classes, index + 1) {
            breaks.push(index);
            significant.clear();
        }
    }
    breaks
}

/// Whether a word segment has a letter or digit in it, as opposed to being
/// whitespace or punctuation.
fn is_word_like(text: &[Scalar]) -> bool {
    let categories = CodePointMapData::<GeneralCategory>::new();
    text.iter().any(|scalar| {
        matches!(
            categories.get(scalar.character),
            GeneralCategory::UppercaseLetter
                | GeneralCategory::LowercaseLetter
                | GeneralCategory::TitlecaseLetter
                | GeneralCategory::ModifierLetter
                | GeneralCategory::OtherLetter
                | GeneralCategory::DecimalNumber
                | GeneralCategory::LetterNumber
                | GeneralCategory::OtherNumber
        )
    })
}

/// Segment ends for `input`, in UTF-16 code units.
pub(super) fn boundaries(
    granularity: SegmenterGranularity,
    input: &[u16],
) -> Vec<ProviderSegmentBoundary> {
    let text = scalars(input);
    let breaks = match granularity {
        SegmenterGranularity::Grapheme => grapheme_breaks(&text),
        SegmenterGranularity::Word => word_breaks(&text),
        SegmenterGranularity::Sentence => sentence_breaks(&text),
    };
    let mut start = 0;
    breaks
        .into_iter()
        .map(|index| {
            let boundary = ProviderSegmentBoundary {
                end: text[index].end,
                is_word_like: is_word_like(&text[start..=index]),
            };
            start = index + 1;
            boundary
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ends(granularity: SegmenterGranularity, text: &str) -> Vec<usize> {
        let units: Vec<u16> = text.encode_utf16().collect();
        boundaries(granularity, &units)
            .iter()
            .map(|boundary| boundary.end)
            .collect()
    }

    #[test]
    fn words_break_around_spaces_and_keep_numbers_and_contractions_whole() {
        assert_eq!(ends(SegmenterGranularity::Word, "123 "), [3, 4]);
        assert_eq!(ends(SegmenterGranularity::Word, "can't stop"), [5, 6, 10]);
        assert_eq!(ends(SegmenterGranularity::Word, "3.14"), [4]);
    }
}
