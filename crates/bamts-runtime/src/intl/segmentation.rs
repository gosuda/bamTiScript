//! UAX #29 text segmentation over UTF-16, from Unicode property data.

use icu_properties::props::{
    ExtendedPictographic, GeneralCategory, GraphemeClusterBreak, IndicConjunctBreak, SentenceBreak,
    WordBreak,
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
    use IndicConjunctBreak as Incb;
    let classes = CodePointMapData::<Gcb>::new();
    let conjuncts = CodePointMapData::<Incb>::new();
    let pictographic = CodePointSetData::new::<ExtendedPictographic>();
    let mut breaks = Vec::new();
    // A pictograph and any Extend after it, which one ZWJ can join to the next.
    let mut pictographic_run = false;
    // A consonant and any Extend or Linker after it. With a Linker among them, the
    // run joins the next consonant.
    let mut consonant_run = false;
    let mut linked = false;
    let mut indicators = 0_usize;
    for (index, scalar) in text.iter().enumerate() {
        let class = classes.get(scalar.character);
        let joining_zwj = class == Gcb::ZWJ && pictographic_run;
        pictographic_run =
            pictographic.contains(scalar.character) || (pictographic_run && class == Gcb::Extend);
        match conjuncts.get(scalar.character) {
            Incb::Consonant => (consonant_run, linked) = (true, false),
            Incb::Linker => linked = consonant_run,
            Incb::Extend => {}
            _ => (consonant_run, linked) = (false, false),
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
            _ if linked && conjuncts.get(next.character) == Incb::Consonant => true,
            (Gcb::ZWJ, _) if joining_zwj && pictographic.contains(next.character) => true,
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

/// What the rules SB6 to SB11 need from the text before a boundary: the last
/// terminator, where only Close and then Sp follow it. A code point that is Extend or
/// Format is not in it, except the first of a sentence.
#[derive(Clone, Copy, Default)]
struct SentenceTail {
    last: Option<SentenceBreak>,
    /// The terminator, and the code point before it.
    terminator: Option<(SentenceBreak, Option<SentenceBreak>)>,
    closed: bool,
    spaced: bool,
}

impl SentenceTail {
    fn push(&mut self, class: SentenceBreak) {
        use SentenceBreak as Sb;
        match class {
            Sb::ATerm | Sb::STerm => {
                self.terminator = Some((class, self.last));
                self.closed = false;
                self.spaced = false;
            }
            Sb::Close if self.terminator.is_some() && !self.spaced => self.closed = true,
            Sb::Sp if self.terminator.is_some() => self.spaced = true,
            _ => self.terminator = None,
        }
        self.last = Some(class);
    }
}

/// The rules SB6 to SB11, for a boundary before a code point of class `first`.
/// `lower_follows` is whether SB8 finds a lowercase letter from there on.
fn sentence_joined(tail: &SentenceTail, first: SentenceBreak, lower_follows: bool) -> bool {
    use SentenceBreak as Sb;
    let Some((terminator, before_terminator)) = tail.terminator else {
        return true;
    };
    let adjacent = !tail.closed && !tail.spaced;
    if terminator == Sb::ATerm {
        if adjacent && first == Sb::Numeric {
            return true;
        }
        if adjacent
            && first == Sb::Upper
            && matches!(before_terminator, Some(Sb::Upper | Sb::Lower))
        {
            return true;
        }
        if lower_follows {
            return true;
        }
    }
    if matches!(first, Sb::SContinue | Sb::ATerm | Sb::STerm) {
        return true;
    }
    if !tail.spaced && matches!(first, Sb::Close | Sb::Sp) {
        return true;
    }
    if tail.spaced && first == Sb::Sp {
        return true;
    }
    // SB9 and SB10: a paragraph separator stays with the terminator before it,
    // with or without Close and Sp between them.
    paragraph_separator(first)
}

/// For each position, whether the first code point from there on that ends the
/// scan of SB8 is a lowercase letter. One pass from the end gives every answer, so
/// a boundary check does not read the rest of the text.
fn lowercase_follows(classes: &[SentenceBreak]) -> Vec<bool> {
    use SentenceBreak as Sb;
    let mut follows = vec![false; classes.len() + 1];
    for index in (0..classes.len()).rev() {
        follows[index] = match classes[index] {
            Sb::Lower => true,
            Sb::OLetter | Sb::Upper | Sb::Sep | Sb::CR | Sb::LF | Sb::ATerm | Sb::STerm => false,
            _ => follows[index + 1],
        };
    }
    follows
}

fn sentence_breaks(text: &[Scalar]) -> Vec<usize> {
    use SentenceBreak as Sb;
    let map = CodePointMapData::<Sb>::new();
    let classes: Vec<Sb> = text.iter().map(|s| map.get(s.character)).collect();
    let lower_follows = lowercase_follows(&classes);
    let mut breaks = Vec::new();
    let mut tail = SentenceTail::default();
    for index in 0..text.len() {
        let class = classes[index];
        if !ignorable_sentence(class) || tail.last.is_none() {
            tail.push(class);
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
            tail = SentenceTail::default();
            continue;
        }
        if ignorable_sentence(next) {
            continue;
        }
        if !sentence_joined(&tail, next, lower_follows[index + 1]) {
            breaks.push(index);
            tail = SentenceTail::default();
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
    fn one_zwj_after_a_pictograph_joins_the_next_pictograph() {
        let grapheme = |text| ends(SegmenterGranularity::Grapheme, text);
        assert_eq!(grapheme("\u{1F468}\u{200D}\u{1F469}"), [5]);
        assert_eq!(grapheme("\u{1F468}\u{301}\u{200D}\u{1F469}"), [6]);
        assert_eq!(grapheme("\u{1F468}\u{200D}\u{200D}\u{1F469}"), [4, 6]);
        assert_eq!(grapheme("\u{1F468}\u{200D}\u{301}\u{1F469}"), [4, 6]);
    }

    #[test]
    fn a_linker_joins_two_consonants_into_one_conjunct() {
        let grapheme = |text| ends(SegmenterGranularity::Grapheme, text);
        // Ka, virama, ssa.
        assert_eq!(grapheme("\u{915}\u{94D}\u{937}"), [3]);
        // Extend and more Linkers can stand on both sides of the Linker.
        assert_eq!(grapheme("\u{915}\u{200D}\u{94D}\u{937}"), [4]);
        assert_eq!(grapheme("\u{915}\u{94D}\u{200D}\u{937}"), [4]);
        assert_eq!(grapheme("\u{915}\u{93C}\u{94D}\u{937}"), [4]);
        assert_eq!(grapheme("\u{915}\u{94D}\u{94D}\u{937}"), [4]);
        // The Linker can come from another script of the rule.
        assert_eq!(grapheme("\u{915}\u{D4D}\u{937}"), [3]);
        // A conjunct can go on, and each link needs its own Linker.
        assert_eq!(grapheme("\u{915}\u{94D}\u{937}\u{94D}\u{915}"), [5]);
        assert_eq!(grapheme("\u{915}\u{94D}\u{937}\u{915}"), [3, 4]);
        // No Linker, no consonant after it, or no consonant before it.
        assert_eq!(grapheme("\u{915}\u{937}"), [1, 2]);
        assert_eq!(grapheme("\u{915}\u{94D}\u{905}"), [2, 3]);
        assert_eq!(grapheme("\u{915}\u{94D}\u{E01}"), [2, 3]);
        assert_eq!(grapheme("\u{905}\u{94D}\u{937}"), [2, 3]);
    }

    #[test]
    fn words_break_around_spaces_and_keep_numbers_and_contractions_whole() {
        assert_eq!(ends(SegmenterGranularity::Word, "123 "), [3, 4]);
        assert_eq!(ends(SegmenterGranularity::Word, "can't stop"), [5, 6, 10]);
        assert_eq!(ends(SegmenterGranularity::Word, "3.14"), [4]);
    }

    /// SB9 and SB10: a paragraph separator ends the sentence of the terminator
    /// before it, also with nothing between them. The ends are those of Node.
    #[test]
    fn a_paragraph_separator_stays_with_the_terminator_before_it() {
        let sentence = |text| ends(SegmenterGranularity::Sentence, text);
        assert_eq!(sentence("Hello!\nWorld"), [7, 12]);
        assert_eq!(sentence("Hello.\nWorld"), [7, 12]);
        assert_eq!(sentence("Hello.\r\nWorld"), [8, 13]);
        assert_eq!(sentence("Hello?\n\nWorld"), [7, 8, 13]);
        assert_eq!(sentence("Hello.\u{2029}World"), [7, 12]);
        assert_eq!(sentence("Hello.\u{85}World"), [7, 12]);
        assert_eq!(sentence("a.\nb.\nc"), [3, 6, 7]);
        assert_eq!(sentence("Hi.\n"), [4]);
        assert_eq!(sentence("3.\n4"), [3, 4]);
        assert_eq!(sentence("e.g.\nfoo"), [5, 8]);
        assert_eq!(sentence("Mr.\nSmith"), [4, 9]);
    }

    /// A boundary check reads neither the text before it nor the text after it
    /// again. Before, this input took time in proportion to the square of its
    /// length, which is minutes for this one.
    #[test]
    fn a_long_run_after_a_terminator_takes_linear_time() {
        for terminator in ['!', '.'] {
            let text = format!("{terminator}{}", " ".repeat(300_000));
            assert_eq!(ends(SegmenterGranularity::Sentence, &text), [300_001]);
        }
    }
}
