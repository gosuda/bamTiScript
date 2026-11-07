//! TransformCase: `String.prototype.toLocaleUpperCase` and `toLocaleLowerCase`.
//!
//! The Unicode Character Database itself carries the language-sensitive case
//! mappings, in SpecialCasing.txt, for exactly three languages, so these need
//! no locale data. Everything else is the default case conversion.

use bamts_bytecode::{EcmaString, EcmaStringBuilder};
use bamts_native::Value;
use icu_properties::CodePointSetData;
use icu_properties::props::{CaseIgnorable, Cased, SoftDotted};
use unicode_normalization::char::canonical_combining_class;

use super::super::allocate_string;
use super::options::canonicalize_locale_list;
use crate::intrinsics::BuiltinOutcome;
use crate::{EvalFailure, Host, Machine};

const CAPITAL_I: u32 = 0x49;
const CAPITAL_J: u32 = 0x4A;
const SMALL_I: u32 = 0x69;
const SMALL_J: u32 = 0x6A;
const DOTLESS_SMALL_I: u32 = 0x131;
const DOTTED_CAPITAL_I: u32 = 0x130;
const CAPITAL_I_OGONEK: u32 = 0x12E;
const SMALL_I_OGONEK: u32 = 0x12F;
const CAPITAL_I_GRAVE: u32 = 0xCC;
const CAPITAL_I_ACUTE: u32 = 0xCD;
const CAPITAL_I_TILDE: u32 = 0x128;
const COMBINING_DOT_ABOVE: u32 = 0x307;
const COMBINING_GRAVE: u32 = 0x300;
const COMBINING_ACUTE: u32 = 0x301;
const COMBINING_TILDE: u32 = 0x303;
const CAPITAL_SIGMA: u32 = 0x3A3;
const FINAL_SIGMA: u32 = 0x3C2;
/// The canonical combining class of marks written above the base.
const CLASS_ABOVE: u8 = 230;

/// Which language-sensitive mappings of SpecialCasing.txt apply.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Tailoring {
    Default,
    Turkic,
    Lithuanian,
}

/// The case to convert to.
#[derive(Clone, Copy, Eq, PartialEq)]
pub(in crate::intrinsics::builtins) enum TargetCase {
    Upper,
    Lower,
}

fn tailoring_of(locale: Option<&String>) -> Tailoring {
    let language = locale.map_or("", |tag| tag.split('-').next().unwrap_or(""));
    match language {
        "tr" | "az" => Tailoring::Turkic,
        "lt" => Tailoring::Lithuanian,
        _ => Tailoring::Default,
    }
}

fn combining_class(code_point: u32) -> u8 {
    char::from_u32(code_point).map_or(0, canonical_combining_class)
}

/// The nearest code point among `candidates` that a combining sequence's
/// conditions stop at: a base, or a mark above.
fn anchor(points: &[u32], mut candidates: impl Iterator<Item = usize>) -> Option<u32> {
    candidates.find_map(|index| {
        let point = points[index];
        matches!(combining_class(point), 0 | CLASS_ABOVE).then_some(point)
    })
}

fn preceding_anchor(points: &[u32], index: usize) -> Option<u32> {
    anchor(points, (0..index).rev())
}

fn following_anchor(points: &[u32], index: usize) -> Option<u32> {
    anchor(points, index + 1..points.len())
}

fn after_capital_i(points: &[u32], index: usize) -> bool {
    preceding_anchor(points, index) == Some(CAPITAL_I)
}

fn before_dot(points: &[u32], index: usize) -> bool {
    following_anchor(points, index) == Some(COMBINING_DOT_ABOVE)
}

fn more_above(points: &[u32], index: usize) -> bool {
    following_anchor(points, index).is_some_and(|point| combining_class(point) == CLASS_ABOVE)
}

fn after_soft_dotted(points: &[u32], index: usize) -> bool {
    preceding_anchor(points, index)
        .is_some_and(|point| CodePointSetData::new::<SoftDotted>().contains32(point))
}

/// Final_Sigma: a cased letter comes before, skipping case-ignorable code
/// points, and none comes after.
fn is_final_sigma(points: &[u32], index: usize) -> bool {
    let cased = CodePointSetData::new::<Cased>();
    let ignorable = CodePointSetData::new::<CaseIgnorable>();
    let significant = |point: &&u32| !ignorable.contains32(**point);
    let before = points[..index].iter().rev().find(significant);
    let after = points[index + 1..].iter().find(significant);
    before.is_some_and(|point| cased.contains32(*point))
        && !after.is_some_and(|point| cased.contains32(*point))
}

/// The tailored lower case of the code point at `index`, if it has one.
fn tailored_lower(tailoring: Tailoring, points: &[u32], index: usize) -> Option<&'static [u32]> {
    let point = points[index];
    match tailoring {
        Tailoring::Default => None,
        Tailoring::Turkic => match point {
            DOTTED_CAPITAL_I => Some(&[SMALL_I]),
            COMBINING_DOT_ABOVE if after_capital_i(points, index) => Some(&[]),
            CAPITAL_I if !before_dot(points, index) => Some(&[DOTLESS_SMALL_I]),
            _ => None,
        },
        Tailoring::Lithuanian => match point {
            CAPITAL_I if more_above(points, index) => Some(&[SMALL_I, COMBINING_DOT_ABOVE]),
            CAPITAL_J if more_above(points, index) => Some(&[SMALL_J, COMBINING_DOT_ABOVE]),
            CAPITAL_I_OGONEK if more_above(points, index) => {
                Some(&[SMALL_I_OGONEK, COMBINING_DOT_ABOVE])
            }
            CAPITAL_I_GRAVE => Some(&[SMALL_I, COMBINING_DOT_ABOVE, COMBINING_GRAVE]),
            CAPITAL_I_ACUTE => Some(&[SMALL_I, COMBINING_DOT_ABOVE, COMBINING_ACUTE]),
            CAPITAL_I_TILDE => Some(&[SMALL_I, COMBINING_DOT_ABOVE, COMBINING_TILDE]),
            _ => None,
        },
    }
}

/// The tailored upper case of the code point at `index`, if it has one.
fn tailored_upper(tailoring: Tailoring, points: &[u32], index: usize) -> Option<&'static [u32]> {
    match (tailoring, points[index]) {
        (Tailoring::Turkic, SMALL_I) => Some(&[DOTTED_CAPITAL_I]),
        (Tailoring::Lithuanian, COMBINING_DOT_ABOVE) if after_soft_dotted(points, index) => {
            Some(&[])
        }
        _ => None,
    }
}

fn push_point(output: &mut EcmaStringBuilder, point: u32) {
    output
        .push_code_point(point)
        .expect("case mappings produce valid code points");
}

fn convert(source: &EcmaString, tailoring: Tailoring, target: TargetCase) -> EcmaString {
    let points: Vec<u32> = source.code_points().map(|(_, point)| point).collect();
    let mut output = EcmaStringBuilder::new();
    for (index, &point) in points.iter().enumerate() {
        let tailored = match target {
            TargetCase::Upper => tailored_upper(tailoring, &points, index),
            TargetCase::Lower => tailored_lower(tailoring, &points, index),
        };
        if let Some(mapped) = tailored {
            for &code_point in mapped {
                push_point(&mut output, code_point);
            }
            continue;
        }
        let Some(character) = char::from_u32(point) else {
            output.push_unit(point as u16);
            continue;
        };
        match target {
            TargetCase::Upper => {
                for mapped in character.to_uppercase() {
                    push_point(&mut output, mapped as u32);
                }
            }
            TargetCase::Lower if point == CAPITAL_SIGMA && is_final_sigma(&points, index) => {
                push_point(&mut output, FINAL_SIGMA);
            }
            TargetCase::Lower => {
                for mapped in character.to_lowercase() {
                    push_point(&mut output, mapped as u32);
                }
            }
        }
    }
    output.finish()
}

/// TransformCase, after the receiver has become a string.
pub(in crate::intrinsics::builtins) fn transform_case<H: Host>(
    machine: &mut Machine<'_, H>,
    source: &EcmaString,
    locales: Value,
    target: TargetCase,
) -> Result<BuiltinOutcome, EvalFailure> {
    let requested = canonicalize_locale_list(machine, locales)?;
    let converted = convert(source, tailoring_of(requested.first()), target);
    allocate_string(machine, converted).map(BuiltinOutcome::Value)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cased(text: &str, tailoring: Tailoring, target: TargetCase) -> String {
        convert(&EcmaString::encode(text), tailoring, target).to_utf8_lossy()
    }

    #[test]
    fn languages_choose_their_tailoring_by_primary_subtag() {
        let tailoring = |tag: &str| tailoring_of(Some(&tag.to_owned()));
        assert!(tailoring("tr-TR") == Tailoring::Turkic);
        assert!(tailoring("az-Cyrl") == Tailoring::Turkic);
        assert!(tailoring("lt") == Tailoring::Lithuanian);
        assert!(tailoring("trv") == Tailoring::Default);
        assert!(tailoring_of(None) == Tailoring::Default);
    }

    #[test]
    fn turkic_dots_follow_the_letter() {
        let lower = |text| cased(text, Tailoring::Turkic, TargetCase::Lower);
        assert_eq!(lower("I"), "\u{131}");
        assert_eq!(lower("I\u{307}"), "i");
        assert_eq!(lower("\u{130}"), "i");
        assert_eq!(cased("i", Tailoring::Turkic, TargetCase::Upper), "\u{130}");
        assert_eq!(cased("i", Tailoring::Default, TargetCase::Upper), "I");
    }

    #[test]
    fn lithuanian_keeps_the_dot_under_accents() {
        let lower = |text| cased(text, Tailoring::Lithuanian, TargetCase::Lower);
        assert_eq!(lower("I"), "i");
        assert_eq!(lower("I\u{300}"), "i\u{307}\u{300}");
        assert_eq!(lower("\u{CC}"), "i\u{307}\u{300}");
        assert_eq!(
            cased("i\u{307}", Tailoring::Lithuanian, TargetCase::Upper),
            "I"
        );
    }

    #[test]
    fn sigma_is_final_only_at_the_end_of_a_word() {
        let lower = |text| cased(text, Tailoring::Default, TargetCase::Lower);
        assert_eq!(lower("A\u{3A3}"), "a\u{3C2}");
        assert_eq!(lower("A\u{3A3}B"), "a\u{3C3}b");
        assert_eq!(lower("\u{3A3}"), "\u{3C3}");
        assert_eq!(lower("A.\u{3A3}"), "a.\u{3C2}");
    }
}
