//! Exact ECMA-262 Unicode property resolution for `\p{...}` and `\P{...}`.
//!
//! Names and values match the ECMA-262 tables with exact, case-sensitive string
//! equality: `General_Category`, `Script`, `Script_Extensions` and their values,
//! the Table 66 binary properties, and the Table 67 properties of strings.
//! ICU "loose" matching is deliberately not used: case, whitespace, `-`, `_` and
//! the `Is` prefix are never normalized away, per the normative note under
//! `UnicodeMatchPropertyValue`. All code-point data comes from the baked ICU4X
//! tables; the properties of strings come from the committed generated tables in
//! `emoji_tables.rs`. No runtime I/O happens here.

use icu_properties::props::{
    Alphabetic, AsciiHexDigit, BidiControl, BidiMirrored, BinaryProperty, CaseIgnorable, Cased,
    ChangesWhenCasefolded, ChangesWhenCasemapped, ChangesWhenLowercased, ChangesWhenNfkcCasefolded,
    ChangesWhenTitlecased, ChangesWhenUppercased, Dash, DefaultIgnorableCodePoint, Deprecated,
    Diacritic, Emoji, EmojiComponent, EmojiModifier, EmojiModifierBase, EmojiPresentation,
    ExtendedPictographic, Extender, GeneralCategory, GeneralCategoryGroup, GraphemeBase,
    GraphemeExtend, HexDigit, IdContinue, IdStart, Ideographic, IdsBinaryOperator,
    IdsTrinaryOperator, JoinControl, LogicalOrderException, Lowercase, Math, NoncharacterCodePoint,
    PatternSyntax, PatternWhiteSpace, QuotationMark, Radical, RegionalIndicator, Script,
    SentenceTerminal, SoftDotted, TerminalPunctuation, UnifiedIdeograph, Uppercase,
    VariationSelector, WhiteSpace, XidContinue, XidStart,
};
use icu_properties::script::ScriptWithExtensionsBorrowed;
use icu_properties::{CodePointMapData, CodePointSetData, PropertyParser};

use super::emoji_tables;
use super::{MAX_CODE_POINT, VError};

/// The result of a Unicode property lookup.
#[derive(Debug)]
pub(super) enum PropertySet {
    /// Single code points only: usable as a pattern atom and as a class operand.
    CodePoints(Vec<(u32, u32)>),
    /// Code points plus multi-code-point strings: usable as a class operand
    /// under `v` only, and never negatable.
    Strings {
        points: Vec<(u32, u32)>,
        strings: Vec<Vec<u32>>,
    },
}

/// The complement of a normalized range set over the whole code point space.
pub(super) fn complement_ranges(ranges: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let mut out = Vec::new();
    let mut cursor = 0u32;
    for &(start, end) in ranges {
        if start > cursor {
            out.push((cursor, start - 1));
        }
        cursor = end.saturating_add(1);
        if cursor > MAX_CODE_POINT {
            break;
        }
    }
    if cursor <= MAX_CODE_POINT {
        out.push((cursor, MAX_CODE_POINT));
    }
    out
}

/// Resolves a property escape after `\p`/`\P`. `unicode_sets` gates the
/// properties of strings behind the `v` flag.
pub(super) fn resolve_property(
    name: &str,
    value: Option<&str>,
    unicode_sets: bool,
) -> Result<PropertySet, VError> {
    if let Some(value) = value {
        let ranges = match name {
            "General_Category" | "gc" => general_category_ranges_for(value)?,
            "Script" | "sc" => script_ranges_for(value)?,
            "Script_Extensions" | "scx" => script_extensions_ranges_for(value)?,
            _ => {
                return Err(VError::new(format!(
                    "invalid Unicode property name '{name}'"
                )));
            }
        };
        return Ok(PropertySet::CodePoints(ranges));
    }
    if let Some(set) = string_property(name) {
        if !unicode_sets {
            return Err(VError::new(format!(
                "the property of strings '{name}' requires the 'v' flag"
            )));
        }
        return Ok(set);
    }
    if let Some(ranges) = binary_property_ranges(name) {
        return Ok(PropertySet::CodePoints(ranges));
    }
    if let Some(ranges) = lone_general_category_ranges(name) {
        return Ok(PropertySet::CodePoints(ranges));
    }
    Err(VError::new(format!(
        "invalid Unicode property escape '\\p{{{name}}}'"
    )))
}

fn ranges(iter: impl Iterator<Item = std::ops::RangeInclusive<u32>>) -> Vec<(u32, u32)> {
    iter.map(|range| (*range.start(), *range.end())).collect()
}

/// `\p{gc=...}`: one strict parse covers the single general categories, the
/// groups `L`, `LC`, `M`, `N`, `P`, `S`, `Z`, `C` and their long aliases.
fn general_category_ranges_for(value: &str) -> Result<Vec<(u32, u32)>, VError> {
    let group = PropertyParser::<GeneralCategoryGroup>::new()
        .get_strict(value)
        .ok_or_else(|| VError::new(format!("invalid Unicode property value '{value}'")))?;
    Ok(ranges(
        CodePointMapData::<GeneralCategory>::new().iter_ranges_for_group(group),
    ))
}

fn lone_general_category_ranges(name: &str) -> Option<Vec<(u32, u32)>> {
    PropertyParser::<GeneralCategoryGroup>::new()
        .get_strict(name)
        .map(|group| {
            ranges(CodePointMapData::<GeneralCategory>::new().iter_ranges_for_group(group))
        })
}

fn script_ranges_for(value: &str) -> Result<Vec<(u32, u32)>, VError> {
    let script = parse_script(value)?;
    Ok(ranges(
        CodePointMapData::<Script>::new().iter_ranges_for_value(script),
    ))
}

fn script_extensions_ranges_for(value: &str) -> Result<Vec<(u32, u32)>, VError> {
    let script = parse_script(value)?;
    Ok(ranges(
        ScriptWithExtensionsBorrowed::new().get_script_extensions_ranges(script),
    ))
}

fn parse_script(value: &str) -> Result<Script, VError> {
    PropertyParser::<Script>::new()
        .get_strict(value)
        .ok_or_else(|| VError::new(format!("invalid Unicode property value '{value}'")))
}

/// The Table 67 properties of strings, backed by the committed generated
/// tables so every one of the seven has a single deterministic owner.
fn string_property(name: &str) -> Option<PropertySet> {
    let property = match name {
        "Basic_Emoji" => emoji_tables::BASIC_EMOJI,
        "Emoji_Keycap_Sequence" => emoji_tables::EMOJI_KEYCAP_SEQUENCE,
        "RGI_Emoji" => emoji_tables::RGI_EMOJI,
        "RGI_Emoji_Flag_Sequence" => emoji_tables::RGI_EMOJI_FLAG_SEQUENCE,
        "RGI_Emoji_Modifier_Sequence" => emoji_tables::RGI_EMOJI_MODIFIER_SEQUENCE,
        "RGI_Emoji_Tag_Sequence" => emoji_tables::RGI_EMOJI_TAG_SEQUENCE,
        "RGI_Emoji_ZWJ_Sequence" => emoji_tables::RGI_EMOJI_ZWJ_SEQUENCE,
        _ => return None,
    };
    Some(PropertySet::Strings {
        points: property.points.to_vec(),
        strings: property
            .strings
            .iter()
            .map(|string| string.to_vec())
            .collect(),
    })
}

/// The Table 66 binary properties, canonical name and alias, each resolved
/// against the baked ICU tables. `Any`, `ASCII` and `Assigned` are computed
/// directly. `ID_Compat_Math_Start` and `ID_Compat_Math_Continue` are absent on
/// purpose: ECMA-262 excludes them even though ICU ships the markers.
fn binary_property_ranges(name: &str) -> Option<Vec<(u32, u32)>> {
    let property = match name {
        "Any" => vec![(0, MAX_CODE_POINT)],
        "ASCII" => vec![(0, 0x7f)],
        "Assigned" => assigned_ranges(),
        "ASCII_Hex_Digit" | "AHex" => marker::<AsciiHexDigit>(),
        "Alphabetic" | "Alpha" => marker::<Alphabetic>(),
        "Bidi_Control" | "Bidi_C" => marker::<BidiControl>(),
        "Bidi_Mirrored" | "Bidi_M" => marker::<BidiMirrored>(),
        "Case_Ignorable" | "CI" => marker::<CaseIgnorable>(),
        "Cased" => marker::<Cased>(),
        "Changes_When_Casefolded" | "CWCF" => marker::<ChangesWhenCasefolded>(),
        "Changes_When_Casemapped" | "CWCM" => marker::<ChangesWhenCasemapped>(),
        "Changes_When_Lowercased" | "CWL" => marker::<ChangesWhenLowercased>(),
        "Changes_When_NFKC_Casefolded" | "CWKCF" => marker::<ChangesWhenNfkcCasefolded>(),
        "Changes_When_Titlecased" | "CWT" => marker::<ChangesWhenTitlecased>(),
        "Changes_When_Uppercased" | "CWU" => marker::<ChangesWhenUppercased>(),
        "Dash" => marker::<Dash>(),
        "Default_Ignorable_Code_Point" | "DI" => marker::<DefaultIgnorableCodePoint>(),
        "Deprecated" | "Dep" => marker::<Deprecated>(),
        "Diacritic" | "Dia" => marker::<Diacritic>(),
        "Emoji" => marker::<Emoji>(),
        "Emoji_Component" | "EComp" => marker::<EmojiComponent>(),
        "Emoji_Modifier" | "EMod" => marker::<EmojiModifier>(),
        "Emoji_Modifier_Base" | "EBase" => marker::<EmojiModifierBase>(),
        "Emoji_Presentation" | "EPres" => marker::<EmojiPresentation>(),
        "Extended_Pictographic" | "ExtPict" => marker::<ExtendedPictographic>(),
        "Extender" | "Ext" => marker::<Extender>(),
        "Grapheme_Base" | "Gr_Base" => marker::<GraphemeBase>(),
        "Grapheme_Extend" | "Gr_Ext" => marker::<GraphemeExtend>(),
        "Hex_Digit" | "Hex" => marker::<HexDigit>(),
        "IDS_Binary_Operator" | "IDSB" => marker::<IdsBinaryOperator>(),
        "IDS_Trinary_Operator" | "IDST" => marker::<IdsTrinaryOperator>(),
        "ID_Continue" | "IDC" => marker::<IdContinue>(),
        "ID_Start" | "IDS" => marker::<IdStart>(),
        "Ideographic" | "Ideo" => marker::<Ideographic>(),
        "Join_Control" | "Join_C" => marker::<JoinControl>(),
        "Logical_Order_Exception" | "LOE" => marker::<LogicalOrderException>(),
        "Lowercase" | "Lower" => marker::<Lowercase>(),
        "Math" => marker::<Math>(),
        "Noncharacter_Code_Point" | "NChar" => marker::<NoncharacterCodePoint>(),
        "Pattern_Syntax" | "Pat_Syn" => marker::<PatternSyntax>(),
        "Pattern_White_Space" | "Pat_WS" => marker::<PatternWhiteSpace>(),
        "Quotation_Mark" | "QMark" => marker::<QuotationMark>(),
        "Radical" => marker::<Radical>(),
        "Regional_Indicator" | "RI" => marker::<RegionalIndicator>(),
        "Sentence_Terminal" | "STerm" => marker::<SentenceTerminal>(),
        "Soft_Dotted" | "SD" => marker::<SoftDotted>(),
        "Terminal_Punctuation" | "Term" => marker::<TerminalPunctuation>(),
        "Unified_Ideograph" | "UIdeo" => marker::<UnifiedIdeograph>(),
        "Uppercase" | "Upper" => marker::<Uppercase>(),
        "Variation_Selector" | "VS" => marker::<VariationSelector>(),
        "White_Space" | "WSpace" | "space" => marker::<WhiteSpace>(),
        "XID_Continue" | "XIDC" => marker::<XidContinue>(),
        "XID_Start" | "XIDS" => marker::<XidStart>(),
        _ => return None,
    };
    Some(property)
}

fn marker<M: BinaryProperty>() -> Vec<(u32, u32)> {
    ranges(CodePointSetData::new::<M>().iter_ranges())
}

/// `Assigned` is the complement of `General_Category = Unassigned`.
fn assigned_ranges() -> Vec<(u32, u32)> {
    complement_ranges(&ranges(
        CodePointMapData::<GeneralCategory>::new()
            .iter_ranges_for_value(GeneralCategory::Unassigned),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn resolve(
        name: &str,
        value: Option<&str>,
        unicode_sets: bool,
    ) -> Result<Vec<(u32, u32)>, String> {
        match resolve_property(name, value, unicode_sets) {
            Ok(PropertySet::CodePoints(ranges)) => Ok(ranges),
            Ok(PropertySet::Strings { .. }) => Err("expected code points".to_owned()),
            Err(error) => Err(error.message().to_owned()),
        }
    }

    #[test]
    fn complement_covers_the_code_point_space() {
        let complement = complement_ranges(&[(10, 20), (30, 40)]);
        assert_eq!(complement, vec![(0, 9), (21, 29), (41, MAX_CODE_POINT)]);
        assert_eq!(
            complement_ranges(&[(0, MAX_CODE_POINT)]),
            Vec::<(u32, u32)>::new()
        );
    }

    #[test]
    fn exact_table_accepts_are_resolved() {
        for name in [
            "ASCII",
            "AHex",
            "space",
            "WSpace",
            "Any",
            "Assigned",
            "Lower",
            "XIDS",
            "Emoji_Presentation",
        ] {
            let ranges = resolve(name, None, false).expect(name);
            assert!(!ranges.is_empty(), "{name} resolves to a nonempty set");
        }
        assert_eq!(resolve("ASCII", None, false), Ok(vec![(0, 0x7f)]));
        assert_eq!(resolve("Any", None, false), Ok(vec![(0, MAX_CODE_POINT)]));
        let uppercase = resolve("Assigned", None, false).expect("assigned");
        assert!(uppercase.windows(2).all(|pair| pair[0].1 < pair[1].0));
        let lu = resolve("gc", Some("Lu"), false).expect("gc=Lu");
        assert!(lu.contains(&(0x41, 0x5a)));
        assert!(resolve("General_Category", Some("Letter"), false).is_ok());
        assert!(resolve("gc", Some("Cased_Letter"), false).is_ok());
        assert!(resolve("L", None, false).is_ok());
        assert!(resolve("Lu", None, false).is_ok());
        assert!(resolve("sc", Some("Grek"), false).is_ok());
        assert!(resolve("Script", Some("Greek"), false).is_ok());
        assert!(resolve("Script_Extensions", Some("Greek"), false).is_ok());
    }

    #[test]
    fn loose_spellings_and_non_table_names_are_rejected() {
        for name in [
            "ascii",
            "LETTER",
            "IsGreek",
            "Greek",
            "ID_Compat_Math_Start",
            "ID_Compat_Math_Continue",
            "script",
            "scx",
            "script_extensions",
            "Scx",
        ] {
            assert!(
                resolve(name, None, false).is_err(),
                "{name} must not resolve"
            );
        }
        assert!(resolve("General_Category ", Some("Lu"), false).is_err());
        assert!(resolve("script", Some("greek"), false).is_err());
        assert!(resolve("Bidi_Class", Some("L"), false).is_err());
        assert!(resolve("sc", Some("greek"), false).is_err());
        assert!(resolve("gc", Some("lu"), false).is_err());
        assert!(resolve("gc", Some("Any"), false).is_err());
    }

    #[test]
    fn script_extensions_cover_the_plain_script() {
        let greek = resolve("sc", Some("Greek"), false).expect("sc=Greek");
        let scx = resolve("scx", Some("Greek"), false).expect("scx=Greek");
        for (start, end) in &greek {
            assert!(
                scx.iter()
                    .any(|(scx_start, scx_end)| scx_start <= start && end <= scx_end),
                "scx must cover {start:#x}-{end:#x}"
            );
        }
    }

    #[test]
    fn string_properties_are_v_only_and_never_empty() {
        for name in [
            "Basic_Emoji",
            "Emoji_Keycap_Sequence",
            "RGI_Emoji",
            "RGI_Emoji_Flag_Sequence",
            "RGI_Emoji_Modifier_Sequence",
            "RGI_Emoji_Tag_Sequence",
            "RGI_Emoji_ZWJ_Sequence",
        ] {
            let error = resolve_property(name, None, false).expect_err("u mode must reject");
            assert!(error.message().contains("requires the 'v' flag"));
            match resolve_property(name, None, true).expect("v mode resolves") {
                PropertySet::Strings { points, strings } => {
                    assert!(
                        !points.is_empty() || !strings.is_empty(),
                        "{name} is nonempty"
                    );
                }
                PropertySet::CodePoints(_) => panic!("{name} must resolve to strings"),
            }
        }
        for name in ["basic_emoji", "rgi_emoji", "RGIE_Moji", "RGI_EMOJI"] {
            assert!(
                resolve_property(name, None, true).is_err(),
                "{name} must not resolve"
            );
        }
    }
}
