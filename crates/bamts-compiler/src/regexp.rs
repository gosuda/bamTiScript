use std::collections::BTreeSet;

enum RegexMode {
    Legacy,
    Unicode,
    UnicodeSets,
}

pub fn validate_regex_literal(literal: &str) -> Option<String> {
    let (head, flags) = literal.rsplit_once('/')?;
    let pattern = head.strip_prefix('/')?;
    let pattern_units: Vec<u16> = pattern.encode_utf16().collect();
    let flag_units: Vec<u16> = flags.encode_utf16().collect();
    if let Some(message) = validate_flags(&flag_units) {
        return Some(message);
    }
    validate_pattern(&pattern_units, mode_for_flags(flags))
}

fn mode_for_flags(flags: &str) -> RegexMode {
    if flags.contains('v') {
        RegexMode::UnicodeSets
    } else if flags.contains('u') {
        RegexMode::Unicode
    } else {
        RegexMode::Legacy
    }
}

fn validate_flags(flags: &[u16]) -> Option<String> {
    let mut seen = BTreeSet::new();
    for &unit in flags {
        let flag = u32::from(unit);
        let valid = matches!(flag, 0x64 | 0x67 | 0x69 | 0x6D | 0x73 | 0x75 | 0x76 | 0x79);
        if !valid {
            return Some(format!("invalid regular expression flag"));
        }
        if !seen.insert(unit) {
            return Some(format!("duplicate regular expression flag"));
        }
    }
    if seen.contains(&0x75) && seen.contains(&0x76) {
        return Some(format!("regular expression flags `u` and `v` cannot be combined"));
    }
    None
}

fn validate_pattern(pattern: &[u16], mode: RegexMode) -> Option<String> {
    validate_disjunction(pattern, mode)
}

fn validate_disjunction(pattern: &[u16], mode: RegexMode) -> Option<String> {
    let _ = mode;
    let _ = pattern;
    None
}
