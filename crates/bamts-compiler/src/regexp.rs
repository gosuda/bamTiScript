use std::collections::BTreeSet;

#[derive(Clone, Copy)]
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
    let mut parser = Parser {
        units: pattern,
        pos: 0,
        mode,
    };
    parser.parse_top()
}

struct Parser<'a> {
    units: &'a [u16],
    pos: usize,
    mode: RegexMode,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<u16> {
        self.units.get(self.pos).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<u16> {
        self.units.get(self.pos + offset).copied()
    }

    fn parse_top(&mut self) -> Option<String> {
        if let Some(message) = self.parse_disjunction() {
            return Some(message);
        }
        if self.pos != self.units.len() {
            return Some(format!("invalid regular expression"));
        }
        None
    }

    fn parse_disjunction(&mut self) -> Option<String> {
        loop {
            if let Some(message) = self.parse_alternative() {
                return Some(message);
            }
            if self.peek() == Some(0x7C) {
                self.pos += 1;
                continue;
            }
            return None;
        }
    }

    fn parse_alternative(&mut self) -> Option<String> {
        loop {
            match self.peek() {
                None | Some(0x7C) | Some(0x29) => return None,
                _ => {}
            }
            if let Some(message) = self.parse_term() {
                return Some(message);
            }
        }
    }

    fn parse_term(&mut self) -> Option<String> {
        match self.peek() {
            Some(0x28) => self.parse_group(),
            Some(0x5B) => self.parse_class(),
            Some(0x5C) => self.parse_escape(),
            Some(0x29) => Some(format!("invalid regular expression")),
            None => None,
            _ => {
                self.pos += 1;
                self.skip_quantifier();
                None
            }
        }
    }

    fn skip_quantifier(&mut self) {
        match self.peek() {
            Some(0x2A) | Some(0x2B) | Some(0x3F) => {
                self.pos += 1;
                if self.peek() == Some(0x3F) {
                    self.pos += 1;
                }
            }
            Some(0x7B) => {
                let start = self.pos;
                self.pos += 1;
                let mut digits = 0;
                while matches!(self.peek(), Some(0x30..=0x39)) {
                    self.pos += 1;
                    digits += 1;
                }
                if digits == 0 {
                    self.pos = start;
                    return;
                }
                if self.peek() == Some(0x2C) {
                    self.pos += 1;
                    while matches!(self.peek(), Some(0x30..=0x39)) {
                        self.pos += 1;
                    }
                }
                if self.peek() != Some(0x7D) {
                    self.pos = start;
                    return;
                }
                self.pos += 1;
                if self.peek() == Some(0x3F) {
                    self.pos += 1;
                }
            }
            _ => {}
        }
    }

    fn parse_group(&mut self) -> Option<String> {
        self.pos += 1;
        if self.peek() != Some(0x3F) {
            if let Some(message) = self.parse_disjunction() {
                return Some(message);
            }
            if self.peek() != Some(0x29) {
                return Some(format!("invalid regular expression"));
            }
            self.pos += 1;
            self.skip_quantifier();
            return None;
        }
        self.pos += 1;
        match self.peek() {
            Some(0x3A) => {
                self.pos += 1;
                if let Some(message) = self.parse_disjunction() {
                    return Some(message);
                }
                if self.peek() != Some(0x29) {
                    return Some(format!("invalid regular expression"));
                }
                self.pos += 1;
                self.skip_quantifier();
                None
            }
            Some(0x3D) | Some(0x21) => {
                self.pos += 1;
                if let Some(message) = self.parse_disjunction() {
                    return Some(message);
                }
                if self.peek() != Some(0x29) {
                    return Some(format!("invalid regular expression"));
                }
                self.pos += 1;
                self.skip_quantifier();
                None
            }
            Some(0x3C) => {
                if matches!(self.peek_at(1), Some(0x3D) | Some(0x21)) {
                    self.pos += 2;
                    if let Some(message) = self.parse_disjunction() {
                        return Some(message);
                    }
                    if self.peek() != Some(0x29) {
                        return Some(format!("invalid regular expression"));
                    }
                    self.pos += 1;
                    self.skip_quantifier();
                    return None;
                }
                self.parse_named_group()
            }
            _ => self.parse_modifiers(),
        }
    }

    fn parse_named_group(&mut self) -> Option<String> {
        self.pos += 1;
        while let Some(unit) = self.peek() {
            if unit == 0x3E {
                self.pos += 1;
                break;
            }
            if unit == 0x29 || unit == 0x2F {
                return Some(format!("invalid regular expression"));
            }
            self.pos += 1;
        }
        if let Some(message) = self.parse_disjunction() {
            return Some(message);
        }
        if self.peek() != Some(0x29) {
            return Some(format!("invalid regular expression"));
        }
        self.pos += 1;
        self.skip_quantifier();
        None
    }

    fn parse_modifiers(&mut self) -> Option<String> {
        let first_start = self.pos;
        while let Some(unit) = self.peek() {
            if unit == 0x2D || unit == 0x3A || unit == 0x29 {
                break;
            }
            self.pos += 1;
        }
        let first: Vec<u16> = self.units[first_start..self.pos].to_vec();
        let mut second = Vec::new();
        let has_dash = self.peek() == Some(0x2D);
        if has_dash {
            self.pos += 1;
            let second_start = self.pos;
            while let Some(unit) = self.peek() {
                if unit == 0x3A || unit == 0x29 {
                    break;
                }
                self.pos += 1;
            }
            second = self.units[second_start..self.pos].to_vec();
        }
        if self.peek() != Some(0x3A) {
            return Some(format!("invalid regular expression"));
        }
        if has_dash {
            if let Some(message) = validate_paired_modifiers(&first, &second) {
                return Some(message);
            }
        } else if let Some(message) = validate_single_modifier(&first) {
            return Some(message);
        }
        self.pos += 1;
        if let Some(message) = self.parse_disjunction() {
            return Some(message);
        }
        if self.peek() != Some(0x29) {
            return Some(format!("invalid regular expression"));
        }
        self.pos += 1;
        self.skip_quantifier();
        None
    }
    fn parse_class(&mut self) -> Option<String> {
        self.pos += 1;
        if self.peek() == Some(0x5E) {
            self.pos += 1;
        }
        if matches!(self.mode, RegexMode::UnicodeSets) {
            return self.parse_class_sets();
        }
        loop {
            match self.peek() {
                None => return Some(format!("invalid regular expression")),
                Some(0x5D) => {
                    self.pos += 1;
                    break;
                }
                Some(0x5C) => {
                    self.pos += 1;
                    if self.peek().is_none() {
                        return Some(format!("invalid regular expression"));
                    }
                    self.pos += 1;
                }
                _ => {
                    self.pos += 1;
                }
            }
        }
        self.skip_quantifier();
        None
    }

    fn parse_class_sets(&mut self) -> Option<String> {
        let mut depth = 1;
        loop {
            match self.peek() {
                None => return Some(format!("invalid regular expression")),
                Some(0x5D) => {
                    self.pos += 1;
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                Some(0x5B) => {
                    self.pos += 1;
                    depth += 1;
                }
                Some(0x5C) => {
                    self.pos += 1;
                    if self.peek().is_none() {
                        return Some(format!("invalid regular expression"));
                    }
                    self.pos += 1;
                }
                _ => {
                    self.pos += 1;
                }
            }
        }
        self.skip_quantifier();
        None
    }

    fn parse_escape(&mut self) -> Option<String> {
        self.pos += 1;
        if self.peek().is_none() {
            return Some(format!("invalid regular expression"));
        }
        self.pos += 1;
        self.skip_quantifier();
        None
    }
}

fn validate_single_modifier(first: &[u16]) -> Option<String> {
    if first.is_empty() {
        return Some(format!("invalid regular expression"));
    }
    check_modifier_list(first).map(|_| format!("invalid regular expression"))
}

fn validate_paired_modifiers(first: &[u16], second: &[u16]) -> Option<String> {
    if first.is_empty() && second.is_empty() {
        return Some(format!("invalid regular expression"));
    }
    if check_modifier_list(first).is_some() {
        return Some(format!("invalid regular expression"));
    }
    if check_modifier_list(second).is_some() {
        return Some(format!("invalid regular expression"));
    }
    if first.iter().any(|unit| second.contains(unit)) {
        return Some(format!("invalid regular expression"));
    }
    None
}

fn check_modifier_list(flags: &[u16]) -> Option<()> {
    if flags.iter().any(|unit| !matches!(unit, 0x69 | 0x6D | 0x73)) {
        return Some(());
    }
    let mut seen = BTreeSet::new();
    for unit in flags {
        if !seen.insert(unit) {
            return Some(());
        }
    }
    None
}
