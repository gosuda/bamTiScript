//! `v`-mode (`unicodeSets`) and `d`-mode (`hasIndices`) RegExp support.
//!
//! The engine in `intrinsics::regexp` owns exactly one matcher. Its pattern AST
//! (`Node`, `ClassItem`, `CharacterClass`) and its parser are private, and its
//! `Flags` type models neither `v` nor `d`. This module is therefore a front end
//! over that single engine rather than a second one: it parses the full flag set,
//! validates `ClassSetExpression` syntax, resolves set operations and string
//! members at compile time, and lowers the result into a pattern the existing
//! engine already accepts. Matching, backtracking and case folding stay in the
//! engine.
//!
//! Only `v` requires rewriting. `d` changes the shape of the match result and
//! nothing about matching, so a `d`-without-`v` pattern reaches the engine
//! verbatim: rewriting it would both impose v-mode syntax rules that do not
//! apply and emit `\u{...}` escapes the engine only accepts under `u`.

mod emoji_tables;
mod unicode;

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use bamts_bytecode::EcmaString;
use bamts_native::Value;

use super::{allocate_array, allocate_string};
use crate::intrinsics::regexp::{Match, Regex, RegexError, RegexErrorKind, STEP_BUDGET};
use crate::{EvalFailure, HeapEntry, Host, Machine, PropertyMap};

const MAX_CODE_POINT: u32 = 0x10_ffff;

/// A v-mode compilation failure. The engine's `RegexError` cannot be built from
/// outside `intrinsics::regexp`, so this module carries its own error type and
/// the machine-facing entry point turns it into a thrown `SyntaxError`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct VError {
    message: String,
}

impl VError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }

    pub(super) fn message(&self) -> &str {
        &self.message
    }
}

/// The full flag set, including the `d` and `v` flags the engine does not model.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct VFlags {
    pub(super) has_indices: bool,
    pub(super) global: bool,
    pub(super) ignore_case: bool,
    pub(super) multiline: bool,
    pub(super) dot_all: bool,
    pub(super) unicode: bool,
    pub(super) unicode_sets: bool,
    pub(super) sticky: bool,
}

impl VFlags {
    pub(super) fn parse(text: &EcmaString) -> Result<Self, VError> {
        let mut flags = Self::default();
        for unit in text.as_units() {
            let Some(flag) = char::from_u32(u32::from(*unit)).filter(char::is_ascii) else {
                return Err(VError::new("invalid regular expression flag"));
            };
            let slot = match flag {
                'd' => &mut flags.has_indices,
                'g' => &mut flags.global,
                'i' => &mut flags.ignore_case,
                'm' => &mut flags.multiline,
                's' => &mut flags.dot_all,
                'u' => &mut flags.unicode,
                'v' => &mut flags.unicode_sets,
                'y' => &mut flags.sticky,
                _ => {
                    return Err(VError::new(format!(
                        "invalid regular expression flag '{flag}'"
                    )));
                }
            };
            if *slot {
                return Err(VError::new(format!(
                    "duplicate regular expression flag '{flag}'"
                )));
            }
            *slot = true;
        }
        if flags.unicode && flags.unicode_sets {
            return Err(VError::new(
                "the 'u' and 'v' regular expression flags are mutually exclusive",
            ));
        }
        Ok(flags)
    }

    /// Flags in specification order (`dgimsuvy`).
    pub(super) fn canonical(self) -> EcmaString {
        let mut result = bamts_bytecode::EcmaStringBuilder::new();
        for (enabled, flag) in [
            (self.has_indices, b'd'),
            (self.global, b'g'),
            (self.ignore_case, b'i'),
            (self.multiline, b'm'),
            (self.dot_all, b's'),
            (self.unicode, b'u'),
            (self.unicode_sets, b'v'),
            (self.sticky, b'y'),
        ] {
            if enabled {
                result.push_unit(u16::from(flag));
            }
        }
        result.finish()
    }

    /// The subset the engine understands. `v` implies Unicode matching, and `d`
    /// carries no matching behaviour of its own.
    fn engine_flags(self) -> EcmaString {
        let mut result = bamts_bytecode::EcmaStringBuilder::new();
        for (enabled, flag) in [
            (self.global, b'g'),
            (self.ignore_case, b'i'),
            (self.multiline, b'm'),
            (self.dot_all, b's'),
            (self.unicode || self.unicode_sets, b'u'),
            (self.sticky, b'y'),
        ] {
            if enabled {
                result.push_unit(u16::from(flag));
            }
        }
        result.finish()
    }
}

/// A resolved `ClassSetExpression`: a set of code points plus the multi-code-point
/// strings contributed by `\q{...}` and properties of strings.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct ClassSet {
    ranges: Vec<(u32, u32)>,
    strings: BTreeSet<Vec<u32>>,
}

impl ClassSet {
    fn single(value: u32) -> Self {
        Self {
            ranges: vec![(value, value)],
            strings: BTreeSet::new(),
        }
    }

    fn range(start: u32, end: u32) -> Self {
        Self {
            ranges: vec![(start, end)],
            strings: BTreeSet::new(),
        }
    }

    fn from_ranges(ranges: &[(u32, u32)]) -> Self {
        let mut set = Self {
            ranges: ranges.to_vec(),
            strings: BTreeSet::new(),
        };
        set.normalize();
        set
    }

    /// A set "may contain strings" when it holds a member that is not exactly one
    /// code point. `\q{a}` contributes a plain character, not a string.
    fn may_contain_strings(&self) -> bool {
        self.strings.iter().any(|string| string.len() != 1)
    }

    /// Adds a `\q{...}` alternative, folding single-code-point members into the
    /// character ranges where they belong.
    fn push_string(&mut self, string: Vec<u32>) {
        if let [single] = string[..] {
            self.ranges.push((single, single));
            self.normalize();
        } else {
            self.strings.insert(string);
        }
    }

    fn normalize(&mut self) {
        self.ranges.sort_unstable();
        let mut merged: Vec<(u32, u32)> = Vec::with_capacity(self.ranges.len());
        for (start, end) in self.ranges.drain(..) {
            match merged.last_mut() {
                Some(last) if start <= last.1.saturating_add(1) => last.1 = last.1.max(end),
                _ => merged.push((start, end)),
            }
        }
        self.ranges = merged;
    }

    fn union(mut self, other: Self) -> Self {
        self.ranges.extend(other.ranges);
        self.normalize();
        self.strings.extend(other.strings);
        self
    }

    fn intersect(self, other: Self) -> Self {
        let mut ranges = Vec::new();
        for (start, end) in &self.ranges {
            for (other_start, other_end) in &other.ranges {
                let low = *start.max(other_start);
                let high = *end.min(other_end);
                if low <= high {
                    ranges.push((low, high));
                }
            }
        }
        let strings = self.strings.intersection(&other.strings).cloned().collect();
        let mut set = Self { ranges, strings };
        set.normalize();
        set
    }

    fn difference(self, other: Self) -> Self {
        let strings = self.strings.difference(&other.strings).cloned().collect();
        // Complementing `other` ignores its string members, which is right: only
        // its code points can be removed from a code point set.
        let mut set = self.intersect(other.complement());
        set.strings = strings;
        set
    }

    /// Complement over the whole code point space. The caller guarantees the set
    /// cannot contain strings, since complementing those is a syntax error.
    fn complement(&self) -> Self {
        let mut ranges = Vec::new();
        let mut cursor = 0u32;
        for (start, end) in &self.ranges {
            if *start > cursor {
                ranges.push((cursor, start - 1));
            }
            cursor = end.saturating_add(1);
            if cursor > MAX_CODE_POINT {
                break;
            }
        }
        if cursor <= MAX_CODE_POINT {
            ranges.push((cursor, MAX_CODE_POINT));
        }
        Self {
            ranges,
            strings: BTreeSet::new(),
        }
    }

    /// A single code point member, when that is all this set holds.
    fn as_single_code_point(&self) -> Option<u32> {
        match self.ranges[..] {
            [(low, high)] if low == high && self.strings.is_empty() => Some(low),
            _ => None,
        }
    }
}

/// Writes one code point so the engine's Unicode-mode parser reads it back
/// unchanged wherever it lands. Lone surrogates use the four-digit form
/// because the engine rejects the braced `\u{d800}` spelling for them.
fn write_code_point(value: u32, out: &mut String) {
    if (0xd800..=0xdfff).contains(&value) {
        out.push_str(&format!("\\u{value:04X}"));
        return;
    }
    out.push_str("\\u{");
    out.push_str(&format!("{value:x}"));
    out.push('}');
}

fn digit_ranges() -> Vec<(u32, u32)> {
    vec![(0x30, 0x39)]
}

fn word_ranges() -> Vec<(u32, u32)> {
    vec![(0x30, 0x39), (0x41, 0x5a), (0x5f, 0x5f), (0x61, 0x7a)]
}

/// `WhiteSpace` plus `LineTerminator`, matching the engine's `\s`.
fn space_ranges() -> Vec<(u32, u32)> {
    vec![
        (0x09, 0x0d),
        (0x20, 0x20),
        (0x85, 0x85),
        (0xa0, 0xa0),
        (0x1680, 0x1680),
        (0x2000, 0x200a),
        (0x2028, 0x2029),
        (0x202f, 0x202f),
        (0x205f, 0x205f),
        (0x3000, 0x3000),
        (0xfeff, 0xfeff),
    ]
}

/// `ClassSetReservedDoublePunctuator`: forbidden unescaped inside a v-mode class.
const RESERVED_DOUBLE_PUNCTUATORS: &[u8] = b"&!#$%*+,.:;<=>?@^`~";

/// `ClassSetSyntaxCharacter`: must be escaped when used literally in a class.
fn is_class_set_syntax_character(value: u16) -> bool {
    matches!(
        value,
        0x28 | 0x29 | 0x5b | 0x5d | 0x7b | 0x7d | 0x2f | 0x2d | 0x5c | 0x7c
    )
}

fn is_pattern_syntax_character(value: u16) -> bool {
    matches!(
        value,
        0x5e | 0x24
            | 0x5c
            | 0x2e
            | 0x2a
            | 0x2b
            | 0x3f
            | 0x28
            | 0x29
            | 0x5b
            | 0x5d
            | 0x7b
            | 0x7d
            | 0x7c
    )
}

/// A compiled pattern under the full flag set: the engine regex, plus the
/// public-to-internal capture-name mapping that duplicate named groups need.
#[derive(Clone, Debug)]
pub(crate) struct CompiledV {
    regex: Regex,
    flags: VFlags,
    /// Public name in source order, paired with the internal names the lowered
    /// pattern declares. A duplicated public name owns more than one internal
    /// name, at most one of which participates in any single match. Empty for a
    /// pattern that reached the engine verbatim; those names come off the match.
    names: Vec<(String, Vec<String>)>,
}

impl CompiledV {
    pub(super) fn engine_regex(&self) -> &Regex {
        &self.regex
    }

    pub(super) fn exec(
        &self,
        input: &EcmaString,
        start: usize,
    ) -> Result<Option<Match>, RegexError> {
        let Some(mut matched) = self.regex.exec(input, start)? else {
            return Ok(None);
        };
        matched.named = self.public_named(&matched).into_iter().collect();
        Ok(Some(matched))
    }

    /// Resolves every public group name against a match. A duplicated name takes
    /// the range of whichever alternative participated, and stays `None` when no
    /// alternative carrying it took part.
    pub(super) fn public_named(&self, matched: &Match) -> Vec<(String, Option<Range<usize>>)> {
        if self.names.is_empty() {
            return matched
                .named
                .iter()
                .map(|(name, range)| (name.clone(), range.clone()))
                .collect();
        }
        self.names
            .iter()
            .map(|(public, internal)| {
                let resolved = internal.iter().find_map(|name| {
                    let found = matched.named.iter().find(|(known, _)| known == name)?;
                    found.1.clone()
                });
                (public.clone(), resolved)
            })
            .collect()
    }
}

/// Compiles a pattern under the full flag set. `v` uses the class-set parser,
/// `u` rewrites only Unicode property escapes, and legacy patterns remain
/// verbatim so Annex B identity escapes keep their meaning.
pub(super) fn compile_v(pattern: &EcmaString, flags: &EcmaString) -> Result<CompiledV, VError> {
    let flags = VFlags::parse(flags)?;
    let engine_flags = flags.engine_flags();
    if flags.unicode_sets {
        let mut parser = VParser::new(pattern.as_units(), flags);
        parser.parse_disjunction(false)?;
        if parser.position < parser.units.len() {
            return Err(VError::new("unexpected token in regular expression"));
        }
        parser.resolve_pending_references()?;
        let lowered = EcmaString::encode(&parser.out);
        let regex = Regex::compile(&lowered, &engine_flags)
            .map_err(|error| VError::new(error.message().to_owned()))?;
        return Ok(CompiledV {
            regex,
            flags,
            names: parser.ordered_names(),
        });
    }

    let lowered = if flags.unicode {
        rewrite_u_property_escapes(pattern.as_units(), flags.ignore_case)?
    } else {
        None
    };
    let regex = Regex::compile(lowered.as_ref().unwrap_or(pattern), &engine_flags)
        .map_err(|error| VError::new(error.message().to_owned()))?;
    Ok(CompiledV {
        regex,
        flags,
        names: Vec::new(),
    })
}

/// Machine-facing compile that throws a `SyntaxError`, mirroring the non-v path.
pub(super) fn compile<H: Host>(
    machine: &mut Machine<'_, H>,
    pattern: &EcmaString,
    flags: &EcmaString,
) -> Result<CompiledV, EvalFailure> {
    compile_v(pattern, flags).map_err(|error| {
        let id = machine
            .intrinsics
            .builtins
            .id_named("SyntaxError")
            .expect("SyntaxError installed");
        machine.throw_error(id, EcmaString::encode(error.message()))
    })
}

pub(super) fn execution_failure(error: RegexError) -> EvalFailure {
    match error.kind() {
        RegexErrorKind::BudgetExhausted => {
            EvalFailure::Runtime(crate::RuntimeErrorKind::RegexpStepBudgetExceeded {
                limit: STEP_BUDGET,
            })
        }
        RegexErrorKind::Compile => {
            unreachable!("compiled RegExp cannot fail compilation during exec")
        }
    }
}

/// `CreateDataProperty`: the result of a match is built with own properties, so
/// a setter on `Array.prototype` cannot observe it.
pub(super) fn create_result_property<H: Host>(
    machine: &mut Machine<'_, H>,
    array: Value,
    name: &str,
    value: Value,
) -> Result<(), EvalFailure> {
    let key = crate::PropertyKey::Named(machine.intern_str(name));
    machine.create_data_property_key(array, key, value)
}

pub(super) fn plain_object<H: Host>(machine: &mut Machine<'_, H>) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: None,
            extensible: true,
            boxed_primitive: None,
        })
        .map_err(EvalFailure::Runtime)
}

fn range_pair<H: Host>(
    machine: &mut Machine<'_, H>,
    range: Option<&Range<usize>>,
) -> Result<Value, EvalFailure> {
    let Some(range) = range else {
        return Ok(Value::UNDEFINED);
    };
    allocate_array(
        machine,
        vec![
            crate::number_value(range.start as f64),
            crate::number_value(range.end as f64),
        ],
    )
}

/// Builds the match result, adding `indices` under the `d` flag and resolving
/// `groups` through the duplicate-name rules.
pub(super) fn match_array<H: Host>(
    machine: &mut Machine<'_, H>,
    input: &EcmaString,
    compiled: &CompiledV,
    matched: &Match,
) -> Result<Value, EvalFailure> {
    let mut values = Vec::with_capacity(matched.captures.len());
    for capture in &matched.captures {
        values.push(match capture {
            Some(range) => {
                allocate_string(machine, super::regexp::slice_units(input, range.clone()))?
            }
            None => Value::UNDEFINED,
        });
    }
    let array = allocate_array(machine, values)?;
    create_result_property(
        machine,
        array,
        "index",
        crate::number_value(matched.range.start as f64),
    )?;
    let input_value = allocate_string(machine, input.clone())?;
    create_result_property(machine, array, "input", input_value)?;

    let resolved = compiled.public_named(matched);
    let groups = if resolved.is_empty() {
        Value::UNDEFINED
    } else {
        let groups = plain_object(machine)?;
        for (name, range) in &resolved {
            let value = match range {
                Some(range) => {
                    allocate_string(machine, super::regexp::slice_units(input, range.clone()))?
                }
                None => Value::UNDEFINED,
            };
            create_result_property(machine, groups, name, value)?;
        }
        groups
    };
    create_result_property(machine, array, "groups", groups)?;

    if compiled.flags.has_indices {
        let indices = build_indices(machine, matched, &resolved)?;
        create_result_property(machine, array, "indices", indices)?;
    }
    Ok(array)
}

fn build_indices<H: Host>(
    machine: &mut Machine<'_, H>,
    matched: &Match,
    resolved: &[(String, Option<Range<usize>>)],
) -> Result<Value, EvalFailure> {
    let mut entries = Vec::with_capacity(matched.captures.len());
    for capture in &matched.captures {
        entries.push(range_pair(machine, capture.as_ref())?);
    }
    let indices = allocate_array(machine, entries)?;
    let groups = if resolved.is_empty() {
        Value::UNDEFINED
    } else {
        let groups = plain_object(machine)?;
        for (name, range) in resolved {
            let value = range_pair(machine, range.as_ref())?;
            create_result_property(machine, groups, name, value)?;
        }
        groups
    };
    create_result_property(machine, indices, "groups", groups)?;
    Ok(indices)
}

/// The operator seen at one nesting level, used to reject mixed operators.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SetOperator {
    Union,
    Intersection,
    Difference,
}

struct VParser<'a> {
    units: &'a [u16],
    position: usize,
    out: String,
    ignore_case: bool,
    /// Public name to internal names, in first-seen order per public name.
    names: BTreeMap<String, Vec<String>>,
    order: Vec<String>,
    /// `\k<name>` uses recorded before every group is known, with the output
    /// offset where the internal name must be spliced in.
    pending_references: Vec<(String, usize)>,
}

impl<'a> VParser<'a> {
    fn new(units: &'a [u16], flags: VFlags) -> Self {
        Self {
            units,
            position: 0,
            out: String::with_capacity(units.len() * 2),
            ignore_case: flags.ignore_case,
            names: BTreeMap::new(),
            order: Vec::new(),
            pending_references: Vec::new(),
        }
    }

    fn ordered_names(&self) -> Vec<(String, Vec<String>)> {
        self.order
            .iter()
            .map(|name| {
                (
                    name.clone(),
                    self.names.get(name).cloned().unwrap_or_default(),
                )
            })
            .collect()
    }

    fn error(&self, message: impl Into<String>) -> VError {
        VError::new(message)
    }

    fn peek(&self) -> Option<u16> {
        self.units.get(self.position).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<u16> {
        self.units.get(self.position + offset).copied()
    }

    fn next(&mut self) -> Option<u16> {
        let unit = self.peek()?;
        self.position += 1;
        Some(unit)
    }

    fn eat(&mut self, unit: u16) -> bool {
        if self.peek() == Some(unit) {
            self.position += 1;
            true
        } else {
            false
        }
    }

    /// Reads one code point. v mode always combines surrogate pairs.
    fn next_code_point(&mut self) -> Option<u32> {
        let first = self.next()?;
        if (0xd800..=0xdbff).contains(&first)
            && let Some(low) = self.peek()
            && (0xdc00..=0xdfff).contains(&low)
        {
            self.position += 1;
            return Some(
                0x1_0000 + ((u32::from(first) - 0xd800) << 10) + (u32::from(low) - 0xdc00),
            );
        }
        Some(u32::from(first))
    }

    // ---- pattern level ----

    /// Parses a disjunction, returning the union of the names its alternatives
    /// declare. Duplicates across sibling alternatives collapse to one entry.
    fn parse_disjunction(&mut self, in_group: bool) -> Result<Vec<String>, VError> {
        let mut declared: Vec<String> = Vec::new();
        loop {
            for name in self.parse_alternative(in_group)? {
                if !declared.contains(&name) {
                    declared.push(name);
                }
            }
            if self.peek() != Some(u16::from(b'|')) {
                break;
            }
            self.position += 1;
            self.out.push('|');
        }
        Ok(declared)
    }

    /// Parses one alternative. Names declared within a single alternative must be
    /// unique; sibling alternatives may reuse them.
    fn parse_alternative(&mut self, in_group: bool) -> Result<Vec<String>, VError> {
        let mut declared: Vec<String> = Vec::new();
        while let Some(token) = self.peek() {
            if token == u16::from(b'|') {
                break;
            }
            if token == u16::from(b')') {
                if in_group {
                    break;
                }
                return Err(self.error("unmatched ')' in regular expression"));
            }
            for name in self.parse_term()? {
                if declared.contains(&name) {
                    return Err(self.error(format!(
                        "duplicate capture group name '{name}' in the same alternative"
                    )));
                }
                declared.push(name);
            }
        }
        Ok(declared)
    }

    fn parse_term(&mut self) -> Result<Vec<String>, VError> {
        let token = self.peek().ok_or_else(|| self.error("unexpected end"))?;
        match token {
            0x2a | 0x2b | 0x3f => Err(self.error("nothing to repeat")),
            0x7b => Err(self.error(
                "lone quantifier brackets are not allowed in a Unicode-sets regular expression",
            )),
            0x7d | 0x5d => Err(self.error(
                "an unescaped '}' or ']' is not allowed in a Unicode-sets regular expression",
            )),
            0x5e | 0x24 => {
                self.position += 1;
                self.out.push(if token == 0x5e { '^' } else { '$' });
                Ok(Vec::new())
            }
            0x2e => {
                self.position += 1;
                self.out.push('.');
                self.parse_quantifier(false)?;
                Ok(Vec::new())
            }
            0x5b => {
                self.position += 1;
                self.parse_class()?;
                self.parse_quantifier(false)?;
                Ok(Vec::new())
            }
            0x28 => {
                self.position += 1;
                let (names, is_assertion) = self.parse_group()?;
                self.parse_quantifier(is_assertion)?;
                Ok(names)
            }
            0x5c => {
                self.position += 1;
                if self.parse_pattern_escape()? {
                    self.parse_quantifier(false)?;
                }
                Ok(Vec::new())
            }
            _ => {
                let value = self
                    .next_code_point()
                    .ok_or_else(|| self.error("unexpected end"))?;
                write_code_point(value, &mut self.out);
                self.parse_quantifier(false)?;
                Ok(Vec::new())
            }
        }
    }

    /// Parses a group, returning its declared names and whether it is a
    /// lookaround assertion, which may not be quantified.
    fn parse_group(&mut self) -> Result<(Vec<String>, bool), VError> {
        let mut is_assertion = false;
        let mut names = Vec::new();
        if self.eat(u16::from(b'?')) {
            match self.next() {
                Some(0x3a) => self.out.push_str("(?:"),
                Some(0x3d) => {
                    is_assertion = true;
                    self.out.push_str("(?=");
                }
                Some(0x21) => {
                    is_assertion = true;
                    self.out.push_str("(?!");
                }
                Some(0x3c) => match self.peek() {
                    Some(0x3d) => {
                        self.position += 1;
                        is_assertion = true;
                        self.out.push_str("(?<=");
                    }
                    Some(0x21) => {
                        self.position += 1;
                        is_assertion = true;
                        self.out.push_str("(?<!");
                    }
                    _ => {
                        let public = self.parse_group_name()?;
                        let internal = self.declare_group(&public);
                        self.out.push_str("(?<");
                        self.out.push_str(&internal);
                        self.out.push('>');
                        names.push(public);
                    }
                },
                Some(unit @ (0x69 | 0x6d | 0x73 | 0x2d)) => {
                    self.out.push_str("(?");
                    self.out.push(char::from(unit as u8));
                    while self.out.as_bytes().last() != Some(&b':') {
                        let modifier = self
                            .next()
                            .and_then(|unit| u8::try_from(unit).ok())
                            .ok_or_else(|| self.error("invalid group"))?;
                        self.out.push(char::from(modifier));
                    }
                }
                _ => return Err(self.error("invalid group")),
            }
        } else {
            self.out.push('(');
        }
        for name in self.parse_disjunction(true)? {
            if !names.contains(&name) {
                names.push(name);
            }
        }
        if !self.eat(u16::from(b')')) {
            return Err(self.error("unterminated group"));
        }
        self.out.push(')');
        Ok((names, is_assertion))
    }

    fn parse_group_name(&mut self) -> Result<String, VError> {
        let mut name = String::new();
        loop {
            let unit = self
                .next()
                .ok_or_else(|| self.error("unterminated capture group name"))?;
            if unit == 0x3e {
                break;
            }
            let value = char::from_u32(u32::from(unit))
                .ok_or_else(|| self.error("invalid capture group name"))?;
            name.push(value);
        }
        if name.is_empty()
            || !name
                .chars()
                .all(|value| value.is_alphanumeric() || value == '_' || value == '$')
        {
            return Err(self.error("invalid capture group name"));
        }
        Ok(name)
    }

    /// Registers a capture name and returns the internal name to emit. The engine
    /// rejects a repeated name outright, so duplicates get distinct internal
    /// names and are reunited by `CompiledV::public_named`.
    fn declare_group(&mut self, public: &str) -> String {
        let entry = self.names.entry(public.to_owned()).or_default();
        if entry.is_empty() {
            self.order.push(public.to_owned());
            entry.push(public.to_owned());
            return public.to_owned();
        }
        let mut suffix = entry.len();
        loop {
            let candidate = format!("{public}_v{suffix}");
            if !self.names.contains_key(&candidate)
                && !self.names.values().any(|list| list.contains(&candidate))
            {
                self.names
                    .get_mut(public)
                    .expect("name registered")
                    .push(candidate.clone());
                return candidate;
            }
            suffix += 1;
        }
    }

    /// Returns whether the escape produced a quantifiable atom.
    fn parse_pattern_escape(&mut self) -> Result<bool, VError> {
        let escaped = self.next().ok_or_else(|| self.error("trailing escape"))?;
        match escaped {
            0x64 | 0x44 | 0x77 | 0x57 | 0x73 | 0x53 => {
                self.out.push('\\');
                self.out
                    .push(char::from_u32(u32::from(escaped)).expect("ascii escape"));
                Ok(true)
            }
            0x62 | 0x42 => {
                self.out.push('\\');
                self.out
                    .push(char::from_u32(u32::from(escaped)).expect("ascii escape"));
                Ok(false)
            }
            0x70 | 0x50 => {
                let negated = escaped == 0x50;
                let (name, value) = self.parse_property()?;
                match unicode::resolve_property(&name, value.as_deref(), true)? {
                    unicode::PropertySet::CodePoints(ranges) => {
                        // A negated class keeps the engine's fold-then-negate
                        // path, which is the specification's ComplementCharSet
                        // order; materialized complement ranges would fold the
                        // orbit back in under `i`.
                        self.emit_ranges(&ranges, negated);
                        Ok(true)
                    }
                    unicode::PropertySet::Strings { .. } => Err(self.error(format!(
                        "the property of strings '{name}' is only allowed inside a class"
                    ))),
                }
            }
            0x6b => {
                if !self.eat(0x3c) {
                    return Err(self.error("invalid named backreference"));
                }
                let name = self.parse_group_name()?;
                self.out.push_str("\\k<");
                let offset = self.out.len();
                self.out.push('>');
                self.pending_references.push((name, offset));
                Ok(true)
            }
            value if (0x31..=0x39).contains(&value) => {
                self.out.push('\\');
                self.out
                    .push(char::from_u32(u32::from(value)).expect("ascii digit"));
                while let Some(digit) = self.peek().filter(|unit| (0x30..=0x39).contains(unit)) {
                    self.position += 1;
                    self.out
                        .push(char::from_u32(u32::from(digit)).expect("ascii digit"));
                }
                Ok(true)
            }
            value => {
                let code_point = self.escape_code_point(value, false)?;
                write_code_point(code_point, &mut self.out);
                Ok(true)
            }
        }
    }

    /// Splices internal names into the `\k<...>` placeholders once every group is
    /// known. Later offsets shift as earlier ones grow, so this walks backwards.
    fn resolve_pending_references(&mut self) -> Result<(), VError> {
        let mut pending = std::mem::take(&mut self.pending_references);
        pending.sort_by_key(|(_, offset)| std::cmp::Reverse(*offset));
        for (name, offset) in pending {
            let Some(internal) = self.names.get(&name) else {
                return Err(self.error(format!(
                    "backreference to an undefined capture group name '{name}'"
                )));
            };
            if internal.len() > 1 {
                return Err(self.error(format!(
                    "a backreference '\\k<{name}>' to a duplicate capture group name is not \
                     supported by this engine"
                )));
            }
            self.out.insert_str(offset, &internal[0]);
        }
        Ok(())
    }

    fn parse_quantifier(&mut self, is_assertion: bool) -> Result<(), VError> {
        let Some(token) = self.peek() else {
            return Ok(());
        };
        let start = self.position;
        let text = match token {
            0x2a | 0x2b | 0x3f => {
                self.position += 1;
                char::from_u32(u32::from(token))
                    .expect("ascii quantifier")
                    .to_string()
            }
            0x7b => match self.parse_braced_quantifier() {
                Some(text) => text,
                None => {
                    self.position = start;
                    return Err(self.error(
                        "lone quantifier brackets are not allowed in a Unicode-sets regular \
                         expression",
                    ));
                }
            },
            _ => return Ok(()),
        };
        if is_assertion {
            return Err(self.error("a lookaround assertion may not be quantified"));
        }
        self.out.push_str(&text);
        if self.eat(0x3f) {
            self.out.push('?');
        }
        Ok(())
    }

    fn parse_braced_quantifier(&mut self) -> Option<String> {
        let start = self.position;
        self.position += 1;
        let min = match self.parse_decimal() {
            Some(min) => min,
            None => {
                self.position = start;
                return None;
            }
        };
        let max = if self.eat(u16::from(b',')) {
            if self.peek() == Some(0x7d) {
                None
            } else {
                match self.parse_decimal() {
                    Some(max) => Some(max),
                    None => {
                        self.position = start;
                        return None;
                    }
                }
            }
        } else {
            Some(min)
        };
        if !self.eat(0x7d) || max.is_some_and(|max| max < min) {
            self.position = start;
            return None;
        }
        Some(match max {
            Some(max) if max == min => format!("{{{min}}}"),
            Some(max) => format!("{{{min},{max}}}"),
            None => format!("{{{min},}}"),
        })
    }

    fn parse_decimal(&mut self) -> Option<usize> {
        let begin = self.position;
        let mut value = 0usize;
        while let Some(digit) = self.peek().filter(|unit| (0x30..=0x39).contains(unit)) {
            self.position += 1;
            value = value
                .checked_mul(10)?
                .checked_add((u32::from(digit) - 0x30) as usize)?;
        }
        (self.position != begin).then_some(value)
    }

    // ---- class level ----

    /// Parses a class and emits its lowering. The opening `[` is already consumed.
    fn parse_class(&mut self) -> Result<(), VError> {
        let negated = self.eat(0x5e);
        let set = self.parse_class_set_expression()?;
        if !self.eat(0x5d) {
            return Err(self.error("unterminated character class"));
        }
        if negated && set.may_contain_strings() {
            return Err(self.error(
                "a negated character class may not contain strings in a Unicode-sets regular \
                 expression",
            ));
        }
        self.emit_class(&set, negated);
        Ok(())
    }

    /// Emits a resolved set. Large string sets use a prefix-sharing trie; small
    /// literal sets retain their compact longest-first alternation.
    fn emit_class(&mut self, set: &ClassSet, negated: bool) {
        if set.strings.is_empty() {
            self.emit_ranges(&set.ranges, negated);
            return;
        }
        if set.strings.len() > 8 {
            let mut trie = StringTrie::default();
            for string in &set.strings {
                trie.insert(string);
            }
            self.out.push_str("(?:");
            trie.emit(&mut self.out);
            if !set.ranges.is_empty() {
                self.out.push('|');
                self.emit_ranges(&set.ranges, false);
            }
            self.out.push(')');
            return;
        }

        let mut strings: Vec<&Vec<u32>> = set.strings.iter().collect();
        strings.sort_by(|left, right| right.len().cmp(&left.len()).then(left.cmp(right)));
        self.out.push_str("(?:");
        for string in strings {
            for value in string {
                write_code_point(*value, &mut self.out);
            }
            self.out.push('|');
        }
        if set.ranges.is_empty() {
            self.out.pop();
        } else {
            self.emit_ranges(&set.ranges, false);
        }
        self.out.push(')');
    }

    fn emit_ranges(&mut self, ranges: &[(u32, u32)], negated: bool) {
        if ranges.is_empty() {
            // An empty set never matches, and its negation always does.
            self.out.push_str(if negated {
                "[\\u{0}-\\u{10ffff}]"
            } else {
                "[^\\u{0}-\\u{10ffff}]"
            });
            return;
        }
        self.out.push('[');
        if negated {
            self.out.push('^');
        }
        for (start, end) in ranges {
            write_code_point(*start, &mut self.out);
            if end != start {
                self.out.push('-');
                write_code_point(*end, &mut self.out);
            }
        }
        self.out.push(']');
    }

    /// Parses a union, intersection or difference chain. Mixing operators at one
    /// nesting level is a syntax error.
    fn parse_class_set_expression(&mut self) -> Result<ClassSet, VError> {
        if self.peek() == Some(0x5d) {
            return Ok(ClassSet::default());
        }
        let mut result = self.parse_class_set_operand()?;
        let mut operator = None;
        loop {
            let next = match self.peek() {
                None | Some(0x5d) => break,
                Some(token) => token,
            };
            let seen = if next == u16::from(b'&') && self.peek_at(1) == Some(u16::from(b'&')) {
                self.position += 2;
                SetOperator::Intersection
            } else if next == u16::from(b'-') && self.peek_at(1) == Some(u16::from(b'-')) {
                self.position += 2;
                SetOperator::Difference
            } else {
                SetOperator::Union
            };
            match operator {
                Some(previous) if previous != seen => {
                    return Err(self.error(
                        "a character class may not mix union, intersection and difference \
                         operators",
                    ));
                }
                _ => operator = Some(seen),
            }
            if seen != SetOperator::Union && self.peek() == Some(0x5d) {
                return Err(self.error("a set operator requires a right operand"));
            }
            let operand = self.parse_class_set_operand()?;
            result = match seen {
                SetOperator::Union => result.union(operand),
                SetOperator::Intersection => result.intersect(operand),
                SetOperator::Difference => result.difference(operand),
            };
        }
        Ok(result)
    }

    fn parse_class_set_operand(&mut self) -> Result<ClassSet, VError> {
        let token = self
            .peek()
            .ok_or_else(|| self.error("unterminated character class"))?;
        if token == 0x5b {
            self.position += 1;
            let negated = self.eat(0x5e);
            let inner = self.parse_class_set_expression()?;
            if !self.eat(0x5d) {
                return Err(self.error("unterminated character class"));
            }
            if !negated {
                return Ok(inner);
            }
            if inner.may_contain_strings() {
                return Err(self.error(
                    "a negated character class may not contain strings in a Unicode-sets regular \
                     expression",
                ));
            }
            return Ok(inner.complement());
        }
        if token == 0x5c {
            let set = self.parse_class_escape_operand()?;
            // A single-character escape may still open a range: `[\x41-\x43]`.
            return match set.as_single_code_point() {
                Some(value) => self.parse_maybe_range(value),
                None => Ok(set),
            };
        }
        self.reject_reserved_punctuator(token)?;
        if is_class_set_syntax_character(token) {
            let shown = char::from_u32(u32::from(token)).unwrap_or('?');
            return Err(self.error(format!(
                "'{shown}' must be escaped inside a Unicode-sets character class"
            )));
        }
        let start = self
            .next_code_point()
            .ok_or_else(|| self.error("unterminated character class"))?;
        self.parse_maybe_range(start)
    }

    /// Rejects `ClassSetReservedDoublePunctuator` sequences.
    fn reject_reserved_punctuator(&self, token: u16) -> Result<(), VError> {
        if self.peek_at(1) == Some(token)
            && u8::try_from(token).is_ok_and(|byte| RESERVED_DOUBLE_PUNCTUATORS.contains(&byte))
        {
            let shown = char::from_u32(u32::from(token)).unwrap_or('?');
            return Err(VError::new(format!(
                "'{shown}{shown}' is a reserved double punctuator inside a Unicode-sets character \
                 class"
            )));
        }
        Ok(())
    }

    /// Extends a code point into a range when a `-` separator follows. `--` is the
    /// difference operator, and a trailing `-` before `]` is a literal member.
    fn parse_maybe_range(&mut self, start: u32) -> Result<ClassSet, VError> {
        if self.peek() != Some(u16::from(b'-'))
            || self.peek_at(1) == Some(u16::from(b'-'))
            || self.peek_at(1) == Some(0x5d)
        {
            return Ok(ClassSet::single(start));
        }
        self.position += 1;
        let end = if self.peek() == Some(0x5c) {
            self.parse_class_escape_operand()?
                .as_single_code_point()
                .ok_or_else(|| self.error("invalid character class range"))?
        } else {
            let token = self
                .peek()
                .ok_or_else(|| self.error("unterminated character class"))?;
            if is_class_set_syntax_character(token) {
                return Err(self.error("invalid character class range"));
            }
            self.next_code_point()
                .ok_or_else(|| self.error("unterminated character class"))?
        };
        if start > end {
            return Err(self.error("character class range is out of order"));
        }
        Ok(ClassSet::range(start, end))
    }

    fn parse_class_escape_operand(&mut self) -> Result<ClassSet, VError> {
        self.position += 1;
        let escaped = self.next().ok_or_else(|| self.error("trailing escape"))?;
        match escaped {
            0x64 => Ok(ClassSet::from_ranges(&digit_ranges())),
            0x44 => Ok(ClassSet::from_ranges(&digit_ranges()).complement()),
            0x77 => Ok(ClassSet::from_ranges(&word_ranges())),
            0x57 => Ok(ClassSet::from_ranges(&word_ranges()).complement()),
            0x73 => Ok(ClassSet::from_ranges(&space_ranges())),
            0x53 => Ok(ClassSet::from_ranges(&space_ranges()).complement()),
            0x62 => Ok(ClassSet::single(0x08)),
            0x71 => self.parse_string_literal_set(),
            0x70 | 0x50 => {
                let negated = escaped == 0x50;
                let (name, value) = self.parse_property()?;
                match unicode::resolve_property(&name, value.as_deref(), true)? {
                    unicode::PropertySet::CodePoints(ranges) => {
                        let ranges = if negated {
                            let excluded = if self.ignore_case {
                                crate::intrinsics::regexp::unicode_simple_fold_closure(&ranges)
                            } else {
                                ranges
                            };
                            unicode::complement_ranges(&excluded)
                        } else {
                            ranges
                        };
                        Ok(ClassSet::from_ranges(&ranges))
                    }
                    unicode::PropertySet::Strings { points, strings } => {
                        if negated {
                            return Err(self.error(format!(
                                "'\\P{{{name}}}' may not negate a property of strings"
                            )));
                        }
                        let mut set = ClassSet::from_ranges(&points);
                        for string in strings {
                            set.push_string(string);
                        }
                        Ok(set)
                    }
                }
            }
            value => self.escape_code_point(value, true).map(ClassSet::single),
        }
    }

    /// Parses `\q{alt|alt}` string members.
    fn parse_string_literal_set(&mut self) -> Result<ClassSet, VError> {
        if !self.eat(0x7b) {
            return Err(self.error("'\\q' must be followed by '{'"));
        }
        let mut set = ClassSet::default();
        let mut current: Vec<u32> = Vec::new();
        loop {
            let token = self
                .peek()
                .ok_or_else(|| self.error("unterminated '\\q{' string literal"))?;
            match token {
                0x7d => {
                    self.position += 1;
                    set.push_string(current);
                    return Ok(set);
                }
                0x7c => {
                    self.position += 1;
                    set.push_string(std::mem::take(&mut current));
                }
                0x5c => {
                    self.position += 1;
                    let escaped = self.next().ok_or_else(|| self.error("trailing escape"))?;
                    current.push(self.escape_code_point(escaped, true)?);
                }
                _ => {
                    let value = self
                        .next_code_point()
                        .ok_or_else(|| self.error("unterminated '\\q{' string literal"))?;
                    current.push(value);
                }
            }
        }
    }

    /// Parses `{Name}` or `{Name=Value}` after a leading `p` or `P`.
    fn parse_property(&mut self) -> Result<(String, Option<String>), VError> {
        if !self.eat(0x7b) {
            return Err(self.error("a Unicode property escape requires '{'"));
        }
        let mut name = String::new();
        let mut value = None::<String>;
        loop {
            let unit = self
                .next()
                .ok_or_else(|| self.error("unterminated Unicode property escape"))?;
            match unit {
                0x7d => break,
                0x3d if value.is_none() => value = Some(String::new()),
                _ => {
                    let character = char::from_u32(u32::from(unit))
                        .filter(char::is_ascii)
                        .ok_or_else(|| self.error("invalid Unicode property escape"))?;
                    if let Some(value) = &mut value {
                        value.push(character);
                    } else {
                        name.push(character);
                    }
                }
            }
        }
        if name.is_empty() {
            return Err(self.error("invalid Unicode property escape"));
        }
        Ok((name, value))
    }

    /// Decodes a character escape. v mode allows the syntax characters and `/` as
    /// identity escapes, plus the class-set syntax characters inside a class.
    fn escape_code_point(&mut self, escaped: u16, in_class: bool) -> Result<u32, VError> {
        match escaped {
            0x6e => Ok(0x0a),
            0x72 => Ok(0x0d),
            0x74 => Ok(0x09),
            0x66 => Ok(0x0c),
            0x76 => Ok(0x0b),
            0x30 => {
                if self
                    .peek()
                    .is_some_and(|unit| (0x30..=0x39).contains(&unit))
                {
                    return Err(self.error("invalid decimal escape"));
                }
                Ok(0)
            }
            0x63 => {
                let letter = self
                    .peek()
                    .filter(|unit| (0x41..=0x5a).contains(unit) || (0x61..=0x7a).contains(unit))
                    .ok_or_else(|| self.error("invalid control escape"))?;
                self.position += 1;
                Ok(u32::from(letter) % 32)
            }
            0x78 => self.hex_escape(2),
            0x75 if self.peek() == Some(0x7b) => {
                self.position += 1;
                let mut value = 0u32;
                let mut digits = 0usize;
                loop {
                    let unit = self
                        .next()
                        .ok_or_else(|| self.error("invalid Unicode escape"))?;
                    if unit == 0x7d {
                        break;
                    }
                    let digit =
                        hex_digit(unit).ok_or_else(|| self.error("invalid Unicode escape"))?;
                    value = value
                        .checked_mul(16)
                        .and_then(|value| value.checked_add(digit))
                        .ok_or_else(|| self.error("invalid Unicode escape"))?;
                    digits += 1;
                }
                if digits == 0 || value > MAX_CODE_POINT || (0xd800..=0xdfff).contains(&value) {
                    return Err(self.error("invalid Unicode escape"));
                }
                Ok(value)
            }
            0x75 => {
                let first = self.hex_escape(4)?;
                if (0xd800..=0xdbff).contains(&first) {
                    let checkpoint = self.position;
                    if self.eat(0x5c)
                        && self.eat(0x75)
                        && let Ok(second) = self.hex_escape(4)
                        && (0xdc00..=0xdfff).contains(&second)
                    {
                        return Ok(0x1_0000 + ((first - 0xd800) << 10) + (second - 0xdc00));
                    }
                    self.position = checkpoint;
                }
                Ok(first)
            }
            value
                if is_pattern_syntax_character(value)
                    || value == u16::from(b'/')
                    || (in_class && is_class_set_syntax_character(value)) =>
            {
                Ok(u32::from(value))
            }
            value => {
                let shown = char::from_u32(u32::from(value)).unwrap_or('?');
                Err(self.error(format!("invalid identity escape '\\{shown}'")))
            }
        }
    }

    fn hex_escape(&mut self, count: usize) -> Result<u32, VError> {
        if self.position + count > self.units.len() {
            return Err(self.error("invalid hexadecimal escape"));
        }
        let mut value = 0u32;
        for offset in 0..count {
            let digit = hex_digit(self.units[self.position + offset])
                .ok_or_else(|| self.error("invalid hexadecimal escape"))?;
            value = value * 16 + digit;
        }
        self.position += count;
        Ok(value)
    }
}

/// A prefix trie over string-class members. Shared prefixes become shared code
/// so properties such as `RGI_Emoji` lower linearly instead of materializing an
/// exponential member-by-member expansion. Child branches are emitted before a
/// terminal member; when one member prefixes another, the longer member wins.
#[derive(Default)]
struct StringTrie {
    terminal: bool,
    children: BTreeMap<u32, StringTrie>,
}

impl StringTrie {
    fn insert(&mut self, string: &[u32]) {
        let mut node = self;
        for &value in string {
            node = node.children.entry(value).or_default();
        }
        node.terminal = true;
    }

    fn emit(&self, out: &mut String) {
        for (index, (&value, child)) in self.children.iter().enumerate() {
            if index != 0 {
                out.push('|');
            }
            write_code_point(value, out);
            out.push_str("(?:");
            child.emit(out);
            out.push(')');
        }
        if self.terminal && !self.children.is_empty() {
            out.push('|');
        }
    }
}

/// Decodes one code point for the lightweight `u`-mode property rewriter. The
/// engine's full parser validates all other syntax later; a malformed escape
/// without a code point is left alone so its original diagnostic survives.
fn read_u_code_point(units: &[u16], position: usize, text: &mut String) -> Option<(u32, usize)> {
    let unit = *units.get(position)?;
    if (0xd800..=0xdbff).contains(&unit) {
        let low = *units.get(position + 1)?;
        if !(0xdc00..=0xdfff).contains(&low) {
            return None;
        }
        text.push(char::from_u32(u32::from(unit))?);
        text.push(char::from_u32(u32::from(low))?);
        Some((
            0x1_0000 + ((u32::from(unit) - 0xd800) << 10) + (u32::from(low) - 0xdc00),
            2,
        ))
    } else if (0xdc00..=0xdfff).contains(&unit) {
        None
    } else {
        text.push(char::from_u32(u32::from(unit))?);
        Some((u32::from(unit), 1))
    }
}

/// Appends a resolved range. Inside a `u` class the ranges are bare members;
/// outside a class they are wrapped in one character class.
fn write_ranges(ranges: &[(u32, u32)], in_class: bool, out: &mut String) {
    if !in_class {
        out.push('[');
    }
    for &(start, end) in ranges {
        write_code_point(start, out);
        if start != end {
            out.push('-');
            write_code_point(end, out);
        }
    }
    if !in_class {
        out.push(']');
    }
}

/// Rewrites `\p{...}` and `\P{...}` for a `u` pattern into ordinary character
/// classes, preserving every other escaped and literal unit verbatim. String
/// properties and invalid aliases remain exact-match `SyntaxError`s.
fn rewrite_u_property_escapes(
    units: &[u16],
    ignore_case: bool,
) -> Result<Option<EcmaString>, VError> {
    let mut rewritten: Option<String> = None;
    let mut dirty = false;
    let mut position = 0;
    let mut class_depth = 0usize;
    // The previous class atom was a property or class escape, which may not
    // serve as a range endpoint.
    let mut prev_atom_escape = false;
    // No atom has been seen since the class opened, so a `^` is negation.
    let mut class_fresh = false;
    let mut can_start_range = false;
    let mut trailing_range_dash = false;

    while let Some(&unit) = units.get(position) {
        if unit == u16::from(b'\\') {
            let Some(&escaped) = units.get(position + 1) else {
                break;
            };
            if matches!(escaped, 0x70 | 0x50) && units.get(position + 2) == Some(&u16::from(b'{')) {
                let start = position;
                position += 3;
                let mut name = String::new();
                let mut value = None::<String>;
                let mut closed = false;
                while let Some(&unit) = units.get(position) {
                    position += 1;
                    match unit {
                        0x7d => {
                            closed = true;
                            break;
                        }
                        0x3d if value.is_none() => value = Some(String::new()),
                        _ => {
                            let character = char::from_u32(u32::from(unit))
                                .filter(char::is_ascii)
                                .ok_or_else(|| VError::new("invalid Unicode property escape"))?;
                            if let Some(value) = &mut value {
                                value.push(character);
                            } else {
                                name.push(character);
                            }
                        }
                    }
                }
                if !closed || name.is_empty() {
                    return Err(VError::new("invalid Unicode property escape"));
                }
                let ranges = match unicode::resolve_property(&name, value.as_deref(), false)? {
                    unicode::PropertySet::CodePoints(ranges) => ranges,
                    unicode::PropertySet::Strings { .. } => {
                        return Err(VError::new(format!(
                            "the property of strings '{name}' requires the 'v' flag"
                        )));
                    }
                };
                if class_depth > 0 {
                    if trailing_range_dash {
                        return Err(VError::new(
                            "a Unicode class range endpoint must be a single character",
                        ));
                    }
                    trailing_range_dash = false;
                    can_start_range = false;
                    prev_atom_escape = true;
                    class_fresh = false;
                } else {
                    prev_atom_escape = false;
                }
                if rewritten.is_none() {
                    let mut out = String::new();
                    for unit in &units[..start] {
                        if let Some(character) = char::from_u32(u32::from(*unit)) {
                            out.push(character);
                        }
                    }
                    rewritten = Some(out);
                }
                let out = rewritten.as_mut().expect("rewriting buffer");
                if class_depth == 0 {
                    out.push('[');
                    if escaped == 0x50 {
                        // Outside a class, a negated class with the positive
                        // ranges preserves the engine's fold-then-negate path,
                        // which is the specification's ComplementCharSet order;
                        // bare complement ranges would fold the orbit back in
                        // under `i`.
                        out.push('^');
                    }
                    write_ranges(&ranges, true, out);
                    out.push(']');
                } else if escaped == 0x50 {
                    let excluded = if ignore_case {
                        crate::intrinsics::regexp::unicode_simple_fold_closure(&ranges)
                    } else {
                        ranges
                    };
                    write_ranges(&unicode::complement_ranges(&excluded), true, out);
                } else {
                    write_ranges(&ranges, true, out);
                }
                dirty = true;
                continue;
            }

            let mut consumed = 2;
            let atom =
                match escaped {
                    0x62 => Some(0x08),
                    0x66 => Some(0x0c),
                    0x6e => Some(0x0a),
                    0x72 => Some(0x0d),
                    0x74 => Some(0x09),
                    0x76 => Some(0x0b),
                    0x30 => Some(0),
                    0x78 => {
                        if units.get(position + 2..position + 4).is_some_and(|digits| {
                            digits.iter().all(|unit| hex_digit(*unit).is_some())
                        }) {
                            let value = units[position + 2..position + 4]
                                .iter()
                                .fold(0, |value, unit| {
                                    value * 16 + hex_digit(*unit).expect("hex digit")
                                });
                            consumed += 2;
                            Some(value)
                        } else {
                            None
                        }
                    }
                    0x75 => {
                        if units.get(position + 2) == Some(&u16::from(b'{')) {
                            let mut cursor = position + 3;
                            let mut value = 0;
                            let mut digits = 0;
                            let mut closed = false;
                            while let Some(&digit_unit) = units.get(cursor) {
                                if digit_unit == u16::from(b'}') {
                                    closed = digits > 0
                                        && value <= MAX_CODE_POINT
                                        && !(0xd800..=0xdfff).contains(&value);
                                    cursor += 1;
                                    break;
                                }
                                let Some(digit) = hex_digit(digit_unit) else {
                                    break;
                                };
                                value = value.saturating_mul(16).saturating_add(digit);
                                digits += 1;
                                cursor += 1;
                            }
                            if closed {
                                consumed = cursor - position;
                                Some(value)
                            } else {
                                None
                            }
                        } else if units.get(position + 2..position + 6).is_some_and(|digits| {
                            digits.iter().all(|unit| hex_digit(*unit).is_some())
                        }) {
                            let value = units[position + 2..position + 6]
                                .iter()
                                .fold(0, |value, unit| {
                                    value * 16 + hex_digit(*unit).expect("hex digit")
                                });
                            consumed += 4;
                            Some(value)
                        } else {
                            None
                        }
                    }
                    _ if class_depth > 0 => Some(u32::from(escaped)),
                    _ => None,
                };
            if let Some(out) = &mut rewritten {
                for unit in &units[position..position + consumed] {
                    if let Some(character) = char::from_u32(u32::from(*unit)) {
                        out.push(character);
                    } else {
                        return Err(VError::new("invalid Unicode escape"));
                    }
                }
            }
            if class_depth > 0 {
                class_fresh = false;
                if atom.is_some() {
                    if trailing_range_dash {
                        trailing_range_dash = false;
                        can_start_range = false;
                    } else {
                        can_start_range = true;
                    }
                    prev_atom_escape = false;
                } else {
                    // A class escape such as `\d`, or a malformed escape left
                    // verbatim for the engine to diagnose: never a range
                    // endpoint.
                    if trailing_range_dash {
                        return Err(VError::new(
                            "a Unicode class range endpoint must be a single character",
                        ));
                    }
                    can_start_range = false;
                    prev_atom_escape = true;
                }
            }
            position += consumed;
            continue;
        }

        let mut text = String::new();
        if let Some((value, width)) = read_u_code_point(units, position, &mut text) {
            if let Some(out) = &mut rewritten {
                out.push_str(&text);
            }
            if class_depth > 0 {
                if value == u32::from(b'[') {
                    if trailing_range_dash {
                        return Err(VError::new(
                            "a Unicode class range endpoint must be a single character",
                        ));
                    }
                    class_depth += 1;
                    can_start_range = false;
                    prev_atom_escape = false;
                    class_fresh = true;
                } else if value == u32::from(b']') {
                    trailing_range_dash = false;
                    class_depth -= 1;
                    can_start_range = false;
                    prev_atom_escape = false;
                } else if value == u32::from(b'^') && class_fresh {
                    // Class negation, not a member.
                } else if value == u32::from(b'-')
                    && (can_start_range || prev_atom_escape)
                    && units.get(position + 1) != Some(&u16::from(b']'))
                {
                    if can_start_range {
                        trailing_range_dash = true;
                        can_start_range = false;
                    } else {
                        return Err(VError::new(
                            "a Unicode class range endpoint must be a single character",
                        ));
                    }
                } else {
                    if trailing_range_dash {
                        trailing_range_dash = false;
                        can_start_range = false;
                    } else {
                        can_start_range = true;
                    }
                    prev_atom_escape = false;
                }
            } else if value == u32::from(b'[') {
                class_depth = 1;
                can_start_range = false;
                trailing_range_dash = false;
                prev_atom_escape = false;
                class_fresh = true;
            }
            position += width;
        } else {
            if let Some(out) = &mut rewritten {
                out.push_str(&String::from_utf16_lossy(&[unit]));
            }
            position += 1;
        }
    }

    if dirty {
        if class_depth != 0 {
            return Err(VError::new("unterminated character class"));
        }
        Ok(Some(EcmaString::encode(
            &rewritten.expect("dirty mark follows rewrite"),
        )))
    } else {
        Ok(None)
    }
}

fn hex_digit(unit: u16) -> Option<u32> {
    let value = u32::from(unit);
    match unit {
        0x30..=0x39 => Some(value - 0x30),
        0x41..=0x46 => Some(value - 0x41 + 10),
        0x61..=0x66 => Some(value - 0x61 + 10),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program};
    use super::*;
    use crate::Limits;

    fn compile(pattern: &str, flags: &str) -> Result<CompiledV, VError> {
        compile_v(&EcmaString::encode(pattern), &EcmaString::encode(flags))
    }

    fn error(pattern: &str, flags: &str) -> String {
        compile(pattern, flags)
            .err()
            .unwrap_or_else(|| panic!("/{pattern}/{flags} must be rejected"))
            .message()
            .to_owned()
    }

    fn units_to_string(units: &[u16]) -> String {
        char::decode_utf16(units.iter().copied())
            .map(|value| value.expect("well-formed match"))
            .collect()
    }

    /// The matched substring, or `None` when the pattern does not match.
    fn matched(pattern: &str, flags: &str, input: &str) -> Option<String> {
        let compiled = compile(pattern, flags).expect("pattern compiles");
        let text = EcmaString::encode(input);
        let matched = compiled.exec(&text, 0).ok()??;
        Some(units_to_string(
            super::super::regexp::slice_units(&text, matched.range).as_units(),
        ))
    }

    fn named(pattern: &str, flags: &str, input: &str) -> Vec<(String, Option<String>)> {
        let compiled = compile(pattern, flags).expect("pattern compiles");
        let text = EcmaString::encode(input);
        let matched = compiled
            .exec(&text, 0)
            .expect("matching completes")
            .expect("pattern matches");
        compiled
            .public_named(&matched)
            .into_iter()
            .map(|(name, range)| {
                (
                    name,
                    range.map(|range| {
                        units_to_string(super::super::regexp::slice_units(&text, range).as_units())
                    }),
                )
            })
            .collect()
    }

    #[test]
    fn flags_parse_and_canonicalize_in_specification_order() {
        let flags = VFlags::parse(&EcmaString::encode("yvsimgd")).expect("valid flags");
        assert!(flags.unicode_sets && flags.has_indices && !flags.unicode);
        assert_eq!(flags.canonical(), EcmaString::encode("dgimsvy"));
        // The engine only understands `u`; `v` lowers onto it and `d` drops out.
        assert_eq!(flags.engine_flags(), EcmaString::encode("gimsuy"));
    }

    #[test]
    fn u_and_v_flags_are_mutually_exclusive() {
        assert!(VFlags::parse(&EcmaString::encode("uv")).is_err());
        assert!(VFlags::parse(&EcmaString::encode("vv")).is_err());
        assert!(VFlags::parse(&EcmaString::encode("vz")).is_err());
        assert!(VFlags::parse(&EcmaString::encode("v")).is_ok());
        assert!(VFlags::parse(&EcmaString::encode("du")).is_ok());
    }

    #[test]
    fn d_without_v_reaches_the_engine_verbatim() {
        // v-mode syntax rules must not leak onto a `d`-only pattern, and the
        // pattern must not be rewritten into `\u{...}` escapes the engine only
        // accepts under `u`.
        assert_eq!(matched("a]", "d", "a]"), Some("a]".to_owned()));
        assert_eq!(matched("[(]", "d", "("), Some("(".to_owned()));
        assert_eq!(matched("a{", "d", "a{"), Some("a{".to_owned()));
        // Legacy (non-Unicode) semantics survive: `\u{61}` is 61 repetitions of
        // `u`, not code point 0x61.
        assert_eq!(
            matched("\\u{61}", "d", &"u".repeat(61)),
            Some("u".repeat(61))
        );
        assert_eq!(matched("\\u{61}", "d", "a"), None);
        // A `d`-only pattern still resolves named groups for `groups`.
        assert_eq!(
            named("(?<a>x)", "d", "x"),
            vec![("a".to_owned(), Some("x".to_owned()))]
        );
    }

    #[test]
    fn nested_classes_union_their_members() {
        assert_eq!(matched("[[a-c][x-z]]", "v", "y"), Some("y".to_owned()));
        assert_eq!(matched("[[a-c][x-z]]", "v", "b"), Some("b".to_owned()));
        assert_eq!(matched("[[a-c][x-z]]", "v", "m"), None);
        // Three levels deep, with a sibling member at the outer level.
        assert_eq!(matched("[[[0-3]]4]", "v", "4"), Some("4".to_owned()));
        assert_eq!(matched("[[[0-3]]4]", "v", "2"), Some("2".to_owned()));
        assert_eq!(matched("[[[0-3]]4]", "v", "5"), None);
    }

    #[test]
    fn intersection_and_difference_resolve_at_compile_time() {
        assert_eq!(matched("[\\w&&[a-f]]", "v", "c"), Some("c".to_owned()));
        assert_eq!(matched("[\\w&&[a-f]]", "v", "z"), None);
        assert_eq!(matched("[[a-z]--[aeiou]]", "v", "b"), Some("b".to_owned()));
        assert_eq!(matched("[[a-z]--[aeiou]]", "v", "e"), None);
        // Difference is left-associative across a chain.
        assert_eq!(
            matched("[[a-z]--[a-c]--[x-z]]", "v", "m"),
            Some("m".to_owned())
        );
        assert_eq!(matched("[[a-z]--[a-c]--[x-z]]", "v", "y"), None);
        // A negated nested operand is complemented before the operation runs.
        assert_eq!(matched("[[a-f]&&[^abc]]", "v", "d"), Some("d".to_owned()));
        assert_eq!(matched("[[a-f]&&[^abc]]", "v", "a"), None);
    }

    #[test]
    fn mixing_set_operators_at_one_level_is_rejected() {
        for pattern in [
            "[[a-z]&&[b]--[c]]",
            "[[a-z]--[b]&&[c]]",
            "[[a-z]&&[b][c]]",
            "[[a-z][b]&&[c]]",
        ] {
            assert!(
                error(pattern, "v").contains("may not mix"),
                "{pattern} must report mixed operators"
            );
        }
        // Nesting disambiguates, so the same members are legal when grouped.
        assert_eq!(
            matched("[[[a-z]&&[b-y]]--[c]]", "v", "d"),
            Some("d".to_owned())
        );
    }

    #[test]
    fn set_operators_require_a_right_operand() {
        assert!(error("[[a]&&]", "v").contains("right operand"));
        assert!(error("[[a]--]", "v").contains("right operand"));
    }

    #[test]
    fn q_strings_match_longest_first() {
        assert_eq!(
            matched("[\\q{abc|ab|a}]", "v", "abcd"),
            Some("abc".to_owned())
        );
        assert_eq!(
            matched("[\\q{abc|ab|a}]", "v", "abd"),
            Some("ab".to_owned())
        );
        assert_eq!(matched("[\\q{abc|ab|a}]", "v", "axx"), Some("a".to_owned()));
        // A single-code-point alternative is an ordinary character member.
        assert_eq!(matched("[\\q{a}b]", "v", "b"), Some("b".to_owned()));
        // The empty alternative matches the empty string.
        assert_eq!(matched("[\\q{ab|}]", "v", "zz"), Some(String::new()));
    }

    #[test]
    fn q_strings_combine_with_ranges_and_operators() {
        assert_eq!(matched("[\\q{ab}0-9]", "v", "7"), Some("7".to_owned()));
        assert_eq!(matched("[\\q{ab}0-9]", "v", "ab"), Some("ab".to_owned()));
        // Intersection keeps only the members present in both operands.
        assert_eq!(matched("[[\\q{ab}\\q{cd}]&&[\\q{ab}]]", "v", "cd"), None);
        assert_eq!(
            matched("[[\\q{ab}\\q{cd}]&&[\\q{ab}]]", "v", "ab"),
            Some("ab".to_owned())
        );
        // Difference removes a string member.
        assert_eq!(matched("[[\\q{ab|cd}]--[\\q{ab}]]", "v", "ab"), None);
        assert_eq!(
            matched("[[\\q{ab|cd}]--[\\q{ab}]]", "v", "cd"),
            Some("cd".to_owned())
        );
        // A code point range survives subtracting a string member.
        assert_eq!(
            matched("[[a-z]--[\\q{ab}]]", "v", "a"),
            Some("a".to_owned())
        );
    }

    #[test]
    fn strings_may_not_appear_in_a_negated_class() {
        assert!(error("[^\\q{ab}]", "v").contains("may not contain strings"));
        assert!(error("[^[\\q{ab}]]", "v").contains("may not contain strings"));
        assert!(error("[[^\\q{ab}]]", "v").contains("may not contain strings"));
        // A single-code-point member is not a string, so this stays legal.
        assert_eq!(matched("[^\\q{a}]", "v", "b"), Some("b".to_owned()));
    }

    #[test]
    fn v_mode_requires_escaping_syntax_characters_in_a_class() {
        for pattern in ["[(]", "[)]", "[{]", "[}]", "[/]", "[|]"] {
            assert!(
                error(pattern, "v").contains("must be escaped"),
                "{pattern} must require escaping"
            );
        }
        assert_eq!(matched("[\\(]", "v", "("), Some("(".to_owned()));
        assert_eq!(matched("[\\|]", "v", "|"), Some("|".to_owned()));
    }

    #[test]
    fn reserved_double_punctuators_are_rejected() {
        for pattern in [
            "[!!]", "[##]", "[$$]", "[%%]", "[**]", "[++]", "[,,]", "[..]", "[::]", "[;;]", "[<<]",
            "[==]", "[>>]", "[??]", "[@@]", "[``]", "[~~]",
        ] {
            assert!(
                error(pattern, "v").contains("reserved double punctuator"),
                "{pattern} must be rejected"
            );
        }
        // A single occurrence is an ordinary member.
        assert_eq!(matched("[!]", "v", "!"), Some("!".to_owned()));
        // `^^` is reserved once the leading negation has been consumed.
        assert!(error("[a^^]", "v").contains("reserved double punctuator"));
    }

    #[test]
    fn properties_of_strings_are_class_only_and_never_negated() {
        assert!(error("\\p{RGI_Emoji}", "v").contains("only allowed inside a class"));
        assert!(error("[\\P{RGI_Emoji}]", "v").contains("may not negate a property of strings"));
        assert_eq!(matched("[\\p{RGI_Emoji}]", "v", "🫜"), Some("🫜".to_owned()));
        assert_eq!(matched("[\\p{Letter}]", "v", "A"), Some("A".to_owned()));
        assert_eq!(matched("\\p{Letter}", "v", "A"), Some("A".to_owned()));
    }

    #[test]
    fn duplicate_names_are_legal_across_alternatives_only() {
        assert!(compile("(?<a>x)|(?<a>y)", "v").is_ok());
        assert!(compile("(?:(?<a>x)|(?<a>y))z", "v").is_ok());
        assert!(compile("(?<a>x)(?<b>y)|(?<a>z)(?<b>w)", "v").is_ok());
        for pattern in [
            "(?<a>x)(?<a>y)",
            "(?<a>x)(?:(?<a>y))",
            "(?:(?<a>x)|q)(?<a>y)",
        ] {
            assert!(
                error(pattern, "v").contains("same alternative"),
                "{pattern} must reject the duplicate"
            );
        }
    }

    #[test]
    fn duplicate_names_resolve_to_the_participating_alternative() {
        assert_eq!(
            named("(?<a>x)|(?<a>y)", "v", "y"),
            vec![("a".to_owned(), Some("y".to_owned()))]
        );
        assert_eq!(
            named("(?<a>x)|(?<a>y)", "v", "x"),
            vec![("a".to_owned(), Some("x".to_owned()))]
        );
        // A name declared only in the alternative that did not run is undefined.
        assert_eq!(
            named("(?:(?<a>x)|(?<b>y))", "v", "y"),
            vec![
                ("a".to_owned(), None),
                ("b".to_owned(), Some("y".to_owned()))
            ]
        );
        // Public order follows first declaration, once per public name.
        assert_eq!(
            named("(?<a>x)(?<b>1)|(?<a>y)(?<b>2)", "v", "y2"),
            vec![
                ("a".to_owned(), Some("y".to_owned())),
                ("b".to_owned(), Some("2".to_owned()))
            ]
        );
    }

    #[test]
    fn named_backreferences_resolve_and_report_unsupported_duplicates() {
        assert_eq!(
            matched("(?<a>ab)\\k<a>", "v", "abab"),
            Some("abab".to_owned())
        );
        // Two placeholders in one pattern must both be spliced correctly.
        assert_eq!(
            matched("(?<a>x)(?<b>y)\\k<a>\\k<b>", "v", "xyxy"),
            Some("xyxy".to_owned())
        );
        assert!(error("\\k<missing>", "v").contains("undefined capture group name"));
        // Reuniting duplicate names behind one backreference needs an engine
        // change, so it is reported rather than silently mismatched.
        assert!(error("(?:(?<a>x)|(?<a>y))\\k<a>", "v").contains("duplicate capture group name"));
    }

    #[test]
    fn lookbehind_accepts_fixed_and_variable_length_bodies() {
        assert_eq!(matched("(?<=ab)c", "v", "abc"), Some("c".to_owned()));
        assert_eq!(matched("(?<=ab)c", "v", "xbc"), None);
        // Variable-length bodies are legal in current ECMAScript.
        assert_eq!(matched("(?<=a+)b", "v", "aaab"), Some("b".to_owned()));
        assert_eq!(matched("(?<=a{1,3})b", "v", "aab"), Some("b".to_owned()));
        assert_eq!(matched("(?<=x|yy)z", "v", "yyz"), Some("z".to_owned()));
        assert_eq!(matched("(?<!a)b", "v", "cb"), Some("b".to_owned()));
        assert_eq!(matched("(?<!a)b", "v", "ab"), None);
    }

    #[test]
    fn lookaround_assertions_may_not_be_quantified() {
        for pattern in ["(?<=a)*b", "(?<!a)+b", "(?=a)?b", "(?!a){2}b"] {
            assert!(
                error(pattern, "v").contains("may not be quantified"),
                "{pattern} must be rejected"
            );
        }
        // A quantifier on a plain group is still fine.
        assert_eq!(matched("(?:ab)+", "v", "abab"), Some("abab".to_owned()));
    }

    #[test]
    fn indices_are_present_only_under_the_d_flag() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let compiled = compile("(?<a>b)(z)?", "dv").expect("pattern compiles");
        let input = EcmaString::encode("ab");
        let matched = compiled
            .exec(&input, 0)
            .expect("matching completes")
            .expect("pattern matches");
        let array = match_array(&mut machine, &input, &compiled, &matched).expect("result built");

        let indices = machine
            .get_named_property(array, "indices")
            .expect("indices present");
        let whole = machine.get_named_property(indices, "0").expect("entry 0");
        assert_eq!(
            machine.get_named_property(whole, "0").expect("start"),
            Value::int32(1)
        );
        assert_eq!(
            machine.get_named_property(whole, "1").expect("end"),
            Value::int32(2)
        );
        // A capture that did not participate has no index pair.
        assert_eq!(
            machine.get_named_property(indices, "2").expect("entry 2"),
            Value::UNDEFINED
        );
        let groups = machine
            .get_named_property(indices, "groups")
            .expect("indices groups");
        let group = machine.get_named_property(groups, "a").expect("group a");
        assert_eq!(
            machine.get_named_property(group, "0").expect("group start"),
            Value::int32(1)
        );

        let plain = compile("(?<a>b)", "v").expect("pattern compiles");
        let plain_match = plain
            .exec(&input, 0)
            .expect("matching completes")
            .expect("pattern matches");
        let plain_array =
            match_array(&mut machine, &input, &plain, &plain_match).expect("result built");
        assert_eq!(
            machine
                .get_named_property(plain_array, "indices")
                .expect("lookup succeeds"),
            Value::UNDEFINED
        );
    }

    #[test]
    fn indices_groups_is_undefined_without_named_groups() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let compiled = compile("(a)", "dv").expect("pattern compiles");
        let input = EcmaString::encode("a");
        let matched = compiled
            .exec(&input, 0)
            .expect("matching completes")
            .expect("pattern matches");
        let array = match_array(&mut machine, &input, &compiled, &matched).expect("result built");
        let indices = machine
            .get_named_property(array, "indices")
            .expect("indices present");
        assert_eq!(
            machine
                .get_named_property(indices, "groups")
                .expect("groups lookup"),
            Value::UNDEFINED
        );
        assert_eq!(
            machine.get_named_property(array, "groups").expect("groups"),
            Value::UNDEFINED
        );
    }

    #[test]
    fn sticky_matching_honours_an_explicit_start_offset() {
        let compiled = compile("[[a-z]--[aeiou]]", "vy").expect("pattern compiles");
        let input = EcmaString::encode("aab");
        // Sticky anchors at the offset, so the two leading vowels fail.
        assert!(
            compiled
                .exec(&input, 0)
                .expect("matching completes")
                .is_none()
        );
        assert!(
            compiled
                .exec(&input, 1)
                .expect("matching completes")
                .is_none()
        );
        let matched = compiled
            .exec(&input, 2)
            .expect("matching completes")
            .expect("matches at the offset");
        assert_eq!(matched.range, 2..3);
    }

    #[test]
    fn v_mode_rejects_lone_brackets_and_bad_escapes() {
        assert!(error("a{", "v").contains("lone quantifier"));
        assert!(error("a]", "v").contains("not allowed"));
        assert!(error("a}", "v").contains("not allowed"));
        assert!(error("\\a", "v").contains("invalid identity escape"));
        assert!(error("[a", "v").contains("unterminated character class"));
        assert!(error("[\\q{ab]", "v").contains("unterminated"));
        assert!(error("(a", "v").contains("unterminated group"));
        assert!(error("a)", "v").contains("unmatched ')'"));
        assert!(error("[\\u{d800}]", "v").contains("invalid Unicode escape"));
    }

    #[test]
    fn escapes_and_ranges_survive_lowering() {
        assert_eq!(matched("[\\x41-\\x43]", "v", "B"), Some("B".to_owned()));
        assert_eq!(
            matched("[\\u{1f600}]", "v", "\u{1f600}"),
            Some("\u{1f600}".to_owned())
        );
        assert_eq!(matched("[\\-]", "v", "-"), Some("-".to_owned()));
        assert_eq!(matched("[a\\-z]", "v", "-"), Some("-".to_owned()));
        assert_eq!(matched("[\\t\\n]", "v", "\t"), Some("\t".to_owned()));
        assert_eq!(
            matched("\\u{1f600}+", "v", "\u{1f600}\u{1f600}"),
            Some("\u{1f600}\u{1f600}".to_owned())
        );
        // A surrogate pair is one code point in v mode, so `.` consumes both.
        assert_eq!(matched(".", "v", "\u{1f600}"), Some("\u{1f600}".to_owned()));
        assert!(error("[b-a]", "v").contains("out of order"));
    }

    #[test]
    fn exact_property_spellings_match_and_loose_spellings_fail() {
        for (pattern, flags) in [
            ("\\p{ASCII}", "u"),
            ("\\p{AHex}", "u"),
            ("\\p{WSpace}", "u"),
            ("\\p{Any}", "u"),
            ("\\p{Assigned}", "u"),
            ("\\p{gc=Lu}", "u"),
            ("\\p{General_Category=Letter}", "u"),
            ("\\p{sc=Grek}", "u"),
            ("\\p{Script=Greek}", "u"),
            ("\\p{Script_Extensions=Greek}", "u"),
            ("\\p{scx=Greek}", "u"),
        ] {
            assert!(
                compile(pattern, flags).is_ok(),
                "/{pattern}/{flags} must compile"
            );
        }
        for (pattern, flags) in [
            ("\\p{ascii}", "u"),
            ("\\p{LETTER}", "u"),
            ("\\p{script=greek}", "u"),
            ("\\p{Scx=Greek}", "u"),
            ("\\p{script_extensions=Greek}", "u"),
            ("\\p{IsGreek}", "u"),
            ("\\p{General_Category = Lu}", "u"),
            ("\\p{ID_Compat_Math_Start}", "u"),
            ("\\p{ID_Compat_Math_Continue}", "u"),
            ("\\p{Bidi_Class=L}", "u"),
            ("\\p{Greek}", "u"),
            ("\\p{gfx=Lu}", "u"),
        ] {
            assert!(
                compile(pattern, flags).is_err(),
                "/{pattern}/{flags} must reject"
            );
        }
    }

    #[test]
    fn general_category_script_and_script_extensions_match_in_u_mode() {
        assert_eq!(matched("\\p{Lu}+", "u", "ABCz"), Some("ABC".to_owned()));
        assert_eq!(
            matched("\\p{Script=Greek}+", "u", "αβa"),
            Some("αβ".to_owned())
        );
        assert_eq!(
            matched("\\p{scx=Greek}+", "u", "\u{0370}A"),
            Some("\u{0370}".to_owned())
        );
        assert_eq!(
            matched("[\\p{ASCII}a]+", "u", "a9!"),
            Some("a9!".to_owned())
        );
    }

    #[test]
    fn unicode_16_emoji_properties_match_new_members() {
        assert!(matched("\\p{Emoji}", "u", "\u{1fadc}").is_some());
        assert_eq!(
            matched("[\\p{RGI_Emoji}]", "v", "\u{1f1e8}\u{1f1f6}"),
            Some("\u{1f1e8}\u{1f1f6}".to_owned())
        );
        assert_eq!(matched("[\\p{RGI_Emoji}]", "v", "🫜"), Some("🫜".to_owned()));
    }

    #[test]
    fn u_and_v_complements_avoid_case_fold_range_expansion() {
        for flags in ["iu", "iv"] {
            assert_eq!(matched("\\P{Lu}", flags, "k"), None);
            assert_eq!(matched("\\P{Lu}", flags, "K"), None);
            assert_eq!(matched("\\P{Lu}", flags, "\u{212a}"), None);
            assert_eq!(matched("\\P{Lu}", flags, "\u{017f}"), None);
            assert_eq!(matched("\\P{Lu}", flags, "1"), Some("1".to_owned()));
            assert_eq!(matched("[^\\p{Lu}]", flags, "k"), None);
            assert_eq!(matched("[^\\p{Lu}]", flags, "1"), Some("1".to_owned()));
        }
    }

    /// Range endpoints copied from the test262 generated property-escape
    /// tests (`General_Category_-_Letter.js`, `Script_-_Latin.js`,
    /// `Script_Extensions_-_Han.js`): every listed code point matches the
    /// positive class, the negated class, and rejects their complements.
    #[test]
    fn property_ranges_match_listed_points_and_reject_complement() {
        let cases: &[(&str, &[u32], &[u32])] = &[
            (
                "Script=Latin",
                &[0xaa, 0xba, 0x41, 0x5a, 0x61, 0x7a, 0x1d00, 0xff21, 0xff3a],
                &[0x30, 0x370, 0x4e00, 0x1f600],
            ),
            (
                "Script_Extensions=Han",
                &[0x2e80, 0x3005, 0x4e00, 0x9fff],
                &[0x41, 0x370, 0x1f600],
            ),
            (
                "General_Category=Letter",
                &[0x41, 0xb5, 0x1e00, 0x10400],
                &[0x21, 0x37e],
            ),
        ];
        for (property, inside, outside) in cases {
            for flags in ["u", "iu"] {
                let members: String = inside
                    .iter()
                    .filter_map(|&value| char::from_u32(value))
                    .collect();
                let strangers: String = outside
                    .iter()
                    .filter_map(|&value| char::from_u32(value))
                    .collect();
                let positive = format!("^\\p{{{property}}}+$");
                let negated = format!("^[^\\p{{{property}}}]+$");
                assert!(
                    matched(&positive, flags, &members).is_some(),
                    "\\p{{{property}}} must match every listed code point ({flags})"
                );
                assert!(
                    matched(&positive, flags, &strangers).is_none(),
                    "\\p{{{property}}} must reject excluded code points ({flags})"
                );
                assert!(
                    matched(&negated, flags, &strangers).is_some(),
                    "[^\\p{{{property}}}] must match excluded code points ({flags})"
                );
                assert!(
                    matched(&negated, flags, &members).is_none(),
                    "[^\\p{{{property}}}] must reject listed code points ({flags})"
                );
            }
        }
    }

    #[test]
    fn property_escapes_compose_with_nested_set_operations() {
        assert_eq!(
            matched("[\\p{Script=Greek}&&\\p{Lu}]", "v", "Α"),
            Some("Α".to_owned())
        );
        assert_eq!(matched("[\\p{Script=Greek}&&\\p{Lu}]", "v", "α"), None);
        assert_eq!(
            matched("[\\p{Letter}--\\p{Lu}]", "v", "α"),
            Some("α".to_owned())
        );
        assert_eq!(matched("[\\p{Letter}--\\p{Lu}]", "v", "A"), None);
        assert_eq!(matched("[[\\p{Lu}]x]", "v", "x"), Some("x".to_owned()));
        assert_eq!(matched("[[\\p{Lu}]x]", "v", "A"), Some("A".to_owned()));
        assert_eq!(matched("[\\P{ASCII}x]", "v", "x"), Some("x".to_owned()));
        assert_eq!(matched("[\\P{ASCII}x]", "v", "α"), Some("α".to_owned()));
        assert_eq!(
            matched("[\\p{Emoji_Keycap_Sequence}]", "v", "1\u{fe0f}\u{20e3}"),
            Some("1\u{fe0f}\u{20e3}".to_owned())
        );
    }

    #[test]
    fn astral_case_folding_and_legacy_escape_behavior_survive() {
        assert_eq!(
            matched("\\p{Lu}", "iu", "\u{10400}"),
            Some("\u{10400}".to_owned())
        );
        assert_eq!(
            matched("\\p{Lu}", "iv", "\u{10400}"),
            Some("\u{10400}".to_owned())
        );
        assert_eq!(
            matched("\u{10428}", "iu", "\u{10400}"),
            Some("\u{10400}".to_owned())
        );
        assert_eq!(matched("\\p", "", "p"), Some("p".to_owned()));
        assert!(error("\\p", "u").contains("invalid"));
        assert!(error("[\\p{Lu}-x]", "u").contains("single character"));
        assert!(error("[x-\\p{Lu}]", "u").contains("single character"));
        assert!(error("[\\w-\\p{Lu}]", "u").contains("single character"));
        assert!(compile("[\\p{Lu}-]", "u").is_ok());
        assert_eq!(matched("[\\p{Lu}-]", "u", "-"), Some("-".to_owned()));
        assert!(error("\\p{RGI_Emoji}", "u").contains("requires the 'v' flag"));
        assert!(error("[\\P{RGI_Emoji}]", "v").contains("may not negate a property of strings"));
        assert!(error("[^\\p{Basic_Emoji}]", "v").contains("may not contain strings"));
    }

    #[test]
    fn ignore_case_still_folds_through_the_engine() {
        assert_eq!(matched("[[a-z]--[aeiou]]", "iv", "B"), Some("B".to_owned()));
        assert_eq!(matched("[[a-z]--[aeiou]]", "iv", "E"), None);
    }
}
