use std::collections::{BTreeMap, HashSet};
use std::ops::Range;

use bamts_bytecode::EcmaString;

/// Backstop for non-dedupable state blowups inside a repetition (e.g.
/// `((a)|(a))*` where branches set different capture groups). Exposed so the
/// builtin boundary can attach the limit to the runtime error it raises when
/// the budget is exhausted — exhaustion must surface as a failure, not a
/// silent non-match.
pub(crate) const STEP_BUDGET: usize = 100_000;

/// Identity of a backtracking state: input position plus capture bindings. Two
/// states sharing one continue identically, so a repetition level keeps only the
/// first — that is what stops equivalent alternatives multiplying per level.
type StateKey = (usize, Vec<Option<(usize, usize)>>);

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Flags {
    pub(crate) global: bool,
    pub(crate) ignore_case: bool,
    pub(crate) multiline: bool,
    pub(crate) dot_all: bool,
    pub(crate) unicode: bool,
    pub(crate) sticky: bool,
}

impl Flags {
    fn parse(text: &EcmaString) -> Result<Self, RegexError> {
        let mut flags = Self::default();
        for unit in text.as_units() {
            let Some(flag) = char::from_u32(u32::from(*unit)).filter(char::is_ascii) else {
                return Err(RegexError::new("invalid regular expression flag"));
            };
            let slot = match flag {
                'g' => &mut flags.global,
                'i' => &mut flags.ignore_case,
                'm' => &mut flags.multiline,
                's' => &mut flags.dot_all,
                'u' => &mut flags.unicode,
                'y' => &mut flags.sticky,
                _ => {
                    return Err(RegexError::new(format!(
                        "invalid regular expression flag '{flag}'"
                    )));
                }
            };
            if *slot {
                return Err(RegexError::new(format!(
                    "duplicate regular expression flag '{flag}'"
                )));
            }
            *slot = true;
        }
        Ok(flags)
    }

    pub(crate) fn canonical(self) -> EcmaString {
        let mut result = bamts_bytecode::EcmaStringBuilder::new();
        for (enabled, flag) in [
            (self.global, b'g'),
            (self.ignore_case, b'i'),
            (self.multiline, b'm'),
            (self.dot_all, b's'),
            (self.unicode, b'u'),
            (self.sticky, b'y'),
        ] {
            if enabled {
                result.push_unit(u16::from(flag));
            }
        }
        result.finish()
    }
}

/// Canonicalize a flags string into the standard `gimsuy` order without
/// compiling the pattern. Reuses `Flags::parse` and `Flags::canonical` so
/// the ordering stays identical to the compile-based path. The flags on a
/// stored RegExp were validated at construction, so parse never fails in
/// practice; the fallback returns the stored string verbatim rather than
/// inventing output for an impossible state.
pub(crate) fn canonical_flags(flags: &EcmaString) -> EcmaString {
    match Flags::parse(flags) {
        Ok(parsed) => parsed.canonical(),
        Err(_) => flags.clone(),
    }
}

/// Distinguishes a compile-time syntax/flag error from a runtime step-budget
/// exhaustion. Compile errors surface as a thrown `SyntaxError`; budget
/// exhaustion surfaces as a `RuntimeErrorKind` so a caller can tell an aborted
/// match apart from a genuine non-match instead of misreading it as `false`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RegexErrorKind {
    Compile,
    BudgetExhausted,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RegexError {
    message: String,
    kind: RegexErrorKind,
}

impl RegexError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            kind: RegexErrorKind::Compile,
        }
    }

    /// Step budget exhausted by a pathologically complex pattern. The matcher
    /// gave up rather than completing — this must not be read as a non-match.
    fn budget_exhausted() -> Self {
        Self {
            message: "regular expression step budget exhausted".into(),
            kind: RegexErrorKind::BudgetExhausted,
        }
    }

    pub(crate) fn message(&self) -> &str {
        &self.message
    }

    pub(crate) fn kind(&self) -> RegexErrorKind {
        self.kind
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Match {
    pub(crate) range: Range<usize>,
    pub(crate) captures: Vec<Option<Range<usize>>>,
    pub(crate) named: BTreeMap<String, Option<Range<usize>>>,
}

#[derive(Clone, Debug)]
pub(crate) struct Regex {
    expression: Node,
    flags: Flags,
    capture_count: usize,
    names: BTreeMap<String, usize>,
}

impl Regex {
    pub(crate) fn compile(pattern: &EcmaString, flags: &EcmaString) -> Result<Self, RegexError> {
        let flags = Flags::parse(flags)?;
        let mut parser = Parser::new(pattern.as_units(), flags.unicode);
        let expression = parser.parse_disjunction(None)?;
        if parser.peek().is_some() {
            return Err(parser.error("unexpected token"));
        }
        Ok(Self {
            expression,
            flags,
            capture_count: parser.capture_count,
            names: parser.names,
        })
    }

    pub(crate) fn flags(&self) -> Flags {
        self.flags
    }

    pub(crate) fn exec(
        &self,
        input: &EcmaString,
        start: usize,
    ) -> Result<Option<Match>, RegexError> {
        let input = input.as_units();
        if start > input.len() {
            return Ok(None);
        }
        let mut position = start;
        loop {
            let state = State {
                position,
                captures: vec![None; self.capture_count + 1],
            };
            if let Some(mut matched) = self
                .match_node(&self.expression, input, state)?
                .into_iter()
                .next()
            {
                matched.captures[0] = Some(position..matched.position);
                let named = self
                    .names
                    .iter()
                    .map(|(name, index)| (name.clone(), matched.captures[*index].clone()))
                    .collect();
                return Ok(Some(Match {
                    range: position..matched.position,
                    captures: matched.captures,
                    named,
                }));
            }
            if self.flags.sticky || position == input.len() {
                return Ok(None);
            }
            position += next_code_point(input, position, self.flags.unicode).1;
        }
    }

    fn match_node(
        &self,
        node: &Node,
        input: &[u16],
        state: State,
    ) -> Result<Vec<State>, RegexError> {
        match node {
            Node::Sequence(nodes) => self.match_sequence(nodes, input, state),
            Node::Alternation(branches) => {
                let mut out = Vec::new();
                for branch in branches {
                    out.extend(self.match_node(branch, input, state.clone())?);
                }
                Ok(out)
            }
            Node::Literal(expected) => {
                if state.position == input.len() {
                    return Ok(Vec::new());
                }
                let (actual, width) = next_code_point(input, state.position, self.flags.unicode);
                Ok(self
                    .code_point_eq(actual, *expected)
                    .then(|| state.advanced(width))
                    .into_iter()
                    .collect())
            }
            Node::Dot => {
                if state.position == input.len() {
                    return Ok(Vec::new());
                }
                let (actual, width) = next_code_point(input, state.position, self.flags.unicode);
                Ok((self.flags.dot_all || !is_line_terminator(actual))
                    .then(|| state.advanced(width))
                    .into_iter()
                    .collect())
            }
            Node::Class(class) => {
                if state.position == input.len() {
                    return Ok(Vec::new());
                }
                let (actual, width) = next_code_point(input, state.position, self.flags.unicode);
                Ok(class
                    .matches(actual, self.flags.ignore_case, self.flags.unicode)
                    .then(|| state.advanced(width))
                    .into_iter()
                    .collect())
            }
            Node::Start => Ok((state.position == 0
                || (self.flags.multiline
                    && state.position > 0
                    && is_line_terminator(u32::from(input[state.position - 1]))))
            .then_some(state)
            .into_iter()
            .collect()),
            Node::End => Ok((state.position == input.len()
                || (self.flags.multiline
                    && input
                        .get(state.position)
                        .is_some_and(|value| is_line_terminator(u32::from(*value)))))
            .then_some(state)
            .into_iter()
            .collect()),
            Node::WordBoundary(positive) => {
                let left = if state.position == 0 {
                    false
                } else {
                    let low = input[state.position - 1];
                    let value = if self.flags.unicode
                        && (0xdc00..=0xdfff).contains(&low)
                        && state.position >= 2
                        && (0xd800..=0xdbff).contains(&input[state.position - 2])
                    {
                        combine_surrogates(input[state.position - 2], low)
                    } else {
                        u32::from(low)
                    };
                    is_word(value, self.flags.ignore_case, self.flags.unicode)
                };
                let right = (state.position < input.len())
                    .then(|| next_code_point(input, state.position, self.flags.unicode).0)
                    .is_some_and(|value| {
                        is_word(value, self.flags.ignore_case, self.flags.unicode)
                    });
                Ok(((left != right) == *positive)
                    .then_some(state)
                    .into_iter()
                    .collect())
            }
            Node::Group { index, body } => {
                let begin = state.position;
                Ok(self
                    .match_node(body, input, state)?
                    .into_iter()
                    .map(|mut matched| {
                        if let Some(index) = index {
                            matched.captures[*index] = Some(begin..matched.position);
                        }
                        matched
                    })
                    .collect())
            }
            Node::BackReference(index) => {
                let Some(range) = state.captures.get(*index).and_then(Clone::clone) else {
                    return Ok(vec![state]);
                };
                Ok(self.match_backreference(input, range, state))
            }
            Node::NamedBackReference(name) => match self.names.get(name) {
                Some(index) => Ok(self.match_node(&Node::BackReference(*index), input, state)?),
                None => Ok(Vec::new()),
            },
            Node::Look {
                body,
                behind,
                positive,
            } => {
                let candidates = if *behind {
                    let mut candidates = Vec::new();
                    let mut begin = 0;
                    loop {
                        let mut initial = state.clone();
                        initial.position = begin;
                        candidates.extend(
                            self.match_node(body, input, initial)?
                                .into_iter()
                                .filter(|matched| matched.position == state.position),
                        );
                        if begin == state.position {
                            break;
                        }
                        begin += next_code_point(input, begin, self.flags.unicode).1;
                        if begin > state.position {
                            break;
                        }
                    }
                    candidates
                } else {
                    self.match_node(body, input, state.clone())?
                };
                Ok(if *positive {
                    candidates
                        .into_iter()
                        .map(|mut matched| {
                            matched.position = state.position;
                            matched
                        })
                        .collect()
                } else if candidates.is_empty() {
                    vec![state]
                } else {
                    Vec::new()
                })
            }
            Node::Repeat { .. } => unreachable!("repeat is handled by its containing sequence"),
        }
    }

    fn match_backreference(&self, input: &[u16], range: Range<usize>, state: State) -> Vec<State> {
        let mut captured = range.start;
        let mut candidate = state.position;
        while captured < range.end {
            if candidate >= input.len() {
                return Vec::new();
            }
            let (left, left_width) = next_code_point(input, captured, self.flags.unicode);
            let (right, right_width) = next_code_point(input, candidate, self.flags.unicode);
            if captured + left_width > range.end || !self.code_point_eq(left, right) {
                return Vec::new();
            }
            captured += left_width;
            candidate += right_width;
        }
        let width = candidate - state.position;
        vec![state.advanced(width)]
    }

    fn match_sequence(
        &self,
        nodes: &[Node],
        input: &[u16],
        state: State,
    ) -> Result<Vec<State>, RegexError> {
        let Some((first, rest)) = nodes.split_first() else {
            return Ok(vec![state]);
        };
        if let Node::Repeat {
            body,
            min,
            max,
            greedy,
            captures,
        } = first
        {
            // Deduplicate states within each repetition level by (position,
            // captures).  Equivalent alternatives like (a|a|a) produce k
            // identical states at every level — without dedup these multiply to
            // k^n states, each cloning its captures Vec.  Two states that share
            // position and captures yield identical continuations, so collapsing
            // duplicates is lossless.
            //
            // The hash set is allocated once and cleared per level so its bucket
            // capacity is reused — ordinary patterns (1 state per level) pay one
            // allocation for the whole repeat, not one per level.  Dedup is kept
            // even for single-source levels because the body itself can be an
            // alternation (e.g. (a|a)*) whose branches yield duplicate
            // (position, captures) states from one prior — skipping would let
            // those duplicates through and reintroduce the multiplication.
            //
            // The step budget remains as a backstop for non-dedupable blowups
            // (e.g. ((a)|(a))* where branches set different capture groups).
            // On exhaustion it returns a distinct error rather than an empty
            // result, so a caller can tell an aborted match from a real non-match.
            let mut levels = vec![vec![state]];
            let limit = max.unwrap_or(input.len().saturating_add(*min).saturating_add(1));
            let mut total_states: usize = 1;
            let mut seen: HashSet<StateKey> = HashSet::new();
            for count in 0..limit {
                let mut next = Vec::new();
                seen.clear();
                for prior in &levels[count] {
                    let mut attempt = prior.clone();
                    attempt.captures[captures.clone()].fill(None);
                    for matched in self.match_node(body, input, attempt)? {
                        if matched.position == prior.position && count + 1 >= *min {
                            continue;
                        }
                        let key = (
                            matched.position,
                            matched
                                .captures
                                .iter()
                                .map(|c| c.as_ref().map(|r| (r.start, r.end)))
                                .collect(),
                        );
                        if seen.insert(key) {
                            next.push(matched);
                        }
                    }
                }
                if next.is_empty() {
                    break;
                }
                total_states += next.len();
                if total_states > STEP_BUDGET {
                    return Err(RegexError::budget_exhausted());
                }
                levels.push(next);
            }
            let counts: Box<dyn Iterator<Item = usize>> = if *greedy {
                Box::new((*min..levels.len()).rev())
            } else {
                Box::new(*min..levels.len())
            };
            let mut result = Vec::new();
            for count in counts {
                // Move ownership instead of cloning: each level is visited
                // exactly once, so the deep copy of every captures allocation
                // on each iteration was pure waste.
                for candidate in std::mem::take(&mut levels[count]) {
                    result.extend(self.match_sequence(rest, input, candidate)?);
                }
            }
            Ok(result)
        } else {
            let mut result = Vec::new();
            for matched in self.match_node(first, input, state)? {
                result.extend(self.match_sequence(rest, input, matched)?);
            }
            Ok(result)
        }
    }

    fn code_point_eq(&self, left: u32, right: u32) -> bool {
        left == right
            || (self.flags.ignore_case
                && canonicalize(left, self.flags.unicode)
                    == canonicalize(right, self.flags.unicode))
    }
}

pub(crate) fn next_code_point(input: &[u16], position: usize, unicode: bool) -> (u32, usize) {
    let first = input[position];
    if unicode
        && (0xd800..=0xdbff).contains(&first)
        && let Some(second @ 0xdc00..=0xdfff) = input.get(position + 1).copied()
    {
        return (
            0x1_0000 + ((u32::from(first) - 0xd800) << 10) + (u32::from(second) - 0xdc00),
            2,
        );
    }
    (u32::from(first), 1)
}

#[derive(Clone, Debug)]
struct State {
    position: usize,
    captures: Vec<Option<Range<usize>>>,
}

impl State {
    fn advanced(mut self, count: usize) -> Self {
        self.position += count;
        self
    }
}

#[derive(Clone, Debug)]
enum Node {
    Sequence(Vec<Node>),
    Alternation(Vec<Node>),
    Literal(u32),
    Dot,
    Class(CharacterClass),
    Start,
    End,
    WordBoundary(bool),
    Group {
        index: Option<usize>,
        body: Box<Node>,
    },
    BackReference(usize),
    NamedBackReference(String),
    Look {
        body: Box<Node>,
        behind: bool,
        positive: bool,
    },
    Repeat {
        body: Box<Node>,
        min: usize,
        max: Option<usize>,
        greedy: bool,
        /// The groups inside `body`, which each iteration starts without.
        captures: Range<usize>,
    },
}

#[derive(Clone, Debug)]
struct CharacterClass {
    negated: bool,
    items: Vec<ClassItem>,
}

impl CharacterClass {
    fn matches(&self, value: u32, ignore_case: bool, unicode: bool) -> bool {
        let matched = self
            .items
            .iter()
            .any(|item| item.matches(value, ignore_case, unicode));
        matched != self.negated
    }
}

#[derive(Clone, Debug)]
enum ClassItem {
    Character(u32),
    Range(u32, u32),
    Digit,
    NotDigit,
    Word,
    NotWord,
    Space,
    NotSpace,
}

impl ClassItem {
    fn matches(&self, value: u32, ignore_case: bool, unicode: bool) -> bool {
        match self {
            Self::Character(expected) => {
                value == *expected
                    || (ignore_case
                        && canonicalize(value, unicode) == canonicalize(*expected, unicode))
            }
            Self::Range(start, end) => {
                (*start..=*end).contains(&value)
                    || (ignore_case && canonicalized_range_contains(*start, *end, value, unicode))
            }
            Self::Digit => value <= 0x7f && (value as u8).is_ascii_digit(),
            Self::NotDigit => !(value <= 0x7f && (value as u8).is_ascii_digit()),
            Self::Word => is_word(value, ignore_case, unicode),
            Self::NotWord => !is_word(value, ignore_case, unicode),
            Self::Space => {
                char::from_u32(value).is_some_and(char::is_whitespace) || value == 0xfeff
            }
            Self::NotSpace => {
                !(char::from_u32(value).is_some_and(char::is_whitespace) || value == 0xfeff)
            }
        }
    }
}

fn canonicalize(value: u32, unicode: bool) -> u32 {
    if unicode {
        return unicode_simple_fold(value);
    }
    let Some(character) = char::from_u32(value) else {
        return value;
    };
    let mut uppercase = character.to_uppercase();
    let Some(first) = uppercase.next() else {
        return value;
    };
    if uppercase.next().is_some() {
        return value;
    }
    let canonical = u32::from(first);
    if value >= 0x80 && canonical < 0x80 {
        value
    } else {
        canonical
    }
}

fn canonicalized_range_contains(start: u32, end: u32, value: u32, unicode: bool) -> bool {
    let canonical = canonicalize(value, unicode);
    let folded = unicode_simple_fold(canonical);
    if (start..=end).contains(&canonical) || (start..=end).contains(&folded) {
        return true;
    }
    if UNICODE_SIMPLE_FOLD_RANGES
        .iter()
        .any(|(first, last, step, delta)| {
            let source = offset_code_point(folded, -*delta);
            source.is_some_and(|source| {
                (*first..=*last).contains(&source)
                    && (source - *first).is_multiple_of(*step)
                    && (start..=end).contains(&source)
                    && canonicalize(source, unicode) == canonical
            })
        })
    {
        return true;
    }
    UNICODE_SIMPLE_FOLD_SINGLETONS
        .iter()
        .any(|(source, target)| {
            *target == folded
                && (start..=end).contains(source)
                && canonicalize(*source, unicode) == canonical
        })
}

fn unicode_simple_fold(value: u32) -> u32 {
    UNICODE_SIMPLE_FOLD_RANGES
        .iter()
        .find(|(start, end, step, _)| {
            (*start..=*end).contains(&value) && (value - *start).is_multiple_of(*step)
        })
        .and_then(|(_, _, _, delta)| offset_code_point(value, *delta))
        .or_else(|| {
            UNICODE_SIMPLE_FOLD_SINGLETONS
                .binary_search_by_key(&value, |(source, _)| *source)
                .ok()
                .map(|index| UNICODE_SIMPLE_FOLD_SINGLETONS[index].1)
        })
        .unwrap_or(value)
}

/// Expands a code-point set to its Unicode simple-case-folding closure. Used
/// when complementing a property escape under `i` so `\P{...}` excludes every
/// case variant of the positive set, not just the literal table members.
pub(crate) fn unicode_simple_fold_closure(ranges: &[(u32, u32)]) -> Vec<(u32, u32)> {
    fn contains(ranges: &[(u32, u32)], value: u32) -> bool {
        ranges
            .iter()
            .any(|&(start, end)| start <= value && value <= end)
    }

    fn merge(mut ranges: Vec<(u32, u32)>) -> Vec<(u32, u32)> {
        if ranges.is_empty() {
            return ranges;
        }
        ranges.sort_unstable_by_key(|&(start, _)| start);
        let mut merged = Vec::with_capacity(ranges.len());
        let mut current = ranges[0];
        for (start, end) in ranges.into_iter().skip(1) {
            if start <= current.1.saturating_add(1) {
                current.1 = current.1.max(end);
            } else {
                merged.push(current);
                current = (start, end);
            }
        }
        merged.push(current);
        merged
    }

    let mut result = ranges.to_vec();
    let mut changed = true;
    while changed {
        changed = false;
        for &(start, end, step, delta) in UNICODE_SIMPLE_FOLD_RANGES {
            let mut segment_hit = false;
            for source in (start..=end).step_by(step as usize) {
                let target = offset_code_point(source, delta).unwrap_or(source);
                if contains(&result, source) || contains(&result, target) {
                    segment_hit = true;
                    break;
                }
            }
            if !segment_hit {
                continue;
            }
            if !contains(&result, start) || !contains(&result, end) {
                result.push((start, end));
                changed = true;
            }
            if let (Some(target_start), Some(target_end)) = (
                offset_code_point(start, delta),
                offset_code_point(end, delta),
            ) {
                let (lo, hi) = if target_start <= target_end {
                    (target_start, target_end)
                } else {
                    (target_end, target_start)
                };
                if !contains(&result, lo) || !contains(&result, hi) {
                    result.push((lo, hi));
                    changed = true;
                }
            }
        }
        for &(source, target) in UNICODE_SIMPLE_FOLD_SINGLETONS {
            if contains(&result, source) || contains(&result, target) {
                for value in [source, target] {
                    if !contains(&result, value) {
                        result.push((value, value));
                        changed = true;
                    }
                }
            }
        }
    }
    merge(result)
}

fn offset_code_point(value: u32, delta: i32) -> Option<u32> {
    if delta < 0 {
        value.checked_sub(delta.unsigned_abs())
    } else {
        value.checked_add(delta as u32)
    }
}

fn is_word(value: u32, ignore_case: bool, unicode: bool) -> bool {
    let value = if ignore_case && unicode {
        unicode_simple_fold(value)
    } else {
        value
    };
    value <= 0x7f && ((value as u8).is_ascii_alphanumeric() || value == u32::from(b'_'))
}

fn is_line_terminator(value: u32) -> bool {
    matches!(value, 0x0a | 0x0d | 0x2028 | 0x2029)
}

const UNICODE_SIMPLE_FOLD_RANGES: &[(u32, u32, u32, i32)] = &[
    (0x41, 0x5a, 1, 32),
    (0xc0, 0xd6, 1, 32),
    (0xd8, 0xde, 1, 32),
    (0x100, 0x12e, 2, 1),
    (0x132, 0x136, 2, 1),
    (0x139, 0x147, 2, 1),
    (0x14a, 0x176, 2, 1),
    (0x179, 0x17d, 2, 1),
    (0x1a0, 0x1a4, 2, 1),
    (0x1cb, 0x1db, 2, 1),
    (0x1de, 0x1ee, 2, 1),
    (0x1f8, 0x21e, 2, 1),
    (0x222, 0x232, 2, 1),
    (0x246, 0x24e, 2, 1),
    (0x388, 0x38a, 1, 37),
    (0x391, 0x3a1, 1, 32),
    (0x3a3, 0x3ab, 1, 32),
    (0x3d8, 0x3ee, 2, 1),
    (0x3fd, 0x3ff, 1, -130),
    (0x400, 0x40f, 1, 80),
    (0x410, 0x42f, 1, 32),
    (0x460, 0x480, 2, 1),
    (0x48a, 0x4be, 2, 1),
    (0x4c1, 0x4cd, 2, 1),
    (0x4d0, 0x52e, 2, 1),
    (0x531, 0x556, 1, 48),
    (0x10a0, 0x10c5, 1, 7264),
    (0x13f8, 0x13fd, 1, -8),
    (0x1c90, 0x1cba, 1, -3008),
    (0x1cbd, 0x1cbf, 1, -3008),
    (0x1e00, 0x1e94, 2, 1),
    (0x1ea0, 0x1efe, 2, 1),
    (0x1f08, 0x1f0f, 1, -8),
    (0x1f18, 0x1f1d, 1, -8),
    (0x1f28, 0x1f2f, 1, -8),
    (0x1f38, 0x1f3f, 1, -8),
    (0x1f48, 0x1f4d, 1, -8),
    (0x1f59, 0x1f5f, 2, -8),
    (0x1f68, 0x1f6f, 1, -8),
    (0x1f88, 0x1f8f, 1, -8),
    (0x1f98, 0x1f9f, 1, -8),
    (0x1fa8, 0x1faf, 1, -8),
    (0x1fc8, 0x1fcb, 1, -86),
    (0x2160, 0x216f, 1, 16),
    (0x24b6, 0x24cf, 1, 26),
    (0x2c00, 0x2c2f, 1, 48),
    (0x2c67, 0x2c6b, 2, 1),
    (0x2c80, 0x2ce2, 2, 1),
    (0xa640, 0xa66c, 2, 1),
    (0xa680, 0xa69a, 2, 1),
    (0xa722, 0xa72e, 2, 1),
    (0xa732, 0xa76e, 2, 1),
    (0xa77e, 0xa786, 2, 1),
    (0xa796, 0xa7a8, 2, 1),
    (0xa7b4, 0xa7c2, 2, 1),
    (0xa7cc, 0xa7da, 2, 1),
    (0xab70, 0xabbf, 1, -38864),
    (0xff21, 0xff3a, 1, 32),
    (0x10400, 0x10427, 1, 40),
    (0x104b0, 0x104d3, 1, 40),
    (0x10570, 0x10594, 2, 39),
    (0x10571, 0x10579, 2, 39),
    (0x1057d, 0x10589, 2, 39),
    (0x1058d, 0x10591, 2, 39),
    (0x10c80, 0x10cb2, 1, 64),
    (0x10d50, 0x10d65, 1, 32),
    (0x118a0, 0x118bf, 1, 32),
    (0x16e40, 0x16e5f, 1, 32),
    (0x16ea0, 0x16eb8, 1, 27),
    (0x1e900, 0x1e921, 1, 34),
];

const UNICODE_SIMPLE_FOLD_SINGLETONS: &[(u32, u32)] = &[
    (0xb5, 0x3bc),
    (0x178, 0xff),
    (0x17f, 0x73),
    (0x181, 0x253),
    (0x182, 0x183),
    (0x184, 0x185),
    (0x186, 0x254),
    (0x187, 0x188),
    (0x189, 0x256),
    (0x18a, 0x257),
    (0x18b, 0x18c),
    (0x18e, 0x1dd),
    (0x18f, 0x259),
    (0x190, 0x25b),
    (0x191, 0x192),
    (0x193, 0x260),
    (0x194, 0x263),
    (0x196, 0x269),
    (0x197, 0x268),
    (0x198, 0x199),
    (0x19c, 0x26f),
    (0x19d, 0x272),
    (0x19f, 0x275),
    (0x1a6, 0x280),
    (0x1a7, 0x1a8),
    (0x1a9, 0x283),
    (0x1ac, 0x1ad),
    (0x1ae, 0x288),
    (0x1af, 0x1b0),
    (0x1b1, 0x28a),
    (0x1b2, 0x28b),
    (0x1b3, 0x1b4),
    (0x1b5, 0x1b6),
    (0x1b7, 0x292),
    (0x1b8, 0x1b9),
    (0x1bc, 0x1bd),
    (0x1c4, 0x1c6),
    (0x1c5, 0x1c6),
    (0x1c7, 0x1c9),
    (0x1c8, 0x1c9),
    (0x1ca, 0x1cc),
    (0x1f1, 0x1f3),
    (0x1f2, 0x1f3),
    (0x1f4, 0x1f5),
    (0x1f6, 0x195),
    (0x1f7, 0x1bf),
    (0x220, 0x19e),
    (0x23a, 0x2c65),
    (0x23b, 0x23c),
    (0x23d, 0x19a),
    (0x23e, 0x2c66),
    (0x241, 0x242),
    (0x243, 0x180),
    (0x244, 0x289),
    (0x245, 0x28c),
    (0x345, 0x3b9),
    (0x370, 0x371),
    (0x372, 0x373),
    (0x376, 0x377),
    (0x37f, 0x3f3),
    (0x386, 0x3ac),
    (0x38c, 0x3cc),
    (0x38e, 0x3cd),
    (0x38f, 0x3ce),
    (0x3c2, 0x3c3),
    (0x3cf, 0x3d7),
    (0x3d0, 0x3b2),
    (0x3d1, 0x3b8),
    (0x3d5, 0x3c6),
    (0x3d6, 0x3c0),
    (0x3f0, 0x3ba),
    (0x3f1, 0x3c1),
    (0x3f4, 0x3b8),
    (0x3f5, 0x3b5),
    (0x3f7, 0x3f8),
    (0x3f9, 0x3f2),
    (0x3fa, 0x3fb),
    (0x4c0, 0x4cf),
    (0x10c7, 0x2d27),
    (0x10cd, 0x2d2d),
    (0x1c80, 0x432),
    (0x1c81, 0x434),
    (0x1c82, 0x43e),
    (0x1c83, 0x441),
    (0x1c84, 0x442),
    (0x1c85, 0x442),
    (0x1c86, 0x44a),
    (0x1c87, 0x463),
    (0x1c88, 0xa64b),
    (0x1c89, 0x1c8a),
    (0x1e9b, 0x1e61),
    (0x1e9e, 0xdf),
    (0x1fb8, 0x1fb0),
    (0x1fb9, 0x1fb1),
    (0x1fba, 0x1f70),
    (0x1fbb, 0x1f71),
    (0x1fbc, 0x1fb3),
    (0x1fbe, 0x3b9),
    (0x1fcc, 0x1fc3),
    (0x1fd3, 0x390),
    (0x1fd8, 0x1fd0),
    (0x1fd9, 0x1fd1),
    (0x1fda, 0x1f76),
    (0x1fdb, 0x1f77),
    (0x1fe3, 0x3b0),
    (0x1fe8, 0x1fe0),
    (0x1fe9, 0x1fe1),
    (0x1fea, 0x1f7a),
    (0x1feb, 0x1f7b),
    (0x1fec, 0x1fe5),
    (0x1ff8, 0x1f78),
    (0x1ff9, 0x1f79),
    (0x1ffa, 0x1f7c),
    (0x1ffb, 0x1f7d),
    (0x1ffc, 0x1ff3),
    (0x2126, 0x3c9),
    (0x212a, 0x6b),
    (0x212b, 0xe5),
    (0x2132, 0x214e),
    (0x2183, 0x2184),
    (0x2c60, 0x2c61),
    (0x2c62, 0x26b),
    (0x2c63, 0x1d7d),
    (0x2c64, 0x27d),
    (0x2c6d, 0x251),
    (0x2c6e, 0x271),
    (0x2c6f, 0x250),
    (0x2c70, 0x252),
    (0x2c72, 0x2c73),
    (0x2c75, 0x2c76),
    (0x2c7e, 0x23f),
    (0x2c7f, 0x240),
    (0x2ceb, 0x2cec),
    (0x2ced, 0x2cee),
    (0x2cf2, 0x2cf3),
    (0xa779, 0xa77a),
    (0xa77b, 0xa77c),
    (0xa77d, 0x1d79),
    (0xa78b, 0xa78c),
    (0xa78d, 0x265),
    (0xa790, 0xa791),
    (0xa792, 0xa793),
    (0xa7aa, 0x266),
    (0xa7ab, 0x25c),
    (0xa7ac, 0x261),
    (0xa7ad, 0x26c),
    (0xa7ae, 0x26a),
    (0xa7b0, 0x29e),
    (0xa7b1, 0x287),
    (0xa7b2, 0x29d),
    (0xa7b3, 0xab53),
    (0xa7c4, 0xa794),
    (0xa7c5, 0x282),
    (0xa7c6, 0x1d8e),
    (0xa7c7, 0xa7c8),
    (0xa7c9, 0xa7ca),
    (0xa7cb, 0x264),
    (0xa7dc, 0x19b),
    (0xa7f5, 0xa7f6),
    (0xfb05, 0xfb06),
    (0x10595, 0x105bc),
];

struct Parser<'a> {
    units: &'a [u16],
    position: usize,
    capture_count: usize,
    names: BTreeMap<String, usize>,
    unicode: bool,
}

impl<'a> Parser<'a> {
    fn new(units: &'a [u16], unicode: bool) -> Self {
        Self {
            units,
            position: 0,
            capture_count: 0,
            names: BTreeMap::new(),
            unicode,
        }
    }

    fn parse_disjunction(&mut self, terminator: Option<u16>) -> Result<Node, RegexError> {
        let mut branches = Vec::new();
        loop {
            branches.push(Node::Sequence(self.parse_sequence(terminator)?));
            if self.peek() != Some(u16::from(b'|')) {
                break;
            }
            self.position += 1;
        }
        if branches.len() == 1 {
            Ok(branches.pop().expect("one branch"))
        } else {
            Ok(Node::Alternation(branches))
        }
    }

    fn parse_sequence(&mut self, terminator: Option<u16>) -> Result<Vec<Node>, RegexError> {
        let mut nodes = Vec::new();
        while let Some(token) = self.peek() {
            if Some(token) == terminator || token == u16::from(b'|') {
                break;
            }
            let first_capture = self.capture_count + 1;
            let atom = self.parse_atom()?;
            nodes.push(self.parse_quantifier(atom, first_capture)?);
        }
        Ok(nodes)
    }

    fn parse_atom(&mut self) -> Result<Node, RegexError> {
        let token = self
            .next()
            .ok_or_else(|| self.error("expected regular expression atom"))?;
        match token {
            0x2e => Ok(Node::Dot),
            0x5e => Ok(Node::Start),
            0x24 => Ok(Node::End),
            0x5b => self.parse_class().map(Node::Class),
            0x28 => self.parse_group(),
            0x5c => self.parse_escape(false),
            0x29 => Err(self.error("unmatched ')'")),
            0x2a | 0x2b | 0x3f => Err(self.error("nothing to repeat")),
            _ => {
                let start = self.position - 1;
                let (value, width) = next_code_point(self.units, start, self.unicode);
                self.position = start + width;
                Ok(Node::Literal(value))
            }
        }
    }

    fn parse_group(&mut self) -> Result<Node, RegexError> {
        let mut index = None;
        let mut look = None;
        if self.peek() == Some(u16::from(b'?')) {
            self.position += 1;
            match self.next() {
                Some(0x3a) => {}
                Some(0x3d) => look = Some((false, true)),
                Some(0x21) => look = Some((false, false)),
                Some(0x3c) => match self.peek() {
                    Some(0x3d) => {
                        self.position += 1;
                        look = Some((true, true));
                    }
                    Some(0x21) => {
                        self.position += 1;
                        look = Some((true, false));
                    }
                    _ => {
                        let name = self.take_until(0x3e)?;
                        if name.is_empty() || self.names.contains_key(&name) {
                            return Err(self.error("invalid duplicate capture group name"));
                        }
                        self.capture_count += 1;
                        index = Some(self.capture_count);
                        self.names.insert(name, self.capture_count);
                    }
                },
                _ => return Err(self.error("invalid group")),
            }
        } else {
            self.capture_count += 1;
            index = Some(self.capture_count);
        }
        let body = self.parse_disjunction(Some(0x29))?;
        if self.next() != Some(0x29) {
            return Err(self.error("unterminated group"));
        }
        Ok(if let Some((behind, positive)) = look {
            Node::Look {
                body: Box::new(body),
                behind,
                positive,
            }
        } else {
            Node::Group {
                index,
                body: Box::new(body),
            }
        })
    }

    fn parse_class(&mut self) -> Result<CharacterClass, RegexError> {
        let negated = if self.peek() == Some(0x5e) {
            self.position += 1;
            true
        } else {
            false
        };
        let mut items = Vec::new();
        let mut first = true;
        while let Some(token) = self.peek() {
            if token == 0x5d && !first {
                self.position += 1;
                return Ok(CharacterClass { negated, items });
            }
            first = false;
            let left = self.parse_class_item()?;
            if self.peek() == Some(0x2d) && self.units.get(self.position + 1) != Some(&0x5d) {
                self.position += 1;
                let right = self.parse_class_item()?;
                match (left, right) {
                    (ClassItem::Character(start), ClassItem::Character(end)) if start <= end => {
                        items.push(ClassItem::Range(start, end));
                    }
                    _ => return Err(self.error("invalid character class range")),
                }
            } else {
                items.push(left);
            }
        }
        Err(self.error("unterminated character class"))
    }

    fn parse_class_item(&mut self) -> Result<ClassItem, RegexError> {
        let token = self
            .next()
            .ok_or_else(|| self.error("unterminated character class"))?;
        if token != 0x5c {
            let start = self.position - 1;
            let (value, width) = next_code_point(self.units, start, self.unicode);
            self.position = start + width;
            return Ok(ClassItem::Character(value));
        }
        let escaped = self.next().ok_or_else(|| self.error("trailing escape"))?;
        match escaped {
            0x64 => Ok(ClassItem::Digit),
            0x44 => Ok(ClassItem::NotDigit),
            0x77 => Ok(ClassItem::Word),
            0x57 => Ok(ClassItem::NotWord),
            0x73 => Ok(ClassItem::Space),
            0x53 => Ok(ClassItem::NotSpace),
            0x62 => Ok(ClassItem::Character(0x08)),
            _ => self
                .escape_character(escaped, true)
                .map(ClassItem::Character),
        }
    }

    fn parse_escape(&mut self, _in_class: bool) -> Result<Node, RegexError> {
        let escaped = self.next().ok_or_else(|| self.error("trailing escape"))?;
        match escaped {
            0x64 => Ok(class_node(ClassItem::Digit)),
            0x44 => Ok(class_node(ClassItem::NotDigit)),
            0x77 => Ok(class_node(ClassItem::Word)),
            0x57 => Ok(class_node(ClassItem::NotWord)),
            0x73 => Ok(class_node(ClassItem::Space)),
            0x53 => Ok(class_node(ClassItem::NotSpace)),
            0x62 => Ok(Node::WordBoundary(true)),
            0x42 => Ok(Node::WordBoundary(false)),
            0x6b if self.next() == Some(0x3c) => {
                Ok(Node::NamedBackReference(self.take_until(0x3e)?))
            }
            value if value <= 0x7f && (value as u8).is_ascii_digit() && value != 0x30 => {
                let mut number = (value - 0x30) as usize;
                while let Some(digit) = self.peek().and_then(decimal_digit) {
                    self.position += 1;
                    number = number
                        .checked_mul(10)
                        .and_then(|number| number.checked_add(digit))
                        .ok_or_else(|| self.error("backreference number is too large"))?;
                }
                Ok(Node::BackReference(number))
            }
            value => self.escape_character(value, false).map(Node::Literal),
        }
    }

    fn escape_character(&mut self, escaped: u16, in_class: bool) -> Result<u32, RegexError> {
        match escaped {
            0x6e => Ok(0x0a),
            0x72 => Ok(0x0d),
            0x74 => Ok(0x09),
            0x66 => Ok(0x0c),
            0x76 => Ok(0x0b),
            0x30 => Ok(0),
            0x78 => self.hex_escape(2),
            0x75 if self.unicode && self.peek() == Some(0x7b) => {
                self.position += 1;
                let digits = self.take_until(0x7d)?;
                u32::from_str_radix(&digits, 16)
                    .ok()
                    .filter(|value| *value <= 0x10ffff && !(0xd800..=0xdfff).contains(value))
                    .ok_or_else(|| self.error("invalid Unicode escape"))
            }
            0x75 => {
                let first = match self.hex_escape(4) {
                    Ok(first) => first,
                    Err(_) if !self.unicode => return Ok(0x75),
                    Err(error) => return Err(error),
                };
                if self.unicode && (0xd800..=0xdbff).contains(&first) {
                    let checkpoint = self.position;
                    if self.next() == Some(0x5c)
                        && self.next() == Some(0x75)
                        && let Ok(second) = self.hex_escape(4)
                        && (0xdc00..=0xdfff).contains(&second)
                    {
                        return Ok(combine_surrogates(first as u16, second as u16));
                    }
                    self.position = checkpoint;
                }
                Ok(first)
            }
            value
                if !self.unicode
                    || is_syntax_character(value)
                    || (in_class && value == u16::from(b'-')) =>
            {
                Ok(u32::from(value))
            }
            _ => Err(self.error("invalid identity escape in Unicode mode")),
        }
    }

    fn hex_escape(&mut self, count: usize) -> Result<u32, RegexError> {
        if self.position + count > self.units.len() {
            return Err(self.error("invalid hexadecimal escape"));
        }
        let mut value = 0u32;
        for unit in &self.units[self.position..self.position + count] {
            let Some(digit) = hex_digit(*unit) else {
                return Err(self.error("invalid hexadecimal escape"));
            };
            value = value * 16 + digit;
        }
        self.position += count;
        Ok(value)
    }

    fn parse_quantifier(&mut self, atom: Node, first_capture: usize) -> Result<Node, RegexError> {
        let Some(token) = self.peek() else {
            return Ok(atom);
        };
        let (min, max) = match token {
            0x2a => {
                self.position += 1;
                (0, None)
            }
            0x2b => {
                self.position += 1;
                (1, None)
            }
            0x3f => {
                self.position += 1;
                (0, Some(1))
            }
            0x7b => {
                let checkpoint = self.position;
                self.position += 1;
                let Some(minimum) = self.parse_decimal() else {
                    self.position = checkpoint;
                    return Ok(atom);
                };
                match self.next() {
                    Some(0x7d) => (minimum, Some(minimum)),
                    Some(0x2c) => {
                        let maximum = self.parse_decimal();
                        if self.next() != Some(0x7d) {
                            return Err(self.error("invalid quantifier"));
                        }
                        if maximum.is_some_and(|value| value < minimum) {
                            return Err(self.error("quantifier range out of order"));
                        }
                        (minimum, maximum)
                    }
                    _ => return Err(self.error("invalid quantifier")),
                }
            }
            _ => return Ok(atom),
        };
        let greedy = if self.peek() == Some(0x3f) {
            self.position += 1;
            false
        } else {
            true
        };
        Ok(Node::Repeat {
            body: Box::new(atom),
            min,
            max,
            greedy,
            captures: first_capture..self.capture_count + 1,
        })
    }

    fn parse_decimal(&mut self) -> Option<usize> {
        let begin = self.position;
        let mut value = 0usize;
        while let Some(digit) = self.peek().and_then(decimal_digit) {
            self.position += 1;
            value = value.checked_mul(10)?.checked_add(digit)?;
        }
        (self.position > begin).then_some(value)
    }

    fn take_until(&mut self, terminator: u16) -> Result<String, RegexError> {
        let begin = self.position;
        while self.peek().is_some_and(|token| token != terminator) {
            self.position += 1;
        }
        if self.next() != Some(terminator) {
            let printable = char::from_u32(u32::from(terminator)).unwrap_or('?');
            return Err(self.error(format!("expected '{printable}'")));
        }
        String::from_utf16(&self.units[begin..self.position - 1])
            .map_err(|_| self.error("invalid Unicode capture name"))
    }

    fn peek(&self) -> Option<u16> {
        self.units.get(self.position).copied()
    }

    fn next(&mut self) -> Option<u16> {
        let value = self.peek()?;
        self.position += 1;
        Some(value)
    }

    fn error(&self, message: impl Into<String>) -> RegexError {
        RegexError::new(format!("{} at position {}", message.into(), self.position))
    }
}

fn class_node(item: ClassItem) -> Node {
    Node::Class(CharacterClass {
        negated: false,
        items: vec![item],
    })
}

fn decimal_digit(unit: u16) -> Option<usize> {
    (unit <= 0x7f)
        .then_some(unit as u8)
        .and_then(|byte| byte.is_ascii_digit().then(|| (byte - b'0') as usize))
}

fn hex_digit(unit: u16) -> Option<u32> {
    (unit <= 0x7f)
        .then_some(unit as u8)
        .and_then(|byte| (byte as char).to_digit(16))
}

fn is_syntax_character(value: u16) -> bool {
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
            | 0x2f
    )
}

fn combine_surrogates(high: u16, low: u16) -> u32 {
    0x1_0000 + ((u32::from(high) - 0xd800) << 10) + (u32::from(low) - 0xdc00)
}

#[cfg(test)]
mod tests {
    use super::{Regex, RegexErrorKind};
    use bamts_bytecode::EcmaString;

    fn text(value: &str) -> EcmaString {
        EcmaString::encode(value)
    }

    fn regex(pattern: &str, flags: &str) -> Regex {
        Regex::compile(&text(pattern), &text(flags)).unwrap()
    }

    fn ranges(pattern: &str, flags: &str, input: &str) -> Vec<Option<std::ops::Range<usize>>> {
        regex(pattern, flags)
            .exec(&text(input), 0)
            .unwrap()
            .unwrap()
            .captures
    }

    #[test]
    fn corpus_escape_patterns_match_byte_exact_node_results() {
        let escaped = regex(r"\\ \^ \$ \* \+ \? \. \( \) \| \{ \} \[ \] \x2d", "");
        assert_eq!(
            escaped
                .exec(&text(r"\ ^ $ * + ? . ( ) | { } [ ] -"), 0)
                .unwrap()
                .unwrap()
                .range,
            0..29
        );
        assert_eq!(
            regex(r"\x2d", "u")
                .exec(&text("-"), 0)
                .unwrap()
                .unwrap()
                .range,
            0..1
        );
        assert_eq!(
            regex(r"\\", "g")
                .exec(&text(r"a\b"), 0)
                .unwrap()
                .unwrap()
                .range,
            1..2
        );
    }

    #[test]
    fn supports_corpus_glob_shapes() {
        assert!(
            regex(r"^(?:[^/]*?)\.js$", "")
                .exec(&text("a.js"), 0)
                .unwrap()
                .is_some()
        );
        assert!(
            regex(r"^(?:.*?)\/?\.ts$", "")
                .exec(&text("src/a/b.ts"), 0)
                .unwrap()
                .is_some()
        );
        assert!(
            regex(r"[abc]at", "")
                .exec(&text("cat"), 0)
                .unwrap()
                .is_some()
        );
        assert!(
            regex(r"^(a|b)\.js$", "")
                .exec(&text("b.js"), 0)
                .unwrap()
                .is_some()
        );
    }

    #[test]
    fn destr_json_signature_matches_number_and_preserves_unmatched_captures() {
        let input = text("123");
        let matched = regex(
            r#"^\s*["[{]|^\s*-?\d{1,16}(\.\d{1,17})?([Ee][+-]?\d+)?\s*$"#,
            "",
        )
        .exec(&input, 0)
        .unwrap()
        .unwrap();

        assert_eq!(matched.range, 0..input.as_units().len());
        assert_eq!(
            matched.captures,
            vec![Some(0..input.as_units().len()), None, None]
        );
    }

    #[test]
    fn captures_backreferences_and_lookarounds() {
        assert_eq!(
            ranges(r"(?<word>[A-z]+)-\k<word>", "i", "Ab-ab")[1],
            Some(0..2)
        );
        assert!(
            regex(r"(?<=foo)bar(?=$)", "")
                .exec(&text("foobar"), 0)
                .unwrap()
                .is_some()
        );
        assert!(
            regex(r"foo(?!bar)", "")
                .exec(&text("foobaz"), 0)
                .unwrap()
                .is_some()
        );
    }

    #[test]
    fn each_repeat_iteration_forgets_the_captures_inside_it() {
        assert_eq!(ranges("(?:(a)|b)*", "", "ab"), [Some(0..2), None]);
    }

    #[test]
    fn lazy_and_sticky_matching() {
        let lazy = regex("a.*?b", "s");
        assert_eq!(lazy.exec(&text("a1b2b"), 0).unwrap().unwrap().range, 0..3);
        let sticky = regex("b", "y");
        assert!(sticky.exec(&text("ab"), 0).unwrap().is_none());
        assert_eq!(sticky.exec(&text("ab"), 1).unwrap().unwrap().range, 1..2);
    }

    #[test]
    fn flags_are_canonical_like_node_24() {
        assert!(regex("", "yusmig").flags().canonical().eq_ascii("gimsuy"));
        assert!(Regex::compile(&text(""), &text("gg")).is_err());
    }

    #[test]
    fn dot_uses_code_units_without_u_and_code_points_with_u() {
        let input = text("😀");
        let plain = regex(".", "g");
        assert_eq!(plain.exec(&input, 0).unwrap().unwrap().range, 0..1);
        assert_eq!(plain.exec(&input, 1).unwrap().unwrap().range, 1..2);
        assert_eq!(
            regex(".", "u").exec(&input, 0).unwrap().unwrap().range,
            0..2
        );
    }

    #[test]
    fn captures_and_match_indices_are_code_unit_offsets() {
        let matched = regex("(x)", "").exec(&text("😀x"), 0).unwrap().unwrap();
        assert_eq!(matched.range, 2..3);
        assert_eq!(matched.captures[1], Some(2..3));
    }

    #[test]
    fn unicode_classes_support_supplementary_ranges() {
        let matched = regex(r"[\u{1F600}-\u{1F64F}]", "u")
            .exec(&text("😀"), 0)
            .unwrap()
            .unwrap();
        assert_eq!(matched.range, 0..2);
    }

    #[test]
    fn lone_surrogates_remain_exact_units() {
        let input = EcmaString::from_units(&[0xd800]);
        let pattern = EcmaString::from_units(&[0xd800]);
        let matched = Regex::compile(&pattern, &text(""))
            .unwrap()
            .exec(&input, 0)
            .unwrap()
            .unwrap();
        assert_eq!(matched.range, 0..1);
        assert_eq!(input.as_units(), &[0xd800]);
    }

    #[test]
    fn sticky_offsets_are_code_units() {
        let sticky = regex("x", "y");
        let input = text("😀x");
        assert!(sticky.exec(&input, 1).unwrap().is_none());
        assert_eq!(sticky.exec(&input, 2).unwrap().unwrap().range, 2..3);
    }

    #[test]
    fn escaped_surrogate_pairs_combine_only_in_unicode_mode() {
        let input = text("😀");
        assert_eq!(
            regex(r"\uD83D\uDE00", "u")
                .exec(&input, 0)
                .unwrap()
                .unwrap()
                .range,
            0..2
        );
        assert_eq!(
            regex(r"\uD83D\uDE00", "")
                .exec(&input, 0)
                .unwrap()
                .unwrap()
                .range,
            0..2
        );
    }

    #[test]
    fn ignore_case_uses_legacy_and_unicode_canonicalization() {
        assert!(regex("^k$", "i").exec(&text("K"), 0).unwrap().is_some());
        for (pattern, value) in [("^k$", "K"), ("^s$", "ſ")] {
            assert!(
                regex(pattern, "iu")
                    .exec(&text(value), 0)
                    .unwrap()
                    .is_some()
            );
            assert!(regex(pattern, "i").exec(&text(value), 0).unwrap().is_none());
        }
        assert!(regex("^å$", "i").exec(&text("Å"), 0).unwrap().is_some());
        assert!(
            regex(r"^(K)\1$", "iu")
                .exec(&text("Kk"), 0)
                .unwrap()
                .is_some()
        );
    }

    #[test]
    fn ignore_case_ranges_keep_the_original_endpoints() {
        assert!(
            regex(r"^[E-f]$", "i")
                .exec(&text("["), 0)
                .unwrap()
                .is_some()
        );
        assert!(
            regex(r"^[a-c]$", "iu")
                .exec(&text("B"), 0)
                .unwrap()
                .is_some()
        );
        assert!(
            regex(r"^[K-K]$", "i")
                .exec(&text("K"), 0)
                .unwrap()
                .is_some()
        );
        assert!(
            regex(r"^[K-K]$", "iu")
                .exec(&text("K"), 0)
                .unwrap()
                .is_some()
        );
        assert!(
            regex(r"^[K-K]$", "i")
                .exec(&text("K"), 0)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn unicode_ignore_case_extends_word_characters_and_boundaries() {
        assert!(
            regex(r"^\b\w\b$", "i")
                .exec(&text("K"), 0)
                .unwrap()
                .is_some()
        );
        for value in ["K", "ſ"] {
            assert!(
                regex(r"^\b\w\b$", "iu")
                    .exec(&text(value), 0)
                    .unwrap()
                    .is_some()
            );
            assert!(
                regex(r"^\b\w\b$", "i")
                    .exec(&text(value), 0)
                    .unwrap()
                    .is_none()
            );
        }
    }

    #[test]
    fn oversized_decimal_backreferences_are_rejected() {
        let pattern = format!(r"\1{}", "0".repeat(usize::BITS as usize));
        assert!(Regex::compile(&text(&pattern), &text("")).is_err());
    }

    #[test]
    fn braced_and_identity_escapes_follow_unicode_mode() {
        assert!(
            regex(r"^\u{61}$", "u")
                .exec(&text("a"), 0)
                .unwrap()
                .is_some()
        );
        assert!(
            regex(r"^\u{61}$", "")
                .exec(&text("a"), 0)
                .unwrap()
                .is_none()
        );
        assert!(
            regex(r"^\u{3}$", "")
                .exec(&text("uuu"), 0)
                .unwrap()
                .is_some()
        );
        assert!(regex(r"^\a$", "").exec(&text("a"), 0).unwrap().is_some());
        assert!(Regex::compile(&text(r"\a"), &text("u")).is_err());
        assert!(Regex::compile(&text(r"[\a]"), &text("u")).is_err());
        assert!(regex(r"^[\-]$", "u").exec(&text("-"), 0).unwrap().is_some());
    }

    #[test]
    fn exponential_alternation_under_star_fails_within_step_budget() {
        // (a|a|a)*b on 40 'a's: without a step budget this builds ~3^40 states
        // (each with its own captures allocation) and exhausts memory before a
        // single candidate is tested against the trailing literal.  With dedup
        // the three alternatives collapse to one state per level (40 total),
        // well under the budget — the match completes and correctly reports a
        // non-match (no 'b' in the input).  The step budget must still abort
        // non-dedupable blowups, but this pattern is dedup-friendly.
        use std::time::Instant;
        let re = regex("(a|a|a)*b", "");
        let input = text(&"a".repeat(40));
        let start = Instant::now();
        let result = re.exec(&input, 0);
        let elapsed = start.elapsed();
        assert!(
            result.as_ref().is_ok_and(|matched| matched.is_none()),
            "dedup-friendly pattern should report a genuine non-match, not an error: {result:?}"
        );
        assert!(
            elapsed.as_secs() < 5,
            "match took {elapsed:?}, expected step budget to abort quickly"
        );
    }

    #[test]
    fn step_budget_exhaustion_surfaces_as_error_not_false_non_match() {
        // A hostile pattern that exceeds the step budget must surface as an
        // error (BudgetExhausted), NOT as a false non-match.  Without this
        // distinction a validation path built on RegExp.test() gets a wrong
        // answer (false) instead of a failure it can handle.
        //
        // ((a)|(a))* sets different capture groups per branch, so the dedup
        // HashSet cannot collapse the states — the state count grows linearly
        // per level (2 states/level) and exceeds the 100_000 budget at ~50_000
        // input units.  The input has 50_001 units so the budget is hit.
        let re = regex("((a)|(a))*", "");
        let input = text(&"a".repeat(50_001));
        let result = re.exec(&input, 0);
        assert!(
            result
                .as_ref()
                .is_err_and(|error| error.kind() == RegexErrorKind::BudgetExhausted),
            "budget exhaustion must surface as an error, not a false non-match: {result:?}"
        );
    }

    #[test]
    fn repeat_dedup_collapses_equivalent_states_and_stays_linear() {
        // (a|a)* on 5_000 'a's: each level's single source produces two
        // identical (position, captures) states that must collapse to one.
        // Without dedup the state count doubles every level (2^5000) and the
        // match never finishes; with dedup (hoisted or not) it stays at 1
        // state per level and completes instantly.  This guards the dedup
        // semantics that the HashSet hoisting must preserve.
        use std::time::Instant;
        let re = regex("(a|a)*", "");
        let input = text(&"a".repeat(5_000));
        let start = Instant::now();
        let matched = re.exec(&input, 0).unwrap().unwrap();
        let elapsed = start.elapsed();
        assert_eq!(matched.range, 0..5_000);
        assert!(
            elapsed.as_millis() < 500,
            "dedup should keep this linear; took {elapsed:?}"
        );
    }
}
