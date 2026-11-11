use std::collections::HashSet;
use std::ops::Range;

use bamts_bytecode::EcmaString;

/// Backstop for non-dedupable state blowups inside a repetition (e.g.
/// `((a)|(a))*` where branches set different capture groups). Exposed so the
/// builtin boundary can attach the limit to the runtime error it raises when
/// the budget is exhausted — exhaustion must surface as a failure, not a
/// silent non-match.
pub(crate) const STEP_BUDGET: usize = 100_000;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Flags {
    pub(crate) global: bool,
    pub(crate) ignore_case: bool,
    pub(crate) multiline: bool,
    pub(crate) dot_all: bool,
    pub(crate) unicode: bool,
    pub(crate) sticky: bool,
    /// Inside a lookbehind, which reads from right to left. Never set by a flag.
    backward: bool,
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
    /// Each group name once, in source order, with the group that participated.
    pub(crate) named: Vec<(String, Option<Range<usize>>)>,
}

#[derive(Clone, Debug)]
pub(crate) struct Regex {
    program: Vec<RegexOp>,
    flags: Flags,
    capture_count: usize,
    names: Vec<(String, Vec<usize>)>,
    num_loops: usize,
}

#[derive(Clone, Debug)]
enum UnitBody {
    Literal(u32),
    Dot,
    Class(CharacterClass),
}

#[derive(Clone, Debug)]
enum RegexOp {
    Literal {
        value: u32,
        flags: Flags,
    },
    Dot {
        flags: Flags,
    },
    Class {
        class: CharacterClass,
        flags: Flags,
    },
    Start {
        multiline: bool,
    },
    End {
        multiline: bool,
    },
    WordBoundary {
        positive: bool,
        flags: Flags,
    },
    GroupStart {
        group: usize,
    },
    GroupEnd {
        group: usize,
        backward: bool,
    },
    BackRef {
        index: usize,
        flags: Flags,
    },
    NamedBackRef {
        name_idx: usize,
        flags: Flags,
    },
    Split {
        primary: usize,
        secondary: usize,
    },
    Jump {
        target: usize,
    },
    Look {
        positive: bool,
        body_start: usize,
        body_end: usize,
    },
    LoopEnter {
        loop_id: usize,
    },
    LoopHead {
        loop_id: usize,
        min: usize,
        max: Option<usize>,
        greedy: bool,
        body_start: usize,
        next: usize,
    },
    ClearCaptures {
        start: usize,
        end: usize,
    },
    LoopEnd {
        loop_id: usize,
        head: usize,
        min: usize,
    },
    RepeatUnit {
        min: usize,
        max: Option<usize>,
        greedy: bool,
        unit: UnitBody,
        flags: Flags,
    },
    Accept,
}

type LoopKey = (usize, usize, Vec<Option<(usize, usize)>>);

struct LoopFrame {
    set: HashSet<LoopKey>,
    steps: usize,
}

struct Backtrack {
    pc: usize,
    pos: usize,
    undo_len: usize,
}

enum Undo {
    Capture {
        index: usize,
        old: Option<Range<usize>>,
    },
    Open {
        index: usize,
        old: Option<usize>,
    },
    LoopCount {
        id: usize,
        old: usize,
    },
    LoopAct {
        id: usize,
        old: usize,
    },
    LoopIter {
        id: usize,
        old: usize,
    },
}

impl Regex {
    pub(crate) fn compile(pattern: &EcmaString, flags: &EcmaString) -> Result<Self, RegexError> {
        let flags = Flags::parse(flags)?;
        let mut parser = Parser::new(pattern.as_units(), flags);
        let expression = parser.parse_disjunction(None)?;
        if parser.peek().is_some() {
            return Err(parser.error("unexpected token"));
        }
        for name in &parser.referenced_names {
            if !parser.names.iter().any(|(known, _)| known == name) {
                return Err(parser.error("invalid named reference"));
            }
        }
        let capture_count = parser.capture_count;
        let names = parser.names;
        let (program, num_loops) = lower_program(&expression, flags, &names)?;
        Ok(Self {
            program,
            flags,
            capture_count,
            names,
            num_loops,
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
        let mut matcher = Matcher::new(self, input, 0, self.program.len(), position);
        loop {
            matcher.reset(self.capture_count, self.num_loops, position);
            let end = matcher.run()?;
            if let Some(end_pos) = end {
                let mut captures = matcher.captures;
                captures[0] = Some(position..end_pos);
                let named = self
                    .names
                    .iter()
                    .map(|(name, indices)| {
                        let participant = indices.iter().find_map(|index| captures[*index].clone());
                        (name.clone(), participant)
                    })
                    .collect();
                return Ok(Some(Match {
                    range: position..end_pos,
                    captures,
                    named,
                }));
            }
            if self.flags.sticky || position == input.len() {
                return Ok(None);
            }
            position += next_code_point(input, position, self.flags.unicode).1;
        }
    }
}

fn lower_program(
    expression: &Node,
    flags: Flags,
    names: &[(String, Vec<usize>)],
) -> Result<(Vec<RegexOp>, usize), RegexError> {
    let mut compiler = Compiler {
        prog: Vec::new(),
        num_loops: 0,
    };
    compiler.compile_node(expression, flags, names)?;
    compiler.prog.push(RegexOp::Accept);
    Ok((compiler.prog, compiler.num_loops))
}

struct Compiler {
    prog: Vec<RegexOp>,
    num_loops: usize,
}

impl Compiler {
    fn compile_node(
        &mut self,
        node: &Node,
        flags: Flags,
        names: &[(String, Vec<usize>)],
    ) -> Result<(), RegexError> {
        match node {
            Node::Sequence(..)
            | Node::Alternation(..)
            | Node::Group { .. }
            | Node::Modified { .. } => self.compile_structure(node, flags, names),
            Node::Literal(..)
            | Node::Dot
            | Node::Class(..)
            | Node::Start
            | Node::End
            | Node::WordBoundary(..) => self.compile_atom(node, flags),
            Node::BackReference(..) | Node::NamedBackReference(..) | Node::Look { .. } => {
                self.compile_assertion(node, flags, names)
            }
            Node::Repeat { .. } => self.compile_repeat(node, flags, names),
        }
    }
    fn compile_atom(&mut self, node: &Node, flags: Flags) -> Result<(), RegexError> {
        match node {
            Node::Literal(value) => self.prog.push(RegexOp::Literal {
                value: *value,
                flags,
            }),
            Node::Dot => self.prog.push(RegexOp::Dot { flags }),
            Node::Class(class) => self.prog.push(RegexOp::Class {
                class: class.clone(),
                flags,
            }),
            Node::Start => self.prog.push(RegexOp::Start {
                multiline: flags.multiline,
            }),
            Node::End => self.prog.push(RegexOp::End {
                multiline: flags.multiline,
            }),
            Node::WordBoundary(positive) => self.prog.push(RegexOp::WordBoundary {
                positive: *positive,
                flags,
            }),
            _ => return Err(RegexError::new("internal dispatch")),
        }
        Ok(())
    }
    fn compile_structure(
        &mut self,
        node: &Node,
        flags: Flags,
        names: &[(String, Vec<usize>)],
    ) -> Result<(), RegexError> {
        match node {
            Node::Sequence(nodes) => self.compile_sequence(nodes, flags, names),
            Node::Alternation(branches) => self.compile_alternation(branches, flags, names),
            Node::Group { index, body } => {
                if let Some(group) = index {
                    self.prog.push(RegexOp::GroupStart { group: *group });
                    self.compile_node(body, flags, names)?;
                    self.prog.push(RegexOp::GroupEnd {
                        group: *group,
                        backward: flags.backward,
                    });
                } else {
                    self.compile_node(body, flags, names)?;
                }
                Ok(())
            }
            Node::Modified {
                flags: modified,
                body,
            } => {
                let inner = Flags {
                    backward: flags.backward,
                    ..*modified
                };
                self.compile_node(body, inner, names)
            }
            _ => Err(RegexError::new("internal dispatch")),
        }
    }
    fn compile_assertion(
        &mut self,
        node: &Node,
        flags: Flags,
        names: &[(String, Vec<usize>)],
    ) -> Result<(), RegexError> {
        match node {
            Node::BackReference(index) => {
                self.prog.push(RegexOp::BackRef {
                    index: *index,
                    flags,
                });
                Ok(())
            }
            Node::NamedBackReference(name) => {
                let Some(name_idx) = names.iter().position(|known| &known.0 == name) else {
                    return Err(RegexError::new("invalid named reference"));
                };
                self.prog.push(RegexOp::NamedBackRef { name_idx, flags });
                Ok(())
            }
            Node::Look {
                body,
                behind,
                positive,
            } => {
                let look_at = self.prog.len();
                self.prog.push(RegexOp::Look {
                    positive: *positive,
                    body_start: 0,
                    body_end: 0,
                });
                let jump_at = self.prog.len();
                self.prog.push(RegexOp::Jump { target: 0 });
                let body_start = self.prog.len();
                let inner = Flags {
                    backward: *behind,
                    ..flags
                };
                self.compile_node(body, inner, names)?;
                let body_end = self.prog.len();
                self.prog[jump_at] = RegexOp::Jump { target: body_end };
                self.prog[look_at] = RegexOp::Look {
                    positive: *positive,
                    body_start,
                    body_end,
                };
                Ok(())
            }
            _ => Err(RegexError::new("internal dispatch")),
        }
    }
    fn compile_repeat(
        &mut self,
        node: &Node,
        flags: Flags,
        names: &[(String, Vec<usize>)],
    ) -> Result<(), RegexError> {
        match node {
            Node::Repeat {
                body,
                min,
                max,
                greedy,
                captures,
            } => {
                if captures.is_empty()
                    && let Some((unit, unit_flags)) = unit_template(body, flags)
                {
                    self.prog.push(RegexOp::RepeatUnit {
                        min: *min,
                        max: *max,
                        greedy: *greedy,
                        unit,
                        flags: unit_flags,
                    });
                    return Ok(());
                }
                let loop_id = self.num_loops;
                self.num_loops += 1;
                self.prog.push(RegexOp::LoopEnter { loop_id });
                let head_at = self.prog.len();
                self.prog.push(RegexOp::LoopHead {
                    loop_id,
                    min: *min,
                    max: *max,
                    greedy: *greedy,
                    body_start: 0,
                    next: 0,
                });
                let body_start = self.prog.len();
                self.prog.push(RegexOp::ClearCaptures {
                    start: captures.start,
                    end: captures.end,
                });
                self.compile_node(body, flags, names)?;
                self.prog.push(RegexOp::LoopEnd {
                    loop_id,
                    head: head_at,
                    min: *min,
                });
                let next = self.prog.len();
                if let RegexOp::LoopHead {
                    body_start: ref mut bs,
                    next: ref mut nx,
                    ..
                } = self.prog[head_at]
                {
                    *bs = body_start;
                    *nx = next;
                }
                Ok(())
            }
            _ => Err(RegexError::new("internal dispatch")),
        }
    }
    fn compile_sequence(
        &mut self,
        nodes: &[Node],
        flags: Flags,
        names: &[(String, Vec<usize>)],
    ) -> Result<(), RegexError> {
        if flags.backward {
            for node in nodes.iter().rev() {
                self.compile_node(node, flags, names)?;
            }
        } else {
            for node in nodes {
                self.compile_node(node, flags, names)?;
            }
        }
        Ok(())
    }
    fn compile_alternation(
        &mut self,
        branches: &[Node],
        flags: Flags,
        names: &[(String, Vec<usize>)],
    ) -> Result<(), RegexError> {
        if branches.len() == 1 {
            return self.compile_node(&branches[0], flags, names);
        }
        let split_at = self.prog.len();
        self.prog.push(RegexOp::Split {
            primary: 0,
            secondary: 0,
        });
        let primary = self.prog.len();
        self.compile_node(&branches[0], flags, names)?;
        let jump_at = self.prog.len();
        self.prog.push(RegexOp::Jump { target: 0 });
        let secondary = self.prog.len();
        self.compile_alternation(&branches[1..], flags, names)?;
        let end = self.prog.len();
        self.prog[split_at] = RegexOp::Split { primary, secondary };
        self.prog[jump_at] = RegexOp::Jump { target: end };
        Ok(())
    }
}

fn unit_template(node: &Node, flags: Flags) -> Option<(UnitBody, Flags)> {
    match node {
        Node::Literal(value) => Some((UnitBody::Literal(*value), flags)),
        Node::Dot => Some((UnitBody::Dot, flags)),
        Node::Class(class) => Some((UnitBody::Class(class.clone()), flags)),
        Node::Modified {
            flags: modified,
            body,
        } => {
            let inner = Flags {
                backward: flags.backward,
                ..*modified
            };
            unit_template(body, inner)
        }
        Node::Group { index: None, body } => unit_template(body, flags),
        Node::Sequence(nodes) => {
            if nodes.len() == 1 {
                unit_template(&nodes[0], flags)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn code_point_eq(flags: Flags, left: u32, right: u32) -> bool {
    left == right
        || (flags.ignore_case
            && canonicalize(left, flags.unicode) == canonicalize(right, flags.unicode))
}

fn match_unit(input: &[u16], pos: usize, unit: &UnitBody, flags: Flags) -> Option<usize> {
    let (actual, width) = adjacent_code_point(input, pos, flags)?;
    let ok = match unit {
        UnitBody::Literal(value) => code_point_eq(flags, actual, *value),
        UnitBody::Dot => flags.dot_all || !is_line_terminator(actual),
        UnitBody::Class(class) => class.matches(actual, flags.ignore_case, flags.unicode),
    };
    if !ok {
        return None;
    }
    if flags.backward {
        pos.checked_sub(width)
    } else {
        Some(pos + width)
    }
}

fn match_backref(input: &[u16], range: &Range<usize>, pos: usize, flags: Flags) -> Option<usize> {
    let width = range.len();
    let start = if flags.backward {
        pos.checked_sub(width)?
    } else {
        if pos + width > input.len() {
            return None;
        }
        pos
    };
    let (mut captured, mut candidate) = (range.start, start);
    while captured < range.end {
        if candidate >= input.len() {
            return None;
        }
        let (left, left_width) = next_code_point(input, captured, flags.unicode);
        let (right, right_width) = next_code_point(input, candidate, flags.unicode);
        if captured + left_width > range.end || !code_point_eq(flags, left, right) {
            return None;
        }
        captured += left_width;
        candidate += right_width;
    }
    if candidate != start + width {
        return None;
    }
    if flags.backward {
        pos.checked_sub(width)
    } else {
        Some(pos + width)
    }
}

enum OpClass {
    Atom,
    Group,
    Control,
    Loop,
    Look,
}

impl RegexOp {
    fn op_class(&self) -> OpClass {
        match self {
            RegexOp::Literal { .. }
            | RegexOp::Dot { .. }
            | RegexOp::Class { .. }
            | RegexOp::Start { .. }
            | RegexOp::End { .. }
            | RegexOp::WordBoundary { .. } => OpClass::Atom,
            RegexOp::GroupStart { .. }
            | RegexOp::GroupEnd { .. }
            | RegexOp::BackRef { .. }
            | RegexOp::NamedBackRef { .. } => OpClass::Group,
            RegexOp::Split { .. }
            | RegexOp::Jump { .. }
            | RegexOp::ClearCaptures { .. }
            | RegexOp::Accept => OpClass::Control,
            RegexOp::LoopEnter { .. }
            | RegexOp::LoopHead { .. }
            | RegexOp::LoopEnd { .. }
            | RegexOp::RepeatUnit { .. } => OpClass::Loop,
            RegexOp::Look { .. } => OpClass::Look,
        }
    }
}

struct HeadJump {
    loop_id: usize,
    min: usize,
    max: Option<usize>,
    greedy: bool,
    body_start: usize,
    next: usize,
}

struct Matcher<'a> {
    program: &'a [RegexOp],
    input: &'a [u16],
    names: &'a [(String, Vec<usize>)],
    captures: Vec<Option<Range<usize>>>,
    opens: Vec<Option<usize>>,
    counts: Vec<usize>,
    acts: Vec<usize>,
    iters: Vec<usize>,
    frames: Vec<LoopFrame>,
    undo: Vec<Undo>,
    backtrack: Vec<Backtrack>,
    limit: usize,
    base_undo: usize,
    pc: usize,
    pos: usize,
    end_pc: usize,
}

impl<'a> Matcher<'a> {
    fn new(
        regex: &'a Regex,
        input: &'a [u16],
        start_pc: usize,
        end_pc: usize,
        start_pos: usize,
    ) -> Self {
        Self {
            program: &regex.program,
            input,
            names: &regex.names,
            captures: vec![None; regex.capture_count + 1],
            opens: vec![None; regex.capture_count + 1],
            counts: vec![0; regex.num_loops],
            acts: vec![0; regex.num_loops],
            iters: vec![0; regex.num_loops],
            frames: Vec::new(),
            undo: Vec::new(),
            backtrack: Vec::new(),
            limit: STEP_BUDGET.max(input.len().saturating_mul(2)),
            base_undo: 0,
            pc: start_pc,
            pos: start_pos,
            end_pc,
        }
    }
    fn reset(&mut self, capture_count: usize, num_loops: usize, start_pos: usize) {
        self.captures.clear();
        self.captures.resize(capture_count + 1, None);
        self.opens.clear();
        self.opens.resize(capture_count + 1, None);
        self.counts.clear();
        self.counts.resize(num_loops, 0);
        self.acts.clear();
        self.acts.resize(num_loops, 0);
        self.iters.clear();
        self.iters.resize(num_loops, 0);
        self.frames.clear();
        self.undo.clear();
        self.backtrack.clear();
        self.base_undo = 0;
        self.pc = 0;
        self.pos = start_pos;
        self.end_pc = self.program.len();
    }
    fn run(&mut self) -> Result<Option<usize>, RegexError> {
        loop {
            if self.pc == self.end_pc {
                return Ok(Some(self.pos));
            }
            let prog = self.program;
            if matches!(prog[self.pc], RegexOp::Accept) {
                return Ok(Some(self.pos));
            }
            let advance = match prog[self.pc].op_class() {
                OpClass::Atom => self.step_atom()?,
                OpClass::Group => self.step_group()?,
                OpClass::Control => self.step_control()?,
                OpClass::Loop => self.step_loop()?,
                OpClass::Look => self.step_look()?,
            };
            if !advance {
                return Ok(None);
            }
        }
    }
    fn step_atom(&mut self) -> Result<bool, RegexError> {
        let prog = self.program;
        match &prog[self.pc] {
            RegexOp::Literal { value, flags } => {
                let value = *value;
                let flags = *flags;
                let input = self.input;
                let pos = self.pos;
                let (actual, width) = match adjacent_code_point(input, pos, flags) {
                    Some(found) => found,
                    None => return Ok(self.fail()),
                };
                if !code_point_eq(flags, actual, value) {
                    return Ok(self.fail());
                }
                if flags.backward {
                    Ok(self.advance_backward(width))
                } else {
                    Ok(self.advance_forward(width))
                }
            }
            RegexOp::Dot { flags } => {
                let flags = *flags;
                let input = self.input;
                let pos = self.pos;
                let (actual, width) = match adjacent_code_point(input, pos, flags) {
                    Some(found) => found,
                    None => return Ok(self.fail()),
                };
                if !flags.dot_all && is_line_terminator(actual) {
                    return Ok(self.fail());
                }
                if flags.backward {
                    Ok(self.advance_backward(width))
                } else {
                    Ok(self.advance_forward(width))
                }
            }
            RegexOp::Class { class, flags } => {
                let flags = *flags;
                let input = self.input;
                let pos = self.pos;
                let (actual, width) = match adjacent_code_point(input, pos, flags) {
                    Some(found) => found,
                    None => return Ok(self.fail()),
                };
                if !class.matches(actual, flags.ignore_case, flags.unicode) {
                    return Ok(self.fail());
                }
                if flags.backward {
                    Ok(self.advance_backward(width))
                } else {
                    Ok(self.advance_forward(width))
                }
            }
            RegexOp::Start { multiline } => {
                let multiline = *multiline;
                let input = self.input;
                let pos = self.pos;
                if pos == 0
                    || (multiline && pos > 0 && is_line_terminator(u32::from(input[pos - 1])))
                {
                    self.pc += 1;
                    Ok(true)
                } else {
                    Ok(self.fail())
                }
            }
            RegexOp::End { multiline } => {
                let multiline = *multiline;
                let input = self.input;
                let pos = self.pos;
                if pos == input.len()
                    || (multiline
                        && input
                            .get(pos)
                            .is_some_and(|value| is_line_terminator(u32::from(*value))))
                {
                    self.pc += 1;
                    Ok(true)
                } else {
                    Ok(self.fail())
                }
            }
            RegexOp::WordBoundary { positive, flags } => {
                let positive = *positive;
                let flags = *flags;
                let input = self.input;
                let pos = self.pos;
                let left = if pos == 0 {
                    false
                } else {
                    let low = input[pos - 1];
                    let value = if flags.unicode
                        && (0xdc00..=0xdfff).contains(&low)
                        && pos >= 2
                        && (0xd800..=0xdbff).contains(&input[pos - 2])
                    {
                        combine_surrogates(input[pos - 2], low)
                    } else {
                        u32::from(low)
                    };
                    is_word(value, flags.ignore_case, flags.unicode)
                };
                let right = (pos < input.len())
                    .then(|| next_code_point(input, pos, flags.unicode).0)
                    .is_some_and(|value| is_word(value, flags.ignore_case, flags.unicode));
                if (left != right) == positive {
                    self.pc += 1;
                    Ok(true)
                } else {
                    Ok(self.fail())
                }
            }
            _ => Err(RegexError::new("internal dispatch")),
        }
    }
    fn step_group(&mut self) -> Result<bool, RegexError> {
        let prog = self.program;
        match &prog[self.pc] {
            RegexOp::GroupStart { group, .. } => {
                let group = *group;
                self.undo.push(Undo::Open {
                    index: group,
                    old: self.opens[group],
                });
                self.opens[group] = Some(self.pos);
                self.pc += 1;
                Ok(true)
            }
            RegexOp::GroupEnd { group, backward } => {
                if *backward {
                    self.op_group_end_backward(*group)
                } else {
                    self.op_group_end_forward(*group)
                }
            }
            RegexOp::BackRef { index, flags } => self.op_backref(*index, *flags),
            RegexOp::NamedBackRef { name_idx, flags } => self.op_named(*name_idx, *flags),
            _ => Err(RegexError::new("internal dispatch")),
        }
    }
    fn step_control(&mut self) -> Result<bool, RegexError> {
        let prog = self.program;
        match &prog[self.pc] {
            RegexOp::Split { primary, secondary } => {
                let primary = *primary;
                let secondary = *secondary;
                self.backtrack.push(Backtrack {
                    pc: secondary,
                    pos: self.pos,
                    undo_len: self.undo.len(),
                });
                self.pc = primary;
                Ok(true)
            }
            RegexOp::Jump { target } => {
                self.pc = *target;
                Ok(true)
            }
            RegexOp::ClearCaptures { start, end } => {
                let start = *start;
                let end = *end;
                for index in start..end {
                    if self.captures[index].is_some() {
                        self.undo.push(Undo::Capture {
                            index,
                            old: self.captures[index].clone(),
                        });
                        self.captures[index] = None;
                    }
                }
                self.pc += 1;
                Ok(true)
            }
            _ => Err(RegexError::new("internal dispatch")),
        }
    }
    fn step_loop(&mut self) -> Result<bool, RegexError> {
        let prog = self.program;
        match &prog[self.pc] {
            RegexOp::LoopEnter { loop_id } => {
                let loop_id = *loop_id;
                let id = self.frames.len();
                self.frames.push(LoopFrame {
                    set: HashSet::new(),
                    steps: 0,
                });
                self.undo.push(Undo::LoopAct {
                    id: loop_id,
                    old: self.acts[loop_id],
                });
                self.acts[loop_id] = id;
                self.undo.push(Undo::LoopCount {
                    id: loop_id,
                    old: self.counts[loop_id],
                });
                self.counts[loop_id] = 0;
                self.undo.push(Undo::LoopIter {
                    id: loop_id,
                    old: self.iters[loop_id],
                });
                self.iters[loop_id] = self.pos;
                self.pc += 1;
                Ok(true)
            }
            RegexOp::LoopHead {
                loop_id,
                min,
                max,
                greedy,
                body_start,
                next,
            } => {
                let op = HeadJump {
                    loop_id: *loop_id,
                    min: *min,
                    max: *max,
                    greedy: *greedy,
                    body_start: *body_start,
                    next: *next,
                };
                self.op_head(op)
            }
            RegexOp::LoopEnd { loop_id, head, min } => {
                let loop_id = *loop_id;
                let head = *head;
                let min = *min;
                let count = self.counts[loop_id];
                if count >= min && self.pos == self.iters[loop_id] {
                    return Ok(self.fail());
                }
                self.undo.push(Undo::LoopCount {
                    id: loop_id,
                    old: self.counts[loop_id],
                });
                self.counts[loop_id] = count + 1;
                self.pc = head;
                Ok(true)
            }
            RegexOp::RepeatUnit {
                min,
                max,
                greedy,
                unit: _,
                flags,
            } => {
                let min = *min;
                let max = *max;
                let greedy = *greedy;
                let flags = *flags;
                let prog = self.program;
                let unit = match &prog[self.pc] {
                    RegexOp::RepeatUnit { unit, .. } => unit,
                    _ => return Err(RegexError::new("internal dispatch")),
                };
                if greedy {
                    self.op_repeat_greedy(min, max, unit, flags)
                } else {
                    self.op_repeat_lazy(min, max, unit, flags)
                }
            }
            _ => Err(RegexError::new("internal dispatch")),
        }
    }
    fn step_look(&mut self) -> Result<bool, RegexError> {
        let prog = self.program;
        let (positive, body_start, body_end) = match &prog[self.pc] {
            RegexOp::Look {
                positive,
                body_start,
                body_end,
                ..
            } => (*positive, *body_start, *body_end),
            _ => return Err(RegexError::new("internal dispatch")),
        };
        if positive {
            self.op_look_positive(body_start, body_end)
        } else {
            self.op_look_negative(body_start, body_end)
        }
    }
    fn op_group_end_forward(&mut self, group: usize) -> Result<bool, RegexError> {
        let Some(begin) = self.opens[group] else {
            return Ok(self.fail());
        };
        if begin > self.pos {
            return Ok(self.fail());
        }
        self.capture_group(group, begin..self.pos);
        Ok(true)
    }
    fn op_group_end_backward(&mut self, group: usize) -> Result<bool, RegexError> {
        let Some(begin) = self.opens[group] else {
            return Ok(self.fail());
        };
        if self.pos > begin {
            return Ok(self.fail());
        }
        self.capture_group(group, self.pos..begin);
        Ok(true)
    }
    fn capture_group(&mut self, group: usize, range: Range<usize>) {
        self.undo.push(Undo::Capture {
            index: group,
            old: self.captures[group].clone(),
        });
        self.captures[group] = Some(range);
        self.pc += 1;
    }
    fn op_backref(&mut self, index: usize, flags: Flags) -> Result<bool, RegexError> {
        let Some(range) = self.captures.get(index).and_then(|entry| entry.clone()) else {
            self.pc += 1;
            return Ok(true);
        };
        match match_backref(self.input, &range, self.pos, flags) {
            Some(next) => {
                self.pos = next;
                self.pc += 1;
                Ok(true)
            }
            None => Ok(self.fail()),
        }
    }
    fn op_named(&mut self, name_idx: usize, flags: Flags) -> Result<bool, RegexError> {
        let found = self.names[name_idx]
            .1
            .iter()
            .find_map(|index| self.captures.get(*index).and_then(|entry| entry.clone()));
        let Some(range) = found else {
            self.pc += 1;
            return Ok(true);
        };
        match match_backref(self.input, &range, self.pos, flags) {
            Some(next) => {
                self.pos = next;
                self.pc += 1;
                Ok(true)
            }
            None => Ok(self.fail()),
        }
    }
    fn op_head(&mut self, op: HeadJump) -> Result<bool, RegexError> {
        let count = self.counts[op.loop_id];
        let act = self.acts[op.loop_id];
        let tracked = if op.max.is_some() {
            count
        } else {
            count.min(op.min)
        };
        let mut key_caps = Vec::with_capacity(self.captures.len());
        for entry in self.captures.iter() {
            key_caps.push(entry.as_ref().map(|range| (range.start, range.end)));
        }
        if !self.frames[act].set.insert((tracked, self.pos, key_caps)) {
            return Ok(self.fail());
        }
        self.frames[act].steps += 1;
        if self.frames[act].steps > self.limit {
            return Err(RegexError::budget_exhausted());
        }
        self.undo.push(Undo::LoopIter {
            id: op.loop_id,
            old: self.iters[op.loop_id],
        });
        self.iters[op.loop_id] = self.pos;
        let can_enter = op.max.is_none_or(|bound| count < bound);
        let can_exit = count >= op.min;
        if !can_enter && !can_exit {
            return Ok(self.fail());
        }
        if can_enter && !can_exit {
            self.pc = op.body_start;
            return Ok(true);
        }
        if !can_enter && can_exit {
            self.pc = op.next;
            return Ok(true);
        }
        if op.greedy {
            self.backtrack.push(Backtrack {
                pc: op.next,
                pos: self.pos,
                undo_len: self.undo.len(),
            });
            self.pc = op.body_start;
        } else {
            self.backtrack.push(Backtrack {
                pc: op.body_start,
                pos: self.pos,
                undo_len: self.undo.len(),
            });
            self.pc = op.next;
        }
        Ok(true)
    }
    fn op_repeat_greedy(
        &mut self,
        min: usize,
        max: Option<usize>,
        unit: &UnitBody,
        flags: Flags,
    ) -> Result<bool, RegexError> {
        let positions = self.repeat_positions(max, unit, flags);
        let have = positions.len() - 1;
        if have < min {
            return Ok(self.fail());
        }
        let next_pc = self.pc + 1;
        for &pos in &positions[min..have] {
            self.backtrack.push(Backtrack {
                pc: next_pc,
                pos,
                undo_len: self.undo.len(),
            });
        }
        self.pos = positions[have];
        self.pc = next_pc;
        Ok(true)
    }
    fn op_repeat_lazy(
        &mut self,
        min: usize,
        max: Option<usize>,
        unit: &UnitBody,
        flags: Flags,
    ) -> Result<bool, RegexError> {
        let positions = self.repeat_positions(max, unit, flags);
        let have = positions.len() - 1;
        if have < min {
            return Ok(self.fail());
        }
        let next_pc = self.pc + 1;
        for index in (min + 1..=have).rev() {
            self.backtrack.push(Backtrack {
                pc: next_pc,
                pos: positions[index],
                undo_len: self.undo.len(),
            });
        }
        self.pos = positions[min];
        self.pc = next_pc;
        Ok(true)
    }
    fn repeat_positions(&self, max: Option<usize>, unit: &UnitBody, flags: Flags) -> Vec<usize> {
        let mut positions = Vec::new();
        positions.push(self.pos);
        let mut cursor = self.pos;
        loop {
            if max.is_some_and(|bound| positions.len() > bound) {
                break;
            }
            let Some(next) = match_unit(self.input, cursor, unit, flags) else {
                break;
            };
            cursor = next;
            positions.push(cursor);
        }
        positions
    }
    fn op_look_positive(&mut self, body_start: usize, body_end: usize) -> Result<bool, RegexError> {
        let entry_undo = self.undo.len();
        match self.exec_look_body(body_start, body_end)? {
            Some(_) => {
                self.pc += 1;
                Ok(true)
            }
            None => {
                self.truncate(entry_undo);
                Ok(self.fail())
            }
        }
    }
    fn op_look_negative(&mut self, body_start: usize, body_end: usize) -> Result<bool, RegexError> {
        let entry_undo = self.undo.len();
        match self.exec_look_body(body_start, body_end)? {
            Some(_) => {
                self.truncate(entry_undo);
                Ok(self.fail())
            }
            None => {
                self.truncate(entry_undo);
                self.pc += 1;
                Ok(true)
            }
        }
    }
    fn exec_look_body(
        &mut self,
        body_start: usize,
        body_end: usize,
    ) -> Result<Option<usize>, RegexError> {
        let entry_undo = self.undo.len();
        let entry_pos = self.pos;
        let saved_backtrack = std::mem::take(&mut self.backtrack);
        let saved_pc = self.pc;
        let saved_end = self.end_pc;
        let saved_base = self.base_undo;
        self.pc = body_start;
        self.pos = entry_pos;
        self.end_pc = body_end;
        self.base_undo = entry_undo;
        let result = self.run()?;
        self.backtrack = saved_backtrack;
        self.pc = saved_pc;
        self.pos = entry_pos;
        self.end_pc = saved_end;
        self.base_undo = saved_base;
        Ok(result)
    }
    fn advance_forward(&mut self, width: usize) -> bool {
        self.advance_to(self.pos + width)
    }
    fn advance_backward(&mut self, width: usize) -> bool {
        match self.pos.checked_sub(width) {
            Some(next) => self.advance_to(next),
            None => self.fail(),
        }
    }
    fn advance_to(&mut self, next: usize) -> bool {
        self.pos = next;
        self.pc += 1;
        true
    }
    fn fail(&mut self) -> bool {
        match self.backtrack.pop() {
            Some(entry) => {
                self.truncate(entry.undo_len);
                self.pc = entry.pc;
                self.pos = entry.pos;
                true
            }
            None => {
                self.truncate(self.base_undo);
                false
            }
        }
    }
    fn truncate(&mut self, len: usize) {
        while self.undo.len() > len {
            match self.undo.pop() {
                Some(Undo::Capture { index, old }) => self.captures[index] = old,
                Some(Undo::Open { index, old }) => self.opens[index] = old,
                Some(Undo::LoopCount { id, old }) => self.counts[id] = old,
                Some(Undo::LoopAct { id, old }) => self.acts[id] = old,
                Some(Undo::LoopIter { id, old }) => self.iters[id] = old,
                None => break,
            }
        }
    }
}

/// The code point the matcher reads next, on whichever side of `position` that is.
fn adjacent_code_point(input: &[u16], position: usize, flags: Flags) -> Option<(u32, usize)> {
    if !flags.backward {
        return (position < input.len()).then(|| next_code_point(input, position, flags.unicode));
    }
    let low = *input.get(position.checked_sub(1)?)?;
    if flags.unicode
        && (0xdc00..=0xdfff).contains(&low)
        && position >= 2
        && (0xd800..=0xdbff).contains(&input[position - 2])
    {
        return Some((combine_surrogates(input[position - 2], low), 2));
    }
    Some((u32::from(low), 1))
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
    /// `(?ims-ims:...)`: its body runs under these flags instead.
    Modified {
        flags: Flags,
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
            Self::Space => is_space(value),
            Self::NotSpace => !is_space(value),
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

/// `WhiteSpace` and `LineTerminator`. Rust's own set adds U+0085 and omits U+FEFF.
fn is_space(value: u32) -> bool {
    value != 0x85 && (value == 0xfeff || char::from_u32(value).is_some_and(char::is_whitespace))
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
    names: Vec<(String, Vec<usize>)>,
    /// Names that could already have matched at this point of the pattern. A
    /// repeat within them is an error; a repeat in another alternative is not.
    reachable_names: Vec<String>,
    unicode: bool,
    flags: Flags,
    /// The pattern's capturing groups, including those not parsed yet.
    total_captures: usize,
    has_named_groups: bool,
    referenced_names: Vec<String>,
}

impl<'a> Parser<'a> {
    fn new(units: &'a [u16], flags: Flags) -> Self {
        let (total_captures, has_named_groups) = scan_groups(units);
        Self {
            units,
            position: 0,
            capture_count: 0,
            names: Vec::new(),
            reachable_names: Vec::new(),
            unicode: flags.unicode,
            flags,
            total_captures,
            has_named_groups,
            referenced_names: Vec::new(),
        }
    }

    fn parse_disjunction(&mut self, terminator: Option<u16>) -> Result<Node, RegexError> {
        let reachable = self.reachable_names.len();
        let mut branch_names = Vec::new();
        let mut branches = Vec::new();
        loop {
            branches.push(Node::Sequence(self.parse_sequence(terminator)?));
            branch_names.extend(self.reachable_names.drain(reachable..));
            if self.peek() != Some(u16::from(b'|')) {
                break;
            }
            self.position += 1;
        }
        self.reachable_names.extend(branch_names);
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
            let assertion = match &atom {
                Node::Start | Node::End | Node::WordBoundary(_) => true,
                Node::Look { behind, .. } => *behind || self.unicode,
                _ => false,
            };
            if assertion && self.at_quantifier()? {
                return Err(self.error("nothing to repeat"));
            }
            let quantified = self.parse_quantifier(atom, first_capture)?;
            let repeated = matches!(quantified, Node::Repeat { .. });
            nodes.push(quantified);
            if repeated && self.at_quantifier()? {
                return Err(self.error("nothing to repeat"));
            }
        }
        Ok(nodes)
    }

    fn parse_atom(&mut self) -> Result<Node, RegexError> {
        let token = self
            .next()
            .ok_or_else(|| self.error("expected regular expression atom"))?;
        if token == 0x7b && !self.unicode {
            self.position -= 1;
            let quantifier = self.at_quantifier()?;
            self.position += 1;
            if quantifier {
                return Err(self.error("nothing to repeat"));
            }
        }
        match token {
            0x2e => Ok(Node::Dot),
            0x5e => Ok(Node::Start),
            0x24 => Ok(Node::End),
            0x5b => self.parse_class().map(Node::Class),
            0x28 => self.parse_group(),
            0x5c => self.parse_escape(false),
            0x29 => Err(self.error("unmatched ')'")),
            0x2a | 0x2b | 0x3f => Err(self.error("nothing to repeat")),
            0x7b | 0x7d | 0x5d if self.unicode => Err(self.error("lone bracket in Unicode mode")),
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
        let outer_flags = self.flags;
        let mut modified = false;
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
                        let name = self.parse_group_name()?;
                        if self.reachable_names.contains(&name) {
                            return Err(self.error("invalid duplicate capture group name"));
                        }
                        self.capture_count += 1;
                        index = Some(self.capture_count);
                        self.reachable_names.push(name.clone());
                        match self.names.iter_mut().find(|(known, _)| *known == name) {
                            Some((_, indices)) => indices.push(self.capture_count),
                            None => self.names.push((name, vec![self.capture_count])),
                        }
                    }
                },
                Some(0x69 | 0x6d | 0x73 | 0x2d) => {
                    self.position -= 1;
                    self.flags = self.parse_modifiers()?;
                    modified = true;
                }
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
        let body_flags = std::mem::replace(&mut self.flags, outer_flags);
        Ok(if modified {
            Node::Modified {
                flags: body_flags,
                body: Box::new(body),
            }
        } else if let Some((behind, positive)) = look {
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

    /// The flags inside `(?ims-ims:`. Each letter may appear once, in either
    /// list, and at least one must appear.
    fn parse_modifiers(&mut self) -> Result<Flags, RegexError> {
        let mut flags = self.flags;
        let mut seen = Vec::new();
        let mut enable = true;
        loop {
            match self.next() {
                Some(0x3a) if !seen.is_empty() => return Ok(flags),
                Some(0x2d) if enable => enable = false,
                Some(unit @ (0x69 | 0x6d | 0x73)) if !seen.contains(&unit) => {
                    seen.push(unit);
                    match unit {
                        0x69 => flags.ignore_case = enable,
                        0x6d => flags.multiline = enable,
                        _ => flags.dot_all = enable,
                    }
                }
                _ => return Err(self.error("invalid group")),
            }
        }
    }

    fn parse_class(&mut self) -> Result<CharacterClass, RegexError> {
        let negated = if self.peek() == Some(0x5e) {
            self.position += 1;
            true
        } else {
            false
        };
        let mut items = Vec::new();
        while let Some(token) = self.peek() {
            if token == 0x5d {
                self.position += 1;
                return Ok(CharacterClass { negated, items });
            }
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
            0x6b if self.unicode || self.has_named_groups => {
                if self.next() != Some(0x3c) {
                    return Err(self.error("invalid named reference"));
                }
                let name = self.parse_group_name()?;
                self.referenced_names.push(name.clone());
                Ok(Node::NamedBackReference(name))
            }
            value if value <= 0x7f && (value as u8).is_ascii_digit() && value != 0x30 => {
                let checkpoint = self.position;
                let mut number = (value - 0x30) as usize;
                while let Some(digit) = self.peek().and_then(decimal_digit) {
                    self.position += 1;
                    number = number
                        .checked_mul(10)
                        .and_then(|number| number.checked_add(digit))
                        .ok_or_else(|| self.error("backreference number is too large"))?;
                }
                if number <= self.total_captures {
                    return Ok(Node::BackReference(number));
                }
                if self.unicode {
                    return Err(self.error("invalid back reference"));
                }
                self.position = checkpoint;
                self.escape_character(value, false).map(Node::Literal)
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
            0x30 if self.unicode && self.peek().and_then(decimal_digit).is_some() => {
                Err(self.error("invalid decimal escape"))
            }
            0x30 if self.unicode || !self.peek().is_some_and(is_octal_digit) => Ok(0),
            0x30..=0x37 if !self.unicode => Ok(self.legacy_octal_escape(escaped)),
            0x63 => self.control_escape(in_class),
            0x78 => match self.hex_escape(2) {
                Err(_) if !self.unicode => Ok(0x78),
                result => result,
            },
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

    /// `\c`. Without a letter, Annex B reads the backslash as itself and leaves the
    /// `c` to be read next, and a class also takes a digit or `_`.
    fn control_escape(&mut self, in_class: bool) -> Result<u32, RegexError> {
        let letter = self.peek().filter(|unit| {
            u8::try_from(*unit).is_ok_and(|byte| {
                byte.is_ascii_alphabetic()
                    || (in_class && !self.unicode && (byte.is_ascii_digit() || byte == b'_'))
            })
        });
        match letter {
            Some(letter) => {
                self.position += 1;
                Ok(u32::from(letter) % 32)
            }
            None if !self.unicode => {
                self.position -= 1;
                Ok(0x5c)
            }
            None => Err(self.error("invalid control escape")),
        }
    }

    /// Annex B `LegacyOctalEscapeSequence`: at most three digits, up to `\377`.
    fn legacy_octal_escape(&mut self, first: u16) -> u32 {
        let mut value = u32::from(first) - 0x30;
        for _ in 0..2 {
            match self.peek().filter(|unit| is_octal_digit(*unit)) {
                Some(unit) if value * 8 + u32::from(unit) - 0x30 <= 0o377 => {
                    value = value * 8 + u32::from(unit) - 0x30;
                    self.position += 1;
                }
                _ => break,
            }
        }
        value
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
                let Some(bounds) = self.parse_braced_bounds()? else {
                    return Ok(atom);
                };
                bounds
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

    /// `{n}`, `{n,}` or `{n,m}` at the cursor. Anything else leaves the cursor
    /// there: it is a literal `{` under Annex B and an error in Unicode mode.
    fn parse_braced_bounds(&mut self) -> Result<Option<(usize, Option<usize>)>, RegexError> {
        let checkpoint = self.position;
        self.position += 1;
        let bounds = self.parse_decimal().and_then(|minimum| match self.next() {
            Some(0x7d) => Some((minimum, Some(minimum))),
            Some(0x2c) => {
                let maximum = self.parse_decimal();
                (self.next() == Some(0x7d)).then_some((minimum, maximum))
            }
            _ => None,
        });
        let Some((minimum, maximum)) = bounds else {
            self.position = checkpoint;
            return if self.unicode {
                Err(self.error("invalid quantifier"))
            } else {
                Ok(None)
            };
        };
        if maximum.is_some_and(|maximum| maximum < minimum) {
            return Err(self.error("quantifier range out of order"));
        }
        Ok(Some((minimum, maximum)))
    }

    /// Whether a quantifier starts here, without consuming it.
    fn at_quantifier(&mut self) -> Result<bool, RegexError> {
        match self.peek() {
            Some(0x2a | 0x2b | 0x3f) => Ok(true),
            Some(0x7b) => {
                let checkpoint = self.position;
                let bounds = self.parse_braced_bounds()?;
                self.position = checkpoint;
                Ok(bounds.is_some())
            }
            _ => Ok(false),
        }
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

    /// `GroupName` up to and including `>`. Escapes name a code point, and each
    /// code point must fit an identifier.
    fn parse_group_name(&mut self) -> Result<String, RegexError> {
        let mut name = String::new();
        loop {
            let invalid = |parser: &Self| parser.error("invalid capture group name");
            let unit = self.next().ok_or_else(|| invalid(self))?;
            if unit == 0x3e {
                break;
            }
            let value = if unit == 0x5c {
                if self.next() != Some(0x75) {
                    return Err(invalid(self));
                }
                self.group_name_escape()?
            } else {
                let start = self.position - 1;
                let (value, width) = next_code_point(self.units, start, true);
                self.position = start + width;
                value
            };
            let character = char::from_u32(value).ok_or_else(|| invalid(self))?;
            let allowed = matches!(character, '$' | '_')
                || character.is_alphabetic()
                || (!name.is_empty()
                    && (character.is_alphanumeric()
                        || matches!(character, '\u{200c}' | '\u{200d}')));
            if !allowed {
                return Err(invalid(self));
            }
            name.push(character);
        }
        if name.is_empty() {
            return Err(self.error("invalid capture group name"));
        }
        Ok(name)
    }

    /// The code point after `\u` in a group name, which reads as in Unicode mode
    /// whatever the pattern's flags are.
    fn group_name_escape(&mut self) -> Result<u32, RegexError> {
        if self.peek() == Some(0x7b) {
            self.position += 1;
            let digits = self.take_until(0x7d)?;
            return u32::from_str_radix(&digits, 16)
                .ok()
                .filter(|value| *value <= 0x10ffff)
                .ok_or_else(|| self.error("invalid Unicode escape"));
        }
        let first = self.hex_escape(4)?;
        if (0xd800..=0xdbff).contains(&first) && self.units.get(self.position) == Some(&0x5c) {
            let checkpoint = self.position;
            self.position += 1;
            if self.next() == Some(0x75)
                && let Ok(second) = self.hex_escape(4)
                && (0xdc00..=0xdfff).contains(&second)
            {
                return Ok(combine_surrogates(first as u16, second as u16));
            }
            self.position = checkpoint;
        }
        Ok(first)
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

fn is_octal_digit(unit: u16) -> bool {
    (0x30..=0x37).contains(&unit)
}

/// Counts the capturing groups in a pattern, and says whether any is named.
fn scan_groups(units: &[u16]) -> (usize, bool) {
    let (mut count, mut named, mut in_class, mut position) = (0, false, false, 0);
    while let Some(unit) = units.get(position).copied() {
        match unit {
            0x5c => position += 1,
            0x5b => in_class = true,
            0x5d => in_class = false,
            0x28 if !in_class => match units.get(position + 1) {
                Some(0x3f) => {
                    let name = units.get(position + 2) == Some(&0x3c)
                        && !matches!(units.get(position + 3), Some(0x3d | 0x21));
                    count += usize::from(name);
                    named |= name;
                }
                _ => count += 1,
            },
            _ => {}
        }
        position += 1;
    }
    (count, named)
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
    fn modifiers_change_flags_only_inside_their_group() {
        assert_eq!(ranges("(?i:a)b", "", "Ab"), [Some(0..2)]);
        assert!(regex("(?i:a)b", "").exec(&text("AB"), 0).unwrap().is_none());
        assert!(
            regex("(?-i:a)b", "i")
                .exec(&text("Ab"), 0)
                .unwrap()
                .is_none()
        );
        assert_eq!(ranges("(?-i:a)b", "i", "aB"), [Some(0..2)]);
        assert_eq!(ranges("(?s:.).", "", "\na"), [Some(0..2)]);
        assert_eq!(ranges("(?m:^b)", "", "a\nb"), [Some(2..3)]);
        assert_eq!(ranges("(?i:(?-i:a)b)", "", "aB"), [Some(0..2)]);
        for pattern in [
            "(?-:a)",
            "(?ii:a)",
            "(?i-i:a)",
            "(?g:a)",
            "(?i--s:a)",
            "(?I:a)",
        ] {
            assert!(
                Regex::compile(&text(pattern), &text("")).is_err(),
                "{pattern}"
            );
        }
    }

    #[test]
    fn a_group_name_may_repeat_only_across_alternatives() {
        let regex = regex("(?<year>a)|(?<year>b)", "");
        let matched = regex.exec(&text("b"), 0).unwrap().unwrap();
        assert_eq!(matched.named, [("year".to_owned(), Some(0..1))]);
        for pattern in ["(?<x>a)(?<x>b)", "(?<x>(?<x>a))", "(?:(?<x>a)|b)(?<x>c)"] {
            assert!(
                Regex::compile(&text(pattern), &text("")).is_err(),
                "{pattern}"
            );
        }
    }

    #[test]
    fn named_groups_keep_source_order() {
        let matched = regex("(?<z>a)(?<b>b)", "")
            .exec(&text("ab"), 0)
            .unwrap()
            .unwrap();
        let names: Vec<_> = matched
            .named
            .iter()
            .map(|(name, _)| name.as_str())
            .collect();
        assert_eq!(names, ["z", "b"]);
    }

    #[test]
    fn annex_b_escapes_read_literally_outside_unicode_mode() {
        assert_eq!(ranges("\\x", "", "x"), [Some(0..1)]);
        assert_eq!(ranges("\\c", "", "\\c"), [Some(0..2)]);
        assert_eq!(ranges("\\ca", "", "\u{1}"), [Some(0..1)]);
        assert_eq!(ranges("[\\c1]", "", "\u{11}"), [Some(0..1)]);
        assert_eq!(ranges("[\\12-\\14]", "", "\n"), [Some(0..1)]);
        assert_eq!(ranges("\\1", "", "\u{1}"), [Some(0..1)]);
        assert_eq!(ranges("a{1,b}", "", "a{1,b}"), [Some(0..6)]);
        assert_eq!(ranges("\\k<a", "", "k<a"), [Some(0..3)]);
        for pattern in ["\\1", "\\c", "a{1,b}", "}", "]"] {
            assert!(
                Regex::compile(&text(pattern), &text("u")).is_err(),
                "{pattern}"
            );
        }
    }

    #[test]
    fn nothing_can_repeat_a_quantifier_or_an_assertion() {
        for pattern in ["a**", "a{1}{2}", "a+?+", "^*", "\\b+", "(?<=a)*", "{1}"] {
            assert!(
                Regex::compile(&text(pattern), &text("")).is_err(),
                "{pattern}"
            );
        }
        assert!(Regex::compile(&text("(?=a)*"), &text("")).is_ok());
        assert!(Regex::compile(&text("(?=a)*"), &text("u")).is_err());
    }

    #[test]
    fn an_empty_class_matches_nothing_and_its_negation_anything() {
        assert!(regex("[]", "").exec(&text("a"), 0).unwrap().is_none());
        assert_eq!(ranges("[^]", "", "a"), [Some(0..1)]);
    }

    #[test]
    fn a_required_iteration_may_match_empty() {
        assert_eq!(ranges("(a*)b\\1+", "", "baaac"), [Some(0..1), Some(0..0)]);
    }

    #[test]
    fn group_names_take_escapes_and_references_must_resolve() {
        let matched = regex("(?<\\u{41}b>x)", "")
            .exec(&text("x"), 0)
            .unwrap()
            .unwrap();
        assert_eq!(matched.named[0].0, "Ab");
        for pattern in ["\\k<x>(?<y>a)", "(?<1a>x)", "(?<>x)"] {
            assert!(
                Regex::compile(&text(pattern), &text("")).is_err(),
                "{pattern}"
            );
        }
    }

    #[test]
    fn a_repeat_explores_each_alternative_before_giving_back_an_iteration() {
        assert_eq!(
            ranges("(aa|aabaac|ba|b|c)*", "", "aabaac"),
            [Some(0..4), Some(2..4)]
        );
        assert_eq!(
            ranges("^([a-z]+)*[a-z]$", "", "abc"),
            [Some(0..3), Some(0..2)]
        );
    }

    #[test]
    fn a_lookahead_keeps_only_its_first_match() {
        assert_eq!(
            ranges("(?=(a+))a*b\\1", "", "baaabac"),
            [Some(3..6), Some(3..4)]
        );
    }

    #[test]
    fn whitespace_follows_the_ecmascript_set() {
        assert_eq!(ranges("\\s", "", "\u{feff}"), [Some(0..1)]);
        assert!(regex("\\s", "").exec(&text("\u{85}"), 0).unwrap().is_none());
    }

    #[test]
    fn a_lookbehind_reads_its_body_from_right_to_left() {
        assert_eq!(
            ranges("(?<=(\\d+)(\\d+))$", "", "1053"),
            [Some(4..4), Some(0..1), Some(1..4)]
        );
        assert_eq!(
            ranges("(?<=([abc])+)def", "", "abcdef"),
            [Some(3..6), Some(0..1)]
        );
        assert_eq!(ranges("(?<=\\1(a))b", "", "aab"), [Some(2..3), Some(1..2)]);
        assert!(
            regex("(?<!abc)\\w\\w\\w", "")
                .exec(&text("abcdef"), 3)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn a_modifier_group_reads_in_the_direction_of_its_lookbehind() {
        assert_eq!(ranges("(?<=(?i:ab))c", "", "ABc"), [Some(2..3)]);
        assert_eq!(ranges("(?<=(?i:a)b)c", "", "Abc"), [Some(2..3)]);
        assert_eq!(
            ranges(r"(?<=(?i:(\d+)(\d+)))$", "", "1053"),
            [Some(4..4), Some(0..1), Some(1..4)]
        );
        assert!(
            regex("(?<=(?-i:a)b)c", "i")
                .exec(&text("ABc"), 0)
                .unwrap()
                .is_none()
        );
        assert_eq!(ranges("(?<=(?-i:a)b)c", "i", "aBc"), [Some(2..3)]);
    }

    #[test]
    fn each_repeat_iteration_forgets_the_captures_inside_it() {
        assert_eq!(ranges("(?:(a)|b)*", "", "ab"), [Some(0..2), None]);
        assert_eq!(
            ranges("(?:(?<x>a)|(?<x>b)){2}\\k<x>", "", "abb"),
            [Some(0..3), None, Some(1..2)]
        );
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
        let re = regex("((a)|(a)|(a))*b", "");
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
    mod oracle {
        use super::super::{
            Flags, Match, Node, Parser, RegexError, STEP_BUDGET, adjacent_code_point, canonicalize,
            combine_surrogates, is_line_terminator, is_word, next_code_point,
        };
        use bamts_bytecode::EcmaString;
        use std::collections::HashSet;
        use std::ops::Range;
        type OracleKey = (usize, usize, Vec<Option<(usize, usize)>>);
        pub(super) struct OracleRegex {
            expression: Node,
            flags: Flags,
            capture_count: usize,
            names: Vec<(String, Vec<usize>)>,
        }
        #[derive(Clone, Debug)]
        struct OracleState {
            position: usize,
            captures: Vec<Option<Range<usize>>>,
        }
        impl OracleState {
            fn moved_forward(self, count: usize) -> Self {
                let next = self.position + count;
                self.set_position(next)
            }
            fn moved_backward(self, count: usize) -> Self {
                let next = self.position - count;
                self.set_position(next)
            }
            fn set_position(mut self, position: usize) -> Self {
                self.position = position;
                self
            }
        }
        struct OracleRepeat<'a> {
            body: &'a Node,
            min: usize,
            max: Option<usize>,
            greedy: bool,
            captures: &'a Range<usize>,
        }
        impl OracleRegex {
            pub(super) fn compile(
                pattern: &EcmaString,
                flags: &EcmaString,
            ) -> Result<Self, RegexError> {
                let flags = Flags::parse(flags)?;
                let mut parser = Parser::new(pattern.as_units(), flags);
                let expression = parser.parse_disjunction(None)?;
                if parser.peek().is_some() {
                    return Err(parser.error("unexpected token"));
                }
                for name in &parser.referenced_names {
                    if !parser.names.iter().any(|(known, _)| known == name) {
                        return Err(parser.error("invalid named reference"));
                    }
                }
                Ok(Self {
                    expression,
                    flags,
                    capture_count: parser.capture_count,
                    names: parser.names,
                })
            }
            pub(super) fn exec(
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
                    let state = OracleState {
                        position,
                        captures: vec![None; self.capture_count + 1],
                    };
                    if let Some(matched) = self
                        .match_node(self.flags, &self.expression, input, state)?
                        .into_iter()
                        .next()
                    {
                        let end = matched.position;
                        let mut captures = matched.captures;
                        captures[0] = Some(position..end);
                        let named = self
                            .names
                            .iter()
                            .map(|(name, indices)| {
                                let participant =
                                    indices.iter().find_map(|index| captures[*index].clone());
                                (name.clone(), participant)
                            })
                            .collect();
                        return Ok(Some(Match {
                            range: position..end,
                            captures,
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
                flags: Flags,
                node: &Node,
                input: &[u16],
                state: OracleState,
            ) -> Result<Vec<OracleState>, RegexError> {
                match node {
                    Node::Sequence(nodes) => self.match_sequence(flags, nodes, input, state),
                    Node::Alternation(branches) => {
                        let mut out = Vec::new();
                        for branch in branches {
                            out.extend(self.match_node(flags, branch, input, state.clone())?);
                        }
                        Ok(out)
                    }
                    Node::Literal(expected) => {
                        let Some((actual, width)) =
                            adjacent_code_point(input, state.position, flags)
                        else {
                            return Ok(Vec::new());
                        };
                        Ok(self
                            .oracle_eq(flags, actual, *expected)
                            .then(|| {
                                if flags.backward {
                                    state.moved_backward(width)
                                } else {
                                    state.moved_forward(width)
                                }
                            })
                            .into_iter()
                            .collect())
                    }
                    Node::Dot => {
                        let Some((actual, width)) =
                            adjacent_code_point(input, state.position, flags)
                        else {
                            return Ok(Vec::new());
                        };
                        Ok((flags.dot_all || !is_line_terminator(actual))
                            .then(|| {
                                if flags.backward {
                                    state.moved_backward(width)
                                } else {
                                    state.moved_forward(width)
                                }
                            })
                            .into_iter()
                            .collect())
                    }
                    Node::Class(class) => {
                        let Some((actual, width)) =
                            adjacent_code_point(input, state.position, flags)
                        else {
                            return Ok(Vec::new());
                        };
                        Ok(class
                            .matches(actual, flags.ignore_case, flags.unicode)
                            .then(|| {
                                if flags.backward {
                                    state.moved_backward(width)
                                } else {
                                    state.moved_forward(width)
                                }
                            })
                            .into_iter()
                            .collect())
                    }
                    Node::Start => Ok((state.position == 0
                        || (flags.multiline
                            && state.position > 0
                            && is_line_terminator(u32::from(input[state.position - 1]))))
                    .then_some(state)
                    .into_iter()
                    .collect()),
                    Node::End => Ok((state.position == input.len()
                        || (flags.multiline
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
                            let value = if flags.unicode
                                && (0xdc00..=0xdfff).contains(&low)
                                && state.position >= 2
                                && (0xd800..=0xdbff).contains(&input[state.position - 2])
                            {
                                combine_surrogates(input[state.position - 2], low)
                            } else {
                                u32::from(low)
                            };
                            is_word(value, flags.ignore_case, flags.unicode)
                        };
                        let right = (state.position < input.len())
                            .then(|| next_code_point(input, state.position, flags.unicode).0)
                            .is_some_and(|value| is_word(value, flags.ignore_case, flags.unicode));
                        Ok(((left != right) == *positive)
                            .then_some(state)
                            .into_iter()
                            .collect())
                    }
                    Node::Group { index, body } => {
                        let begin = state.position;
                        Ok(self
                            .match_node(flags, body, input, state)?
                            .into_iter()
                            .map(|mut matched| {
                                if let Some(index) = index {
                                    matched.captures[*index] = Some(if flags.backward {
                                        matched.position..begin
                                    } else {
                                        begin..matched.position
                                    });
                                }
                                matched
                            })
                            .collect())
                    }
                    Node::Modified {
                        flags: modified,
                        body,
                    } => {
                        let inside = Flags {
                            backward: flags.backward,
                            ..*modified
                        };
                        self.match_node(inside, body, input, state)
                    }
                    Node::BackReference(index) => {
                        let Some(range) = state.captures.get(*index).and_then(Clone::clone) else {
                            return Ok(vec![state]);
                        };
                        Ok(self.match_backreference(flags, input, range, state))
                    }
                    Node::NamedBackReference(name) => {
                        let Some((_, indices)) = self.names.iter().find(|(known, _)| known == name)
                        else {
                            return Ok(Vec::new());
                        };
                        match indices
                            .iter()
                            .find_map(|index| state.captures[*index].clone())
                        {
                            Some(range) => Ok(self.match_backreference(flags, input, range, state)),
                            None => Ok(vec![state]),
                        }
                    }
                    Node::Look {
                        body,
                        behind,
                        positive,
                    } => {
                        let direction = Flags {
                            backward: *behind,
                            ..flags
                        };
                        let candidates = self.match_node(direction, body, input, state.clone())?;
                        Ok(if *positive {
                            candidates
                                .into_iter()
                                .take(1)
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
                    Node::Repeat { .. } => {
                        unreachable!("repeat is handled by its containing sequence")
                    }
                }
            }
            fn match_backreference(
                &self,
                flags: Flags,
                input: &[u16],
                range: Range<usize>,
                state: OracleState,
            ) -> Vec<OracleState> {
                let width = range.len();
                let start = if flags.backward {
                    state.position.checked_sub(width)
                } else {
                    Some(state.position).filter(|position| position + width <= input.len())
                };
                let Some(start) = start else {
                    return Vec::new();
                };
                let (mut captured, mut candidate) = (range.start, start);
                while captured < range.end {
                    if candidate >= input.len() {
                        return Vec::new();
                    }
                    let (left, left_width) = next_code_point(input, captured, flags.unicode);
                    let (right, right_width) = next_code_point(input, candidate, flags.unicode);
                    if captured + left_width > range.end || !self.oracle_eq(flags, left, right) {
                        return Vec::new();
                    }
                    captured += left_width;
                    candidate += right_width;
                }
                if candidate != start + width {
                    return Vec::new();
                }
                vec![if flags.backward {
                    state.moved_backward(width)
                } else {
                    state.moved_forward(width)
                }]
            }
            fn match_sequence(
                &self,
                flags: Flags,
                nodes: &[Node],
                input: &[u16],
                state: OracleState,
            ) -> Result<Vec<OracleState>, RegexError> {
                let split = if flags.backward {
                    nodes.split_last()
                } else {
                    nodes.split_first()
                };
                let Some((first, rest)) = split else {
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
                    self.match_repeat(
                        flags,
                        &OracleRepeat {
                            body,
                            min: *min,
                            max: *max,
                            greedy: *greedy,
                            captures,
                        },
                        rest,
                        input,
                        state,
                    )
                } else {
                    let mut result = Vec::new();
                    for matched in self.match_node(flags, first, input, state)? {
                        result.extend(self.match_sequence(flags, rest, input, matched)?);
                    }
                    Ok(result)
                }
            }
            fn match_repeat(
                &self,
                flags: Flags,
                repeat: &OracleRepeat<'_>,
                rest: &[Node],
                input: &[u16],
                state: OracleState,
            ) -> Result<Vec<OracleState>, RegexError> {
                enum Step {
                    Expand { state: OracleState, count: usize },
                    Continue(OracleState),
                }
                let mut result = Vec::new();
                let mut steps = 0;
                let mut seen: HashSet<OracleKey> = HashSet::new();
                let mut stack = vec![Step::Expand { state, count: 0 }];
                while let Some(step) = stack.pop() {
                    let (state, count) = match step {
                        Step::Continue(state) => {
                            result.extend(self.match_sequence(flags, rest, input, state)?);
                            continue;
                        }
                        Step::Expand { state, count } => (state, count),
                    };
                    let tracked = if repeat.max.is_some() {
                        count
                    } else {
                        count.min(repeat.min)
                    };
                    let key = (
                        tracked,
                        state.position,
                        state
                            .captures
                            .iter()
                            .map(|capture| capture.as_ref().map(|range| (range.start, range.end)))
                            .collect(),
                    );
                    if !seen.insert(key) {
                        continue;
                    }
                    steps += 1;
                    if steps > STEP_BUDGET.max(input.len().saturating_mul(2)) {
                        return Err(RegexError::budget_exhausted());
                    }
                    let mut iterations = Vec::new();
                    if repeat.max.is_none_or(|max| count < max) {
                        let mut attempt = state.clone();
                        attempt.captures[repeat.captures.clone()].fill(None);
                        iterations = self.match_node(flags, repeat.body, input, attempt)?;
                        iterations.retain(|matched| {
                            count < repeat.min || matched.position != state.position
                        });
                    }
                    let stop = (count >= repeat.min).then_some(Step::Continue(state));
                    let next = iterations.into_iter().rev().map(|state| Step::Expand {
                        state,
                        count: count + 1,
                    });
                    if repeat.greedy {
                        stack.extend(stop);
                        stack.extend(next);
                    } else {
                        stack.extend(next);
                        stack.extend(stop);
                    }
                }
                Ok(result)
            }
            fn oracle_eq(&self, flags: Flags, left: u32, right: u32) -> bool {
                left == right
                    || (flags.ignore_case
                        && canonicalize(left, flags.unicode) == canonicalize(right, flags.unicode))
            }
        }
    }
    struct XorShift64(u64);
    impl XorShift64 {
        fn seed() -> Self {
            Self(0x1A2B3C4D5E6F7081)
        }
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn below(&mut self, n: usize) -> usize {
            let span = u64::try_from(n).unwrap_or(u64::MAX);
            usize::try_from(self.next() % span).unwrap_or(0)
        }
    }
    fn gen_atom(rng: &mut XorShift64) -> String {
        match rng.below(9) {
            0 | 1 | 2 => ["a", "b", "c"][rng.below(3)].to_string(),
            3 => ".".to_string(),
            4 => "[ab]".to_string(),
            5 => "\\d".to_string(),
            6 => "^".to_string(),
            7 => "$".to_string(),
            _ => ["\\1", "\\2", "1"][rng.below(3)].to_string(),
        }
    }
    fn gen_quant(rng: &mut XorShift64) -> &'static str {
        ["*", "+", "?", "*?", "+?", "??", "{1,2}", "{2}"][rng.below(8)]
    }
    fn gen_pattern(rng: &mut XorShift64, depth: usize) -> String {
        if depth == 0 {
            return gen_atom(rng);
        }
        match rng.below(9) {
            0 => gen_atom(rng) + gen_quant(rng),
            1 => "(".to_string() + &gen_pattern(rng, depth - 1) + ")",
            2 => "(?:".to_string() + &gen_pattern(rng, depth - 1) + ")",
            3 => gen_pattern(rng, depth - 1) + &gen_pattern(rng, depth - 1),
            4 => gen_pattern(rng, depth - 1) + "|" + &gen_pattern(rng, depth - 1),
            5 => "(?=".to_string() + &gen_pattern(rng, depth - 1) + ")",
            6 => "(?!".to_string() + &gen_pattern(rng, depth - 1) + ")",
            7 => "(?<=".to_string() + &gen_pattern(rng, depth - 1) + ")",
            _ => "(?<!".to_string() + &gen_pattern(rng, depth - 1) + ")",
        }
    }
    fn gen_subject(rng: &mut XorShift64) -> String {
        let len = rng.below(9);
        let mut out = String::new();
        for _ in 0..len {
            out.push_str(["a", "b", "c", "1"][rng.below(4)]);
        }
        out
    }
    #[test]
    fn compiled_matcher_agrees_with_tree_walker() {
        let flag_sets = ["", "i", "m", "s", "y", "u", "gi", "ms"];
        let mut rng = XorShift64::seed();
        for _ in 0..2000 {
            let pattern = gen_pattern(&mut rng, 2);
            let flags = flag_sets[rng.below(flag_sets.len())];
            let subject = gen_subject(&mut rng);
            let oracle = oracle::OracleRegex::compile(&text(&pattern), &text(flags));
            let compiled = Regex::compile(&text(&pattern), &text(flags));
            match (oracle, compiled) {
                (Err(_), Err(_)) => {}
                (Ok(o), Ok(n)) => {
                    let o_exec = o.exec(&text(&subject), 0);
                    let n_exec = n.exec(&text(&subject), 0);
                    match (o_exec, n_exec) {
                        (Err(a), Err(b)) => assert_eq!(
                            a.kind(),
                            b.kind(),
                            "kinds differ on {pattern:?} {flags:?} {subject:?}"
                        ),
                        (Ok(a), Ok(b)) => {
                            assert_eq!(a, b, "matches differ on {pattern:?} {flags:?} {subject:?}")
                        }
                        _ => panic!("exec diverged on {pattern:?} {flags:?} {subject:?}"),
                    }
                }
                _ => panic!("compile diverged on {pattern:?} {flags:?}"),
            }
        }
    }
}
