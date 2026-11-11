//! The generic RegExp protocol: `RegExpExec`, the `Symbol`-keyed methods of
//! `%RegExp.prototype%`, and `GetSubstitution`.
//!
//! Every algorithm here is written against the observable object protocol, not
//! the matcher. A receiver need not be a RegExp, `exec` may be user code, and
//! the order of `Get`, `Set` and coercion is part of the specification, so the
//! only path to the engine is the builtin `exec`.

use bamts_bytecode::{EcmaString, EcmaStringBuilder};
use bamts_native::{Decoded, Value};

use super::array_es2023::{index_key, integer_or_infinity, length_of_array_like};
use super::array_generic::tick;
use super::regexp::{builtin_exec, regexp_parts};
use super::{allocate_array, allocate_string, keep_root, type_error, with_roots};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, Property};

const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;

fn argument(args: &[Value], index: usize) -> Value {
    args.get(index).copied().unwrap_or(Value::UNDEFINED)
}

fn require_object<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
    operation: &'static str,
) -> Result<(), EvalFailure> {
    if machine.is_object(value) {
        Ok(())
    } else {
        Err(type_error(operation))
    }
}

fn append(output: &mut EcmaStringBuilder, units: &[u16]) {
    for &unit in units {
        output.push_unit(unit);
    }
}

fn contains_flag(flags: &EcmaString, flag: u8) -> bool {
    flags.as_units().contains(&u16::from(flag))
}

fn is_full_unicode(flags: &EcmaString) -> bool {
    contains_flag(flags, b'u') || contains_flag(flags, b'v')
}

/// `ToString(? Get(rx, "flags"))`.
fn flags_text<H: Host>(machine: &mut Machine<'_, H>, rx: Value) -> Result<EcmaString, EvalFailure> {
    let flags = machine.get_named_property(rx, "flags")?;
    machine.coerce_string_observable(flags)
}

/// `ToLength`, with user conversion. Lengths are bounded by 2^53 - 1, which fits
/// a `usize` on every supported target.
pub(super) fn to_length<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<usize, EvalFailure> {
    let length = integer_or_infinity(machine, value)?;
    Ok(length.clamp(0.0, MAX_SAFE_INTEGER) as usize)
}

/// `AdvanceStringIndex`. Positions past the end stay simple increments, because
/// `lastIndex` can hold any length.
fn advance_string_index(string: &EcmaString, index: usize, unicode: bool) -> usize {
    if !unicode || index + 1 >= string.len_units() {
        return index + 1;
    }
    index + crate::intrinsics::regexp::next_code_point(string.as_units(), index, true).1
}

fn set_last_index<H: Host>(
    machine: &mut Machine<'_, H>,
    rx: Value,
    index: usize,
) -> Result<(), EvalFailure> {
    machine.set_data_property(rx, "lastIndex", crate::number_value(index as f64))
}

/// `RegExpExec`: a callable `exec` wins, whatever the receiver is. The builtin
/// runs only when `exec` is not callable, and then the receiver must be a RegExp.
pub(super) fn regexp_exec<H: Host>(
    machine: &mut Machine<'_, H>,
    regexp: Value,
    input: Value,
) -> Result<Value, EvalFailure> {
    let exec = machine.get_named_property(regexp, "exec")?;
    if machine.is_callable(exec)? {
        let result = machine.call_value(exec, regexp, &[input])?;
        if result == Value::NULL || machine.is_object(result) {
            return Ok(result);
        }
        return Err(type_error("RegExp exec method returned a non-object"));
    }
    let text = machine.string_value(input).unwrap_or_default();
    builtin_exec(machine, regexp, &text)
}

/// The step every global loop shares: an empty match would never advance, so it
/// moves `lastIndex` past itself explicitly.
fn advance_past_empty_match<H: Host>(
    machine: &mut Machine<'_, H>,
    rx: Value,
    string: &EcmaString,
    unicode: bool,
) -> Result<(), EvalFailure> {
    let last_index = machine.get_named_property(rx, "lastIndex")?;
    let this_index = to_length(machine, last_index)?;
    let next_index = advance_string_index(string, this_index, unicode);
    set_last_index(machine, rx, next_index)
}

/// `RegExp.prototype.test`.
pub(super) fn test<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_object(machine, this, "RegExp.prototype.test requires an object")?;
    let string = machine.coerce_string_observable(argument(args, 0))?;
    let input = allocate_string(machine, string)?;
    let result = with_roots(machine, &[this, input], |machine, _| {
        regexp_exec(machine, this, input)
    })?;
    Ok(BuiltinOutcome::Value(Value::boolean(result != Value::NULL)))
}

/// `RegExp.prototype[@@match]`.
pub(super) fn symbol_match<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_object(
        machine,
        this,
        "RegExp.prototype[Symbol.match] requires an object",
    )?;
    let string = machine.coerce_string_observable(argument(args, 0))?;
    let input = allocate_string(machine, string.clone())?;
    with_roots(machine, &[this, input], |machine, depth| {
        let flags = flags_text(machine, this)?;
        if !contains_flag(&flags, b'g') {
            return regexp_exec(machine, this, input);
        }
        let unicode = is_full_unicode(&flags);
        set_last_index(machine, this, 0)?;
        let mut matches = Vec::new();
        loop {
            let result = regexp_exec(machine, this, input)?;
            if result == Value::NULL {
                return if matches.is_empty() {
                    Ok(Value::NULL)
                } else {
                    allocate_array(machine, matches)
                };
            }
            let matched = machine.get_named_property(result, "0")?;
            let matched = machine.coerce_string_observable(matched)?;
            let empty = matched.is_empty();
            let value = allocate_string(machine, matched)?;
            keep_root(machine, depth, value);
            matches.push(value);
            if empty {
                advance_past_empty_match(machine, this, &string, unicode)?;
            }
        }
    })
    .map(BuiltinOutcome::Value)
}

/// `RegExp.prototype[@@search]`. `lastIndex` is restored, so a search leaves the
/// receiver as it found it.
pub(super) fn symbol_search<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_object(
        machine,
        this,
        "RegExp.prototype[Symbol.search] requires an object",
    )?;
    let string = machine.coerce_string_observable(argument(args, 0))?;
    let input = allocate_string(machine, string)?;
    with_roots(machine, &[this, input], |machine, depth| {
        let previous = machine.get_named_property(this, "lastIndex")?;
        keep_root(machine, depth, previous);
        if !machine.same_value(previous, Value::int32(0)) {
            set_last_index(machine, this, 0)?;
        }
        let result = regexp_exec(machine, this, input)?;
        keep_root(machine, depth, result);
        let current = machine.get_named_property(this, "lastIndex")?;
        if !machine.same_value(current, previous) {
            machine.set_data_property(this, "lastIndex", previous)?;
        }
        if result == Value::NULL {
            return Ok(Value::int32(-1i32 as u32));
        }
        machine.get_named_property(result, "index")
    })
    .map(BuiltinOutcome::Value)
}

/// `SpeciesConstructor`.
pub(super) fn species_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    default: Value,
) -> Result<Value, EvalFailure> {
    let constructor = machine.get_named_property(object, "constructor")?;
    if constructor == Value::UNDEFINED {
        return Ok(default);
    }
    if !machine.is_object(constructor) {
        return Err(type_error("constructor property is not an object"));
    }
    let key = machine.to_property_key(machine.intrinsics.builtins.symbol_species())?;
    let species = machine.get_property_key(constructor, &key)?;
    if matches!(species.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        return Ok(default);
    }
    if machine.is_constructor(species)? {
        Ok(species)
    } else {
        Err(type_error("Symbol.species is not a constructor"))
    }
}

fn regexp_constructor<H: Host>(machine: &Machine<'_, H>) -> Result<Value, EvalFailure> {
    machine
        .intrinsics
        .global("RegExp")
        .ok_or_else(|| type_error("RegExp constructor is unavailable"))
}

/// `RegExp.prototype[@@split]`. The search runs on a sticky copy, so each step
/// asks "does a separator start exactly here" and the loop advances itself.
pub(super) fn symbol_split<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_object(
        machine,
        this,
        "RegExp.prototype[Symbol.split] requires an object",
    )?;
    let string = machine.coerce_string_observable(argument(args, 0))?;
    let input = allocate_string(machine, string.clone())?;
    let limit = argument(args, 1);
    with_roots(machine, &[this, input, limit], |machine, depth| {
        let default = regexp_constructor(machine)?;
        let constructor = species_constructor(machine, this, default)?;
        keep_root(machine, depth, constructor);
        let flags = flags_text(machine, this)?;
        let unicode = is_full_unicode(&flags);
        let new_flags = if contains_flag(&flags, b'y') {
            flags
        } else {
            let mut sticky = EcmaStringBuilder::with_capacity(flags.len_units() + 1);
            for &unit in flags.as_units() {
                sticky.push_unit(unit);
            }
            sticky.push_unit(u16::from(b'y'));
            sticky.finish()
        };
        let new_flags = allocate_string(machine, new_flags)?;
        let splitter = machine.construct_value(constructor, &[this, new_flags])?;
        keep_root(machine, depth, splitter);
        let limit = if limit == Value::UNDEFINED {
            u32::MAX
        } else {
            crate::to_uint32(super::value_number(
                machine.coerce_number_observable(limit)?,
            ))
        };
        if limit == 0 {
            return allocate_array(machine, Vec::new());
        }
        split_steps(machine, depth, splitter, &string, input, limit, unicode)
    })
    .map(BuiltinOutcome::Value)
}

fn split_steps<H: Host>(
    machine: &mut Machine<'_, H>,
    depth: usize,
    splitter: Value,
    string: &EcmaString,
    input: Value,
    limit: u32,
    unicode: bool,
) -> Result<Value, EvalFailure> {
    let limit = limit as usize;
    let size = string.len_units();
    if size == 0 {
        if regexp_exec(machine, splitter, input)? != Value::NULL {
            return allocate_array(machine, Vec::new());
        }
        return allocate_array(machine, vec![input]);
    }
    let mut pieces = Vec::new();
    let (mut piece_start, mut search_at) = (0, 0);
    while search_at < size {
        set_last_index(machine, splitter, search_at)?;
        let matched = regexp_exec(machine, splitter, input)?;
        if matched == Value::NULL {
            search_at = advance_string_index(string, search_at, unicode);
            continue;
        }
        keep_root(machine, depth, matched);
        let end = machine.get_named_property(splitter, "lastIndex")?;
        let end = to_length(machine, end)?.min(size);
        if end == piece_start {
            search_at = advance_string_index(string, search_at, unicode);
            continue;
        }
        let piece = allocate_string(
            machine,
            super::regexp::slice_units(string, piece_start..search_at),
        )?;
        keep_root(machine, depth, piece);
        pieces.push(piece);
        if pieces.len() == limit {
            return allocate_array(machine, pieces);
        }
        piece_start = end;
        let captures = length_of_array_like(machine, matched)?.saturating_sub(1);
        // The pieces of every match so far count too: each match can claim again.
        budget_claimed_captures(
            machine,
            pieces.len() + captures.min(limit - pieces.len()),
            2 * std::mem::size_of::<Value>(),
        )?;
        for index in 1..=captures {
            tick(machine)?;
            let capture = machine.get_property_key(matched, &index_key(index))?;
            keep_root(machine, depth, capture);
            pieces.push(capture);
            if pieces.len() == limit {
                return allocate_array(machine, pieces);
            }
        }
        search_at = piece_start;
    }
    let tail = allocate_string(
        machine,
        super::regexp::slice_units(string, piece_start..size),
    )?;
    pieces.push(tail);
    allocate_array(machine, pieces)
}

/// Holds `count` captures of `size` bytes each against the heap budget before a loop
/// reads them. A result of `exec` can claim any length, so the claim reserves no
/// memory, and a claim past the budget is a runtime failure in place of a loop that
/// ends when the host has no more memory.
fn budget_claimed_captures<H: Host>(
    machine: &Machine<'_, H>,
    count: usize,
    size: usize,
) -> Result<(), EvalFailure> {
    machine
        .ensure_allocation_capacity(0, count.saturating_mul(size))
        .map_err(EvalFailure::Runtime)
}

/// One match result read in full, as `@@replace` requires before it calls user
/// code for any replacement.
struct ReplaceStep {
    matched: EcmaString,
    position: usize,
    captures: Vec<Option<EcmaString>>,
    named: Value,
}

fn read_replace_step<H: Host>(
    machine: &mut Machine<'_, H>,
    result: Value,
    length: usize,
) -> Result<ReplaceStep, EvalFailure> {
    let capture_count = length_of_array_like(machine, result)?.saturating_sub(1);
    let matched = machine.get_named_property(result, "0")?;
    let matched = machine.coerce_string_observable(matched)?;
    let position = machine.get_named_property(result, "index")?;
    let position = integer_or_infinity(machine, position)?.clamp(0.0, length as f64) as usize;
    budget_claimed_captures(
        machine,
        capture_count,
        std::mem::size_of::<Option<EcmaString>>(),
    )?;
    let mut captures = Vec::new();
    for index in 1..=capture_count {
        tick(machine)?;
        let capture = machine.get_property_key(result, &index_key(index))?;
        captures.push(if capture == Value::UNDEFINED {
            None
        } else {
            Some(machine.coerce_string_observable(capture)?)
        });
    }
    let named = machine.get_named_property(result, "groups")?;
    Ok(ReplaceStep {
        matched,
        position,
        captures,
        named,
    })
}

fn functional_replacement<H: Host>(
    machine: &mut Machine<'_, H>,
    replacer: Value,
    step: &ReplaceStep,
    input: Value,
) -> Result<EcmaString, EvalFailure> {
    let mut arguments = Vec::with_capacity(step.captures.len() + 4);
    arguments.push(allocate_string(machine, step.matched.clone())?);
    for capture in &step.captures {
        arguments.push(match capture {
            Some(text) => allocate_string(machine, text.clone())?,
            None => Value::UNDEFINED,
        });
    }
    arguments.push(crate::number_value(step.position as f64));
    arguments.push(input);
    if step.named != Value::UNDEFINED {
        arguments.push(step.named);
    }
    let value = machine.call_value(replacer, Value::UNDEFINED, &arguments)?;
    machine.coerce_string_observable(value)
}

/// `RegExp.prototype[@@replace]`. All matching finishes before the first
/// replacement runs, so a replacer cannot change what was matched.
pub(super) fn symbol_replace<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_object(
        machine,
        this,
        "RegExp.prototype[Symbol.replace] requires an object",
    )?;
    let string = machine.coerce_string_observable(argument(args, 0))?;
    let replace_value = argument(args, 1);
    let functional = machine.is_callable(replace_value)?;
    let template = if functional {
        None
    } else {
        Some(machine.coerce_string_observable(replace_value)?)
    };
    let input = allocate_string(machine, string.clone())?;
    with_roots(machine, &[this, input, replace_value], |machine, depth| {
        let flags = flags_text(machine, this)?;
        let global = contains_flag(&flags, b'g');
        let unicode = is_full_unicode(&flags);
        if global {
            set_last_index(machine, this, 0)?;
        }
        let mut results = Vec::new();
        loop {
            let result = regexp_exec(machine, this, input)?;
            if result == Value::NULL {
                break;
            }
            keep_root(machine, depth, result);
            results.push(result);
            if !global {
                break;
            }
            let matched = machine.get_named_property(result, "0")?;
            if machine.coerce_string_observable(matched)?.is_empty() {
                advance_past_empty_match(machine, this, &string, unicode)?;
            }
        }
        let length = string.len_units();
        let mut output = EcmaStringBuilder::new();
        let mut next_source_position = 0;
        for result in results {
            let step = read_replace_step(machine, result, length)?;
            keep_root(machine, depth, step.named);
            let replacement = match &template {
                None => functional_replacement(machine, replace_value, &step, input)?,
                Some(template) => {
                    let named = if step.named == Value::UNDEFINED {
                        Value::UNDEFINED
                    } else {
                        let object = machine.value_to_object(step.named)?;
                        keep_root(machine, depth, object);
                        object
                    };
                    get_substitution(
                        machine,
                        &step.matched,
                        &string,
                        step.position,
                        &step.captures,
                        named,
                        template,
                    )?
                }
            };
            if step.position >= next_source_position {
                append(
                    &mut output,
                    &string.as_units()[next_source_position..step.position],
                );
                append(&mut output, replacement.as_units());
                next_source_position = step.position + step.matched.len_units();
            }
        }
        if next_source_position < length {
            append(&mut output, &string.as_units()[next_source_position..]);
        }
        allocate_string(machine, output.finish())
    })
    .map(BuiltinOutcome::Value)
}

fn ascii_digit(unit: u16) -> Option<usize> {
    (0x30..=0x39)
        .contains(&unit)
        .then(|| usize::from(unit - 0x30))
}

/// `GetSubstitution`. `captures` and `named` are empty and `undefined` for a
/// string search, which leaves `$1` and `$<` literal. `named` is an object or
/// `undefined`, and looking a group up in it can run user code.
pub(super) fn get_substitution<H: Host>(
    machine: &mut Machine<'_, H>,
    matched: &EcmaString,
    string: &EcmaString,
    position: usize,
    captures: &[Option<EcmaString>],
    named: Value,
    template: &EcmaString,
) -> Result<EcmaString, EvalFailure> {
    let units = template.as_units();
    let source = string.as_units();
    let mut output = EcmaStringBuilder::new();
    let mut offset = 0;
    while offset < units.len() {
        let unit = units[offset];
        if unit != u16::from(b'$') || offset + 1 == units.len() {
            output.push_unit(unit);
            offset += 1;
            continue;
        }
        let next = units[offset + 1];
        if next == u16::from(b'$') {
            output.push_unit(unit);
            offset += 2;
        } else if next == u16::from(b'&') {
            append(&mut output, matched.as_units());
            offset += 2;
        } else if next == u16::from(b'`') {
            append(&mut output, &source[..position.min(source.len())]);
            offset += 2;
        } else if next == u16::from(b'\'') {
            let tail = position
                .saturating_add(matched.len_units())
                .min(source.len());
            append(&mut output, &source[tail..]);
            offset += 2;
        } else if let Some(first) = ascii_digit(next) {
            let second = units.get(offset + 2).copied().and_then(ascii_digit);
            let (index, width) = match second {
                Some(second) if first * 10 + second <= captures.len() => (first * 10 + second, 2),
                _ => (first, 1),
            };
            if index == 0 || index > captures.len() {
                append(&mut output, &units[offset..offset + 1 + width]);
            } else if let Some(capture) = &captures[index - 1] {
                append(&mut output, capture.as_units());
            }
            offset += 1 + width;
        } else if next == u16::from(b'<') {
            let close = units[offset + 2..]
                .iter()
                .position(|candidate| *candidate == u16::from(b'>'));
            let (Some(close), false) = (close, named == Value::UNDEFINED) else {
                append(&mut output, &units[offset..offset + 2]);
                offset += 2;
                continue;
            };
            let name = EcmaString::from_units(&units[offset + 2..offset + 2 + close]);
            let capture = machine.get_property_key(named, &crate::PropertyKey::Named(name))?;
            if capture != Value::UNDEFINED {
                append(
                    &mut output,
                    machine.coerce_string_observable(capture)?.as_units(),
                );
            }
            offset += close + 3;
        } else {
            output.push_unit(unit);
            offset += 1;
        }
    }
    Ok(output.finish())
}

/// `CreateRegExpStringIterator`. The hidden state array is reachable only from
/// the iterator, and `position` going to `None` is the `done` state.
fn regexp_string_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    matcher: Value,
    input: Value,
    global: bool,
    unicode: bool,
) -> Result<Value, EvalFailure> {
    let state = machine
        .allocate(HeapEntry::Array {
            elements: vec![
                matcher,
                input,
                Value::boolean(global),
                Value::boolean(unicode),
            ],
            properties: crate::PropertyMap::default(),
            prototype: None,
            extensible: false,
            length_writable: false,
        })
        .map_err(EvalFailure::Runtime)?;
    machine
        .allocate(HeapEntry::BuiltinIterator {
            source: state,
            kind: crate::IterationKind::RegExpString,
            position: Some(0),
            properties: crate::PropertyMap::default(),
            prototype: Some(
                machine
                    .intrinsics
                    .builtins
                    .regexp_string_iterator_prototype(),
            ),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)
}

/// `RegExp.prototype[@@matchAll]`.
pub(super) fn symbol_match_all<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_object(
        machine,
        this,
        "RegExp.prototype[Symbol.matchAll] requires an object",
    )?;
    let string = machine.coerce_string_observable(argument(args, 0))?;
    let input = allocate_string(machine, string)?;
    with_roots(machine, &[this, input], |machine, depth| {
        let default = regexp_constructor(machine)?;
        let constructor = species_constructor(machine, this, default)?;
        keep_root(machine, depth, constructor);
        let flags = flags_text(machine, this)?;
        let global = contains_flag(&flags, b'g');
        let unicode = is_full_unicode(&flags);
        let flags_value = allocate_string(machine, flags)?;
        let matcher = machine.construct_value(constructor, &[this, flags_value])?;
        keep_root(machine, depth, matcher);
        let last_index = machine.get_named_property(this, "lastIndex")?;
        let last_index = to_length(machine, last_index)?;
        set_last_index(machine, matcher, last_index)?;
        regexp_string_iterator(machine, matcher, input, global, unicode)
    })
    .map(BuiltinOutcome::Value)
}

fn iterator_result<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    done: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    machine
        .iterator_result(value, done)
        .map(BuiltinOutcome::Value)
}

fn finish_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator: Value,
) -> Result<(), EvalFailure> {
    let index = machine
        .runtime_slot(iterator)
        .map_err(EvalFailure::Runtime)?;
    if let Some(index) = index
        && let HeapEntry::BuiltinIterator { position, .. } = &mut machine.heap[index]
    {
        *position = None;
    }
    Ok(())
}

/// `%RegExpStringIteratorPrototype%.next`.
pub(super) fn regexp_string_iterator_next<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let index = machine.runtime_slot(this).map_err(EvalFailure::Runtime)?;
    let Some(HeapEntry::BuiltinIterator {
        source,
        kind: crate::IterationKind::RegExpString,
        position,
        ..
    }) = index.map(|index| &machine.heap[index])
    else {
        return Err(type_error(
            "%RegExpStringIteratorPrototype%.next called on incompatible receiver",
        ));
    };
    let (source, done) = (*source, position.is_none());
    if done {
        return iterator_result(machine, Value::UNDEFINED, true);
    }
    let state = machine.array_elements(source)?.unwrap_or_default();
    let &[matcher, input, global, unicode] = state.as_slice() else {
        unreachable!("the hidden iterator state has four slots")
    };
    let result = with_roots(machine, &[this], |machine, depth| {
        let result = regexp_exec(machine, matcher, input)?;
        keep_root(machine, depth, result);
        if result == Value::NULL {
            finish_iterator(machine, this)?;
            return iterator_result(machine, Value::UNDEFINED, true);
        }
        if global != Value::TRUE {
            finish_iterator(machine, this)?;
            return iterator_result(machine, result, false);
        }
        let matched = machine.get_named_property(result, "0")?;
        if machine.coerce_string_observable(matched)?.is_empty() {
            let text = machine.string_value(input).unwrap_or_default();
            advance_past_empty_match(machine, matcher, &text, unicode == Value::TRUE)?;
        }
        iterator_result(machine, result, false)
    })?;
    Ok(result)
}

/// Whether a RegExp receiver owns flag `flag`, for the flag accessors. The
/// prototype itself answers `undefined`, which is what makes it inspectable.
fn has_flag<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    flag: u8,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_object(machine, this, "RegExp flag getter requires an object")?;
    if let Some((_, flags)) = regexp_parts(machine, this) {
        return Ok(BuiltinOutcome::Value(Value::boolean(contains_flag(
            &flags, flag,
        ))));
    }
    if this == machine.intrinsics.regexp_prototype() {
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    }
    Err(type_error("RegExp flag getter requires a RegExp"))
}

macro_rules! flag_getter {
    ($name:ident, $flag:literal) => {
        fn $name<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            has_flag(machine, this, $flag)
        }
    };
}
flag_getter!(dot_all, b's');
flag_getter!(global, b'g');
flag_getter!(has_indices, b'd');
flag_getter!(ignore_case, b'i');
flag_getter!(multiline, b'm');
flag_getter!(sticky, b'y');
flag_getter!(unicode, b'u');
flag_getter!(unicode_sets, b'v');

/// `get RegExp.prototype.flags`: built from the individual accessors, in
/// `dgimsuvy` order, so each one is an observable `Get`.
pub(super) fn flags_getter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_object(
        machine,
        this,
        "RegExp.prototype.flags getter requires an object",
    )?;
    let mut flags = EcmaStringBuilder::new();
    for (name, flag) in [
        ("hasIndices", b'd'),
        ("global", b'g'),
        ("ignoreCase", b'i'),
        ("multiline", b'm'),
        ("dotAll", b's'),
        ("unicode", b'u'),
        ("unicodeSets", b'v'),
        ("sticky", b'y'),
    ] {
        let value = machine.get_named_property(this, name)?;
        if machine.to_boolean(value) {
            flags.push_unit(u16::from(flag));
        }
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        flags.finish(),
    )?))
}

pub(super) fn species_getter<H: Host>(
    _machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(this))
}

fn is_escaped_punctuator(unit: u32) -> bool {
    char::from_u32(unit).is_some_and(|c| ",-=<>#&!%:;@~'`\"".contains(c))
}

fn is_whitespace_or_line_terminator(unit: u32) -> bool {
    matches!(
        unit,
        0x09..=0x0d
            | 0x20
            | 0xa0
            | 0x1680
            | 0x2000..=0x200a
            | 0x2028
            | 0x2029
            | 0x202f
            | 0x205f
            | 0x3000
            | 0xfeff
    )
}

/// `EncodeForRegExpEscape`.
fn encode_for_escape(output: &mut EcmaStringBuilder, code_point: u32) {
    let control = match code_point {
        0x09 => Some("\\t"),
        0x0a => Some("\\n"),
        0x0b => Some("\\v"),
        0x0c => Some("\\f"),
        0x0d => Some("\\r"),
        _ => None,
    };
    if let Some(control) = control {
        output.push_utf8(control);
    } else if char::from_u32(code_point).is_some_and(|c| "^$\\.*+?()[]{}|/".contains(c)) {
        output.push_unit(u16::from(b'\\'));
        output.push_unit(code_point as u16);
    } else if is_escaped_punctuator(code_point)
        || is_whitespace_or_line_terminator(code_point)
        || (0xd800..=0xdfff).contains(&code_point)
    {
        if code_point <= 0xff {
            output.push_utf8(&format!("\\x{code_point:02x}"));
        } else {
            output.push_utf8(&format!("\\u{code_point:04x}"));
        }
    } else {
        output
            .push_code_point(code_point)
            .expect("a code point read from a string is valid");
    }
}

/// `RegExp.escape(S)`. The first character is hex-escaped when it could join a
/// preceding `\0`-style escape or a `\c` control, so the result is safe anywhere
/// in a pattern.
fn escape<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let Some(text) = machine.string_value(argument(args, 0)) else {
        return Err(type_error("RegExp.escape requires a string"));
    };
    let mut output = EcmaStringBuilder::with_capacity(text.len_units());
    for (offset, code_point) in text.code_points() {
        let initial_alphanumeric =
            offset == 0 && u8::try_from(code_point).is_ok_and(|byte| byte.is_ascii_alphanumeric());
        if initial_alphanumeric {
            output.push_utf8(&format!("\\x{code_point:02x}"));
        } else {
            encode_for_escape(&mut output, code_point);
        }
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}

/// Installs the flag accessors, the `Symbol`-keyed methods and `RegExp.escape`.
pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    builtins: &mut BuiltinTable<H>,
    prototype: Value,
    constructor: Value,
) {
    use super::{define_symbol_property, install_function};
    use crate::intrinsics::BuiltinHandler;

    for (property, getter_name, handler) in [
        ("dotAll", "get dotAll", dot_all::<H> as BuiltinHandler<H>),
        ("global", "get global", global::<H>),
        ("hasIndices", "get hasIndices", has_indices::<H>),
        ("ignoreCase", "get ignoreCase", ignore_case::<H>),
        ("multiline", "get multiline", multiline::<H>),
        ("sticky", "get sticky", sticky::<H>),
        ("unicode", "get unicode", unicode::<H>),
        ("unicodeSets", "get unicodeSets", unicode_sets::<H>),
    ] {
        let getter = install_function(heap, builtins, getter_name, 0, handler);
        super::regexp::define_getter(heap, prototype, property, getter);
    }
    let symbols = [
        (
            builtins.symbol_match(),
            "[Symbol.match]",
            1,
            symbol_match::<H> as BuiltinHandler<H>,
        ),
        (
            builtins.symbol_match_all(),
            "[Symbol.matchAll]",
            1,
            symbol_match_all::<H>,
        ),
        (
            builtins.symbol_replace(),
            "[Symbol.replace]",
            2,
            symbol_replace::<H>,
        ),
        (
            builtins.symbol_search(),
            "[Symbol.search]",
            1,
            symbol_search::<H>,
        ),
        (
            builtins.symbol_split(),
            "[Symbol.split]",
            2,
            symbol_split::<H>,
        ),
    ];
    for (symbol, name, length, handler) in symbols {
        let function = install_function(heap, builtins, name, length, handler);
        define_symbol_property(heap, prototype, symbol, super::builtin_property(function));
    }
    let escape_function = install_function(heap, builtins, "escape", 1, escape::<H>);
    super::define_data(heap, constructor, "escape", escape_function);
    let species = install_function(
        heap,
        builtins,
        "get [Symbol.species]",
        0,
        species_getter::<H>,
    );
    define_symbol_property(
        heap,
        constructor,
        builtins.symbol_species(),
        Property::Accessor {
            getter: Some(species),
            setter: None,
            enumerable: false,
            configurable: true,
        },
    );
    let iterator_prototype = crate::intrinsics::push(
        heap,
        HeapEntry::Object {
            properties: crate::PropertyMap::default(),
            prototype: Some(builtins.iterator_prototype()),
            extensible: true,
            boxed_primitive: None,
        },
    );
    let next = install_function(heap, builtins, "next", 0, regexp_string_iterator_next::<H>);
    super::define_data(heap, iterator_prototype, "next", next);
    super::define_to_string_tag(
        heap,
        iterator_prototype,
        builtins.symbol_to_string_tag(),
        "RegExp String Iterator",
    );
    builtins.set_regexp_string_iterator_prototype(iterator_prototype);
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, RuntimeErrorKind, ThrowOrigin};

    fn regexp(machine: &mut Machine<'_, TestHost>, pattern: &str, flags: &str) -> Value {
        let constructor = machine.intrinsics.global("RegExp").unwrap();
        let pattern = allocate_string(machine, EcmaString::encode(pattern)).unwrap();
        let flags = allocate_string(machine, EcmaString::encode(flags)).unwrap();
        machine
            .construct_value(constructor, &[pattern, flags])
            .unwrap()
    }

    #[test]
    fn flag_accessors_answer_for_regexps_and_the_prototype_only() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let value = regexp(&mut machine, "x", "gi");
        assert_eq!(
            machine.get_named_property(value, "global").unwrap(),
            Value::TRUE
        );
        assert_eq!(
            machine.get_named_property(value, "sticky").unwrap(),
            Value::FALSE
        );
        let key = crate::PropertyKey::Named(EcmaString::encode("global"));
        assert_eq!(
            machine.own_descriptor(value, &key).unwrap(),
            None,
            "a flag is an accessor on the prototype, not an own property"
        );
        let prototype = machine.intrinsics.regexp_prototype();
        assert_eq!(
            machine.get_named_property(prototype, "global").unwrap(),
            Value::UNDEFINED
        );
        let object = ordinary_object(&mut machine);
        machine
            .internal_set_prototype_of(object, Some(prototype))
            .unwrap();
        assert!(matches!(
            machine.get_named_property(object, "global"),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn flags_reads_each_accessor_so_an_override_is_seen() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let object = ordinary_object(&mut machine);
        for (name, value) in [("global", Value::TRUE), ("sticky", Value::int32(1))] {
            machine.set_data_property(object, name, value).unwrap();
        }
        let BuiltinOutcome::Value(flags) = flags_getter(&mut machine, object, &[], false).unwrap()
        else {
            panic!("the flags getter returns a value");
        };
        assert!(machine.string_value(flags).unwrap().eq_ascii("gy"));
        assert!(matches!(
            flags_getter(&mut machine, Value::int32(1), &[], false),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    fn text(machine: &mut Machine<'_, TestHost>, value: &str) -> Value {
        allocate_string(machine, EcmaString::encode(value)).unwrap()
    }

    fn outcome_value(outcome: BuiltinOutcome) -> Value {
        match outcome {
            BuiltinOutcome::Value(value) => value,
            _ => panic!("the builtin returns a value"),
        }
    }

    /// A user `exec` that reports a match of `b` at index 1, whatever the input.
    fn fixed_exec(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let matched = allocate_string(machine, EcmaString::encode("b"))?;
        let result = allocate_array(machine, vec![matched])?;
        machine.set_data_property(result, "index", Value::int32(1))?;
        Ok(BuiltinOutcome::Value(result))
    }

    #[test]
    fn replace_is_driven_by_a_user_exec_rather_than_the_matcher() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let rx = regexp(&mut machine, "never", "");
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "fixed exec",
            length: 1,
            handler: fixed_exec,
        });
        let exec = native_function(&mut machine.heap, id, "fixed exec", 1);
        machine.set_data_property(rx, "exec", exec).unwrap();
        let (string, replacement) = (text(&mut machine, "abc"), text(&mut machine, "[$&]"));
        let result =
            outcome_value(symbol_replace(&mut machine, rx, &[string, replacement], false).unwrap());
        assert!(machine.string_value(result).unwrap().eq_ascii("a[b]c"));
    }

    /// A match of `b` at index 1 in an object that claims `length` elements.
    fn claiming_result(
        machine: &mut Machine<'_, TestHost>,
        length: f64,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let matched = allocate_string(machine, EcmaString::encode("b"))?;
        let result = ordinary_object(machine);
        machine.set_data_property(result, "0", matched)?;
        machine.set_data_property(result, "index", Value::int32(1))?;
        machine.set_data_property(result, "length", crate::number_value(length))?;
        Ok(BuiltinOutcome::Value(result))
    }

    fn endless_exec(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        claiming_result(machine, MAX_SAFE_INTEGER)
    }

    fn long_exec(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        claiming_result(machine, 1000.0)
    }

    /// Makes `handler` the `exec` of every RegExp, also of the splitter that
    /// `@@split` constructs.
    fn replace_exec(
        machine: &mut Machine<'_, TestHost>,
        handler: crate::intrinsics::BuiltinHandler<TestHost>,
    ) {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "claiming exec",
            length: 1,
            handler,
        });
        let exec = native_function(&mut machine.heap, id, "claiming exec", 1);
        let prototype = machine.intrinsics.regexp_prototype();
        machine.set_data_property(prototype, "exec", exec).unwrap();
    }

    /// A result of `exec` can claim 2^53 - 1 elements. Before, `@@replace` reserved
    /// memory for all of them, which ended the process.
    #[test]
    fn a_result_that_claims_endless_captures_is_a_runtime_failure() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let rx = regexp(&mut machine, "b", "");
        replace_exec(&mut machine, endless_exec);
        let (string, replacement) = (text(&mut machine, "abc"), text(&mut machine, "x"));
        assert!(matches!(
            symbol_replace(&mut machine, rx, &[string, replacement], false),
            Err(EvalFailure::Runtime(
                RuntimeErrorKind::HeapByteLimitExceeded { .. }
            ))
        ));
        assert!(matches!(
            symbol_split(&mut machine, rx, &[string], false),
            Err(EvalFailure::Runtime(
                RuntimeErrorKind::HeapByteLimitExceeded { .. }
            ))
        ));
        // A limit bounds what `@@split` keeps, so the claim does not matter there.
        let limited = outcome_value(
            symbol_split(&mut machine, rx, &[string, Value::int32(3)], false).unwrap(),
        );
        assert_eq!(machine.array_elements(limited).unwrap().unwrap().len(), 3);
    }

    thread_local! {
        static EXEC_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    }

    /// A claim that the budget of the test below holds one time and not two times.
    fn counted_exec(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        EXEC_CALLS.with(|calls| calls.set(calls.get() + 1));
        claiming_result(machine, 40_001.0)
    }

    /// Each match of `@@split` can claim again, so the pieces of all matches count
    /// together. The second match fails here, before `exec` runs for a third.
    #[test]
    fn the_captures_of_every_split_match_count_against_the_budget_together() {
        let module = blank_program("<test>");
        let used = {
            let mut host = TestHost;
            Machine::new(&module, &mut host, Limits::default()).heap_bytes
        };
        let mut host = TestHost;
        let limits = Limits {
            max_heap_bytes: used + (1 << 20),
            ..Limits::default()
        };
        let mut machine = Machine::new(&module, &mut host, limits);
        let rx = regexp(&mut machine, "b", "");
        replace_exec(&mut machine, counted_exec);
        let string = text(&mut machine, "abcdefgh");
        EXEC_CALLS.with(|calls| calls.set(0));
        assert!(matches!(
            symbol_split(&mut machine, rx, &[string], false),
            Err(EvalFailure::Runtime(
                RuntimeErrorKind::HeapByteLimitExceeded { .. }
            ))
        ));
        // Two calls find no progress, and two calls find a match.
        assert_eq!(EXEC_CALLS.with(std::cell::Cell::get), 4);
    }

    #[test]
    fn a_loop_over_claimed_captures_runs_out_of_fuel() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let limits = Limits {
            fuel: 16,
            ..Limits::default()
        };
        let mut machine = Machine::new(&module, &mut host, limits);
        let rx = regexp(&mut machine, "b", "");
        replace_exec(&mut machine, long_exec);
        let (string, replacement) = (text(&mut machine, "abc"), text(&mut machine, "x"));
        assert!(matches!(
            symbol_replace(&mut machine, rx, &[string, replacement], false),
            Err(EvalFailure::Runtime(RuntimeErrorKind::FuelExhausted { .. }))
        ));
        assert!(matches!(
            symbol_split(&mut machine, rx, &[string], false),
            Err(EvalFailure::Runtime(RuntimeErrorKind::FuelExhausted { .. }))
        ));
    }

    #[test]
    fn a_receiver_without_exec_must_be_a_regexp() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let object = ordinary_object(&mut machine);
        let string = text(&mut machine, "abc");
        assert!(matches!(
            symbol_search(&mut machine, object, &[string], false),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn a_global_match_steps_past_an_empty_match_by_code_point_under_unicode() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let string = text(&mut machine, "😀");
        for (flags, expected) in [("g", 3), ("gu", 2)] {
            let rx = regexp(&mut machine, "(?:)", flags);
            let result = outcome_value(symbol_match(&mut machine, rx, &[string], false).unwrap());
            assert_eq!(
                machine.array_elements(result).unwrap().unwrap().len(),
                expected,
                "with flags {flags}"
            );
        }
    }

    #[test]
    fn search_leaves_last_index_as_it_found_it() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let rx = regexp(&mut machine, "b", "g");
        machine
            .set_data_property(rx, "lastIndex", Value::int32(9))
            .unwrap();
        let string = text(&mut machine, "abc");
        assert_eq!(
            outcome_value(symbol_search(&mut machine, rx, &[string], false).unwrap()),
            Value::int32(1)
        );
        assert_eq!(
            machine.get_named_property(rx, "lastIndex").unwrap(),
            Value::int32(9)
        );
    }

    #[test]
    fn split_keeps_captures_and_stops_at_the_limit() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let rx = regexp(&mut machine, "(b)", "");
        let string = text(&mut machine, "abcbd");
        let pieces = |machine: &mut Machine<'_, TestHost>, result| -> Vec<String> {
            let values = machine.array_elements(result).unwrap().unwrap();
            values
                .into_iter()
                .map(|value| machine.string_value(value).unwrap().to_utf8_lossy())
                .collect()
        };
        let all = outcome_value(symbol_split(&mut machine, rx, &[string], false).unwrap());
        assert_eq!(pieces(&mut machine, all), ["a", "b", "c", "b", "d"]);
        let limited = outcome_value(
            symbol_split(&mut machine, rx, &[string, Value::int32(2)], false).unwrap(),
        );
        assert_eq!(pieces(&mut machine, limited), ["a", "b"]);
    }

    #[test]
    fn match_all_stays_done_once_exhausted() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let rx = regexp(&mut machine, "a", "g");
        let string = text(&mut machine, "aa");
        let iterator = outcome_value(symbol_match_all(&mut machine, rx, &[string], false).unwrap());
        let step = |machine: &mut Machine<'_, TestHost>| {
            let result =
                outcome_value(regexp_string_iterator_next(machine, iterator, &[], false).unwrap());
            machine.get_named_property(result, "done").unwrap()
        };
        assert_eq!(step(&mut machine), Value::FALSE);
        assert_eq!(step(&mut machine), Value::FALSE);
        assert_eq!(step(&mut machine), Value::TRUE);
        assert_eq!(step(&mut machine), Value::TRUE);
        assert!(matches!(
            regexp_string_iterator_next(&mut machine, string, &[], false),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    fn escaped(machine: &mut Machine<'_, TestHost>, units: &[u16]) -> Vec<u16> {
        let input = allocate_string(machine, EcmaString::from_units(units)).unwrap();
        let result = outcome_value(escape(machine, Value::UNDEFINED, &[input], false).unwrap());
        machine.string_value(result).unwrap().as_units().to_vec()
    }

    #[test]
    fn escape_is_safe_at_the_start_of_a_pattern_and_after_any_syntax() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        for (input, expected) in [
            ("abc", "\\x61bc"),
            ("1", "\\x31"),
            ("_a", "_a"),
            (".*", "\\.\\*"),
            ("a/b", "\\x61\\/b"),
            ("\n", "\\n"),
            ("-", "\\x2d"),
            (" ", "\\x20"),
            ("\u{2028}", "\\u2028"),
        ] {
            let units: Vec<u16> = input.encode_utf16().collect();
            let expected: Vec<u16> = expected.encode_utf16().collect();
            assert_eq!(escaped(&mut machine, &units), expected, "{input:?}");
        }
        let lone: Vec<u16> = "\\ud800".encode_utf16().collect();
        assert_eq!(escaped(&mut machine, &[0xd800]), lone);
        assert!(matches!(
            escape(&mut machine, Value::UNDEFINED, &[Value::int32(1)], false),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn substitution_reads_each_reference_form() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let captures = [Some(EcmaString::encode("x")), None];
        for (template, expected) in [
            ("$$", "$"),
            ("$&", "b"),
            ("$`", "a"),
            ("$'", "c"),
            ("$1", "x"),
            ("$01", "x"),
            ("$2", ""),
            ("$10", "x0"),
            ("$0", "$0"),
            ("$3", "$3"),
            ("$<n>", "$<n>"),
            ("$", "$"),
        ] {
            let result = get_substitution(
                &mut machine,
                &EcmaString::encode("b"),
                &EcmaString::encode("abc"),
                1,
                &captures,
                Value::UNDEFINED,
                &EcmaString::encode(template),
            )
            .unwrap();
            assert!(result.eq_ascii(expected), "{template}");
        }
        let groups = ordinary_object(&mut machine);
        let value = text(&mut machine, "named");
        machine.set_data_property(groups, "n", value).unwrap();
        let result = get_substitution(
            &mut machine,
            &EcmaString::encode("b"),
            &EcmaString::encode("abc"),
            1,
            &[],
            groups,
            &EcmaString::encode("$<n>$<missing>"),
        )
        .unwrap();
        assert!(result.eq_ascii("named"));
    }
}
