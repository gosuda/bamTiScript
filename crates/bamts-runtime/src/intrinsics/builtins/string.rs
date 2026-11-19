use crate::heap::Heap;
use std::collections::BTreeMap;
use std::mem::size_of;

use bamts_bytecode::{EcmaString, EcmaStringBuilder};
use bamts_native::{Decoded, Value};
use unicode_normalization::UnicodeNormalization;

use super::intl::{TargetCase, compare_with_collator, transform_case};
use super::{
    allocate_array, allocate_string, define_data, install_constructor_function, install_function,
    range_error, to_integer_or_infinity, type_error, uri_error, value_number, with_roots,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, IterationKind, Machine, PropertyKey, RuntimeErrorKind};

pub(super) fn install<H: Host>(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = builtins.string_prototype();
    let constructor = install_constructor_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "String",
            length: 1,
            handler: constructor::<H>,
        },
    );
    builtins.set_constructor_prototype(heap, atoms, shapes, constructor, prototype);
    globals.insert(EcmaString::encode("String"), constructor);
    for (name, length, handler) in [
        ("fromCharCode", 1, from_char_code::<H> as BuiltinHandler<H>),
        ("raw", 1, raw::<H>),
        ("fromCodePoint", 1, from_code_point::<H>),
    ] {
        let f = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name,
                length,
                handler,
            },
        );
        define_static(heap, atoms, shapes, constructor, name, f)
    }
    for (name, length, handler) in [
        ("toString", 0, this_string_value::<H> as BuiltinHandler<H>),
        ("valueOf", 0, this_string_value::<H>),
        ("charAt", 1, char_at::<H>),
        ("charCodeAt", 1, char_code_at::<H>),
        ("codePointAt", 1, code_point_at::<H>),
        ("at", 1, at::<H>),
        ("slice", 2, slice::<H>),
        ("substring", 2, substring::<H>),
        ("indexOf", 1, index_of::<H>),
        ("lastIndexOf", 1, last_index_of::<H>),
        ("includes", 1, includes::<H>),
        ("startsWith", 1, starts_with::<H>),
        ("endsWith", 1, ends_with::<H>),
        ("split", 2, split::<H>),
        ("replace", 2, replace::<H>),
        ("trim", 0, trim::<H>),
        ("trimStart", 0, trim_start::<H>),
        ("trimEnd", 0, trim_end::<H>),
        ("toUpperCase", 0, to_upper::<H>),
        ("toLowerCase", 0, to_lower::<H>),
        ("toLocaleUpperCase", 0, to_locale_upper::<H>),
        ("toLocaleLowerCase", 0, to_locale_lower::<H>),
        ("padStart", 1, pad_start::<H>),
        ("padEnd", 1, pad_end::<H>),
        ("repeat", 1, repeat::<H>),
        ("concat", 1, concat::<H>),
        ("normalize", 0, normalize::<H>),
        ("match", 1, string_match::<H>),
        ("matchAll", 1, match_all::<H>),
        ("search", 1, search::<H>),
        ("localeCompare", 1, locale_compare::<H>),
        ("isWellFormed", 0, is_well_formed::<H>),
        ("toWellFormed", 0, to_well_formed::<H>),
        ("replaceAll", 2, replace_all::<H>),
    ] {
        let f = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name,
                length,
                handler,
            },
        );
        define_data(heap, atoms, shapes, prototype, name, f)
    }
    let iterator = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "[Symbol.iterator]",
            length: 0,
            handler: string_iterator::<H>,
        },
    );
    let HeapEntry::Object { properties, .. } = &mut heap[super::heap_index(prototype)] else {
        unreachable!()
    };
    properties.insert(
        shapes,
        PropertyKey::Symbol(super::heap_index(builtins.symbol_iterator()) as u32),
        super::builtin_property(iterator),
    );
}
fn define_static(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    constructor: Value,
    name: &str,
    value: Value,
) {
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[super::heap_index(constructor)]
    else {
        panic!("String constructor must be native")
    };
    properties.insert(
        shapes,
        PropertyKey::Named(atoms.intern_str(name)),
        super::builtin_property(value),
    );
}
fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let text = if args.is_empty() {
        EcmaString::default()
    } else if constructing {
        machine.coerce_string_observable(args[0])?
    } else {
        machine.string_constructor_text(args[0])?
    };
    let value = allocate_string(machine, text)?;
    if constructing {
        let prototype = machine.intrinsics.string_prototype;
        super::wrap_for_new_target(machine, value, prototype)
    } else {
        Ok(BuiltinOutcome::Value(value))
    }
}
fn text<H: Host>(machine: &mut Machine<'_, H>, this: Value) -> Result<EcmaString, EvalFailure> {
    if matches!(this.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        return Err(type_error("String method called on null or undefined"));
    }
    machine.coerce_string_observable(this)
}
fn locale_compare<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if matches!(this.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        return Err(type_error("String method called on null or undefined"));
    }
    let this = machine.coerce_string_observable(this)?;
    let other =
        machine.coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let locales = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let options = args.get(2).copied().unwrap_or(Value::UNDEFINED);
    if locales != Value::UNDEFINED || options != Value::UNDEFINED {
        return compare_with_collator(machine, &this, &other, locales, options);
    }
    let result: i32 = match this.as_units().cmp(other.as_units()) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    };
    Ok(BuiltinOutcome::Value(Value::int32(result as u32)))
}
fn append(out: &mut EcmaStringBuilder, text: &EcmaString) {
    for &unit in text.as_units() {
        out.push_unit(unit);
    }
}
fn integer<H: Host>(machine: &mut Machine<'_, H>, value: Value) -> Result<isize, EvalFailure> {
    Ok(super::to_integer_or_infinity(machine, value)? as isize)
}
/// Rejects a search string that is a RegExp, for the methods that take text only.
fn require_not_regexp<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    operation: &'static str,
) -> Result<(), EvalFailure> {
    if is_regexp(machine, value)? {
        return Err(type_error(operation));
    }
    Ok(())
}
/// `String.prototype.toString` and `valueOf`: the receiver's own string. Neither
/// coerces, so a receiver that is not a String throws.
fn this_string_value<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = machine.unbox_primitive(this, "String.prototype.toString")?;
    if machine.string_value(value).is_some() {
        Ok(BuiltinOutcome::Value(value))
    } else {
        Err(type_error(
            "String.prototype.toString called on incompatible receiver",
        ))
    }
}

fn from_char_code<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let mut out = EcmaStringBuilder::with_capacity(args.len());
    for arg in args {
        out.push_unit(
            crate::to_uint32(value_number(machine.coerce_number_observable(*arg)?)) as u16,
        );
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        out.finish(),
    )?))
}
fn char_at<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let string = text(machine, this)?;
    let index = integer(machine, args.first().copied().unwrap_or(Value::int32(0)))?;
    let result = if index < 0 {
        EcmaString::default()
    } else {
        string
            .unit_at(index as usize)
            .map_or_else(EcmaString::default, |unit| EcmaString::from_units(&[unit]))
    };
    Ok(BuiltinOutcome::Value(allocate_string(machine, result)?))
}
fn char_code_at<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let string = text(machine, this)?;
    let index = integer(machine, args.first().copied().unwrap_or(Value::int32(0)))?;
    let result = if index < 0 {
        f64::NAN
    } else {
        string.unit_at(index as usize).map_or(f64::NAN, f64::from)
    };
    Ok(BuiltinOutcome::Value(crate::number_value(result)))
}
fn code_point_at<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let string = text(machine, this)?;
    let index = integer(machine, args.first().copied().unwrap_or(Value::int32(0)))?;
    if index < 0 || index as usize >= string.len_units() {
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    }
    let offset = index as usize;
    // Read the code unit at the offset directly. If it is a high surrogate
    // followed by a low surrogate, combine them into the supplementary code
    // point (ECMA-262 §11.1.5). This touches at most two units instead of
    // rescanning the whole string from index 0 on every call.
    let first = string.unit_at(offset).expect("offset is in bounds");
    let code_point = match (first, string.unit_at(offset + 1)) {
        (0xD800..=0xDBFF, Some(second @ 0xDC00..=0xDFFF)) => {
            0x1_0000 + ((u32::from(first) - 0xD800) << 10) + (u32::from(second) - 0xDC00)
        }
        _ => u32::from(first),
    };
    Ok(BuiltinOutcome::Value(crate::number_value(
        code_point as f64,
    )))
}
fn rel(i: isize, len: usize) -> usize {
    if i < 0 {
        (len as isize + i).max(0) as usize
    } else {
        (i as usize).min(len)
    }
}
fn slice<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let string = text(machine, this)?;
    let start = rel(
        integer(machine, args.first().copied().unwrap_or(Value::int32(0)))?,
        string.len_units(),
    );
    let end = match args.get(1).copied() {
        None | Some(Value::UNDEFINED) => string.len_units(),
        Some(end) => rel(integer(machine, end)?, string.len_units()),
    };
    let result = if end > start {
        string
            .slice_units(start..end)
            .expect("slice bounds were clamped to the string")
    } else {
        EcmaString::default()
    };
    Ok(BuiltinOutcome::Value(allocate_string(machine, result)?))
}
fn substring<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let string = text(machine, this)?;
    let mut start =
        integer(machine, args.first().copied().unwrap_or(Value::int32(0)))?.max(0) as usize;
    start = start.min(string.len_units());
    let mut end = if args.len() < 2 || args[1] == Value::UNDEFINED {
        string.len_units()
    } else {
        integer(machine, args[1])?.max(0) as usize
    };
    end = end.min(string.len_units());
    if start > end {
        std::mem::swap(&mut start, &mut end);
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        string
            .slice_units(start..end)
            .expect("substring bounds were clamped to the string"),
    )?))
}
fn search_units(h: &[u16], n: &[u16], start: usize) -> Option<usize> {
    if n.is_empty() {
        return Some(start.min(h.len()));
    }
    h.get(start..)?
        .windows(n.len())
        .position(|w| w == n)
        .map(|i| i + start)
}
fn index_of<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let haystack = text(machine, this)?;
    let needle =
        machine.coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let start = integer(machine, args.get(1).copied().unwrap_or(Value::int32(0)))?.max(0) as usize;
    Ok(BuiltinOutcome::Value(crate::number_value(
        search_units(haystack.as_units(), needle.as_units(), start).map_or(-1.0, |i| i as f64),
    )))
}
fn last_index_of<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let haystack = text(machine, this)?;
    let needle =
        machine.coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let position = value_number(
        machine.coerce_number_observable(args.get(1).copied().unwrap_or(Value::UNDEFINED))?,
    );
    let end = if position.is_nan() {
        haystack.len_units()
    } else {
        (position.max(0.0) as usize).min(haystack.len_units())
    };
    let found = (0..=end).rev().find(|index| {
        haystack
            .as_units()
            .get(*index..index.saturating_add(needle.len_units()))
            .is_some_and(|window| window == needle.as_units())
    });
    Ok(BuiltinOutcome::Value(crate::number_value(
        found.map_or(-1.0, |i| i as f64),
    )))
}
fn includes<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let haystack = text(machine, this)?;
    let search = args.first().copied().unwrap_or(Value::UNDEFINED);
    require_not_regexp(
        machine,
        search,
        "String.prototype.includes cannot search for a RegExp",
    )?;
    let needle = machine.coerce_string_observable(search)?;
    let start = integer(machine, args.get(1).copied().unwrap_or(Value::int32(0)))?.max(0) as usize;
    Ok(BuiltinOutcome::Value(Value::boolean(
        search_units(haystack.as_units(), needle.as_units(), start).is_some(),
    )))
}
fn starts_with<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let haystack = text(machine, this)?;
    let search = args.first().copied().unwrap_or(Value::UNDEFINED);
    require_not_regexp(
        machine,
        search,
        "String.prototype.startsWith cannot search for a RegExp",
    )?;
    let needle = machine.coerce_string_observable(search)?;
    let position = (integer(machine, args.get(1).copied().unwrap_or(Value::int32(0)))?.max(0)
        as usize)
        .min(haystack.len_units());
    Ok(BuiltinOutcome::Value(Value::boolean(
        haystack
            .as_units()
            .get(position..position.saturating_add(needle.len_units()))
            .is_some_and(|window| window == needle.as_units()),
    )))
}
fn ends_with<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let haystack = text(machine, this)?;
    let search = args.first().copied().unwrap_or(Value::UNDEFINED);
    require_not_regexp(
        machine,
        search,
        "String.prototype.endsWith cannot search for a RegExp",
    )?;
    let needle = machine.coerce_string_observable(search)?;
    let end = if args.len() < 2 || args[1] == Value::UNDEFINED {
        haystack.len_units()
    } else {
        integer(machine, args[1])?.max(0) as usize
    }
    .min(haystack.len_units());
    Ok(BuiltinOutcome::Value(Value::boolean(
        end >= needle.len_units()
            && haystack.as_units()[end - needle.len_units()..end] == *needle.as_units(),
    )))
}

fn require_coercible(value: Value) -> Result<(), EvalFailure> {
    if matches!(value.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        return Err(type_error("String method called on null or undefined"));
    }
    Ok(())
}

/// `GetMethod(argument, symbol)` for the methods that delegate to a pattern. A
/// primitive argument is never consulted, so a method added to
/// `Number.prototype` cannot take over a plain string search.
fn pattern_method<H: Host>(
    machine: &mut Machine<'_, H>,
    argument: Value,
    symbol: Value,
) -> Result<Option<Value>, EvalFailure> {
    if !machine.is_object(argument) {
        return Ok(None);
    }
    let key = machine.property_key_from_value(symbol)?;
    let method = machine.get_property_key(argument, &key)?;
    if matches!(method.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        return Ok(None);
    }
    if machine.is_callable(method)? {
        Ok(Some(method))
    } else {
        Err(type_error("pattern method is not callable"))
    }
}

/// `Invoke(rx, symbol, «input»)` on a RegExp this method just created.
fn invoke_on_new_regexp<H: Host>(
    machine: &mut Machine<'_, H>,
    regexp: Value,
    symbol: Value,
    input: Value,
) -> Result<BuiltinOutcome, EvalFailure> {
    with_roots(machine, &[regexp, input], |machine, _| {
        let key = machine.property_key_from_value(symbol)?;
        let method = machine.get_property_key(regexp, &key)?;
        machine.call_value(method, regexp, &[input])
    })
    .map(BuiltinOutcome::Value)
}

fn split<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_coercible(this)?;
    let separator = args.first().copied().unwrap_or(Value::UNDEFINED);
    let limit = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let symbol = machine.intrinsics.builtins.symbol_split();
    if let Some(method) = pattern_method(machine, separator, symbol)? {
        return Ok(BuiltinOutcome::Value(machine.call_value(
            method,
            separator,
            &[this, limit],
        )?));
    }
    let string = text(machine, this)?;
    let limit = if limit == Value::UNDEFINED {
        u32::MAX
    } else {
        crate::to_uint32(value_number(machine.coerce_number_observable(limit)?))
    } as usize;
    let separator_text = machine.coerce_string_observable(separator)?;
    if limit == 0 {
        return Ok(BuiltinOutcome::Value(allocate_array(machine, Vec::new())?));
    }
    let parts = if separator == Value::UNDEFINED {
        vec![string]
    } else if separator_text.is_empty() {
        string
            .as_units()
            .iter()
            .map(|unit| EcmaString::from_units(&[*unit]))
            .collect()
    } else {
        let mut parts = Vec::new();
        let mut cursor = 0;
        while let Some(offset) = search_units(string.as_units(), separator_text.as_units(), cursor)
        {
            parts.push(
                string
                    .slice_units(cursor..offset)
                    .expect("separator search returns string bounds"),
            );
            cursor = offset + separator_text.len_units();
        }
        parts.push(
            string
                .slice_units(cursor..string.len_units())
                .expect("separator search preserves string bounds"),
        );
        parts
    };
    let mut values = Vec::new();
    for part in parts.into_iter().take(limit) {
        values.push(allocate_string(machine, part)?);
    }
    Ok(BuiltinOutcome::Value(allocate_array(machine, values)?))
}

fn replace<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_coercible(this)?;
    let search = args.first().copied().unwrap_or(Value::UNDEFINED);
    let replace_value = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let symbol = machine.intrinsics.builtins.symbol_replace();
    if let Some(method) = pattern_method(machine, search, symbol)? {
        return Ok(BuiltinOutcome::Value(machine.call_value(
            method,
            search,
            &[this, replace_value],
        )?));
    }
    let string = text(machine, this)?;
    let needle = machine.coerce_string_observable(search)?;
    let functional = machine.is_callable(replace_value)?;
    let template = if functional {
        None
    } else {
        Some(machine.coerce_string_observable(replace_value)?)
    };
    let Some(position) = search_units(string.as_units(), needle.as_units(), 0) else {
        return Ok(BuiltinOutcome::Value(allocate_string(machine, string)?));
    };
    let replacement = match template {
        Some(template) => super::regexp::get_substitution(
            machine,
            &needle,
            &string,
            position,
            &[],
            Value::UNDEFINED,
            &template,
        )?,
        None => {
            let matched = allocate_string(machine, needle.clone())?;
            let whole = allocate_string(machine, string.clone())?;
            let value = machine.call_value(
                replace_value,
                Value::UNDEFINED,
                &[matched, crate::number_value(position as f64), whole],
            )?;
            machine.coerce_string_observable(value)?
        }
    };
    let mut output = EcmaStringBuilder::new();
    append(
        &mut output,
        &super::regexp::slice_units(&string, 0..position),
    );
    append(&mut output, &replacement);
    append(
        &mut output,
        &super::regexp::slice_units(&string, position + needle.len_units()..string.len_units()),
    );
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}
fn is_js_whitespace(unit: u16) -> bool {
    matches!(
        unit,
        0x0009..=0x000D
            | 0x0020
            | 0x00A0
            | 0x1680
            | 0x2000..=0x200A
            | 0x2028
            | 0x2029
            | 0x202F
            | 0x205F
            | 0x3000
            | 0xFEFF
    )
}


fn to_upper<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = text(machine, this)?;
    let mut output = EcmaStringBuilder::new();
    for (_, code_point) in source.code_points() {
        if let Some(character) = char::from_u32(code_point) {
            for mapped in character.to_uppercase() {
                output
                    .push_code_point(mapped as u32)
                    .expect("Rust char is valid");
            }
        } else {
            output.push_unit(code_point as u16);
        }
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}
fn to_locale_upper<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if matches!(this.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        return Err(type_error("String method called on null or undefined"));
    }
    let source = machine.coerce_string_observable(this)?;
    let locales = args.first().copied().unwrap_or(Value::UNDEFINED);
    transform_case(machine, &source, locales, TargetCase::Upper)
}
fn to_locale_lower<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if matches!(this.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        return Err(type_error("String method called on null or undefined"));
    }
    let source = machine.coerce_string_observable(this)?;
    let locales = args.first().copied().unwrap_or(Value::UNDEFINED);
    transform_case(machine, &source, locales, TargetCase::Lower)
}
fn to_lower<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = text(machine, this)?;
    let mut output = EcmaStringBuilder::new();
    // Lowering whole runs lets str::to_lowercase see the context Final_Sigma needs.
    let mut run = String::new();
    for (_, code_point) in source.code_points() {
        if let Some(character) = char::from_u32(code_point) {
            run.push(character);
        } else {
            output.push_utf8(&run.to_lowercase());
            run.clear();
            output.push_unit(code_point as u16);
        }
    }
    output.push_utf8(&run.to_lowercase());
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}
fn concat<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if matches!(this.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        return Err(type_error("String method called on null or undefined"));
    }
    let primitive = machine.coerce_primitive_observable(this, true)?;
    let mut result = machine.coerce_string_value(primitive)?;
    for argument in args {
        let primitive = machine.coerce_primitive_observable(*argument, true)?;
        let next = machine.coerce_string_value(primitive)?;
        result = machine.concat_string_values(result, next)?;
    }
    Ok(BuiltinOutcome::Value(result))
}
fn uri_unescaped(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || b"-_.!~*'()".contains(&byte)
}
pub(super) fn encode_uri_component<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = machine
        .to_string(args.first().copied().unwrap_or(Value::UNDEFINED))?
        .to_utf8_strict()
        .map_err(|_| uri_error("URI malformed"))?;
    let mut output = String::new();
    for byte in source.bytes() {
        if uri_unescaped(byte) {
            output.push(char::from(byte));
        } else {
            output.push_str(&format!("%{byte:02X}"));
        }
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        EcmaString::encode(&output),
    )?))
}
fn hex_value(unit: u16) -> Option<u8> {
    match unit {
        0x30..=0x39 => Some((unit - 0x30) as u8),
        0x41..=0x46 => Some((unit - 0x41 + 10) as u8),
        0x61..=0x66 => Some((unit - 0x61 + 10) as u8),
        _ => None,
    }
}

fn percent_octet(units: &[u16], offset: usize) -> Option<u8> {
    if units.get(offset) != Some(&u16::from(b'%')) {
        return None;
    }
    let high = hex_value(*units.get(offset + 1)?)?;
    let low = hex_value(*units.get(offset + 2)?)?;
    Some((high << 4) | low)
}

pub(super) fn unescape<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source =
        machine.coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let units = source.as_units();
    let mut output = EcmaStringBuilder::with_capacity(units.len());
    let mut offset = 0;
    while offset < units.len() {
        if units[offset] != u16::from(b'%') {
            output.push_unit(units[offset]);
            offset += 1;
            continue;
        }
        if units.get(offset + 1) == Some(&u16::from(b'u')) {
            let digits = (0..4).try_fold(0_u16, |value, index| {
                Some((value << 4) | u16::from(hex_value(*units.get(offset + index + 2)?)?))
            });
            if let Some(unit) = digits {
                output.push_unit(unit);
                offset += 6;
                continue;
            }
        }
        if let Some(octet) = percent_octet(units, offset) {
            output.push_unit(u16::from(octet));
            offset += 3;
            continue;
        }
        output.push_unit(units[offset]);
        offset += 1;
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}

fn utf8_sequence_len(first: u8) -> Option<usize> {
    match first {
        0x00..=0x7f => Some(1),
        0xc0..=0xdf => Some(2),
        0xe0..=0xef => Some(3),
        0xf0..=0xf7 => Some(4),
        _ => None,
    }
}

pub(super) fn decode_uri_component<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source =
        machine.coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let units = source.as_units();
    let mut output = EcmaStringBuilder::with_capacity(units.len());
    let mut offset = 0;
    while offset < units.len() {
        if units[offset] != u16::from(b'%') {
            output.push_unit(units[offset]);
            offset += 1;
            continue;
        }

        let first = percent_octet(units, offset).ok_or_else(|| uri_error("URI malformed"))?;
        let sequence_len = utf8_sequence_len(first).ok_or_else(|| uri_error("URI malformed"))?;
        if sequence_len == 1 {
            output.push_unit(u16::from(first));
            offset += 3;
            continue;
        }

        let mut octets = [0; 4];
        octets[0] = first;
        for octet in &mut octets[1..sequence_len] {
            offset += 3;
            *octet = percent_octet(units, offset).ok_or_else(|| uri_error("URI malformed"))?;
        }
        let decoded =
            std::str::from_utf8(&octets[..sequence_len]).map_err(|_| uri_error("URI malformed"))?;
        output.push_utf8(decoded);
        offset += 3;
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}

fn string_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let string = text(machine, this)?;
    let count = string.code_points().count();
    // The iterator protocol is lazy, so materializing every code point up
    // front charges the machine slot by slot. Preflight the full allocation
    // (one heap string per code point plus the backing array) before building
    // anything, matching the pad/repeat discipline that fails fast on an
    // oversized source instead of allocating toward the heap limit.
    let piece_bytes = string.len_units().saturating_mul(2);
    let array_bytes = count
        .saturating_mul(std::mem::size_of::<Value>())
        .saturating_add(1);
    let total_bytes = piece_bytes.saturating_add(array_bytes).saturating_add(1);
    let total_slots = count.saturating_add(2);
    machine
        .ensure_allocation_capacity(total_slots, total_bytes)
        .map_err(EvalFailure::Runtime)?;
    let mut values = Vec::with_capacity(count);
    for (_, code_point) in string.code_points() {
        let mut builder = EcmaStringBuilder::new();
        builder
            .push_code_point(code_point)
            .expect("EcmaString code point is valid");
        values.push(allocate_string(machine, builder.finish())?);
    }
    let source = allocate_array(machine, values)?;
    Ok(BuiltinOutcome::Value(super::collections::iterator(
        machine,
        source,
        IterationKind::StringCodePoint,
    )?))
}

fn string_match<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    delegate_to_pattern(
        machine,
        this,
        args,
        machine.intrinsics.builtins.symbol_match(),
    )
}

fn search<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    delegate_to_pattern(
        machine,
        this,
        args,
        machine.intrinsics.builtins.symbol_search(),
    )
}

/// The shared shape of `match` and `search`: use the argument's own method, or
/// build a RegExp from the argument and use that one.
fn delegate_to_pattern<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    symbol: Value,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_coercible(this)?;
    let pattern = args.first().copied().unwrap_or(Value::UNDEFINED);
    if let Some(method) = pattern_method(machine, pattern, symbol)? {
        return Ok(BuiltinOutcome::Value(machine.call_value(
            method,
            pattern,
            &[this],
        )?));
    }
    let string = text(machine, this)?;
    let regexp = super::regexp::regexp_create(machine, pattern, Value::UNDEFINED)?;
    let input = allocate_string(machine, string)?;
    invoke_on_new_regexp(machine, regexp, symbol, input)
}

fn match_all<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_coercible(this)?;
    let pattern = args.first().copied().unwrap_or(Value::UNDEFINED);
    if machine.is_object(pattern) && is_regexp(machine, pattern)? {
        let flags = machine.get_named_property(pattern, "flags")?;
        require_coercible(flags)?;
        let flags = machine.coerce_string_observable(flags)?;
        if !flags.as_units().contains(&u16::from(b'g')) {
            return Err(type_error(
                "String.prototype.matchAll requires a global RegExp",
            ));
        }
    }
    let symbol = machine.intrinsics.builtins.symbol_match_all();
    if let Some(method) = pattern_method(machine, pattern, symbol)? {
        return Ok(BuiltinOutcome::Value(machine.call_value(
            method,
            pattern,
            &[this],
        )?));
    }
    let string = text(machine, this)?;
    let global = allocate_string(machine, EcmaString::encode("g"))?;
    let regexp = super::regexp::regexp_create(machine, pattern, global)?;
    let input = allocate_string(machine, string)?;
    invoke_on_new_regexp(machine, regexp, symbol, input)
}
const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;
fn string_receiver<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
) -> Result<EcmaString, EvalFailure> {
    require_coercible(this)?;
    machine.coerce_string_observable(this)
}

fn number<H: Host>(machine: &mut Machine<'_, H>, value: Value) -> Result<f64, EvalFailure> {
    machine.coerce_number_observable(value).map(value_number)
}
fn length_of_array_like<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<usize, EvalFailure> {
    require_coercible(value)?;
    let length = machine.get_named_property(value, "length")?;
    let length = to_integer_or_infinity(machine, length)?.clamp(0.0, MAX_SAFE_INTEGER);
    Ok(length as usize)
}
fn heap_limit(machine: &Machine<'_, impl Host>) -> EvalFailure {
    EvalFailure::Runtime(RuntimeErrorKind::HeapByteLimitExceeded {
        limit: machine.limits.max_heap_bytes,
    })
}

fn preflight_units<H: Host>(machine: &Machine<'_, H>, units: usize) -> Result<(), EvalFailure> {
    let bytes = units
        .checked_mul(size_of::<u16>())
        .ok_or_else(|| heap_limit(machine))?;
    machine
        .ensure_allocation_capacity(1, bytes)
        .map_err(EvalFailure::Runtime)
}
fn from_code_point<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let mut output = EcmaStringBuilder::with_capacity(args.len());
    for &argument in args {
        let code_point = number(machine, argument)?;
        if !code_point.is_finite()
            || code_point.fract() != 0.0
            || !(0.0..=0x10_FFFF as f64).contains(&code_point)
        {
            return Err(range_error("Invalid code point"));
        }
        output
            .push_code_point(code_point as u32)
            .expect("validated Unicode code point");
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}
fn raw<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let template = args.first().copied().unwrap_or(Value::UNDEFINED);
    require_coercible(template)?;
    let literals = machine.get_named_property(template, "raw")?;
    require_coercible(literals)?;
    let literal_count = length_of_array_like(machine, literals)?;
    if literal_count == 0 {
        return Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            EcmaString::default(),
        )?));
    }

    let mut output = EcmaStringBuilder::new();
    for index in 0..literal_count {
        super::array::tick(machine)?;
        let key = PropertyKey::Named(machine.intern_str(&index.to_string()));
        let literal = machine.get_property_key(literals, &key)?;
        append(&mut output, &machine.coerce_string_observable(literal)?);
        if index + 1 < literal_count && index + 1 < args.len() {
            append(
                &mut output,
                &machine.coerce_string_observable(args[index + 1])?,
            );
        }
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}
fn is_well_formed_units(units: &[u16]) -> bool {
    let mut index = 0;
    while index < units.len() {
        match units[index] {
            0xD800..=0xDBFF
                if units
                    .get(index + 1)
                    .is_some_and(|unit| matches!(*unit, 0xDC00..=0xDFFF)) =>
            {
                index += 2;
            }

            0xD800..=0xDFFF => return false,
            _ => index += 1,
        }
    }
    true
}

fn is_well_formed<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = string_receiver(machine, this)?;
    Ok(BuiltinOutcome::Value(Value::boolean(is_well_formed_units(
        source.as_units(),
    ))))
}

fn well_formed_units(units: &[u16]) -> EcmaString {
    let mut output = EcmaStringBuilder::with_capacity(units.len());
    let mut index = 0;
    while index < units.len() {
        match units[index] {
            lead @ 0xD800..=0xDBFF
                if units
                    .get(index + 1)
                    .is_some_and(|unit| matches!(*unit, 0xDC00..=0xDFFF)) =>
            {
                output.push_unit(lead);
                output.push_unit(units[index + 1]);
                index += 2;
            }
            0xD800..=0xDFFF => {
                output.push_unit(0xFFFD);
                index += 1;
            }
            unit => {
                output.push_unit(unit);
                index += 1;
            }
        }
    }
    output.finish()
}

fn to_well_formed<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = string_receiver(machine, this)?;
    let result = if is_well_formed_units(source.as_units()) {
        source
    } else {
        well_formed_units(source.as_units())
    };
    Ok(BuiltinOutcome::Value(allocate_string(machine, result)?))
}
fn at<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = string_receiver(machine, this)?;
    let relative = to_integer_or_infinity(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let index = if relative >= 0.0 {
        relative
    } else {
        source.len_units() as f64 + relative
    };
    if index < 0.0 || index >= source.len_units() as f64 {
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    }
    let unit = source
        .unit_at(index as usize)
        .expect("index was checked against the UTF-16 length");
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        EcmaString::from_units(&[unit]),
    )?))
}
fn replacement_text(
    template: &EcmaString,
    matched: &EcmaString,
    position: usize,
    source: &EcmaString,
) -> EcmaString {
    let mut output = EcmaStringBuilder::new();
    let units = template.as_units();
    let mut index = 0;
    while index < units.len() {
        if units[index] != u16::from(b'$') || index + 1 == units.len() {
            output.push_unit(units[index]);
            index += 1;
            continue;
        }
        match units[index + 1] {
            unit if unit == u16::from(b'$') => output.push_unit(u16::from(b'$')),
            unit if unit == u16::from(b'&') => append(&mut output, matched),
            unit if unit == u16::from(b'`') => append(
                &mut output,
                &source
                    .slice_units(0..position)
                    .expect("replacement position is within source"),
            ),
            unit if unit == u16::from(b'\'') => append(
                &mut output,
                &source
                    .slice_units(position + matched.len_units()..source.len_units())
                    .expect("replacement match is within source"),
            ),
            _ => {
                output.push_unit(units[index]);
                index += 1;
                continue;
            }
        }
        index += 2;
    }
    output.finish()
}

fn symbol_key<H: Host>(
    machine: &Machine<'_, H>,
    symbol: Value,
    name: &'static str,
) -> Result<PropertyKey, EvalFailure> {
    let index = machine
        .runtime_slot(symbol)
        .map_err(EvalFailure::Runtime)?
        .unwrap_or_else(|| panic!("{name} belongs to the runtime heap"));
    Ok(PropertyKey::Symbol(index as u32))
}
pub(super) fn is_regexp<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<bool, EvalFailure> {
    if !machine.is_object(value) {
        return Ok(false);
    }
    let match_key = symbol_key(
        machine,
        machine.intrinsics.builtins.symbol_match(),
        "Symbol.match",
    )?;
    let matcher = machine.get_property_key(value, &match_key)?;
    if matcher != Value::UNDEFINED {
        return Ok(machine.to_boolean(matcher));
    }
    Ok(super::regexp::regexp_parts(machine, value).is_some())
}
fn replace_all<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_coercible(this)?;
    let search = args.first().copied().unwrap_or(Value::UNDEFINED);
    let replacement = args.get(1).copied().unwrap_or(Value::UNDEFINED);

    if machine.is_object(search) {
        if is_regexp(machine, search)? {
            let flags = machine.get_named_property(search, "flags")?;
            require_coercible(flags)?;
            let flags = machine.coerce_string_observable(flags)?;
            if !flags.as_units().contains(&u16::from(b'g')) {
                return Err(type_error(
                    "String.prototype.replaceAll requires a global RegExp",
                ));
            }
        }
        let replace_key = symbol_key(
            machine,
            machine.intrinsics.builtins.symbol_replace(),
            "Symbol.replace",
        )?;
        let method = machine.get_property_key(search, &replace_key)?;
        if !matches!(method.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            if !machine.is_callable(method)? {
                return Err(type_error("Symbol.replace property is not callable"));
            }
            return Ok(BuiltinOutcome::Value(machine.call_value(
                method,
                search,
                &[this, replacement],
            )?));
        }
    }

    let source = machine.coerce_string_observable(this)?;
    let needle = machine.coerce_string_observable(search)?;
    let functional = machine.is_callable(replacement)?;
    let template = if functional {
        None
    } else {
        Some(machine.coerce_string_observable(replacement)?)
    };
    let mut output = EcmaStringBuilder::new();

    if needle.is_empty() {
        for position in 0..=source.len_units() {
            let replacement = if functional {
                let matched = allocate_string(machine, EcmaString::default())?;
                let source_value = allocate_string(machine, source.clone())?;
                let value = machine.call_value(
                    replacement,
                    Value::UNDEFINED,
                    &[matched, crate::number_value(position as f64), source_value],
                )?;
                machine.coerce_string_observable(value)?
            } else {
                replacement_text(
                    template
                        .as_ref()
                        .expect("non-callable replacement has template"),
                    &EcmaString::default(),
                    position,
                    &source,
                )
            };
            append(&mut output, &replacement);
            if let Some(unit) = source.unit_at(position) {
                output.push_unit(unit);
            }
        }
    } else {
        let mut cursor = 0;
        while let Some(position) = search_units(source.as_units(), needle.as_units(), cursor) {
            append(
                &mut output,
                &source
                    .slice_units(cursor..position)
                    .expect("search position is within source"),
            );
            let replacement = if functional {
                let matched = allocate_string(machine, needle.clone())?;
                let source_value = allocate_string(machine, source.clone())?;
                let value = machine.call_value(
                    replacement,
                    Value::UNDEFINED,
                    &[matched, crate::number_value(position as f64), source_value],
                )?;
                machine.coerce_string_observable(value)?
            } else {
                replacement_text(
                    template
                        .as_ref()
                        .expect("non-callable replacement has template"),
                    &needle,
                    position,
                    &source,
                )
            };
            append(&mut output, &replacement);
            cursor = position + needle.len_units();
        }
        append(
            &mut output,
            &source
                .slice_units(cursor..source.len_units())
                .expect("replacement cursor is within source"),
        );
    }

    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}
#[derive(Copy, Clone)]
enum NormalizationForm {
    Nfc,
    Nfd,
    Nfkc,
    Nfkd,
}

fn normalize_run(run: &[u16], form: NormalizationForm, output: &mut EcmaStringBuilder) {
    if run.is_empty() {
        return;
    }
    let text = String::from_utf16(run).expect("normalization run is well-formed UTF-16");
    let normalized: String = match form {
        NormalizationForm::Nfc => text.nfc().collect(),
        NormalizationForm::Nfd => text.nfd().collect(),
        NormalizationForm::Nfkc => text.nfkc().collect(),
        NormalizationForm::Nfkd => text.nfkd().collect(),
    };
    output.push_utf8(&normalized);
}

fn normalize_units(source: &EcmaString, form: NormalizationForm) -> EcmaString {
    let units = source.as_units();
    let mut output = EcmaStringBuilder::with_capacity(units.len());
    let mut run_start = 0;
    let mut index = 0;
    while index < units.len() {
        match units[index] {
            0xD800..=0xDBFF
                if units
                    .get(index + 1)
                    .is_some_and(|unit| matches!(*unit, 0xDC00..=0xDFFF)) =>
            {
                index += 2;
            }

            unit @ 0xD800..=0xDFFF => {
                normalize_run(&units[run_start..index], form, &mut output);
                output.push_unit(unit);
                index += 1;
                run_start = index;
            }
            _ => index += 1,
        }
    }
    normalize_run(&units[run_start..], form, &mut output);
    output.finish()
}

fn normalize<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = string_receiver(machine, this)?;
    let form = match args.first().copied().unwrap_or(Value::UNDEFINED) {
        Value::UNDEFINED => NormalizationForm::Nfc,
        value => {
            let form = machine.coerce_string_observable(value)?;
            if form.eq_ascii("NFC") {
                NormalizationForm::Nfc
            } else if form.eq_ascii("NFD") {
                NormalizationForm::Nfd
            } else if form.eq_ascii("NFKC") {
                NormalizationForm::Nfkc
            } else if form.eq_ascii("NFKD") {
                NormalizationForm::Nfkd
            } else {
                return Err(range_error(
                    "The normalization form should be one of NFC, NFD, NFKC, NFKD",
                ));
            }
        }
    };
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        normalize_units(&source, form),
    )?))
}

fn pad<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    at_start: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = string_receiver(machine, this)?;
    let target = to_integer_or_infinity(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?
        .clamp(0.0, MAX_SAFE_INTEGER);
    if target <= source.len_units() as f64 {
        return Ok(BuiltinOutcome::Value(allocate_string(machine, source)?));
    }
    let filler = match args.get(1).copied().unwrap_or(Value::UNDEFINED) {
        Value::UNDEFINED => EcmaString::encode(" "),
        value => machine.coerce_string_observable(value)?,
    };
    if filler.is_empty() {
        return Ok(BuiltinOutcome::Value(allocate_string(machine, source)?));
    }
    if target > usize::MAX as f64 {
        return Err(heap_limit(machine));
    }
    let target = target as usize;
    preflight_units(machine, target)?;
    let fill_length = target - source.len_units();
    let mut output = EcmaStringBuilder::with_capacity(target);
    if at_start {
        for unit in filler.as_units().iter().copied().cycle().take(fill_length) {
            output.push_unit(unit);
        }
    }
    append(&mut output, &source);
    if !at_start {
        for unit in filler.as_units().iter().copied().cycle().take(fill_length) {
            output.push_unit(unit);
        }
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}

fn pad_start<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    pad(machine, this, args, true)
}

fn pad_end<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    pad(machine, this, args, false)
}
fn trimmed(source: &EcmaString, start: bool, end: bool) -> EcmaString {
    let units = source.as_units();
    let first = if start {
        units
            .iter()
            .position(|unit| !is_js_whitespace(*unit))
            .unwrap_or(units.len())
    } else {
        0
    };
    let last = if end {
        units
            .iter()
            .rposition(|unit| !is_js_whitespace(*unit))
            .map_or(first, |index| index + 1)
    } else {
        units.len()
    };
    source
        .slice_units(first..last.max(first))
        .expect("trim bounds come from source")
}

fn trim_impl<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    start: bool,
    end: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = string_receiver(machine, this)?;
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        trimmed(&source, start, end),
    )?))
}
fn trim<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    trim_impl(machine, this, true, true)
}

fn trim_start<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    trim_impl(machine, this, true, false)
}

fn trim_end<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    trim_impl(machine, this, false, true)
}
fn repeat<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = string_receiver(machine, this)?;
    let count = to_integer_or_infinity(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    if count < 0.0 || count == f64::INFINITY {
        return Err(range_error("Invalid count value"));
    }
    if source.is_empty() || count == 0.0 {
        let empty = EcmaString::encode("");
        return Ok(BuiltinOutcome::Value(allocate_string(machine, empty)?));
    }
    if count > usize::MAX as f64 {
        return Err(heap_limit(machine));
    }
    let count = count as usize;
    let units = source
        .len_units()
        .checked_mul(count)
        .ok_or_else(|| heap_limit(machine))?;
    preflight_units(machine, units)?;
    let mut output = EcmaStringBuilder::with_capacity(units);
    for _ in 0..count {
        append(&mut output, &source);
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}

#[cfg(test)]
mod unescape_tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, ThrowOrigin};

    fn escape_string(
        machine: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(
            machine
                .allocate(HeapEntry::String(EcmaString::encode("%u0041")))
                .map_err(EvalFailure::Runtime)?,
        ))
    }

    fn throw_on_coercion(
        _: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "unescape coercion hook",
        }))
    }

    fn native(
        machine: &mut Machine<'_, TestHost>,
        name: &'static str,
        handler: BuiltinHandler<TestHost>,
    ) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name,
            length: 0,
            handler,
        });
        native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            name,
            0,
        )
    }

    #[test]
    fn locale_compare_uses_observable_utf16_lexical_signs() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let locale_compare = machine
            .get_named_property(
                machine.intrinsics.builtins.string_prototype(),
                "localeCompare",
            )
            .expect("localeCompare is installed");
        let lower_a = machine
            .allocate(HeapEntry::String(EcmaString::encode("alpha")))
            .unwrap();
        let lower_b = machine
            .allocate(HeapEntry::String(EcmaString::encode("beta")))
            .unwrap();
        let lower_a_again = machine
            .allocate(HeapEntry::String(EcmaString::encode("alpha")))
            .unwrap();
        let upper_a = machine
            .allocate(HeapEntry::String(EcmaString::encode("Alpha")))
            .unwrap();

        assert_eq!(
            machine
                .call_value(locale_compare, lower_a, &[lower_b])
                .unwrap(),
            Value::int32((-1_i32) as u32)
        );
        assert_eq!(
            machine
                .call_value(locale_compare, lower_b, &[lower_a])
                .unwrap(),
            Value::int32(1)
        );
        assert_eq!(
            machine
                .call_value(locale_compare, lower_a, &[lower_a_again])
                .unwrap(),
            Value::int32(0)
        );
        assert_eq!(
            machine
                .call_value(locale_compare, lower_a, &[upper_a])
                .unwrap(),
            Value::int32(1)
        );

        let coercible = ordinary_object(&mut machine);
        let to_string = native(&mut machine, "localeCompare toString", escape_string);
        machine
            .set_data_property(coercible, "toString", to_string)
            .unwrap();
        assert_eq!(
            machine
                .call_value(locale_compare, coercible, &[lower_a])
                .unwrap(),
            Value::int32((-1_i32) as u32)
        );
    }

    #[test]
    fn string_constructor_renders_symbols_without_relaxing_implicit_coercion() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let symbol_constructor = machine
            .intrinsics
            .global("Symbol")
            .expect("Symbol is installed");
        let description = machine
            .allocate(HeapEntry::String(EcmaString::encode("event")))
            .expect("description allocation succeeds");
        let symbol = machine
            .call_value(symbol_constructor, Value::UNDEFINED, &[description])
            .expect("Symbol creates a symbol");

        assert!(matches!(
            machine.to_string(symbol),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "convert symbol to string"
            }))
        ));

        let string_constructor = machine
            .intrinsics
            .global("String")
            .expect("String is installed");
        let rendered = machine
            .call_value(string_constructor, Value::UNDEFINED, &[symbol])
            .expect("String(Symbol) succeeds");
        assert!(
            machine
                .string_value(rendered)
                .is_some_and(|text| text.eq_ascii("Symbol(event)"))
        );
    }

    #[test]
    fn string_constructor_uses_error_to_string_for_constructed_errors() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let message = machine
            .allocate(HeapEntry::String(EcmaString::encode("message")))
            .expect("message allocation succeeds");
        let error_constructor = machine
            .intrinsics
            .global("Error")
            .expect("Error is installed");
        let error_index = machine
            .runtime_slot(error_constructor)
            .expect("Error is a runtime value")
            .expect("Error is heap allocated");
        let HeapEntry::NativeFunction {
            callable: crate::NativeCallable::Builtin(id),
            ..
        } = machine.heap[error_index]
        else {
            panic!("Error constructor is native");
        };
        let crate::intrinsics::BuiltinOutcome::Value(error) = machine
            .call_builtin(id, Value::UNDEFINED, &[message], true)
            .expect("new Error succeeds")
        else {
            panic!("new Error returns a value");
        };

        let string_constructor = machine
            .intrinsics
            .global("String")
            .expect("String is installed");
        let rendered = machine
            .call_value(string_constructor, Value::UNDEFINED, &[error])
            .expect("String(new Error) succeeds");
        assert!(
            machine
                .string_value(rendered)
                .is_some_and(|text| text.eq_ascii("Error: message"))
        );
    }

    #[test]
    fn unescape_observes_string_coercion_and_preserves_malformed_utf16() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let unescape = machine
            .intrinsics
            .global("unescape")
            .expect("unescape installs");
        let coercible = ordinary_object(&mut machine);
        let to_string = native(&mut machine, "toString", escape_string);
        machine
            .set_data_property(coercible, "toString", to_string)
            .unwrap();
        let coerced = machine
            .call_value(unescape, Value::UNDEFINED, &[coercible])
            .unwrap();
        assert!(
            machine
                .string_value(coerced)
                .is_some_and(|text| text.eq_ascii("A"))
        );

        let malformed = machine
            .allocate(HeapEntry::String(EcmaString::encode(
                "%uD800%u0041%uZZZZ%4G%u12",
            )))
            .unwrap();
        let decoded = machine
            .call_value(unescape, Value::UNDEFINED, &[malformed])
            .unwrap();
        assert_eq!(
            machine.string_value(decoded).unwrap().as_units(),
            &[
                0xd800,
                0x0041,
                b'%' as u16,
                b'u' as u16,
                b'Z' as u16,
                b'Z' as u16,
                b'Z' as u16,
                b'Z' as u16,
                b'%' as u16,
                b'4' as u16,
                b'G' as u16,
                b'%' as u16,
                b'u' as u16,
                b'1' as u16,
                b'2' as u16,
            ]
        );

        let throwing = ordinary_object(&mut machine);
        let throwing_to_string = native(&mut machine, "throwing toString", throw_on_coercion);
        machine
            .set_data_property(throwing, "toString", throwing_to_string)
            .unwrap();
        assert!(
            machine
                .call_value(unescape, Value::UNDEFINED, &[throwing])
                .is_err()
        );
    }

    #[test]
    fn pad_and_repeat_preflight_large_finite_outputs() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let source = machine
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .expect("source string allocation succeeds");
        let pad_start = machine
            .get_named_property(machine.intrinsics.builtins.string_prototype(), "padStart")
            .expect("padStart is installed");
        let repeat = machine
            .get_named_property(machine.intrinsics.builtins.string_prototype(), "repeat")
            .expect("repeat is installed");
        let before = (
            machine.heap.len(),
            machine.heap_bytes,
            machine.machine_bytes,
        );
        machine.limits.max_heap_bytes = machine.heap_bytes;

        for method in [pad_start, repeat] {
            assert!(matches!(
                machine.call_value(method, source, &[Value::number(1e300)]),
                Err(EvalFailure::Runtime(
                    crate::RuntimeErrorKind::HeapByteLimitExceeded { .. }
                ))
            ));
            assert_eq!(
                (
                    machine.heap.len(),
                    machine.heap_bytes,
                    machine.machine_bytes
                ),
                before,
                "failed string expansion must not allocate or charge the machine"
            );
        }
    }

    #[test]
    fn string_iterator_preflights_oversized_sources() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let source = machine
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .expect("source string allocation succeeds");
        let iterator_key = machine
            .property_key_from_value(machine.intrinsics.builtins.symbol_iterator())
            .expect("Symbol.iterator is a property key");
        let iterator = machine
            .get_property_key(
                machine.intrinsics.builtins.string_prototype(),
                &iterator_key,
            )
            .expect("string iterator is installed");
        let before = (
            machine.heap.len(),
            machine.heap_bytes,
            machine.machine_bytes,
        );
        // With no remaining heap budget, the iterator must fail fast instead
        // of allocating one heap string per code point toward the limit.
        machine.limits.max_heap_bytes = machine.heap_bytes;
        assert!(matches!(
            machine.call_value(iterator, source, &[]),
            Err(EvalFailure::Runtime(
                crate::RuntimeErrorKind::HeapByteLimitExceeded { .. }
            ))
        ));
        assert_eq!(
            (
                machine.heap.len(),
                machine.heap_bytes,
                machine.machine_bytes
            ),
            before,
            "a failed string iterator must not allocate or charge the machine"
        );
    }
}

/// Regression tests for codePointAt, split_regexp, and GetSubstitution.
#[cfg(test)]
mod split_replace_tests {
    use super::super::test_support::{TestHost, blank_program};
    use super::*;
    use crate::Limits;
    use crate::intrinsics::{BuiltinDef, native_function};

    fn replacement_argument_count(
        _: &mut Machine<'_, TestHost>,
        _: Value,
        args: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(
            crate::number_value(args.len() as f64),
        ))
    }

    fn native_replacer(
        machine: &mut Machine<'_, TestHost>,
        handler: BuiltinHandler<TestHost>,
    ) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "replacementArgumentCount",
            length: 0,
            handler,
        });
        native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            "replacementArgumentCount",
            0,
        )
    }

    /// Constructs a RegExp the same way the `RegExp` constructor does, so
    /// `regexp_parts` recognises the result in split/replace dispatch.
    fn construct_regexp(machine: &mut Machine<'_, TestHost>, pattern: &str, flags: &str) -> Value {
        let constructor = machine.intrinsics.global("RegExp").expect("RegExp exists");
        let pattern_val = machine
            .allocate(HeapEntry::String(EcmaString::encode(pattern)))
            .unwrap();
        let flags_val = machine
            .allocate(HeapEntry::String(EcmaString::encode(flags)))
            .unwrap();
        let index = machine.runtime_slot(constructor).unwrap().unwrap();
        let HeapEntry::NativeFunction {
            callable: crate::NativeCallable::Builtin(id),
            ..
        } = machine.heap[index]
        else {
            panic!("RegExp constructor is native");
        };
        let BuiltinOutcome::Value(value) = machine
            .call_builtin(id, Value::UNDEFINED, &[pattern_val, flags_val], true)
            .unwrap()
        else {
            panic!("RegExp constructor returns a value");
        };
        value
    }

    /// Calls a String.prototype method on `this_string` with `args`, returning
    /// the raw result value.
    fn call_string_method(
        machine: &mut Machine<'_, TestHost>,
        method: &str,
        this_string: &str,
        args: &[Value],
    ) -> Value {
        let method_fn = machine
            .get_named_property(machine.intrinsics.builtins.string_prototype(), method)
            .unwrap_or_else(|_| panic!("{method} is installed"));
        let this_val = machine
            .allocate(HeapEntry::String(EcmaString::encode(this_string)))
            .unwrap();
        machine
            .call_value(method_fn, this_val, args)
            .expect("string method call succeeds")
    }

    /// Extracts the string elements of an Array result.
    fn array_strings(machine: &mut Machine<'_, TestHost>, array: Value) -> Vec<String> {
        let elements = machine
            .array_elements(array)
            .unwrap()
            .expect("result is an array");
        elements
            .into_iter()
            .map(|value| {
                machine
                    .string_value(value)
                    .map(|text| text.to_utf8_lossy())
                    .unwrap_or_default()
            })
            .collect()
    }

    // ── Finding 1: codePointAt ──────────────────────────────────────────

    #[test]
    fn code_point_at_surrogate_pair_boundary() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        // "a😀b" — 😀 is U+1F600, a surrogate pair at UTF-16 indices 1..2.
        let s = "a😀b";
        let code_point_at = machine
            .get_named_property(
                machine.intrinsics.builtins.string_prototype(),
                "codePointAt",
            )
            .unwrap();
        let this_val = machine
            .allocate(HeapEntry::String(EcmaString::encode(s)))
            .unwrap();

        // Index 0: 'a' = U+0061
        let result = machine
            .call_value(code_point_at, this_val, &[Value::int32(0)])
            .unwrap();
        assert_eq!(value_number(result), 97.0); // U+0061 = 97

        // Index 1: high surrogate → full code point U+1F600
        let result = machine
            .call_value(code_point_at, this_val, &[Value::int32(1)])
            .unwrap();
        assert_eq!(value_number(result), 128512.0); // U+1F600 = 128512

        // Index 2: low surrogate alone → 0xDC00 (the trailing surrogate unit)
        let result = machine
            .call_value(code_point_at, this_val, &[Value::int32(2)])
            .unwrap();
        assert_eq!(value_number(result), f64::from(0xDE00u16));

        // Index 3: 'b' = U+0062
        let result = machine
            .call_value(code_point_at, this_val, &[Value::int32(3)])
            .unwrap();
        assert_eq!(value_number(result), 98.0); // U+0062 = 98

        // Out of bounds → undefined
        let result = machine
            .call_value(code_point_at, this_val, &[Value::int32(4)])
            .unwrap();
        assert_eq!(result, Value::UNDEFINED);
    }

    // ── Finding 2: split_regexp empty-match data loss ───────────────────

    #[test]
    fn split_regexp_empty_pattern_preserves_every_character() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "(?:)", "");
        let result = call_string_method(&mut machine, "split", "abc", &[regexp]);
        assert_eq!(
            array_strings(&mut machine, result),
            vec!["a".to_string(), "b".to_string(), "c".to_string()],
            "empty-pattern split must preserve every character"
        );
    }

    #[test]
    fn split_regexp_empty_pattern_on_two_chars() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "(?:)", "");
        let result = call_string_method(&mut machine, "split", "ab", &[regexp]);
        assert_eq!(
            array_strings(&mut machine, result),
            vec!["a".to_string(), "b".to_string()],
        );
    }

    #[test]
    fn split_regexp_star_pattern_preserves_characters() {
        // "abc".split(/b*/) — /b*/ matches "b" at index 1, so the separator
        // consumes "b" and the result is ["a", "c"]. The data-loss bug would
        // have dropped "a" (the empty match at position 0 advanced past it
        // without pushing). Verify "a" and "c" survive.
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "b*", "");
        let result = call_string_method(&mut machine, "split", "abc", &[regexp]);
        assert_eq!(
            array_strings(&mut machine, result),
            vec!["a".to_string(), "c".to_string()],
            "split(/b*/) must not drop 'a' via the empty match at position 0"
        );
    }

    #[test]
    fn split_regexp_empty_pattern_unicode_surrogate_pair() {
        // "😀x".split(/(?:)/u) — the surrogate pair must be one piece under /u.
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "(?:)", "u");
        let result = call_string_method(&mut machine, "split", "😀x", &[regexp]);
        let pieces = array_strings(&mut machine, result);
        assert_eq!(
            pieces.len(),
            2,
            "😀x split on empty /u pattern yields 2 pieces"
        );
        assert_eq!(pieces[0], "😀");
        assert_eq!(pieces[1], "x");
    }

    #[test]
    fn split_regexp_non_empty_still_works() {
        // The non-empty path was already correct; make sure the fix didn't
        // break it.
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "\\d", "");
        let result = call_string_method(&mut machine, "split", "a1b2c", &[regexp]);
        assert_eq!(array_strings(&mut machine, result), vec!["a", "b", "c"],);
    }

    // ── Finding 3: GetSubstitution replacement patterns ─────────────────

    #[test]
    fn replace_dollar_dollar_escapes_to_literal_dollar() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "x", "");
        let replacement = machine
            .allocate(HeapEntry::String(EcmaString::encode("$$")))
            .unwrap();
        let result = call_string_method(&mut machine, "replace", "axb", &[regexp, replacement]);
        assert_eq!(machine.string_value(result).unwrap().to_utf8_lossy(), "a$b");
    }

    #[test]
    fn replace_dollar_ampersand_inserts_matched_substring() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "x", "");
        let replacement = machine
            .allocate(HeapEntry::String(EcmaString::encode("[$&]")))
            .unwrap();
        let result = call_string_method(&mut machine, "replace", "axb", &[regexp, replacement]);
        assert_eq!(
            machine.string_value(result).unwrap().to_utf8_lossy(),
            "a[x]b"
        );
    }

    #[test]
    fn replace_dollar_backtick_inserts_before_match() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "x", "");
        let replacement = machine
            .allocate(HeapEntry::String(EcmaString::encode("[$`]")))
            .unwrap();
        let result = call_string_method(&mut machine, "replace", "axb", &[regexp, replacement]);
        assert_eq!(
            machine.string_value(result).unwrap().to_utf8_lossy(),
            "a[a]b"
        );
    }

    #[test]
    fn replace_dollar_quote_inserts_after_match() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "x", "");
        let replacement = machine
            .allocate(HeapEntry::String(EcmaString::encode("[$']")))
            .unwrap();
        let result = call_string_method(&mut machine, "replace", "axb", &[regexp, replacement]);
        assert_eq!(
            machine.string_value(result).unwrap().to_utf8_lossy(),
            "a[b]b"
        );
    }

    #[test]
    fn replace_two_digit_group_prefers_group_10_when_it_exists() {
        // With 10+ capture groups, $10 must resolve to group 10, not group 1
        // followed by a literal "0".
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        // (a)(b)(c)(d)(e)(f)(g)(h)(i)(j) — 10 groups; group 10 = "j"
        let regexp = construct_regexp(&mut machine, "(a)(b)(c)(d)(e)(f)(g)(h)(i)(j)", "");
        let replacement = machine
            .allocate(HeapEntry::String(EcmaString::encode("$10")))
            .unwrap();
        let result = call_string_method(
            &mut machine,
            "replace",
            "abcdefghij",
            &[regexp, replacement],
        );
        assert_eq!(
            machine.string_value(result).unwrap().to_utf8_lossy(),
            "j",
            "$10 must prefer group 10 when it exists"
        );
    }

    #[test]
    fn replace_two_digit_group_falls_back_to_one_digit_when_group_absent() {
        // With only 1 capture group, $10 resolves to group 1 + literal "0".
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "(a)", "");
        let replacement = machine
            .allocate(HeapEntry::String(EcmaString::encode("$10")))
            .unwrap();
        let result = call_string_method(&mut machine, "replace", "aX", &[regexp, replacement]);
        assert_eq!(
            machine.string_value(result).unwrap().to_utf8_lossy(),
            "a0X",
            "$10 with only group 1 must yield group-1 + literal '0'"
        );
    }

    #[test]
    fn replace_named_group_reference() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "(?<id>\\d+)", "");
        let replacement = machine
            .allocate(HeapEntry::String(EcmaString::encode("id=$<id>")))
            .unwrap();
        let result =
            call_string_method(&mut machine, "replace", "/users/7", &[regexp, replacement]);
        assert_eq!(
            machine.string_value(result).unwrap().to_utf8_lossy(),
            "/users/id=7"
        );
    }

    #[test]
    fn replace_callback_omits_groups_argument_without_named_captures() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "x", "");
        let replacer = native_replacer(&mut machine, replacement_argument_count);
        let result = call_string_method(&mut machine, "replace", "x", &[regexp, replacer]);
        assert_eq!(machine.string_value(result).unwrap().to_utf8_lossy(), "3");
    }

    #[test]
    fn replace_named_reference_stays_literal_without_named_captures() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "x", "");
        let replacement = machine
            .allocate(HeapEntry::String(EcmaString::encode("$<foo>")))
            .unwrap();
        let result = call_string_method(&mut machine, "replace", "x", &[regexp, replacement]);
        assert_eq!(
            machine.string_value(result).unwrap().to_utf8_lossy(),
            "$<foo>"
        );
    }

    #[test]
    fn replace_absent_named_group_substitutes_empty() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "(?<name>x)", "");
        let replacement = machine
            .allocate(HeapEntry::String(EcmaString::encode("[$<missing>]")))
            .unwrap();
        let result = call_string_method(&mut machine, "replace", "x", &[regexp, replacement]);
        assert_eq!(machine.string_value(result).unwrap().to_utf8_lossy(), "[]");
    }

    #[test]
    fn replace_named_group_undefined_substitutes_empty() {
        // A named group that did not participate substitutes the empty string.
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        // (a)(?<name>b)? — the named group is optional and won't match "a".
        let regexp = construct_regexp(&mut machine, "(a)(?<name>b)?", "");
        let replacement = machine
            .allocate(HeapEntry::String(EcmaString::encode("[$<name>]")))
            .unwrap();
        let result = call_string_method(&mut machine, "replace", "a", &[regexp, replacement]);
        assert_eq!(machine.string_value(result).unwrap().to_utf8_lossy(), "[]");
    }

    fn match_exec_override(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "matchOverrideSeen", Value::boolean(true))?;
        Ok(BuiltinOutcome::Value(Value::NULL))
    }

    #[test]
    fn string_match_honours_own_exec_override() {
        let program = blank_program("<string match exec override>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "a", "");
        let override_fn = native_replacer(&mut machine, match_exec_override);
        machine
            .set_data_property(regexp, "exec", override_fn)
            .expect("override installed");
        let result = call_string_method(&mut machine, "match", "xa", &[regexp]);
        assert_eq!(result, Value::NULL);
        assert_eq!(
            machine
                .get_named_property(regexp, "matchOverrideSeen")
                .unwrap(),
            Value::boolean(true)
        );
    }
}
#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{ArrayElementKind, Limits, Property, PropertyMap, ThrowOrigin};

    macro_rules! test_machine {
        ($program:ident, $host:ident, $machine:ident) => {
            let $program = blank_program("<string-edge>");
            let mut $host = TestHost;
            let mut $machine = Machine::new(&$program, &mut $host, Limits::default());
        };
    }

    fn string(machine: &mut Machine<'_, TestHost>, units: &[u16]) -> Value {
        machine
            .allocate(HeapEntry::String(EcmaString::from_units(units)))
            .expect("string allocation succeeds")
    }

    fn result_text(machine: &mut Machine<'_, TestHost>, outcome: BuiltinOutcome) -> Vec<u16> {
        let BuiltinOutcome::Value(value) = outcome else {
            panic!("String builtin returns a value")
        };
        machine
            .string_value(value)
            .expect("result is a String")
            .as_units()
            .to_vec()
    }

    fn result_value(outcome: BuiltinOutcome) -> Value {
        let BuiltinOutcome::Value(value) = outcome else {
            panic!("String builtin returns a value")
        };
        value
    }

    #[test]
    fn well_formed_operations_preserve_pairs_and_replace_lone_surrogates() {
        test_machine!(program, host, machine);
        let paired = string(&mut machine, &[0xD83D, 0xDE00]);
        let malformed = string(&mut machine, &[b'a' as u16, 0xD800, 0xDC00, 0xDFFF]);
        assert_eq!(
            result_value(is_well_formed(&mut machine, paired, &[], false).unwrap()),
            Value::TRUE
        );
        assert_eq!(
            result_value(is_well_formed(&mut machine, malformed, &[], false).unwrap()),
            Value::FALSE
        );
        let repaired = to_well_formed(&mut machine, malformed, &[], false).unwrap();
        assert_eq!(
            result_text(&mut machine, repaired),
            [b'a' as u16, 0xD800, 0xDC00, 0xFFFD]
        );
    }

    #[test]
    fn at_indexes_utf16_units_from_either_end() {
        test_machine!(program, host, machine);
        let source = string(&mut machine, &[0xD83D, 0xDE00, b'x' as u16]);
        let forward = at(&mut machine, source, &[Value::int32(1)], false).unwrap();
        assert_eq!(result_text(&mut machine, forward), [0xDE00]);
        let backward = at(&mut machine, source, &[crate::number_value(-1.0)], false).unwrap();
        assert_eq!(result_text(&mut machine, backward), [b'x' as u16]);
    }

    #[test]
    fn empty_replace_pattern_visits_every_utf16_boundary() {
        test_machine!(program, host, machine);
        let source = string(&mut machine, &[b'a' as u16, 0xD800]);
        let empty = string(&mut machine, &[]);
        let dash = string(&mut machine, &[b'-' as u16]);
        let replaced = replace_all(&mut machine, source, &[empty, dash], false).unwrap();
        assert_eq!(
            result_text(&mut machine, replaced),
            [b'-' as u16, b'a' as u16, b'-' as u16, 0xD800, b'-' as u16]
        );
    }

    fn throwing_to_string<H: Host>(
        _machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(type_error("receiver coercion must not run"))
    }

    fn symbol_replace_hook<H: Host>(
        _machine: &mut Machine<'_, H>,
        this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        assert_eq!(args.len(), 2);
        assert_eq!(args[1], Value::int32(9));
        Ok(BuiltinOutcome::Value(this))
    }
    fn literal_dollar_replacer<H: Host>(
        machine: &mut Machine<'_, H>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        assert_eq!(args.len(), 3);
        Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            EcmaString::from_units(&[b'$' as u16, b'&' as u16]),
        )?))
    }

    #[test]
    fn replace_all_dispatches_symbol_replace_before_receiver_coercion() {
        test_machine!(program, host, machine);
        let search = ordinary_object(&mut machine);
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "replace hook",
            length: 2,
            handler: symbol_replace_hook::<TestHost>,
        });
        let hook = native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            "replace hook",
            2,
        );
        let symbol = machine.intrinsics.builtins.symbol_replace();
        let key = machine.property_key_from_value(symbol).unwrap();
        machine.set_data_property_key(search, key, hook).unwrap();
        let receiver = ordinary_object(&mut machine);
        let coercion_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "throwing toString",
            length: 0,
            handler: throwing_to_string::<TestHost>,
        });
        let coercion = native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            coercion_id,
            "throwing toString",
            0,
        );
        machine
            .set_data_property(receiver, "toString", coercion)
            .unwrap();
        assert_eq!(
            result_value(
                replace_all(&mut machine, receiver, &[search, Value::int32(9)], false,).unwrap(),
            ),
            search,
        );
    }

    #[test]
    fn normalization_supports_all_forms_and_preserves_lone_surrogates() {
        test_machine!(program, host, machine);
        let decomposed = string(&mut machine, &[b'e' as u16, 0x0301, 0xD800]);
        let nfc = string(
            &mut machine,
            b"NFC"
                .iter()
                .map(|b| u16::from(*b))
                .collect::<Vec<_>>()
                .as_slice(),
        );
        let normalized = normalize(&mut machine, decomposed, &[nfc], false).unwrap();
        assert_eq!(result_text(&mut machine, normalized), [0x00E9, 0xD800]);
        for form in ["NFD", "NFKC", "NFKD"] {
            let form_value = string(&mut machine, &form.encode_utf16().collect::<Vec<_>>());
            normalize(&mut machine, decomposed, &[form_value], false).unwrap();
        }
        let invalid = string(&mut machine, &[b'X' as u16]);
        assert!(matches!(
            normalize(&mut machine, decomposed, &[invalid], false),
            Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
        ));
    }
    #[test]
    fn at_handles_fractional_non_finite_and_surrogate_indices() {
        test_machine!(program, host, machine);
        let source = string(&mut machine, &[0xD83D, 0xDE00, b'x' as u16, 0xD800]);
        for (index, expected) in [
            (0.9, Some(0xD83D)),
            (1.9, Some(0xDE00)),
            (-1.0, Some(0xD800)),
            (-4.0, Some(0xD83D)),
            (4.0, None),
            (-5.0, None),
            (f64::INFINITY, None),
            (f64::NEG_INFINITY, None),
        ] {
            let outcome = at(&mut machine, source, &[crate::number_value(index)], false).unwrap();
            match expected {
                Some(unit) => assert_eq!(result_text(&mut machine, outcome), [unit]),
                None => assert_eq!(result_value(outcome), Value::UNDEFINED),
            }
        }
        let nan = at(
            &mut machine,
            source,
            &[crate::number_value(f64::NAN)],
            false,
        )
        .unwrap();
        assert_eq!(result_text(&mut machine, nan), [0xD83D]);
    }

    #[test]
    fn replace_all_preserves_utf16_and_expands_only_defined_substitutions() {
        test_machine!(program, host, machine);
        let source = string(&mut machine, &[b'a' as u16, 0xD800, b'c' as u16]);
        let needle = string(&mut machine, &[0xD800]);
        let template = string(
            &mut machine,
            &"$$|$&|$\x60|$'|$1".encode_utf16().collect::<Vec<_>>(),
        );
        let replaced = replace_all(&mut machine, source, &[needle, template], false).unwrap();
        assert_eq!(
            result_text(&mut machine, replaced),
            [
                b'a' as u16,
                b'$' as u16,
                b'|' as u16,
                0xD800,
                b'|' as u16,
                b'a' as u16,
                b'|' as u16,
                b'c' as u16,
                b'|' as u16,
                b'$' as u16,
                b'1' as u16,
                b'c' as u16,
            ]
        );
    }
    #[test]
    fn callable_replace_all_results_are_not_substitution_processed() {
        test_machine!(program, host, machine);
        let source = string(&mut machine, &[b'a' as u16, b'a' as u16]);
        let needle = string(&mut machine, &[b'a' as u16]);
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "literal dollar replacer",
            length: 3,
            handler: literal_dollar_replacer::<TestHost>,
        });
        let replacer = native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            "literal dollar replacer",
            3,
        );
        let replaced = replace_all(&mut machine, source, &[needle, replacer], false).unwrap();
        assert_eq!(
            result_text(&mut machine, replaced),
            [b'$' as u16, b'&' as u16, b'$' as u16, b'&' as u16]
        );
    }

    #[test]
    fn replace_all_honors_symbol_match_before_symbol_replace() {
        test_machine!(program, host, machine);
        let search = ordinary_object(&mut machine);
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "replace hook",
            length: 2,
            handler: symbol_replace_hook::<TestHost>,
        });
        let hook = native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            "replace hook",
            2,
        );
        let match_symbol = machine.intrinsics.builtins.symbol_match();
        let match_key = machine.property_key_from_value(match_symbol).unwrap();
        let replace_symbol = machine.intrinsics.builtins.symbol_replace();
        let replace_key = machine.property_key_from_value(replace_symbol).unwrap();
        machine
            .set_data_property_key(search, match_key.clone(), Value::TRUE)
            .unwrap();
        let flags = string(&mut machine, &[b'i' as u16]);
        machine.set_data_property(search, "flags", flags).unwrap();
        machine
            .set_data_property_key(search, replace_key, hook)
            .unwrap();
        assert!(matches!(
            replace_all(
                &mut machine,
                Value::int32(7),
                &[search, Value::int32(9)],
                false
            ),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));

        machine
            .set_data_property_key(search, match_key, Value::FALSE)
            .unwrap();
        assert_eq!(
            result_value(
                replace_all(
                    &mut machine,
                    Value::int32(7),
                    &[search, Value::int32(9)],
                    false
                )
                .unwrap()
            ),
            search
        );
    }

    #[test]
    fn installed_string_iterator_preserves_code_point_and_lone_surrogate_edges() {
        test_machine!(program, host, machine);
        let source = string(&mut machine, &[0xD83D, 0xDE00, 0xD800, b'x' as u16, 0xDFFF]);
        let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
        let iterator_key = machine.property_key_from_value(iterator_symbol).unwrap();
        let iterator_method = machine.get_property_key(source, &iterator_key).unwrap();
        let iterator = machine.call_value(iterator_method, source, &[]).unwrap();
        let next = machine.get_named_property(iterator, "next").unwrap();

        for expected in [
            vec![0xD83D, 0xDE00],
            vec![0xD800],
            vec![b'x' as u16],
            vec![0xDFFF],
        ] {
            let result = machine.call_value(next, iterator, &[]).unwrap();
            assert_eq!(
                machine.get_named_property(result, "done").unwrap(),
                Value::FALSE
            );
            let value = machine.get_named_property(result, "value").unwrap();
            assert_eq!(machine.string_value(value).unwrap().as_units(), expected);
        }
        for _ in 0..2 {
            let result = machine.call_value(next, iterator, &[]).unwrap();
            assert_eq!(
                machine.get_named_property(result, "done").unwrap(),
                Value::TRUE
            );
            assert_eq!(
                machine.get_named_property(result, "value").unwrap(),
                Value::UNDEFINED
            );
        }
    }

    #[test]
    fn from_code_point_raw_pad_trim_and_repeat_boundaries() {
        test_machine!(program, host, machine);
        let encoded = from_code_point(
            &mut machine,
            Value::UNDEFINED,
            &[Value::int32(0x1F600)],
            false,
        )
        .unwrap();
        assert_eq!(result_text(&mut machine, encoded), [0xD83D, 0xDE00]);
        assert!(matches!(
            from_code_point(
                &mut machine,
                Value::UNDEFINED,
                &[crate::number_value(0x11_0000 as f64)],
                false
            ),
            Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
        ));

        let literal_a = string(&mut machine, &[b'a' as u16]);
        let literal_b = string(&mut machine, &[b'b' as u16]);
        let literals = machine
            .allocate(HeapEntry::Array {
                kind: ArrayElementKind::for_elements(&[literal_a, literal_b]),
                elements: vec![literal_a, literal_b],
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.array_prototype),
                extensible: true,
                length_writable: true,
            })
            .unwrap();
        let template = ordinary_object(&mut machine);
        machine
            .set_data_property(template, "raw", literals)
            .unwrap();
        let substitution = string(&mut machine, &[b'x' as u16]);
        let raw_result = raw(
            &mut machine,
            Value::UNDEFINED,
            &[template, substitution],
            false,
        )
        .unwrap();
        assert_eq!(
            result_text(&mut machine, raw_result),
            [b'a' as u16, b'x' as u16, b'b' as u16]
        );

        let source = string(&mut machine, &[0x00A0, b'x' as u16, 0xFEFF]);
        let trimmed = trim(&mut machine, source, &[], false).unwrap();
        assert_eq!(result_text(&mut machine, trimmed), [b'x' as u16]);
        let fill = string(&mut machine, &[b'a' as u16, b'b' as u16]);
        let x = string(&mut machine, &[b'x' as u16]);
        let padded = pad_end(&mut machine, x, &[Value::int32(4), fill], false).unwrap();
        assert_eq!(
            result_text(&mut machine, padded),
            [b'x' as u16, b'a' as u16, b'b' as u16, b'a' as u16]
        );
        let unused_filler = ordinary_object(&mut machine);
        let coercion_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "unused filler toString",
            length: 0,
            handler: throwing_to_string::<TestHost>,
        });
        let coercion = native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            coercion_id,
            "unused filler toString",
            0,
        );
        machine
            .set_data_property(unused_filler, "toString", coercion)
            .unwrap();

        let unchanged = pad_end(&mut machine, x, &[Value::int32(1), unused_filler], false).unwrap();
        assert_eq!(result_text(&mut machine, unchanged), [b'x' as u16]);
        let empty = string(&mut machine, &[]);
        let huge_empty =
            repeat(&mut machine, empty, &[crate::number_value(f64::MAX)], false).unwrap();
        assert!(result_text(&mut machine, huge_empty).is_empty());
        let none = repeat(&mut machine, x, &[Value::int32(0)], false).unwrap();
        assert!(result_text(&mut machine, none).is_empty());
        assert!(matches!(
            repeat(
                &mut machine,
                x,
                &[crate::number_value(f64::INFINITY)],
                false
            ),
            Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
        ));
    }
    #[test]
    fn installer_preserves_string_identity_and_builtin_descriptors() {
        test_machine!(program, host, machine);
        let constructor = machine
            .intrinsics
            .global("String")
            .expect("String is installed");
        let prototype = machine.intrinsics.builtins.string_prototype();
        assert_eq!(
            machine
                .get_named_property(constructor, "prototype")
                .unwrap(),
            prototype,
        );
        for (owner, name, length) in [
            (constructor, "fromCodePoint", 1),
            (constructor, "raw", 1),
            (prototype, "isWellFormed", 0),
            (prototype, "toWellFormed", 0),
            (prototype, "at", 1),
            (prototype, "replaceAll", 2),
            (prototype, "normalize", 0),
            (prototype, "padStart", 1),
            (prototype, "padEnd", 1),
            (prototype, "trim", 0),
            (prototype, "trimStart", 0),
            (prototype, "trimEnd", 0),
            (prototype, "repeat", 1),
        ] {
            let function = machine.get_named_property(owner, name).unwrap();
            assert!(machine.is_callable(function).unwrap());
            for (property, expected) in [("name", None), ("length", Some(length))] {
                let descriptor_key = PropertyKey::Named(machine.intern_str(property));
                let descriptor = machine.own_descriptor(function, &descriptor_key).unwrap();
                assert!(matches!(
                    descriptor,
                    Some(Property::Data {
                        value,
                        writable: false,
                        enumerable: false,
                        configurable: true,
                    }) if expected.map_or_else(
                        || machine.string_value(value).is_some_and(|text| text.eq_ascii(name)),
                        |length| value == Value::int32(length),
                    )
                ));
            }
            let owner_key = PropertyKey::Named(machine.intern_str(name));
            assert!(matches!(
                machine
                    .own_descriptor(owner, &owner_key)
                    .unwrap(),
                Some(Property::Data {
                    value,
                    writable: true,
                    enumerable: false,
                    configurable: true,
                }) if value == function
            ));
        }
    }

    #[test]
    fn receiver_coercion_precedes_argument_coercion_and_large_outputs_preflight() {
        test_machine!(program, host, machine);
        assert!(matches!(
            at(&mut machine, Value::NULL, &[Value::int32(0)], false),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        let source = string(&mut machine, &[b'x' as u16]);
        let before = (
            machine.heap.len(),
            machine.heap_bytes,
            machine.machine_bytes,
        );
        machine.limits.max_heap_bytes = machine.heap_bytes;
        assert!(matches!(
            repeat(&mut machine, source, &[Value::int32(2)], false),
            Err(EvalFailure::Runtime(
                RuntimeErrorKind::HeapByteLimitExceeded { .. }
            ))
        ));
        assert_eq!(
            (
                machine.heap.len(),
                machine.heap_bytes,
                machine.machine_bytes
            ),
            before
        );
    }
}
