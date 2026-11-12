use std::collections::BTreeMap;

use bamts_bytecode::{EcmaString, EcmaStringBuilder};
use bamts_native::{Decoded, Value};

use super::intl::{TargetCase, compare_with_collator, transform_case};
use super::{
    allocate_array, allocate_string, define_data, install_constructor_function, install_function,
    range_error, type_error, uri_error, value_number, with_roots,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, IterationKind, Machine, PropertyKey};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
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
    heap: &mut [HeapEntry],
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
    Ok(super::array_es2023::integer_or_infinity(machine, value)? as isize)
}
/// Rejects a search string that is a RegExp, for the methods that take text only.
fn require_not_regexp<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    operation: &'static str,
) -> Result<(), EvalFailure> {
    if super::string_edge::is_regexp(machine, value)? {
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
fn raw<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let template = args.first().copied().unwrap_or(Value::UNDEFINED);
    let raw = machine.get_named_property(template, "raw")?;
    let values = machine
        .array_elements(raw)?
        .ok_or_else(|| type_error("String.raw requires template.raw"))?;
    let mut out = EcmaStringBuilder::new();
    for (i, value) in values.iter().enumerate() {
        append(&mut out, &machine.coerce_string_observable(*value)?);
        if i + 1 < values.len() {
            append(
                &mut out,
                &machine.coerce_string_observable(
                    args.get(i + 1).copied().unwrap_or(Value::UNDEFINED),
                )?,
            );
        }
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
fn at<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let string = text(machine, this)?;
    let mut index = integer(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    if index < 0 {
        index += string.len_units() as isize;
    }
    let Some(unit) = (index >= 0)
        .then(|| string.unit_at(index as usize))
        .flatten()
    else {
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    };
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        EcmaString::from_units(&[unit]),
    )?))
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
        Some(template) => super::regexp_protocol::get_substitution(
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

fn trim_range(text: &EcmaString, trim_start: bool, trim_end: bool) -> EcmaString {
    let units = text.as_units();
    let start = if trim_start {
        units
            .iter()
            .position(|unit| !is_js_whitespace(*unit))
            .unwrap_or(units.len())
    } else {
        0
    };
    let end = if trim_end {
        units
            .iter()
            .rposition(|unit| !is_js_whitespace(*unit))
            .map_or(start, |index| index + 1)
    } else {
        units.len()
    };
    text.slice_units(start..end.max(start))
        .expect("trim bounds were derived from the source string")
}

macro_rules! trim_fn {
    ($name:ident, $start:literal, $end:literal) => {
        fn $name<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _: &[Value],
            _: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let string = text(machine, this)?;
            Ok(BuiltinOutcome::Value(allocate_string(
                machine,
                trim_range(&string, $start, $end),
            )?))
        }
    };
}
trim_fn!(trim, true, true);
trim_fn!(trim_start, true, false);
trim_fn!(trim_end, false, true);
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
fn pad<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    start: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let string = text(machine, this)?;
    let target = super::array_es2023::integer_or_infinity(
        machine,
        args.first().copied().unwrap_or(Value::UNDEFINED),
    )?
    .max(0.0);
    if target <= string.len_units() as f64 {
        return Ok(BuiltinOutcome::Value(allocate_string(machine, string)?));
    }
    let filler = if args.len() < 2 || args[1] == Value::UNDEFINED {
        EcmaString::encode(" ")
    } else {
        machine.coerce_string_observable(args[1])?
    };
    if filler.is_empty() {
        return Ok(BuiltinOutcome::Value(allocate_string(machine, string)?));
    }
    if target > (machine.limits.max_heap_bytes / std::mem::size_of::<u16>()) as f64 {
        return Err(EvalFailure::Runtime(
            crate::RuntimeErrorKind::HeapByteLimitExceeded {
                limit: machine.limits.max_heap_bytes,
            },
        ));
    }
    let target = target as usize;
    preflight_string_allocation(machine, target)?;
    let needed = target - string.len_units();
    let mut output = EcmaStringBuilder::with_capacity(target);
    if start {
        for unit in filler.as_units().iter().copied().cycle().take(needed) {
            output.push_unit(unit);
        }
        append(&mut output, &string);
    } else {
        append(&mut output, &string);
        for unit in filler.as_units().iter().copied().cycle().take(needed) {
            output.push_unit(unit);
        }
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}
fn preflight_string_allocation<H: Host>(
    machine: &Machine<'_, H>,
    units: usize,
) -> Result<(), EvalFailure> {
    let bytes = units
        .checked_mul(std::mem::size_of::<u16>())
        .ok_or(EvalFailure::Runtime(
            crate::RuntimeErrorKind::HeapByteLimitExceeded {
                limit: machine.limits.max_heap_bytes,
            },
        ))?;
    machine
        .ensure_allocation_capacity(1, bytes)
        .map_err(EvalFailure::Runtime)
}
fn pad_start<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    pad(machine, this, args, true)
}
fn pad_end<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    pad(machine, this, args, false)
}
fn repeat<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let string = text(machine, this)?;
    let count = super::array_es2023::integer_or_infinity(
        machine,
        args.first().copied().unwrap_or(Value::UNDEFINED),
    )?;
    if count < 0.0 || count.is_infinite() {
        return Err(range_error("Invalid count value"));
    }
    if string.is_empty() {
        return Ok(BuiltinOutcome::Value(allocate_string(machine, string)?));
    }
    if count > (machine.limits.max_heap_bytes / std::mem::size_of::<u16>()) as f64 {
        return Err(EvalFailure::Runtime(
            crate::RuntimeErrorKind::HeapByteLimitExceeded {
                limit: machine.limits.max_heap_bytes,
            },
        ));
    }
    let count = count as usize;
    let output_units = string
        .len_units()
        .checked_mul(count)
        .ok_or(EvalFailure::Runtime(
            crate::RuntimeErrorKind::HeapByteLimitExceeded {
                limit: machine.limits.max_heap_bytes,
            },
        ))?;
    preflight_string_allocation(machine, output_units)?;
    let mut output = EcmaStringBuilder::with_capacity(output_units);
    for _ in 0..count {
        append(&mut output, &string);
    }
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
    let mut output = EcmaStringBuilder::new();
    append(&mut output, &text(machine, this)?);
    for argument in args {
        append(&mut output, &machine.coerce_string_observable(*argument)?);
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}
fn normalize<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if let Some(form) = args.first().filter(|value| **value != Value::UNDEFINED) {
        let form = machine.coerce_string_observable(*form)?;
        if !form.eq_ascii("NFC")
            && !form.eq_ascii("NFD")
            && !form.eq_ascii("NFKC")
            && !form.eq_ascii("NFKD")
        {
            return Err(range_error(
                "The normalization form should be one of NFC, NFD, NFKC, NFKD",
            ));
        }
    }
    let string = text(machine, this)?;
    Ok(BuiltinOutcome::Value(allocate_string(machine, string)?))
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
    if machine.is_object(pattern) && super::string_edge::is_regexp(machine, pattern)? {
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
    fn array_strings(machine: &Machine<'_, TestHost>, array: Value) -> Vec<String> {
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
            array_strings(&machine, result),
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
            array_strings(&machine, result),
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
            array_strings(&machine, result),
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
        let pieces = array_strings(&machine, result);
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
        assert_eq!(array_strings(&machine, result), vec!["a", "b", "c"],);
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
