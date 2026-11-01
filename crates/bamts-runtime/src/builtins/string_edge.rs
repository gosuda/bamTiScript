use std::collections::BTreeMap;

use bamts_bytecode::{EcmaString, EcmaStringBuilder};
use bamts_native::{Decoded, Value};
use unicode_normalization::UnicodeNormalization;

use super::{
    allocate_string, builtin_property, heap_index, install_function, range_error, type_error,
    value_number,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, PropertyKey, RuntimeErrorKind};

const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;

/// Installs the modern and edge-sensitive String operations after the core
/// String constructor and prototype have been created.
pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let constructor = *globals
        .iter()
        .find_map(|(name, value)| name.eq_ascii("String").then_some(value))
        .expect("String core builtin must be installed first");
    let prototype = builtins.string_prototype();

    for (name, length, handler) in [
        (
            "fromCodePoint",
            1,
            from_code_point::<H> as BuiltinHandler<H>,
        ),
        ("raw", 1, raw::<H>),
    ] {
        let function = install_function(heap, builtins, name, length, handler);
        let HeapEntry::NativeFunction { properties, .. } = &mut heap[heap_index(constructor)]
        else {
            panic!("String constructor must be native")
        };
        properties.insert(
            PropertyKey::Named(EcmaString::encode(name)),
            builtin_property(function),
        );
    }

    for (name, length, handler) in [
        ("isWellFormed", 0, is_well_formed::<H> as BuiltinHandler<H>),
        ("toWellFormed", 0, to_well_formed::<H>),
        ("at", 1, at::<H>),
        ("replaceAll", 2, replace_all::<H>),
        ("normalize", 0, normalize::<H>),
        ("padStart", 1, pad_start::<H>),
        ("padEnd", 1, pad_end::<H>),
        ("trim", 0, trim::<H>),
        ("trimStart", 0, trim_start::<H>),
        ("trimEnd", 0, trim_end::<H>),
        ("repeat", 1, repeat::<H>),
    ] {
        let function = install_function(heap, builtins, name, length, handler);
        super::define_data(heap, prototype, name, function);
    }
}

fn require_coercible(value: Value) -> Result<(), EvalFailure> {
    if matches!(value.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        Err(type_error("String method called on null or undefined"))
    } else {
        Ok(())
    }
}

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

fn integer_or_infinity<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<f64, EvalFailure> {
    let value = number(machine, value)?;
    Ok(if value.is_nan() || value == 0.0 {
        0.0
    } else {
        value.trunc()
    })
}

fn length_of_array_like<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<usize, EvalFailure> {
    require_coercible(value)?;
    let length = machine.get_named_property(value, "length")?;
    let length = integer_or_infinity(machine, length)?.clamp(0.0, MAX_SAFE_INTEGER);
    Ok(length as usize)
}

fn append(builder: &mut EcmaStringBuilder, text: &EcmaString) {
    for &unit in text.as_units() {
        builder.push_unit(unit);
    }
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
        let key = PropertyKey::Named(EcmaString::encode(&index.to_string()));
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
    let relative = integer_or_infinity(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
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

fn search_units(haystack: &[u16], needle: &[u16], start: usize) -> Option<usize> {
    if needle.is_empty() {
        return Some(start.min(haystack.len()));
    }
    haystack
        .get(start..)?
        .windows(needle.len())
        .position(|window| window == needle)
        .map(|offset| start + offset)
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

    if !matches!(search.decode(), Some(Decoded::Undefined | Decoded::Null)) {
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
    let target = integer_or_infinity(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?
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
    let count = integer_or_infinity(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    if count < 0.0 || count == f64::INFINITY {
        return Err(range_error("Invalid count value"));
    }
    if source.is_empty() || count == 0.0 {
        return Ok(BuiltinOutcome::Value(allocate_string(machine, source)?));
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
mod tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, Property, PropertyMap, ThrowOrigin};

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

    fn result_text(machine: &Machine<'_, TestHost>, outcome: BuiltinOutcome) -> Vec<u16> {
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
            result_text(&machine, repaired),
            [b'a' as u16, 0xD800, 0xDC00, 0xFFFD]
        );
    }

    #[test]
    fn at_indexes_utf16_units_from_either_end() {
        test_machine!(program, host, machine);
        let source = string(&mut machine, &[0xD83D, 0xDE00, b'x' as u16]);
        let forward = at(&mut machine, source, &[Value::int32(1)], false).unwrap();
        assert_eq!(result_text(&machine, forward), [0xDE00]);
        let backward = at(&mut machine, source, &[crate::number_value(-1.0)], false).unwrap();
        assert_eq!(result_text(&machine, backward), [b'x' as u16]);
    }

    #[test]
    fn empty_replace_pattern_visits_every_utf16_boundary() {
        test_machine!(program, host, machine);
        let source = string(&mut machine, &[b'a' as u16, 0xD800]);
        let empty = string(&mut machine, &[]);
        let dash = string(&mut machine, &[b'-' as u16]);
        let replaced = replace_all(&mut machine, source, &[empty, dash], false).unwrap();
        assert_eq!(
            result_text(&machine, replaced),
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
        let hook = native_function(&mut machine.heap, id, "replace hook", 2);
        let symbol = machine.intrinsics.builtins.symbol_replace();
        let key = machine.to_property_key(symbol).unwrap();
        machine.set_data_property_key(search, key, hook).unwrap();
        let receiver = ordinary_object(&mut machine);
        let coercion_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "throwing toString",
            length: 0,
            handler: throwing_to_string::<TestHost>,
        });
        let coercion = native_function(&mut machine.heap, coercion_id, "throwing toString", 0);
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
        assert_eq!(result_text(&machine, normalized), [0x00E9, 0xD800]);
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
                Some(unit) => assert_eq!(result_text(&machine, outcome), [unit]),
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
        assert_eq!(result_text(&machine, nan), [0xD83D]);
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
            result_text(&machine, replaced),
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
        let replacer = native_function(&mut machine.heap, id, "literal dollar replacer", 3);
        let replaced = replace_all(&mut machine, source, &[needle, replacer], false).unwrap();
        assert_eq!(
            result_text(&machine, replaced),
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
        let hook = native_function(&mut machine.heap, id, "replace hook", 2);
        let match_symbol = machine.intrinsics.builtins.symbol_match();
        let match_key = machine.to_property_key(match_symbol).unwrap();
        let replace_symbol = machine.intrinsics.builtins.symbol_replace();
        let replace_key = machine.to_property_key(replace_symbol).unwrap();
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
        let iterator_key = machine.to_property_key(iterator_symbol).unwrap();
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
        assert_eq!(result_text(&machine, encoded), [0xD83D, 0xDE00]);
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
            result_text(&machine, raw_result),
            [b'a' as u16, b'x' as u16, b'b' as u16]
        );

        let source = string(&mut machine, &[0x00A0, b'x' as u16, 0xFEFF]);
        let trimmed = trim(&mut machine, source, &[], false).unwrap();
        assert_eq!(result_text(&machine, trimmed), [b'x' as u16]);
        let fill = string(&mut machine, &[b'a' as u16, b'b' as u16]);
        let x = string(&mut machine, &[b'x' as u16]);
        let padded = pad_end(&mut machine, x, &[Value::int32(4), fill], false).unwrap();
        assert_eq!(
            result_text(&machine, padded),
            [b'x' as u16, b'a' as u16, b'b' as u16, b'a' as u16]
        );
        let unused_filler = ordinary_object(&mut machine);
        let coercion_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "unused filler toString",
            length: 0,
            handler: throwing_to_string::<TestHost>,
        });
        let coercion = native_function(&mut machine.heap, coercion_id, "unused filler toString", 0);
        machine
            .set_data_property(unused_filler, "toString", coercion)
            .unwrap();

        let unchanged = pad_end(&mut machine, x, &[Value::int32(1), unused_filler], false).unwrap();
        assert_eq!(result_text(&machine, unchanged), [b'x' as u16]);
        let empty = string(&mut machine, &[]);
        let huge_empty =
            repeat(&mut machine, empty, &[crate::number_value(f64::MAX)], false).unwrap();
        assert!(result_text(&machine, huge_empty).is_empty());
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
                let descriptor = machine
                    .own_descriptor(function, &PropertyKey::Named(EcmaString::encode(property)))
                    .unwrap();
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
            assert!(matches!(
                machine
                    .own_descriptor(owner, &PropertyKey::Named(EcmaString::encode(name)))
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
