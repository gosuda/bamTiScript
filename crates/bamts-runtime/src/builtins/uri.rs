use std::collections::BTreeMap;

use bamts_bytecode::{EcmaString, EcmaStringBuilder};
use bamts_native::Value;

use super::{allocate_string, install_function, uri_error};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine};

const URI_RESERVED: &[u8] = b";/?:@&=+$,#";
const URI_UNESCAPED: &[u8] = b"-_.!~*'()";
const ESCAPE_UNESCAPED: &[u8] = b"@*_+-./";
const HEX: &[u8; 16] = b"0123456789ABCDEF";

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    for (name, handler) in [
        ("encodeURI", encode_uri::<H> as BuiltinHandler<H>),
        ("encodeURIComponent", encode_uri_component::<H>),
        ("decodeURI", decode_uri::<H>),
        ("decodeURIComponent", decode_uri_component::<H>),
        ("escape", escape::<H>),
        ("unescape", unescape::<H>),
    ] {
        let function = install_function(heap, atoms, builtins, name, 1, handler);
        globals.insert(EcmaString::encode(name), function);
    }
}

fn is_ascii_alphanumeric(unit: u16) -> bool {
    unit <= u16::from(u8::MAX) && (unit as u8).is_ascii_alphanumeric()
}

fn component_unescaped(unit: u16) -> bool {
    is_ascii_alphanumeric(unit)
        || (unit <= u16::from(u8::MAX) && URI_UNESCAPED.contains(&(unit as u8)))
}

fn encode_unescaped(unit: u16, preserve_reserved: bool) -> bool {
    component_unescaped(unit)
        || (preserve_reserved && unit <= u16::from(u8::MAX) && URI_RESERVED.contains(&(unit as u8)))
}

fn push_percent_octet(output: &mut EcmaStringBuilder, octet: u8) {
    output.push_unit(u16::from(b'%'));
    output.push_unit(u16::from(HEX[usize::from(octet >> 4)]));
    output.push_unit(u16::from(HEX[usize::from(octet & 0x0f)]));
}

fn push_utf8_percent_encoded(output: &mut EcmaStringBuilder, scalar: u32) {
    if scalar <= 0x7f {
        push_percent_octet(output, scalar as u8);
    } else if scalar <= 0x7ff {
        push_percent_octet(output, 0xc0 | ((scalar >> 6) as u8));
        push_percent_octet(output, 0x80 | ((scalar & 0x3f) as u8));
    } else if scalar <= 0xffff {
        push_percent_octet(output, 0xe0 | ((scalar >> 12) as u8));
        push_percent_octet(output, 0x80 | (((scalar >> 6) & 0x3f) as u8));
        push_percent_octet(output, 0x80 | ((scalar & 0x3f) as u8));
    } else {
        push_percent_octet(output, 0xf0 | ((scalar >> 18) as u8));
        push_percent_octet(output, 0x80 | (((scalar >> 12) & 0x3f) as u8));
        push_percent_octet(output, 0x80 | (((scalar >> 6) & 0x3f) as u8));
        push_percent_octet(output, 0x80 | ((scalar & 0x3f) as u8));
    }
}

fn encode(source: &EcmaString, preserve_reserved: bool) -> Result<EcmaString, ()> {
    let units = source.as_units();
    let mut output = EcmaStringBuilder::with_capacity(units.len());
    let mut offset = 0;
    while offset < units.len() {
        let first = units[offset];
        if encode_unescaped(first, preserve_reserved) {
            output.push_unit(first);
            offset += 1;
            continue;
        }
        let scalar = match first {
            0xd800..=0xdbff => {
                let Some(&second @ 0xdc00..=0xdfff) = units.get(offset + 1) else {
                    return Err(());
                };
                offset += 2;
                0x1_0000 + ((u32::from(first) - 0xd800) << 10) + (u32::from(second) - 0xdc00)
            }
            0xdc00..=0xdfff => return Err(()),
            _ => {
                offset += 1;
                u32::from(first)
            }
        };
        push_utf8_percent_encoded(&mut output, scalar);
    }
    Ok(output.finish())
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

fn utf8_sequence_width(first: u8) -> Option<usize> {
    match first {
        0x00..=0x7f => Some(1),
        0xc2..=0xdf => Some(2),
        0xe0..=0xef => Some(3),
        0xf0..=0xf4 => Some(4),
        _ => None,
    }
}

fn decode_percent_scalar(units: &[u16], offset: usize) -> Option<(u32, usize)> {
    let first = percent_octet(units, offset)?;
    let width = utf8_sequence_width(first)?;
    let mut scalar = if width == 1 {
        u32::from(first)
    } else {
        u32::from(first & (0x7f >> width))
    };
    for index in 1..width {
        let octet = percent_octet(units, offset + index * 3)?;
        if !(0x80..=0xbf).contains(&octet) {
            return None;
        }
        scalar = (scalar << 6) | u32::from(octet & 0x3f);
    }
    let minimum = match width {
        1 => 0,
        2 => 0x80,
        3 => 0x800,
        4 => 0x1_0000,
        _ => unreachable!(),
    };
    if scalar < minimum || (0xd800..=0xdfff).contains(&scalar) || scalar > 0x10_ffff {
        return None;
    }
    Some((scalar, width * 3))
}

fn push_scalar(output: &mut EcmaStringBuilder, scalar: u32) {
    if scalar <= 0xffff {
        output.push_unit(scalar as u16);
    } else {
        let supplementary = scalar - 0x1_0000;
        output.push_unit(0xd800 | ((supplementary >> 10) as u16));
        output.push_unit(0xdc00 | ((supplementary & 0x3ff) as u16));
    }
}

fn decode(source: &EcmaString, preserve_reserved: bool) -> Result<EcmaString, ()> {
    let units = source.as_units();
    let mut output = EcmaStringBuilder::with_capacity(units.len());
    let mut offset = 0;
    while offset < units.len() {
        if units[offset] != u16::from(b'%') {
            output.push_unit(units[offset]);
            offset += 1;
            continue;
        }
        let Some((scalar, consumed)) = decode_percent_scalar(units, offset) else {
            return Err(());
        };
        if preserve_reserved
            && scalar <= u32::from(u8::MAX)
            && URI_RESERVED.contains(&(scalar as u8))
        {
            for &unit in &units[offset..offset + consumed] {
                output.push_unit(unit);
            }
        } else {
            push_scalar(&mut output, scalar);
        }
        offset += consumed;
    }
    Ok(output.finish())
}

fn encode_argument<H: Host>(
    machine: &mut Machine<'_, H>,
    args: &[Value],
    preserve_reserved: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source =
        machine.coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let encoded = encode(&source, preserve_reserved).map_err(|()| uri_error("URI malformed"))?;
    Ok(BuiltinOutcome::Value(allocate_string(machine, encoded)?))
}

fn decode_argument<H: Host>(
    machine: &mut Machine<'_, H>,
    args: &[Value],
    preserve_reserved: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source =
        machine.coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let decoded = decode(&source, preserve_reserved).map_err(|()| uri_error("URI malformed"))?;
    Ok(BuiltinOutcome::Value(allocate_string(machine, decoded)?))
}

fn encode_uri<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    encode_argument(machine, args, true)
}

fn encode_uri_component<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    encode_argument(machine, args, false)
}

fn decode_uri<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    decode_argument(machine, args, true)
}

fn decode_uri_component<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    decode_argument(machine, args, false)
}

fn escape_units(source: &EcmaString) -> EcmaString {
    let mut output = EcmaStringBuilder::with_capacity(source.len_units());
    for &unit in source.as_units() {
        if is_ascii_alphanumeric(unit)
            || (unit <= u16::from(u8::MAX) && ESCAPE_UNESCAPED.contains(&(unit as u8)))
        {
            output.push_unit(unit);
        } else if unit <= u16::from(u8::MAX) {
            push_percent_octet(&mut output, unit as u8);
        } else {
            output.push_utf8("%u");
            output.push_unit(u16::from(HEX[usize::from((unit >> 12) & 0x0f)]));
            output.push_unit(u16::from(HEX[usize::from((unit >> 8) & 0x0f)]));
            output.push_unit(u16::from(HEX[usize::from((unit >> 4) & 0x0f)]));
            output.push_unit(u16::from(HEX[usize::from(unit & 0x0f)]));
        }
    }
    output.finish()
}

fn unescape_units(source: &EcmaString) -> EcmaString {
    let units = source.as_units();
    let mut output = EcmaStringBuilder::with_capacity(units.len());
    let mut offset = 0;
    while offset < units.len() {
        if units[offset] == u16::from(b'%') && units.get(offset + 1) == Some(&u16::from(b'u')) {
            let decoded = (0..4).try_fold(0_u16, |value, index| {
                Some((value << 4) | u16::from(hex_value(*units.get(offset + index + 2)?)?))
            });
            if let Some(unit) = decoded {
                output.push_unit(unit);
                offset += 6;
                continue;
            }
        }
        if let Some(octet) = percent_octet(units, offset) {
            output.push_unit(u16::from(octet));
            offset += 3;
        } else {
            output.push_unit(units[offset]);
            offset += 1;
        }
    }
    output.finish()
}

fn escape<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source =
        machine.coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        escape_units(&source),
    )?))
}

fn unescape<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source =
        machine.coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        unescape_units(&source),
    )?))
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, Property, PropertyKey, ThrowOrigin};

    fn text(value: &str) -> EcmaString {
        EcmaString::encode(value)
    }

    fn assert_text(actual: EcmaString, expected: &str) {
        assert_eq!(actual.as_units(), EcmaString::encode(expected).as_units());
    }

    #[test]
    fn encode_handles_reserved_sets_and_multibyte_scalars() {
        assert_text(
            encode(&text(";/?:@&=+$,# []é😀"), true).unwrap(),
            ";/?:@&=+$,#%20%5B%5D%C3%A9%F0%9F%98%80",
        );
        assert_text(
            encode(&text(";/?:@&=+$,#-_.!~*'()"), false).unwrap(),
            "%3B%2F%3F%3A%40%26%3D%2B%24%2C%23-_.!~*'()",
        );
    }
    #[test]
    fn encode_and_decode_cover_every_utf8_width_boundary() {
        let scalars = EcmaString::from_units(&[
            0x007f, 0x0080, 0x07ff, 0x0800, 0xffff, 0xd800, 0xdc00, 0xdbff, 0xdfff,
        ]);
        let encoded = encode(&scalars, false).unwrap();
        let decoded = decode(&encoded, false).unwrap();
        assert_text(
            encoded,
            "%7F%C2%80%DF%BF%E0%A0%80%EF%BF%BF%F0%90%80%80%F4%8F%BF%BF",
        );
        assert_eq!(decoded.as_units(), scalars.as_units());
    }

    #[test]
    fn decode_preserves_uri_reserved_spelling_but_components_decode_it() {
        let source = text("%2f%2F%3f%23%25%C3%A9%f0%9f%98%80");
        assert_text(decode(&source, true).unwrap(), "%2f%2F%3f%23%é😀");
        assert_text(decode(&source, false).unwrap(), "//?#%é😀");
    }

    #[test]
    fn decode_rejects_malformed_truncated_and_non_scalar_utf8() {
        for malformed in [
            "%",
            "%2",
            "%GG",
            "%80",
            "%C0%AF",
            "%C1%BF",
            "%C2",
            "%C2%20",
            "%E0%80%80",
            "%E2%82",
            "%E2%28%A1",
            "%E2%82%20",
            "%ED%A0%80",
            "%F0%80%80%80",
            "%F0%9F%98",
            "%F0%90%80%20",
            "%F4%90%80%80",
            "%F5%80%80%80",
        ] {
            assert!(
                decode(&text(malformed), false).is_err(),
                "accepted {malformed}"
            );
        }
    }

    #[test]
    fn encode_rejects_each_lone_surrogate_shape() {
        for units in [&[0xd800][..], &[0xdc00][..], &[0xd800, 0x0041][..]] {
            assert!(encode(&EcmaString::from_units(units), false).is_err());
        }
        assert_text(
            encode(&EcmaString::from_units(&[0xd83d, 0xde00]), false).unwrap(),
            "%F0%9F%98%80",
        );
    }

    #[test]
    fn encode_reports_lone_surrogates_as_uri_error() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let malformed = machine
            .allocate(HeapEntry::String(EcmaString::from_units(&[0xd800])))
            .unwrap();
        assert!(matches!(
            encode_uri(&mut machine, Value::UNDEFINED, &[malformed], false),
            Err(EvalFailure::Throw(ThrowOrigin::UriError {
                operation: "URI malformed"
            }))
        ));
    }
    #[test]
    fn decode_reports_malformed_utf8_as_uri_error() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let malformed = machine
            .allocate(HeapEntry::String(text("%ED%A0%80")))
            .unwrap();
        assert!(matches!(
            decode_uri_component(&mut machine, Value::UNDEFINED, &[malformed], false),
            Err(EvalFailure::Throw(ThrowOrigin::UriError {
                operation: "URI malformed"
            }))
        ));
    }

    #[test]
    fn annex_b_escape_operates_on_utf16_code_units() {
        assert_text(
            escape_units(&EcmaString::from_units(&[
                b'A' as u16,
                b'@' as u16,
                0x00ff,
                0xd83d,
                0xde00,
            ])),
            "A@%FF%uD83D%uDE00",
        );
        assert_eq!(
            unescape_units(&text("%41%u00ff%uD83D%uDE00%uZZZZ%4G%U0041")).as_units(),
            &[
                0x0041,
                0x00ff,
                0xd83d,
                0xde00,
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
                b'U' as u16,
                b'0' as u16,
                b'0' as u16,
                b'4' as u16,
                b'1' as u16,
            ],
        );
    }

    fn coercion_result(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let calls = machine.get_named_property(this, "calls")?;
        let count = match calls.decode() {
            Some(bamts_native::Decoded::Int32(count)) => count,
            _ => 0,
        };
        machine.set_data_property(this, "calls", Value::int32(count + 1))?;
        let result = machine
            .allocate(HeapEntry::String(EcmaString::encode("%C0%AF")))
            .map_err(EvalFailure::Runtime)?;
        Ok(BuiltinOutcome::Value(result))
    }

    fn native(machine: &mut Machine<'_, TestHost>, handler: BuiltinHandler<TestHost>) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "coercion hook",
            length: 0,
            handler,
        });
        native_function(
            &mut machine.heap,
            &mut machine.atoms,
            id,
            "coercion hook",
            0,
        )
    }

    #[test]
    fn uri_coerces_once_before_reporting_malformed_input() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let object = ordinary_object(&mut machine);
        machine
            .set_data_property(object, "calls", Value::int32(0))
            .unwrap();
        let hook = native(&mut machine, coercion_result);
        machine.set_data_property(object, "toString", hook).unwrap();

        assert!(matches!(
            decode_uri_component(&mut machine, Value::UNDEFINED, &[object], false),
            Err(EvalFailure::Throw(ThrowOrigin::UriError {
                operation: "URI malformed"
            }))
        ));
        assert_eq!(
            machine
                .get_named_property(object, "calls")
                .unwrap()
                .decode(),
            Some(bamts_native::Decoded::Int32(1))
        );
    }

    #[test]
    fn installed_globals_have_standard_function_contract() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        for name in [
            "encodeURI",
            "encodeURIComponent",
            "decodeURI",
            "decodeURIComponent",
            "escape",
            "unescape",
        ] {
            let function = machine
                .intrinsics
                .global(name)
                .expect("URI global installs");
            assert!(machine.is_callable(function).unwrap());
            let name_key = PropertyKey::Named(machine.intern_str("name"));
            assert!(matches!(
                machine.own_descriptor(function, &name_key).unwrap(),
                Some(Property::Data { value, writable: false, enumerable: false, configurable: true })
                    if machine.string_value(value).is_some_and(|text| text.eq_ascii(name))
            ));
            let length_key = PropertyKey::Named(machine.intern_str("length"));
            assert!(matches!(
                machine.own_descriptor(function, &length_key).unwrap(),
                Some(Property::Data { value, writable: false, enumerable: false, configurable: true })
                    if value.decode() == Some(bamts_native::Decoded::Int32(1))
            ));
            assert!(
                machine
                    .inherits_from_prototype(
                        function,
                        machine.intrinsics.builtins.function_prototype()
                    )
                    .unwrap()
            );
        }
    }
}
