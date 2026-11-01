use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, Value};

use super::{
    allocate_string, define_data, install_constructor_function, install_function, number_format,
    range_error, to_integer_or_infinity, type_error, value_number,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, PropertyKey};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = builtins.number_prototype();
    let constructor = install_constructor_function(heap, builtins, "Number", 1, constructor::<H>);
    builtins.set_constructor_prototype(heap, constructor, prototype);
    globals.insert(EcmaString::encode("Number"), constructor);
    for (name, length, handler) in [
        ("isInteger", 1, is_integer::<H> as BuiltinHandler<H>),
        ("isSafeInteger", 1, is_safe_integer::<H>),
        ("isFinite", 1, is_finite::<H>),
        ("isNaN", 1, is_nan::<H>),
    ] {
        let f = install_function(heap, builtins, name, length, handler);
        define_static(heap, constructor, name, f)
    }
    for (name, value) in [
        ("MAX_SAFE_INTEGER", 9007199254740991.0),
        ("MIN_SAFE_INTEGER", -9007199254740991.0),
        ("EPSILON", f64::EPSILON),
        ("MAX_VALUE", f64::MAX),
        ("MIN_VALUE", f64::from_bits(1)),
        ("POSITIVE_INFINITY", f64::INFINITY),
        ("NEGATIVE_INFINITY", f64::NEG_INFINITY),
        ("NaN", f64::NAN),
    ] {
        let HeapEntry::NativeFunction { properties, .. } =
            &mut heap[super::heap_index(constructor)]
        else {
            panic!("Number constructor must be native")
        };
        properties.insert(
            PropertyKey::Named(EcmaString::encode(name)),
            crate::Property::Data {
                value: crate::number_value(value),
                writable: false,
                enumerable: false,
                configurable: false,
            },
        );
    }
    for (name, length, handler) in [
        ("toString", 1, to_string::<H> as BuiltinHandler<H>),
        ("toLocaleString", 0, to_locale_string::<H>),
        ("toFixed", 1, to_fixed::<H>),
        ("toExponential", 1, to_exponential::<H>),
        ("toPrecision", 1, to_precision::<H>),
        ("valueOf", 0, value_of::<H>),
    ] {
        let f = install_function(heap, builtins, name, length, handler);
        define_data(heap, prototype, name, f)
    }
}
/// `Number.parseFloat` and `Number.parseInt` are the global functions themselves.
pub(super) fn share_global_parsers(heap: &mut [HeapEntry], globals: &BTreeMap<EcmaString, Value>) {
    let constructor = globals[&EcmaString::encode("Number")];
    for name in ["parseFloat", "parseInt"] {
        define_static(heap, constructor, name, globals[&EcmaString::encode(name)]);
    }
}
fn define_static(heap: &mut [HeapEntry], constructor: Value, name: &str, value: Value) {
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[super::heap_index(constructor)]
    else {
        panic!("Number constructor must be native")
    };
    properties.insert(
        PropertyKey::Named(EcmaString::encode(name)),
        super::builtin_property(value),
    );
}
fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = if let Some(value) = args.first() {
        let primitive = machine.coerce_primitive_observable(*value, false)?;
        match super::bigint::bigint_to_number(machine, primitive)? {
            Some(number) => number,
            None => machine.coerce_number_observable(primitive)?,
        }
    } else {
        Value::int32(0)
    };
    if constructing {
        let prototype = machine.intrinsics.number_prototype;
        super::wrap_for_new_target(machine, value, prototype)
    } else {
        Ok(BuiltinOutcome::Value(value))
    }
}
fn primitive_number<H: Host>(
    machine: &Machine<'_, H>,
    this: Value,
    op: &'static str,
) -> Result<f64, EvalFailure> {
    let value = machine.unbox_primitive_or_self(this)?;
    match value.decode() {
        Some(Decoded::Number(n)) => Ok(n),
        Some(Decoded::Int32(n)) => Ok(f64::from(n as i32)),
        _ => Err(type_error(op)),
    }
}
fn numeric(value: Value) -> Option<f64> {
    match value.decode() {
        Some(Decoded::Number(n)) => Some(n),
        Some(Decoded::Int32(n)) => Some(f64::from(n as i32)),
        _ => None,
    }
}
fn is_integer<H: Host>(
    _: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let result = args
        .first()
        .and_then(|v| numeric(*v))
        .is_some_and(|n| n.is_finite() && n.fract() == 0.0);
    Ok(BuiltinOutcome::Value(Value::boolean(result)))
}
fn is_safe_integer<H: Host>(
    _: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let result = args
        .first()
        .and_then(|v| numeric(*v))
        .is_some_and(|n| n.is_finite() && n.fract() == 0.0 && n.abs() <= 9007199254740991.0);
    Ok(BuiltinOutcome::Value(Value::boolean(result)))
}
fn is_finite<H: Host>(
    _: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(Value::boolean(
        args.first()
            .and_then(|v| numeric(*v))
            .is_some_and(f64::is_finite),
    )))
}
fn is_nan<H: Host>(
    _: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(Value::boolean(
        args.first()
            .and_then(|v| numeric(*v))
            .is_some_and(f64::is_nan),
    )))
}
pub(super) fn parse_float<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let text = machine
        .coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?
        .to_utf8_lossy();
    Ok(BuiltinOutcome::Value(crate::number_value(
        number_format::parse_float(&text),
    )))
}
/// ECMAScript ToInt32 applied to the parseInt radix argument: wraps the
/// number modulo 2^32 into the signed 32-bit range. `value_number(...) as
/// i32` saturates in Rust, so radices like 2^32 and 2^32 + 10 must be
/// converted here instead of cast.
fn to_int32_radix(number: f64) -> i32 {
    if !number.is_finite() || number == 0.0 {
        0
    } else {
        number.trunc().rem_euclid(4_294_967_296.0) as u32 as i32
    }
}
pub(super) fn parse_int<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let text = machine
        .coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?
        .to_utf8_lossy();
    let requested = to_int32_radix(value_number(
        machine.coerce_number_observable(args.get(1).copied().unwrap_or(Value::UNDEFINED))?,
    ));
    Ok(BuiltinOutcome::Value(crate::number_value(
        number_format::parse_int(&text, requested),
    )))
}
pub(super) fn global_is_nan<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let n = value_number(
        machine.coerce_number_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?,
    );
    Ok(BuiltinOutcome::Value(Value::boolean(n.is_nan())))
}
pub(super) fn global_is_finite<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let n = value_number(
        machine.coerce_number_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?,
    );
    Ok(BuiltinOutcome::Value(Value::boolean(n.is_finite())))
}
/// `Number.prototype.toLocaleString` without a locale: the ECMAScript form.
fn to_locale_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let n = primitive_number(
        machine,
        this,
        "Number.prototype.toLocaleString requires that 'this' be a Number",
    )?;
    let text =
        number_format::to_string_radix(n, 10.0).map_err(|error| range_error(error.message()))?;
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        EcmaString::encode(&text),
    )?))
}
fn to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let n = primitive_number(
        machine,
        this,
        "Number.prototype.toString requires that 'this' be a Number",
    )?;
    let radix = match args.first().copied() {
        None | Some(Value::UNDEFINED) => 10.0,
        Some(value) => to_integer_or_infinity(machine, value)?,
    };
    let text =
        number_format::to_string_radix(n, radix).map_err(|error| range_error(error.message()))?;
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        EcmaString::encode(&text),
    )?))
}
fn to_fixed<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let n = primitive_number(
        machine,
        this,
        "Number.prototype.toFixed requires that 'this' be a Number",
    )?;
    let digits =
        to_integer_or_infinity(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let text = number_format::to_fixed(n, digits).map_err(|error| range_error(error.message()))?;
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        EcmaString::encode(&text),
    )?))
}
fn to_exponential<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let n = primitive_number(
        machine,
        this,
        "Number.prototype.toExponential requires that 'this' be a Number",
    )?;
    let digits = match args.first().copied() {
        None | Some(Value::UNDEFINED) => None,
        Some(value) => Some(to_integer_or_infinity(machine, value)?),
    };
    let text =
        number_format::to_exponential(n, digits).map_err(|error| range_error(error.message()))?;
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        EcmaString::encode(&text),
    )?))
}

fn to_precision<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let n = primitive_number(
        machine,
        this,
        "Number.prototype.toPrecision requires that 'this' be a Number",
    )?;
    let precision = match args.first().copied() {
        None | Some(Value::UNDEFINED) => None,
        Some(value) => Some(to_integer_or_infinity(machine, value)?),
    };
    let text =
        number_format::to_precision(n, precision).map_err(|error| range_error(error.message()))?;
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        EcmaString::encode(&text),
    )?))
}

fn value_of<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let n = primitive_number(
        machine,
        this,
        "Number.prototype.valueOf requires that 'this' be a Number",
    )?;
    Ok(BuiltinOutcome::Value(crate::number_value(n)))
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program};
    use super::*;
    use crate::Limits;

    #[test]
    fn exponentiation_differs_from_powf_for_a_unit_base() {
        assert!(crate::number_exponentiate(1.0, f64::INFINITY).is_nan());
        assert!(crate::number_exponentiate(-1.0, f64::NEG_INFINITY).is_nan());
        assert!(crate::number_exponentiate(1.0, f64::NAN).is_nan());
        assert_eq!(crate::number_exponentiate(f64::NAN, 0.0), 1.0);
        assert_eq!(crate::number_exponentiate(2.0, 10.0), 1024.0);
    }

    #[test]
    fn number_parsers_are_the_global_functions() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Number").unwrap();
        for name in ["parseFloat", "parseInt"] {
            assert_eq!(
                machine.get_named_property(constructor, name).unwrap(),
                machine.intrinsics.global(name).unwrap()
            );
        }
    }

    #[test]
    fn number_constants_are_read_only() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Number").unwrap();
        for name in [
            "MAX_SAFE_INTEGER",
            "MIN_SAFE_INTEGER",
            "EPSILON",
            "MAX_VALUE",
            "MIN_VALUE",
            "POSITIVE_INFINITY",
            "NEGATIVE_INFINITY",
            "NaN",
        ] {
            let key = PropertyKey::Named(EcmaString::encode(name));
            assert!(matches!(
                machine.own_descriptor(constructor, &key).unwrap(),
                Some(crate::Property::Data {
                    writable: false,
                    enumerable: false,
                    configurable: false,
                    ..
                })
            ));
        }
    }

    #[test]
    fn numeric_prefixes_stop_at_lone_surrogates() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let text = machine
            .allocate(HeapEntry::String(EcmaString::from_units(&[
                u16::from(b'1'),
                0xd800,
            ])))
            .expect("malformed UTF-16 string allocation succeeds");

        let BuiltinOutcome::Value(float) =
            parse_float(&mut machine, Value::UNDEFINED, &[text], false)
                .expect("parseFloat handles a lone surrogate after its prefix")
        else {
            panic!("parseFloat returns a value");
        };
        let BuiltinOutcome::Value(integer) = parse_int(
            &mut machine,
            Value::UNDEFINED,
            &[text, Value::int32(10)],
            false,
        )
        .expect("parseInt handles a lone surrogate after its prefix") else {
            panic!("parseInt returns a value");
        };

        assert_eq!(float, Value::int32(1));
        assert_eq!(integer, Value::int32(1));
    }

    fn parse_int_radix(machine: &mut Machine<'_, TestHost>, input: &str, radix: Value) -> Value {
        let text = machine
            .allocate(HeapEntry::String(EcmaString::encode(input)))
            .expect("input string allocation succeeds");
        let BuiltinOutcome::Value(result) =
            parse_int(&mut *machine, Value::UNDEFINED, &[text, radix], false)
                .expect("parseInt returns a value")
        else {
            panic!("parseInt returns a value");
        };
        result
    }

    #[test]
    fn parse_int_wraps_radix_through_to_int32() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());

        // ToInt32 wraps modulo 2^32: 2^32 -> 0 (defaults to 10), 2^32 + 10 -> 10.
        assert_eq!(
            parse_int_radix(&mut machine, "10", Value::number(4_294_967_296.0)),
            Value::int32(10),
            "radix 2^32 must wrap to 0 and default to base 10"
        );
        assert_eq!(
            parse_int_radix(&mut machine, "10", Value::number(4_294_967_306.0)),
            Value::int32(10),
            "radix 2^32 + 10 must wrap to 10"
        );
        // 2^32 + 2 wraps to 2, so "10" parses as binary.
        assert_eq!(
            parse_int_radix(&mut machine, "10", Value::number(4_294_967_298.0)),
            Value::int32(2),
            "radix 2^32 + 2 must wrap to 2"
        );
        // A non-integer radix is truncated by ToInt32: 10.5 -> 10.
        assert_eq!(
            parse_int_radix(&mut machine, "10", Value::number(10.5)),
            Value::int32(10),
            "non-integer radix 10.5 must truncate to 10"
        );
        // 2^32 - 1 wraps to -1, which is outside [2, 36], so NaN results.
        assert!(
            value_number(parse_int_radix(
                &mut machine,
                "10",
                Value::number(4_294_967_295.0)
            ))
            .is_nan(),
            "radix 2^32 - 1 must wrap to -1 and yield NaN"
        );
    }

    #[test]
    fn parse_int_stops_accumulating_once_the_value_overflows() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let input = "9".repeat(500);
        let result = parse_int_radix(&mut machine, &input, Value::int32(10));
        assert_eq!(
            value_number(result),
            f64::INFINITY,
            "an overflowing integer literal must saturate to Infinity"
        );
    }

    fn outcome_text(machine: &Machine<'_, TestHost>, outcome: BuiltinOutcome) -> String {
        let BuiltinOutcome::Value(value) = outcome else {
            panic!("expected a string value outcome");
        };
        machine
            .to_string(value)
            .expect("string result")
            .to_utf8_lossy()
    }

    #[test]
    fn implicit_and_prototype_number_formatting_agree_on_boundaries() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let corpus = [
            0.0,
            -0.0,
            1.0,
            -1.0,
            0.5,
            0.1,
            0.1 + 0.2,
            1.0 / 3.0,
            1e-6,
            1e-7,
            -1e-7,
            1e20,
            9.999e20,
            1e21,
            -1e21,
            9_007_199_254_740_991.0,
            9_007_199_254_740_992.0,
            123_456_789_012_345_678_901.0,
            f64::from_bits(1),
            f64::MAX,
            f64::MIN_POSITIVE,
        ];
        for value in corpus {
            let expected = bamts_bytecode::format_number(value);
            let implicit = Machine::<TestHost>::ordinary_number_to_string(value);
            let number = crate::number_value(value);
            let prototype_outcome = to_string(&mut machine, number, &[], false).expect("toString");
            let prototype = outcome_text(&machine, prototype_outcome);
            let radix_outcome =
                to_string(&mut machine, number, &[Value::int32(10)], false).expect("toString(10)");
            let radix_ten = outcome_text(&machine, radix_outcome);
            let precision_outcome =
                to_precision(&mut machine, number, &[], false).expect("toPrecision");
            let precision_default = outcome_text(&machine, precision_outcome);
            assert_eq!(implicit, expected, "implicit ToString for {value}");
            assert_eq!(prototype, expected, "Number.prototype.toString for {value}");
            assert_eq!(
                radix_ten, expected,
                "Number.prototype.toString(10) for {value}"
            );
            assert_eq!(
                precision_default, expected,
                "Number.prototype.toPrecision() for {value}"
            );
            assert_eq!(
                number_format::to_string_radix(value, 10.0),
                Ok(expected.clone()),
                "radix-10 leaf for {value}"
            );
        }

        for (value, expected) in [
            (f64::NAN, "NaN"),
            (f64::INFINITY, "Infinity"),
            (f64::NEG_INFINITY, "-Infinity"),
        ] {
            assert_eq!(bamts_bytecode::format_number(value), expected);
            assert_eq!(
                Machine::<TestHost>::ordinary_number_to_string(value),
                expected
            );
            let number = crate::number_value(value);
            let outcome = to_string(&mut machine, number, &[], false).expect("toString");
            assert_eq!(outcome_text(&machine, outcome), expected);
        }
    }

    #[test]
    fn number_wrapper_coercion_is_observable_for_formatting_methods() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let boxed = machine
            .box_primitive(crate::number_value(1e21))
            .expect("Number wrapper");
        let text_outcome = to_string(&mut machine, boxed, &[], false).expect("wrapper toString");
        assert_eq!(outcome_text(&machine, text_outcome), "1e+21");
        let fixed_outcome =
            to_fixed(&mut machine, boxed, &[Value::int32(2)], false).expect("wrapper toFixed");
        assert_eq!(outcome_text(&machine, fixed_outcome), "1e+21");
    }
}
