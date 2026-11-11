#[cfg(test)]
use bamts_bytecode::EcmaString;
use bamts_bytecode::IteratorKind;
use bamts_native::{Decoded, Value};

use super::{define_data, define_frozen_data, install_function, type_error, value_number};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine};

/// Installs the ES2025 `Math` surface that the baseline installer either omits or
/// implements without user-observable coercion.
///
/// The caller owns the `Math` namespace object and its `@@toStringTag`. Every
/// function installed here converts arguments through `ToNumber` on the
/// observable path, so `valueOf`/`toString` hooks run in specification order.
///
/// https://tc39.es/ecma262/2025/multipage/numbers-and-dates.html#sec-math-object
pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    builtins: &mut BuiltinTable<H>,
    math: Value,
) {
    // 21.3.1: every value property is non-writable, non-enumerable, and
    // non-configurable.
    for (name, value) in CONSTANTS {
        define_frozen_data(heap, atoms, math, name, crate::number_value(value));
    }
    for (name, length, handler) in functions::<H>() {
        let function = install_function(heap, atoms, builtins, name, length, handler);
        define_data(heap, atoms, math, name, function);
    }
}

const CONSTANTS: [(&str, f64); 8] = [
    ("E", std::f64::consts::E),
    ("LN10", std::f64::consts::LN_10),
    ("LN2", std::f64::consts::LN_2),
    ("LOG10E", std::f64::consts::LOG10_E),
    ("LOG2E", std::f64::consts::LOG2_E),
    ("PI", std::f64::consts::PI),
    ("SQRT1_2", std::f64::consts::FRAC_1_SQRT_2),
    ("SQRT2", std::f64::consts::SQRT_2),
];

fn functions<H: Host>() -> [(&'static str, u32, BuiltinHandler<H>); 30] {
    [
        ("acos", 1, acos::<H> as BuiltinHandler<H>),
        ("acosh", 1, acosh::<H>),
        ("asin", 1, asin::<H>),
        ("asinh", 1, asinh::<H>),
        ("atan", 1, atan::<H>),
        ("atanh", 1, atanh::<H>),
        ("atan2", 2, atan2::<H>),
        ("cbrt", 1, cbrt::<H>),
        ("clz32", 1, clz32::<H>),
        ("cos", 1, cos::<H>),
        ("cosh", 1, cosh::<H>),
        ("exp", 1, exp::<H>),
        ("expm1", 1, expm1::<H>),
        ("f16round", 1, f16round::<H>),
        ("fround", 1, fround::<H>),
        ("hypot", 2, hypot::<H>),
        ("imul", 2, imul::<H>),
        ("log", 1, log::<H>),
        ("log1p", 1, log1p::<H>),
        ("log10", 1, log10::<H>),
        ("log2", 1, log2::<H>),
        ("max", 2, max::<H>),
        ("min", 2, min::<H>),
        ("sign", 1, sign::<H>),
        ("sin", 1, sin::<H>),
        ("sinh", 1, sinh::<H>),
        ("sumPrecise", 1, sum_precise::<H>),
        ("tan", 1, tan::<H>),
        ("tanh", 1, tanh::<H>),
        ("trunc", 1, trunc::<H>),
    ]
}

fn argument(args: &[Value], index: usize) -> Value {
    args.get(index).copied().unwrap_or(Value::UNDEFINED)
}

/// Enough limbs for any sum the iterator protocol can produce: a finite Number
/// is below 2^2098 of these units, and a list holds fewer than 2^53 of them.
const EXACT_SUM_LIMBS: usize = 36;

/// A two's-complement fixed-point total in units of 2^-1074, the spacing of
/// every Number. Each finite Number is a whole count of those units, so the
/// total is exact and `Math.sumPrecise` rounds exactly once, at the end.
struct ExactSum {
    limbs: [u64; EXACT_SUM_LIMBS],
}

impl ExactSum {
    fn new() -> Self {
        Self {
            limbs: [0; EXACT_SUM_LIMBS],
        }
    }

    fn add(&mut self, value: f64) {
        let bits = value.to_bits();
        let biased_exponent = (bits >> 52) & 0x7ff;
        let fraction = bits & ((1 << 52) - 1);
        let (mantissa, shift) = if biased_exponent == 0 {
            (fraction, 0)
        } else {
            (fraction | (1 << 52), biased_exponent - 1)
        };
        let first = (shift / 64) as usize;
        let wide = u128::from(mantissa) << (shift % 64);
        let parts = [wide as u64, (wide >> 64) as u64];
        let mut carry = false;
        for (offset, limb) in self.limbs[first..].iter_mut().enumerate() {
            let part = parts.get(offset).copied().unwrap_or(0);
            if offset >= parts.len() && !carry {
                break;
            }
            let (partial, first_carry, second_carry) = if value.is_sign_negative() {
                let (partial, borrowed) = limb.overflowing_sub(part);
                let (partial, again) = partial.overflowing_sub(u64::from(carry));
                (partial, borrowed, again)
            } else {
                let (partial, carried) = limb.overflowing_add(part);
                let (partial, again) = partial.overflowing_add(u64::from(carry));
                (partial, carried, again)
            };
            *limb = partial;
            carry = first_carry || second_carry;
        }
    }

    /// The total rounded to the nearest Number, ties to even. An exact zero is
    /// `+0`; the all-`-0` case never reaches here.
    fn round(&self) -> f64 {
        let negative = self.limbs[EXACT_SUM_LIMBS - 1] >> 63 == 1;
        let mut magnitude = self.limbs;
        if negative {
            let mut carry = true;
            for limb in &mut magnitude {
                let (negated, carried) = (!*limb).overflowing_add(u64::from(carry));
                *limb = negated;
                carry = carried;
            }
        }
        let Some(top) = magnitude.iter().rposition(|limb| *limb != 0) else {
            return 0.0;
        };
        let bit_length = top * 64 + (64 - magnitude[top].leading_zeros() as usize);
        let result = if bit_length <= 53 {
            // The encoding of Numbers below 2^-1021 is continuous, so a count
            // of units that fits in 53 bits is its own bit pattern.
            f64::from_bits(magnitude[0])
        } else {
            round_magnitude(&magnitude, bit_length)
        };
        if negative { -result } else { result }
    }
}

fn round_magnitude(magnitude: &[u64; EXACT_SUM_LIMBS], bit_length: usize) -> f64 {
    let bit = |position: usize| magnitude[position / 64] >> (position % 64) & 1 == 1;
    let mut shift = bit_length - 53;
    let (limb, offset) = (shift / 64, shift % 64);
    let low = magnitude[limb] >> offset;
    let high = match offset {
        0 => 0,
        _ => magnitude
            .get(limb + 1)
            .map_or(0, |next| next << (64 - offset)),
    };
    let mut mantissa = (low | high) & ((1 << 53) - 1);
    let round_position = shift - 1;
    let sticky = magnitude[..round_position / 64]
        .iter()
        .any(|limb| *limb != 0)
        || magnitude[round_position / 64] & ((1u64 << (round_position % 64)) - 1) != 0;
    if bit(round_position) && (sticky || mantissa & 1 == 1) {
        mantissa += 1;
        if mantissa == 1 << 53 {
            mantissa >>= 1;
            shift += 1;
        }
    }
    let biased_exponent = shift as u64 + 1;
    if biased_exponent >= 0x7ff {
        return f64::INFINITY;
    }
    f64::from_bits((biased_exponent << 52) | (mantissa & ((1 << 52) - 1)))
}

/// `Math.sumPrecise(items)`: the exact sum of an iterable of Numbers. A
/// non-Number closes the iterator; infinities and NaN are only recorded, since
/// later items must still be checked.
fn sum_precise<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let items = argument(args, 0);
    if matches!(items.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        return Err(type_error("Math.sumPrecise requires an iterable"));
    }
    let iterator = machine.create_iterator(items, IteratorKind::Sync)?;
    let depth = machine.native_roots.len();
    machine.push_native_roots(depth, &[iterator]);
    let total = sum_iterator(machine, iterator);
    machine.pop_native_roots(depth);
    Ok(BuiltinOutcome::Value(
        number_value_preserving_negative_zero(total?),
    ))
}

fn sum_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator: Value,
) -> Result<f64, EvalFailure> {
    let mut sum = ExactSum::new();
    let (mut saw_nan, mut saw_positive, mut saw_negative) = (false, false, false);
    let mut only_negative_zero = true;
    loop {
        let (done, next) = machine.iterator_next(iterator)?;
        if done {
            break;
        }
        if !matches!(next.decode(), Some(Decoded::Int32(_) | Decoded::Number(_))) {
            let (closed, _) = machine.close_iterator_raw(iterator);
            if let Err(EvalFailure::Runtime(kind)) = closed {
                return Err(EvalFailure::Runtime(kind));
            }
            return Err(type_error("Math.sumPrecise requires Number items"));
        }
        let number = value_number(next);
        if number.is_nan() {
            saw_nan = true;
        } else if number == f64::INFINITY {
            saw_positive = true;
        } else if number == f64::NEG_INFINITY {
            saw_negative = true;
        } else {
            only_negative_zero &= number == 0.0 && number.is_sign_negative();
            sum.add(number);
        }
    }
    Ok(if saw_nan || (saw_positive && saw_negative) {
        f64::NAN
    } else if saw_positive {
        f64::INFINITY
    } else if saw_negative {
        f64::NEG_INFINITY
    } else if only_negative_zero {
        -0.0
    } else {
        sum.round()
    })
}

/// `? ToNumber(arg)` on the observable path: an object argument runs its
/// `valueOf`/`toString` hook and propagates an abrupt completion.
fn to_number<H: Host>(machine: &mut Machine<'_, H>, value: Value) -> Result<f64, EvalFailure> {
    machine.coerce_number_observable(value).map(value_number)
}

fn coerce_all<H: Host>(
    machine: &mut Machine<'_, H>,
    args: &[Value],
) -> Result<Vec<f64>, EvalFailure> {
    let mut coerced = Vec::with_capacity(args.len());
    for value in args {
        coerced.push(to_number(machine, *value)?);
    }
    Ok(coerced)
}

fn number_value_preserving_negative_zero(value: f64) -> Value {
    if value == 0.0 && value.is_sign_negative() {
        Value::number(value)
    } else {
        crate::number_value(value)
    }
}

fn number(value: f64) -> BuiltinOutcome {
    BuiltinOutcome::Value(number_value_preserving_negative_zero(value))
}

macro_rules! unary_math {
    ($name:ident, $operation:expr) => {
        fn $name<H: Host>(
            machine: &mut Machine<'_, H>,
            _this: Value,
            args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let x = to_number(machine, argument(args, 0))?;
            Ok(number(($operation)(x)))
        }
    };
}

// Signed zero, NaN, and infinity results are mandated by ECMA-262 but not
// guaranteed by the host libm, so each boundary case is decided here before
// delegating the ordinary finite case.
unary_math!(acos, |x: f64| if x == 1.0 { 0.0 } else { x.acos() });
unary_math!(acosh, |x: f64| if x == 1.0 { 0.0 } else { x.acosh() });
unary_math!(asin, |x: f64| if x == 0.0 { x } else { x.asin() });
unary_math!(asinh, |x: f64| if !x.is_finite() || x == 0.0 {
    x
} else {
    x.asinh()
});
unary_math!(atan, |x: f64| if x == 0.0 { x } else { x.atan() });
unary_math!(atanh, |x: f64| if x == 0.0 { x } else { x.atanh() });
unary_math!(cbrt, |x: f64| if !x.is_finite() || x == 0.0 {
    x
} else {
    x.cbrt()
});
unary_math!(cos, |x: f64| if x == 0.0 { 1.0 } else { x.cos() });
unary_math!(cosh, |x: f64| if x == 0.0 { 1.0 } else { x.cosh() });
unary_math!(exp, |x: f64| if x == f64::NEG_INFINITY {
    0.0
} else {
    x.exp()
});
unary_math!(
    expm1,
    |x: f64| if x.is_nan() || x == 0.0 || x == f64::INFINITY {
        x
    } else if x == f64::NEG_INFINITY {
        -1.0
    } else {
        x.exp_m1()
    }
);
unary_math!(fround, |x: f64| f64::from(x as f32));
unary_math!(f16round, round_to_binary16);
unary_math!(log, f64::ln);
unary_math!(
    log1p,
    |x: f64| if x.is_nan() || x == 0.0 || x == f64::INFINITY {
        x
    } else if x == -1.0 {
        f64::NEG_INFINITY
    } else if x < -1.0 {
        f64::NAN
    } else {
        x.ln_1p()
    }
);
unary_math!(log10, f64::log10);
unary_math!(log2, f64::log2);
unary_math!(sin, |x: f64| if x == 0.0 { x } else { x.sin() });
unary_math!(sinh, |x: f64| if !x.is_finite() || x == 0.0 {
    x
} else {
    x.sinh()
});
unary_math!(tan, |x: f64| if x == 0.0 { x } else { x.tan() });
unary_math!(tanh, |x: f64| if x == 0.0 { x } else { x.tanh() });
unary_math!(trunc, |x: f64| if !x.is_finite() || x == 0.0 {
    x
} else {
    x.trunc()
});
unary_math!(sign, |x: f64| if x.is_nan() || x == 0.0 {
    x
} else if x.is_sign_negative() {
    -1.0
} else {
    1.0
});

fn atan2<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let y = to_number(machine, argument(args, 0))?;
    let x = to_number(machine, argument(args, 1))?;
    Ok(number(y.atan2(x)))
}

fn clz32<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = crate::to_uint32(to_number(machine, argument(args, 0))?);
    Ok(number(f64::from(value.leading_zeros())))
}

/// 21.3.2.26: `+0𝔽` never displaces a previously seen `-0𝔽`.
fn min<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let coerced = coerce_all(machine, args)?;
    let mut lowest = f64::INFINITY;
    for value in coerced {
        if value.is_nan() {
            return Ok(number(f64::NAN));
        }
        if value == 0.0 && lowest == 0.0 {
            if value.is_sign_negative() {
                lowest = -0.0;
            }
        } else if value < lowest {
            lowest = value;
        }
    }
    Ok(number(lowest))
}

/// 21.3.2.25: `-0𝔽` never displaces a previously seen `+0𝔽`.
fn max<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let coerced = coerce_all(machine, args)?;
    let mut highest = f64::NEG_INFINITY;
    for value in coerced {
        if value.is_nan() {
            return Ok(number(f64::NAN));
        }
        if value == 0.0 && highest == 0.0 {
            if value.is_sign_positive() {
                highest = 0.0;
            }
        } else if value > highest {
            highest = value;
        }
    }
    Ok(number(highest))
}

fn hypot<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    // 21.3.2.19 coerces every argument before inspecting any of them, so an
    // infinity or NaN in an early argument never suppresses a later hook.
    let coerced = coerce_all(machine, args)?;
    if coerced.iter().any(|value| value.is_infinite()) {
        return Ok(number(f64::INFINITY));
    }
    if coerced.iter().any(|value| value.is_nan()) {
        return Ok(number(f64::NAN));
    }
    let scale = coerced
        .iter()
        .map(|value| value.abs())
        .fold(0.0_f64, f64::max);
    if scale == 0.0 {
        return Ok(number(0.0));
    }

    // Normalizing by the largest magnitude keeps every square in range, and
    // compensated accumulation retains the small terms that plain summation
    // would drop.
    let mut sum = 0.0_f64;
    let mut compensation = 0.0_f64;
    for value in coerced {
        let term = (value / scale).powi(2);
        let total = sum + term;
        compensation += if sum.abs() >= term {
            (sum - total) + term
        } else {
            (term - total) + sum
        };
        sum = total;
    }
    Ok(number(scale * (sum + compensation).sqrt()))
}

/// 21.3.2.20: two `ToUint32` conversions, a product taken modulo 2^32, and a
/// signed reinterpretation of the low 32 bits.
fn imul<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let left = crate::to_uint32(to_number(machine, argument(args, 0))?);
    let right = crate::to_uint32(to_number(machine, argument(args, 1))?);
    Ok(BuiltinOutcome::Value(Value::int32(
        left.wrapping_mul(right),
    )))
}

fn round_shift_ties_even(significand: u64, shift: u32) -> u64 {
    if shift == 0 {
        return significand;
    }
    if shift >= 64 {
        return 0;
    }
    let quotient = significand >> shift;
    let remainder = significand & ((1_u64 << shift) - 1);
    let halfway = 1_u64 << (shift - 1);
    quotient + u64::from(remainder > halfway || (remainder == halfway && quotient & 1 != 0))
}

/// Rounds binary64 straight to binary16 under roundTiesToEven, then widens the
/// result back to binary64. Rounding directly avoids the binary64 -> binary32 ->
/// binary16 double-rounding cases that 21.3.2.18 warns about.
fn round_to_binary16(value: f64) -> f64 {
    if !value.is_finite() || value == 0.0 {
        return value;
    }

    let bits = value.to_bits();
    let negative = bits >> 63 != 0;
    let exponent = ((bits >> 52) & 0x7ff) as i32 - 1023;
    let significand = (1_u64 << 52) | (bits & ((1_u64 << 52) - 1));

    // binary16 carries 11 significand bits, so a normal result keeps bits 52..42
    // and the subnormal range shifts by the distance below the 2^-14 boundary.
    let (encoded_exponent, encoded_significand) = if exponent > 15 {
        (31_u16, 0_u16)
    } else if exponent >= -14 {
        let rounded = round_shift_ties_even(significand, 42);
        let (carried, fraction) = if rounded == 2048 {
            (1, 0)
        } else {
            (0, (rounded - 1024) as u16)
        };
        let encoded = (exponent + 15) as u16 + carried;
        if encoded >= 31 {
            (31, 0)
        } else {
            (encoded, fraction)
        }
    } else if exponent < -25 {
        (0, 0)
    } else {
        let rounded = round_shift_ties_even(significand, (28 - exponent) as u32);
        if rounded == 1024 {
            (1, 0)
        } else {
            (0, rounded as u16)
        }
    };

    let magnitude = match encoded_exponent {
        31 => f64::INFINITY,
        0 => f64::from(encoded_significand) * 2_f64.powi(-24),
        _ => {
            (1.0 + f64::from(encoded_significand) / 1024.0)
                * 2_f64.powi(i32::from(encoded_exponent) - 15)
        }
    };
    if negative { -magnitude } else { magnitude }
}

#[cfg(test)]
mod exact_sum_tests {
    use super::ExactSum;

    fn total(values: &[f64]) -> f64 {
        let mut sum = ExactSum::new();
        for value in values {
            sum.add(*value);
        }
        sum.round()
    }

    #[test]
    fn intermediate_overflow_and_cancellation_stay_exact() {
        assert_eq!(total(&[f64::MAX, f64::MAX, -f64::MAX]), f64::MAX);
        assert_eq!(total(&[1e308, 1e308, -1e308, -1e308]), 0.0);
        assert_eq!(total(&[1e30, 0.1, -1e30]), 0.1);
        assert_eq!(total(&[f64::MAX, f64::MAX]), f64::INFINITY);
        assert_eq!(total(&[-f64::MAX, -f64::MAX]), f64::NEG_INFINITY);
    }

    #[test]
    fn rounding_is_to_nearest_with_ties_to_even() {
        let tiny = 2f64.powi(-53);
        assert_eq!(total(&[1.0, tiny]), 1.0, "a tie rounds down to even");
        let odd = 1.0 + 2f64.powi(-52);
        assert_eq!(
            total(&[odd, tiny]),
            1.0 + 2f64.powi(-51),
            "a tie rounds up to even"
        );
        assert_eq!(
            total(&[1.0, tiny, 2f64.powi(-1000)]),
            1.0 + 2f64.powi(-52),
            "anything past the tie breaks it upward"
        );
    }

    #[test]
    fn subnormal_totals_are_exact() {
        let smallest = f64::from_bits(1);
        assert_eq!(total(&[smallest, smallest]), f64::from_bits(2));
        assert_eq!(
            total(&[f64::MIN_POSITIVE, -smallest]).to_bits(),
            (1 << 52) - 1
        );
        assert_eq!(total(&[-smallest]), -smallest);
    }

    #[test]
    fn an_exact_zero_is_positive() {
        assert!(total(&[1.5, -1.5]).is_sign_positive());
        assert!(total(&[]).is_sign_positive());
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, Property, PropertyKey, ThrowOrigin};

    macro_rules! test_machine {
        ($program:ident, $host:ident, $machine:ident) => {
            let $program = blank_program("<math-edge>");
            let mut $host = TestHost;
            let mut $machine = Machine::new(&$program, &mut $host, Limits::default());
        };
    }

    const ORDER_SINK: &str = "mathEdgeCoercionOrder";

    fn result(outcome: Result<BuiltinOutcome, EvalFailure>) -> Value {
        let BuiltinOutcome::Value(value) = outcome.expect("Math operation succeeds") else {
            panic!("Math operation returns a value")
        };
        value
    }

    fn call(
        machine: &mut Machine<'_, TestHost>,
        handler: BuiltinHandler<TestHost>,
        args: &[Value],
    ) -> f64 {
        value_number(result(handler(machine, Value::UNDEFINED, args, false)))
    }

    fn call_unary(
        machine: &mut Machine<'_, TestHost>,
        handler: BuiltinHandler<TestHost>,
        value: f64,
    ) -> f64 {
        call(
            machine,
            handler,
            &[number_value_preserving_negative_zero(value)],
        )
    }

    #[test]
    fn preserves_negative_zero_where_the_specification_requires_it() {
        test_machine!(program, host, machine);
        for handler in [
            sign::<TestHost> as BuiltinHandler<TestHost>,
            trunc::<TestHost>,
            fround::<TestHost>,
            f16round::<TestHost>,
            cbrt::<TestHost>,
            asin::<TestHost>,
            asinh::<TestHost>,
            atan::<TestHost>,
            atanh::<TestHost>,
            expm1::<TestHost>,
            log1p::<TestHost>,
            sin::<TestHost>,
            sinh::<TestHost>,
            tan::<TestHost>,
            tanh::<TestHost>,
        ] {
            assert_eq!(
                call_unary(&mut machine, handler, -0.0).to_bits(),
                (-0.0_f64).to_bits(),
            );
            assert_eq!(
                call_unary(&mut machine, handler, 0.0).to_bits(),
                0.0_f64.to_bits()
            );
        }

        let zero = Value::number(0.0);
        let negative_zero = Value::number(-0.0);
        assert_eq!(
            call(&mut machine, min::<TestHost>, &[zero, negative_zero]).to_bits(),
            (-0.0_f64).to_bits(),
        );
        assert_eq!(
            call(&mut machine, min::<TestHost>, &[negative_zero, zero]).to_bits(),
            (-0.0_f64).to_bits(),
        );
        assert_eq!(
            call(&mut machine, max::<TestHost>, &[negative_zero, zero]).to_bits(),
            0.0_f64.to_bits(),
        );
        assert_eq!(
            call(&mut machine, max::<TestHost>, &[zero, negative_zero]).to_bits(),
            0.0_f64.to_bits(),
        );
        assert_eq!(call(&mut machine, min::<TestHost>, &[]), f64::INFINITY,);
        assert_eq!(call(&mut machine, max::<TestHost>, &[]), f64::NEG_INFINITY,);
        assert_eq!(
            call_unary(&mut machine, acos::<TestHost>, 1.0).to_bits(),
            0.0_f64.to_bits()
        );
        assert_eq!(
            call_unary(&mut machine, acosh::<TestHost>, 1.0).to_bits(),
            0.0_f64.to_bits()
        );
        assert_eq!(call_unary(&mut machine, cos::<TestHost>, -0.0), 1.0);
        assert_eq!(call_unary(&mut machine, cosh::<TestHost>, -0.0), 1.0);
        assert!(call_unary(&mut machine, sign::<TestHost>, f64::NAN).is_nan());
        assert_eq!(call_unary(&mut machine, sign::<TestHost>, -3.5), -1.0);
        assert_eq!(call_unary(&mut machine, sign::<TestHost>, 3.5), 1.0);
        assert_eq!(
            call_unary(&mut machine, trunc::<TestHost>, -0.7).to_bits(),
            (-0.0_f64).to_bits()
        );
        assert_eq!(
            call_unary(&mut machine, exp::<TestHost>, f64::NEG_INFINITY),
            0.0
        );
        assert_eq!(
            call_unary(&mut machine, log2::<TestHost>, -0.0),
            f64::NEG_INFINITY
        );
        assert!(call_unary(&mut machine, log2::<TestHost>, -1.0).is_nan());
        assert_eq!(
            call_unary(&mut machine, asinh::<TestHost>, f64::INFINITY),
            f64::INFINITY
        );
        assert_eq!(call_unary(&mut machine, cbrt::<TestHost>, -8.0), -2.0);
    }

    fn recording_value_of(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let marker = value_number(machine.get_named_property(this, "marker")?);
        let order = machine
            .intrinsics
            .global(ORDER_SINK)
            .map_or(0.0, value_number);
        machine.intrinsics.globals.insert(
            EcmaString::encode(ORDER_SINK),
            crate::number_value(order * 10.0 + marker),
        );
        machine
            .get_named_property(this, "numericValue")
            .map(BuiltinOutcome::Value)
    }

    fn throwing_value_of(
        _machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(super::super::type_error("hostile valueOf"))
    }

    fn hook(machine: &mut Machine<'_, TestHost>, handler: BuiltinHandler<TestHost>) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "math valueOf",
            length: 0,
            handler,
        });
        native_function(&mut machine.heap, &mut machine.atoms, id, "math valueOf", 0)
    }

    fn coercible(
        machine: &mut Machine<'_, TestHost>,
        value_of: Value,
        marker: u32,
        numeric_value: f64,
    ) -> Value {
        let object = ordinary_object(machine);
        machine
            .set_data_property(object, "marker", Value::int32(marker))
            .unwrap();
        machine
            .set_data_property(object, "numericValue", crate::number_value(numeric_value))
            .unwrap();
        machine
            .set_data_property(object, "valueOf", value_of)
            .unwrap();
        object
    }

    fn recorded_order(machine: &Machine<'_, TestHost>) -> f64 {
        machine
            .intrinsics
            .global(ORDER_SINK)
            .map_or(0.0, value_number)
    }

    fn reset_order(machine: &mut Machine<'_, TestHost>) {
        machine
            .intrinsics
            .globals
            .insert(EcmaString::encode(ORDER_SINK), crate::number_value(0.0));
    }

    #[test]
    fn variadic_math_coerces_every_argument_left_to_right() {
        test_machine!(program, host, machine);
        let value_of = hook(&mut machine, recording_value_of);
        let nan = coercible(&mut machine, value_of, 1, f64::NAN);
        let infinite = coercible(&mut machine, value_of, 2, f64::INFINITY);
        let finite = coercible(&mut machine, value_of, 3, 4.0);

        // A NaN or infinity in the first argument must not skip later hooks.
        for (handler, expect) in [
            (min::<TestHost> as BuiltinHandler<TestHost>, f64::NAN),
            (max::<TestHost>, f64::NAN),
            (hypot::<TestHost>, f64::INFINITY),
        ] {
            reset_order(&mut machine);
            let actual = call(&mut machine, handler, &[nan, infinite, finite]);
            assert_eq!(actual.is_nan(), expect.is_nan());
            if !expect.is_nan() {
                assert_eq!(actual, expect);
            }
            assert_eq!(recorded_order(&machine), 123.0);
        }

        reset_order(&mut machine);
        assert_eq!(
            call(&mut machine, imul::<TestHost>, &[finite, finite]),
            16.0
        );
        assert_eq!(recorded_order(&machine), 33.0);
        reset_order(&mut machine);
        assert_eq!(
            call(&mut machine, atan2::<TestHost>, &[finite, finite]),
            4.0_f64.atan2(4.0)
        );
        assert_eq!(recorded_order(&machine), 33.0);
        reset_order(&mut machine);
        assert_eq!(call(&mut machine, trunc::<TestHost>, &[finite]), 4.0);
        assert_eq!(recorded_order(&machine), 3.0);
    }

    #[test]
    fn hostile_value_of_aborts_before_later_arguments_are_read() {
        test_machine!(program, host, machine);
        let recorder = hook(&mut machine, recording_value_of);
        let thrower = hook(&mut machine, throwing_value_of);
        let hostile = coercible(&mut machine, thrower, 1, 0.0);
        let observed = coercible(&mut machine, recorder, 2, 1.0);
        for handler in [
            min::<TestHost> as BuiltinHandler<TestHost>,
            max::<TestHost>,
            hypot::<TestHost>,
            imul::<TestHost>,
            atan2::<TestHost>,
        ] {
            reset_order(&mut machine);
            assert!(matches!(
                handler(&mut machine, Value::UNDEFINED, &[hostile, observed], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. })),
            ));
            assert_eq!(recorded_order(&machine), 0.0);
        }
    }

    #[test]
    fn imul_and_clz32_apply_to_uint32_before_arithmetic() {
        test_machine!(program, host, machine);
        for (left, right, expected) in [
            (4_294_967_295.0, 5.0, -5.0),
            (4_294_967_297.0, 3.0, 3.0),
            (-1.5, 2.0, -2.0),
            (f64::NAN, 7.0, 0.0),
            (f64::INFINITY, 7.0, 0.0),
            (-0.0, 7.0, 0.0),
            (65_536.0, 65_536.0, 0.0),
            (2.0, 4.0, 8.0),
            (-5.0, 12.0, -60.0),
        ] {
            assert_eq!(
                call(
                    &mut machine,
                    imul::<TestHost>,
                    &[crate::number_value(left), crate::number_value(right)],
                ),
                expected,
                "imul({left}, {right})",
            );
        }
        assert_eq!(call(&mut machine, imul::<TestHost>, &[]), 0.0);
        for (input, expected) in [
            (0.0, 32.0),
            (-0.0, 32.0),
            (1.0, 31.0),
            (-1.0, 0.0),
            (f64::NAN, 32.0),
            (f64::INFINITY, 32.0),
            (4_294_967_296.0, 32.0),
            (2_147_483_648.0, 0.0),
        ] {
            assert_eq!(
                call_unary(&mut machine, clz32::<TestHost>, input),
                expected,
                "clz32({input})",
            );
        }
    }

    #[test]
    fn hypot_scales_extreme_magnitudes_and_keeps_small_terms() {
        test_machine!(program, host, machine);
        for scale in [1.0, 1e200, 1e-200] {
            assert_eq!(
                call(
                    &mut machine,
                    hypot::<TestHost>,
                    &[
                        crate::number_value(3.0 * scale),
                        crate::number_value(4.0 * scale),
                    ],
                ),
                5.0 * scale,
                "hypot scaled by {scale}",
            );
        }
        // Naive summation squares f64::MAX into an infinity; scaling must not.
        assert_eq!(
            call(
                &mut machine,
                hypot::<TestHost>,
                &[crate::number_value(f64::MAX), crate::number_value(0.0)],
            ),
            f64::MAX,
        );
        assert_eq!(
            call(
                &mut machine,
                hypot::<TestHost>,
                &[
                    crate::number_value(f64::MIN_POSITIVE),
                    crate::number_value(0.0),
                ],
            ),
            f64::MIN_POSITIVE,
        );
        assert_eq!(
            call(
                &mut machine,
                hypot::<TestHost>,
                &[crate::number_value(-0.0), crate::number_value(-0.0),],
            )
            .to_bits(),
            0.0_f64.to_bits(),
        );
        assert_eq!(
            call(&mut machine, hypot::<TestHost>, &[]).to_bits(),
            0.0_f64.to_bits()
        );
        assert_eq!(
            call(
                &mut machine,
                hypot::<TestHost>,
                &[
                    crate::number_value(f64::NAN),
                    crate::number_value(f64::NEG_INFINITY),
                ],
            ),
            f64::INFINITY,
        );
        assert!(
            call(
                &mut machine,
                hypot::<TestHost>,
                &[crate::number_value(f64::NAN), crate::number_value(1.0)],
            )
            .is_nan()
        );
    }

    fn assert_relative_close(actual: f64, expected: f64, max_epsilon: f64) {
        let error = (actual - expected).abs();
        let tolerance = expected.abs() * f64::EPSILON * max_epsilon;
        assert!(
            error <= tolerance,
            "expected {actual:e} to be within {max_epsilon} epsilons of {expected:e}; error {error:e}, tolerance {tolerance:e}",
        );
    }

    #[test]
    fn cbrt_expm1_and_log1p_define_exceptional_results() {
        test_machine!(program, host, machine);

        assert!(call_unary(&mut machine, cbrt::<TestHost>, f64::NAN).is_nan());
        assert_eq!(
            call_unary(&mut machine, cbrt::<TestHost>, f64::INFINITY),
            f64::INFINITY,
        );
        assert_eq!(
            call_unary(&mut machine, cbrt::<TestHost>, f64::NEG_INFINITY),
            f64::NEG_INFINITY,
        );

        assert!(call_unary(&mut machine, expm1::<TestHost>, f64::NAN).is_nan());
        assert_eq!(
            call_unary(&mut machine, expm1::<TestHost>, f64::INFINITY),
            f64::INFINITY,
        );
        assert_eq!(
            call_unary(&mut machine, expm1::<TestHost>, f64::NEG_INFINITY),
            -1.0,
        );

        assert!(call_unary(&mut machine, log1p::<TestHost>, f64::NAN).is_nan());
        assert_eq!(
            call_unary(&mut machine, log1p::<TestHost>, f64::INFINITY),
            f64::INFINITY,
        );
        assert_eq!(
            call_unary(&mut machine, log1p::<TestHost>, -1.0),
            f64::NEG_INFINITY,
        );
        assert!(call_unary(&mut machine, log1p::<TestHost>, -1.000_000_000_000_000_2).is_nan());
    }

    #[test]
    fn near_zero_math_uses_cancellation_avoiding_operations() {
        test_machine!(program, host, machine);

        // ECMA-262 permits implementation-approximated transcendental results.
        // Eight binary64 epsilons admits normal libm variation while still
        // rejecting the cancellation from computing exp(x) - 1 or ln(1 + x).
        for (input, expected_expm1, expected_log1p) in [
            (
                2_f64.powi(-54),
                5.551_115_123_125_783e-17,
                5.551_115_123_125_782e-17,
            ),
            (
                -2_f64.powi(-54),
                -5.551_115_123_125_782e-17,
                -5.551_115_123_125_783e-17,
            ),
            (1e-12, 1.000_000_000_000_5e-12, 9.999_999_999_995e-13),
            (-1e-12, -9.999_999_999_995e-13, -1.000_000_000_000_5e-12),
        ] {
            assert_relative_close(
                call_unary(&mut machine, expm1::<TestHost>, input),
                expected_expm1,
                8.0,
            );
            assert_relative_close(
                call_unary(&mut machine, log1p::<TestHost>, input),
                expected_log1p,
                8.0,
            );
        }

        assert_relative_close(
            call_unary(&mut machine, cbrt::<TestHost>, f64::from_bits(1)),
            1.703_183_936_003_260_3e-108,
            8.0,
        );
    }

    #[test]
    fn hypot_distinguishes_true_overflow_from_large_finite_results() {
        test_machine!(program, host, machine);

        assert!(
            call(
                &mut machine,
                hypot::<TestHost>,
                &[crate::number_value(f64::MAX), crate::number_value(f64::MAX)],
            )
            .is_infinite()
        );
        assert_relative_close(
            call(
                &mut machine,
                hypot::<TestHost>,
                &[
                    crate::number_value(f64::MAX / 2.0),
                    crate::number_value(f64::MAX / 2.0),
                ],
            ),
            1.271_161_006_153_646_2e308,
            8.0,
        );
        assert_eq!(
            call(
                &mut machine,
                hypot::<TestHost>,
                &[
                    crate::number_value(f64::from_bits(1)),
                    crate::number_value(0.0)
                ],
            )
            .to_bits(),
            1,
        );

        for args in [[f64::INFINITY, f64::NAN], [f64::NAN, f64::NEG_INFINITY]] {
            assert_eq!(
                call(
                    &mut machine,
                    hypot::<TestHost>,
                    &[crate::number_value(args[0]), crate::number_value(args[1])],
                ),
                f64::INFINITY,
            );
        }
    }
    #[test]
    fn binary16_rounding_covers_ties_subnormals_and_overflow() {
        assert_eq!(round_to_binary16(1.0), 1.0);
        assert_eq!(round_to_binary16(1.0 + 2_f64.powi(-11)), 1.0);
        assert_eq!(
            round_to_binary16(1.0 + 3.0 * 2_f64.powi(-11)),
            1.0 + 2_f64.powi(-9),
        );
        assert_eq!(
            round_to_binary16(1.0 + 2_f64.powi(-10)),
            1.0 + 2_f64.powi(-10)
        );
        assert_eq!(round_to_binary16(65_504.0), 65_504.0);
        assert_eq!(round_to_binary16(65_519.0), 65_504.0);
        assert_eq!(round_to_binary16(65_520.0), f64::INFINITY);
        assert_eq!(round_to_binary16(-65_520.0), f64::NEG_INFINITY);
        assert_eq!(round_to_binary16(2_f64.powi(-24)), 2_f64.powi(-24));
        assert_eq!(round_to_binary16(2_f64.powi(-25)), 0.0);
        assert_eq!(
            round_to_binary16(3.0 * 2_f64.powi(-25)),
            2.0 * 2_f64.powi(-24),
        );
        assert_eq!(
            round_to_binary16(2_f64.powi(-15) + 2_f64.powi(-25)),
            2_f64.powi(-15),
        );
        assert_eq!(round_to_binary16(-0.0).to_bits(), (-0.0_f64).to_bits());
        assert_eq!(round_to_binary16(0.0).to_bits(), 0.0_f64.to_bits());
        assert!(round_to_binary16(f64::NAN).is_nan());
        assert_eq!(round_to_binary16(f64::INFINITY), f64::INFINITY);
        assert_eq!(round_to_binary16(1.0 / 3.0), 0.333251953125);
    }

    #[test]
    fn installer_defines_every_constant_function_name_length_and_descriptor() {
        test_machine!(program, host, machine);
        let math = machine
            .intrinsics
            .global("Math")
            .expect("Math is installed");
        install(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.intrinsics.builtins,
            math,
        );

        for (name, expected) in CONSTANTS {
            let key = PropertyKey::Named(machine.intern_str(name));
            assert!(
                matches!(
                    machine.own_descriptor(math, &key).unwrap(),
                    Some(Property::Data {
                        value,
                        writable: false,
                        enumerable: false,
                        configurable: false,
                    }) if value_number(value) == expected
                ),
                "Math.{name} is a frozen value property",
            );
        }

        for (name, length, _) in functions::<TestHost>() {
            let function = machine.get_named_property(math, name).unwrap();
            assert!(
                machine.is_callable(function).unwrap(),
                "Math.{name} is callable"
            );
            for (property, expected_length) in [("name", None), ("length", Some(length))] {
                let descriptor_key = PropertyKey::Named(machine.intern_str(property));
                let descriptor = machine.own_descriptor(function, &descriptor_key).unwrap();
                assert!(
                    matches!(
                        descriptor,
                        Some(Property::Data {
                            value,
                            writable: false,
                            enumerable: false,
                            configurable: true,
                        }) if expected_length.map_or_else(
                            || machine.string_value(value).is_some_and(|text| text.eq_ascii(name)),
                            |length| value == Value::int32(length),
                        )
                    ),
                    "Math.{name} has the standard {property} descriptor",
                );
            }
            let math_key = PropertyKey::Named(machine.intern_str(name));
            assert!(
                matches!(
                    machine
                        .own_descriptor(math, &math_key)
                        .unwrap(),
                    Some(Property::Data {
                        value,
                        writable: true,
                        enumerable: false,
                        configurable: true,
                    }) if value == function
                ),
                "Math.{name} is writable, non-enumerable, configurable",
            );
        }
    }
}
