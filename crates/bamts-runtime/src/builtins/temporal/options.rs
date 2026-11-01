//! Option reading. Every function here performs exactly the property reads and
//! conversions its abstract operation does; callers sequence them in the
//! proposal's alphabetical order, which test262 observes through Proxies.

use bamts_native::{Decoded, Value};

use super::{OrThrow, is_object, range_error, type_error};
use crate::temporal::instant_duration::{RoundingMode, Unit, UnitCategory};
use crate::temporal::now_rounding::{FractionalSecondDigits, SecondsStringPrecision};
use crate::{EvalFailure, Host, Machine};

/// A resolved options argument. `None` stands for the empty null-prototype
/// object of `GetOptionsObject(undefined)`, which no read can observe.
pub(super) type Options = Option<Value>;

/// GetOptionsObject.
pub(super) fn get_options_object<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<Options, EvalFailure> {
    if value == Value::UNDEFINED {
        Ok(None)
    } else if is_object(machine, value)? {
        Ok(Some(value))
    } else {
        Err(type_error(machine, "options must be an object"))
    }
}

fn read<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    name: &str,
) -> Result<Value, EvalFailure> {
    match options {
        Some(object) => machine.get_named_property(object, name),
        None => Ok(Value::UNDEFINED),
    }
}

/// GetOption with type string, no default, and a closed set of values.
fn string_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    name: &str,
    allowed: &[&str],
) -> Result<Option<String>, EvalFailure> {
    let value = read(machine, options, name)?;
    if value == Value::UNDEFINED {
        return Ok(None);
    }
    let text = machine.coerce_string_observable(value)?.to_utf8_lossy();
    if allowed.contains(&text.as_str()) {
        Ok(Some(text))
    } else {
        Err(range_error(
            machine,
            format!("{text} is not a valid value for {name}"),
        ))
    }
}

/// GetRoundingModeOption.
pub(super) fn rounding_mode_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    fallback: RoundingMode,
) -> Result<RoundingMode, EvalFailure> {
    let value = string_option(
        machine,
        options,
        "roundingMode",
        &[
            "ceil",
            "floor",
            "expand",
            "trunc",
            "halfCeil",
            "halfFloor",
            "halfExpand",
            "halfTrunc",
            "halfEven",
        ],
    )?;
    Ok(value
        .as_deref()
        .and_then(RoundingMode::from_name)
        .unwrap_or(fallback))
}

/// GetRoundingIncrementOption.
pub(super) fn rounding_increment_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
) -> Result<i128, EvalFailure> {
    let value = read(machine, options, "roundingIncrement")?;
    if value == Value::UNDEFINED {
        return Ok(1);
    }
    let increment = super::fields::to_integer_with_truncation(machine, value)?;
    if !(1.0..=1e9).contains(&increment) {
        return Err(range_error(machine, "roundingIncrement is out of range"));
    }
    Ok(increment as i128)
}

/// GetTemporalFractionalSecondDigitsOption.
pub(super) fn fractional_second_digits_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
) -> Result<FractionalSecondDigits, EvalFailure> {
    let value = read(machine, options, "fractionalSecondDigits")?;
    if value == Value::UNDEFINED {
        return Ok(FractionalSecondDigits::Auto);
    }
    let number = match value.decode() {
        Some(Decoded::Int32(number)) => f64::from(number as i32),
        Some(Decoded::Number(number)) => number,
        _ => {
            let text = machine.coerce_string_observable(value)?.to_utf8_lossy();
            if text == "auto" {
                return Ok(FractionalSecondDigits::Auto);
            }
            return Err(range_error(
                machine,
                format!("{text} is not a valid value for fractionalSecondDigits"),
            ));
        }
    };
    let digits = number.floor();
    if !digits.is_finite() || digits < 0.0 {
        return Err(range_error(
            machine,
            "fractionalSecondDigits must be from 0 to 9",
        ));
    }
    FractionalSecondDigits::digits(digits.min(255.0) as u8).or_throw(machine)
}

/// The value of a unit option before it is validated against a unit group.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum UnitOption {
    Unset,
    Auto,
    Unit(Unit),
}

const UNIT_NAMES: [&str; 21] = [
    "year",
    "years",
    "month",
    "months",
    "week",
    "weeks",
    "day",
    "days",
    "hour",
    "hours",
    "minute",
    "minutes",
    "second",
    "seconds",
    "millisecond",
    "milliseconds",
    "microsecond",
    "microseconds",
    "nanosecond",
    "nanoseconds",
    "auto",
];

/// GetTemporalUnitValuedOption.
pub(super) fn unit_valued_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    name: &str,
) -> Result<UnitOption, EvalFailure> {
    Ok(match string_option(machine, options, name, &UNIT_NAMES)? {
        None => UnitOption::Unset,
        Some(text) if text == "auto" => UnitOption::Auto,
        Some(text) => Unit::from_name(&text).map_or(UnitOption::Unset, UnitOption::Unit),
    })
}

/// The argument of `round` and `total`: a string is shorthand for the one
/// required unit option.
pub(super) struct UnitArgument {
    pub(super) options: Options,
    shorthand: Option<String>,
}

/// Reads such an argument. `undefined` is not an empty options object here.
pub(super) fn unit_argument<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<UnitArgument, EvalFailure> {
    if value == Value::UNDEFINED {
        return Err(type_error(machine, "a unit or options object is required"));
    }
    if let Some(text) = machine.string_value(value) {
        return Ok(UnitArgument {
            options: None,
            shorthand: Some(text.to_utf8_lossy()),
        });
    }
    Ok(UnitArgument {
        options: get_options_object(machine, value)?,
        shorthand: None,
    })
}

impl UnitArgument {
    /// The unit under `key`, unset when neither form supplies one.
    pub(super) fn unit<H: Host>(
        &self,
        machine: &mut Machine<'_, H>,
        key: &str,
    ) -> Result<UnitOption, EvalFailure> {
        let Some(text) = &self.shorthand else {
            return unit_valued_option(machine, self.options, key);
        };
        if text == "auto" {
            return Ok(UnitOption::Auto);
        }
        match Unit::from_name(text) {
            Some(unit) => Ok(UnitOption::Unit(unit)),
            None => Err(range_error(machine, format!("{text} is not a valid unit"))),
        }
    }

    /// The same, for an operation that cannot proceed without it.
    pub(super) fn required_unit<H: Host>(
        &self,
        machine: &mut Machine<'_, H>,
        key: &str,
    ) -> Result<UnitOption, EvalFailure> {
        match self.unit(machine, key)? {
            UnitOption::Unset => Err(range_error(machine, format!("{key} is required"))),
            value => Ok(value),
        }
    }
}

/// The units an option may name: one category, or both.
pub(super) type UnitGroup = Option<UnitCategory>;
pub(super) const TIME_UNITS: UnitGroup = Some(UnitCategory::Time);
pub(super) const ALL_UNITS: UnitGroup = None;

/// ValidateTemporalUnitValue. `extra` is a unit allowed outside the group.
pub(super) fn validate_unit_value<H: Host>(
    machine: &mut Machine<'_, H>,
    value: UnitOption,
    group: UnitGroup,
    extra: Option<UnitOption>,
) -> Result<(), EvalFailure> {
    if value == UnitOption::Unset || Some(value) == extra {
        return Ok(());
    }
    let valid = match value {
        UnitOption::Unit(unit) => group.is_none_or(|category| category == unit.category()),
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err(range_error(machine, "unit is not allowed in this context"))
    }
}

/// ToSecondsStringPrecisionRecord. `smallestUnit` takes precedence, and a
/// `fractionalSecondDigits` it overrides has already been read and validated.
pub(super) fn seconds_precision<H: Host>(
    machine: &mut Machine<'_, H>,
    smallest: UnitOption,
    digits: FractionalSecondDigits,
) -> Result<SecondsStringPrecision, EvalFailure> {
    let unit = match smallest {
        UnitOption::Unit(unit) => Some(unit),
        _ => None,
    };
    SecondsStringPrecision::resolve(unit, digits).or_throw(machine)
}
