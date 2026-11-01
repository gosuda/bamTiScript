//! `Temporal.PlainTime`.

use bamts_native::Value;

use super::super::intl::temporal_to_locale_string;
use super::fields::{
    FieldNames, prepare_partial_fields, require_partial_temporal_object, time_from_fields,
    to_integer_with_truncation, to_temporal_duration, to_temporal_time,
};
use super::options::{
    DifferencePolicy, TIME_UNITS, UnitOption, difference_settings, fractional_second_digits_option,
    get_options_object, overflow_option, rounding_increment_option, rounding_mode_option,
    unit_argument, unit_valued_option, validate_unit_value,
};
use super::{
    Class, OrThrow, arg, construct, create, install_class, number_outcome, range_error,
    require_new, string_outcome, temporal_record, type_error, value_of_throws,
};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::temporal::instant_duration::{
    Overflow, Precision, RoundingMode, Unit, validate_rounding_increment,
};
use crate::temporal::now_rounding::{ToStringRoundingOptions, serialize_plain_time};
use crate::temporal::plain_types::PlainTime;
use crate::temporal::zoned_date_time::CalendarId;
use crate::temporal::{TemporalKind, TemporalObject};
use crate::{EvalFailure, HeapEntry, Host, Machine};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    builtins: &mut BuiltinTable<H>,
    namespace: Value,
) {
    install_class(
        heap,
        builtins,
        namespace,
        &Class {
            kind: TemporalKind::PlainTime,
            name: "PlainTime",
            tag: "Temporal.PlainTime",
            length: 0,
            constructor: constructor::<H>,
            statics: &[("from", 1, from::<H>), ("compare", 2, compare::<H>)],
            getters: &[
                ("hour", "get hour", hour::<H>),
                ("minute", "get minute", minute::<H>),
                ("second", "get second", second::<H>),
                ("millisecond", "get millisecond", millisecond::<H>),
                ("microsecond", "get microsecond", microsecond::<H>),
                ("nanosecond", "get nanosecond", nanosecond::<H>),
            ],
            methods: &[
                ("add", 1, add::<H>),
                ("subtract", 1, subtract::<H>),
                ("with", 1, with::<H>),
                ("until", 1, until::<H>),
                ("since", 1, since::<H>),
                ("round", 1, round::<H>),
                ("equals", 1, equals::<H>),
                ("toString", 0, to_string::<H>),
                ("toLocaleString", 0, to_locale_string::<H>),
                ("toJSON", 0, to_json::<H>),
                ("valueOf", 0, value_of_throws::<H>),
            ],
        },
    );
}

fn this_time<H: Host>(machine: &mut Machine<'_, H>, this: Value) -> Result<PlainTime, EvalFailure> {
    match temporal_record(machine, this)? {
        Some(TemporalObject::PlainTime(value)) => Ok(value),
        _ => Err(type_error(machine, "receiver is not a Temporal.PlainTime")),
    }
}

fn time_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    value: PlainTime,
) -> Result<BuiltinOutcome, EvalFailure> {
    create(machine, TemporalObject::PlainTime(value)).map(BuiltinOutcome::Value)
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_new(machine, constructing, "PlainTime")?;
    let mut fields = [0_f64; 6];
    for (index, field) in fields.iter_mut().enumerate() {
        let value = arg(args, index);
        if value != Value::UNDEFINED {
            *field = to_integer_with_truncation(machine, value)?;
        }
    }
    let [hour, minute, second, millisecond, microsecond, nanosecond] = fields.map(|v| v as i64);
    let value = PlainTime::new(
        hour,
        minute,
        second,
        millisecond,
        microsecond,
        nanosecond,
        Overflow::Reject,
    )
    .or_throw(machine)?;
    construct(machine, TemporalObject::PlainTime(value))
}

fn from<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = to_temporal_time(machine, arg(args, 0), arg(args, 1))?;
    time_outcome(machine, value)
}

fn compare<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let one = to_temporal_time(machine, arg(args, 0), Value::UNDEFINED)?;
    let two = to_temporal_time(machine, arg(args, 1), Value::UNDEFINED)?;
    number_outcome(f64::from(one.cmp(&two) as i8))
}

macro_rules! field_getter {
    ($($name:ident),+) => {
        $(fn $name<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            number_outcome(f64::from(this_time(machine, this)?.$name))
        })+
    };
}

field_getter!(hour, minute, second, millisecond, microsecond, nanosecond);

fn add<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time = this_time(machine, this)?;
    let duration = to_temporal_duration(machine, arg(args, 0))?;
    time_outcome(machine, time.add(&duration))
}

fn subtract<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time = this_time(machine, this)?;
    let duration = to_temporal_duration(machine, arg(args, 0))?;
    time_outcome(machine, time.subtract(&duration))
}

fn with<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time = this_time(machine, this)?;
    let like = arg(args, 0);
    require_partial_temporal_object(machine, like)?;
    let partial = prepare_partial_fields(machine, &CalendarId::iso8601(), like, FieldNames::TIME)?;
    let options = get_options_object(machine, arg(args, 1))?;
    let overflow = overflow_option(machine, options)?;
    let fields = super::fields::CalendarFields::default()
        .with_time(time)
        .merged_with(partial);
    let value = time_from_fields(machine, &fields, overflow)?;
    time_outcome(machine, value)
}

/// DifferenceTemporalPlainTime.
fn difference<H: Host>(
    machine: &mut Machine<'_, H>,
    since: bool,
    time: PlainTime,
    other: Value,
    options: Value,
) -> Result<BuiltinOutcome, EvalFailure> {
    let other = to_temporal_time(machine, other, Value::UNDEFINED)?;
    let options = get_options_object(machine, options)?;
    let settings = difference_settings(
        machine,
        since,
        options,
        DifferencePolicy {
            group: TIME_UNITS,
            disallowed: &[],
            fallback_smallest: Unit::Nanosecond,
            smallest_largest_default: Unit::Hour,
        },
    )?;
    let value = time
        .until(
            other,
            settings.largest_unit,
            settings.smallest_unit,
            settings.rounding_increment,
            settings.rounding_mode,
        )
        .or_throw(machine)?;
    let value = if since { value.negated() } else { value };
    create(machine, TemporalObject::Duration(value)).map(BuiltinOutcome::Value)
}

fn until<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time = this_time(machine, this)?;
    difference(machine, false, time, arg(args, 0), arg(args, 1))
}

fn since<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time = this_time(machine, this)?;
    difference(machine, true, time, arg(args, 0), arg(args, 1))
}

fn round<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time = this_time(machine, this)?;
    let round_to = unit_argument(machine, arg(args, 0))?;
    let increment = rounding_increment_option(machine, round_to.options)?;
    let mode = rounding_mode_option(machine, round_to.options, RoundingMode::HalfExpand)?;
    let smallest = round_to.required_unit(machine, "smallestUnit")?;
    validate_unit_value(machine, smallest, TIME_UNITS, None)?;
    let UnitOption::Unit(unit) = smallest else {
        return Err(range_error(machine, "smallestUnit is required"));
    };
    validate_rounding_increment(unit, increment, false).or_throw(machine)?;
    let value = time.round(unit, increment, mode).or_throw(machine)?;
    time_outcome(machine, value)
}

fn equals<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time = this_time(machine, this)?;
    let other = to_temporal_time(machine, arg(args, 0), Value::UNDEFINED)?;
    Ok(BuiltinOutcome::Value(Value::boolean(time == other)))
}

fn to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time = this_time(machine, this)?;
    let options = get_options_object(machine, arg(args, 0))?;
    let digits = fractional_second_digits_option(machine, options)?;
    let rounding_mode = rounding_mode_option(machine, options, RoundingMode::Trunc)?;
    let smallest = unit_valued_option(machine, options, "smallestUnit")?;
    validate_unit_value(machine, smallest, TIME_UNITS, None)?;
    if smallest == UnitOption::Unit(Unit::Hour) {
        return Err(range_error(machine, "smallestUnit must not be hour"));
    }
    let smallest_unit = match smallest {
        UnitOption::Unit(unit) => Some(unit),
        _ => None,
    };
    let text = serialize_plain_time(
        &time,
        ToStringRoundingOptions {
            smallest_unit,
            fractional_second_digits: digits,
            rounding_mode,
        },
    )
    .or_throw(machine)?;
    string_outcome(machine, &text)
}

fn to_json<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let text = this_time(machine, this)?.format(Precision::Auto);
    string_outcome(machine, &text)
}

fn to_locale_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    this_time(machine, this)?;
    temporal_to_locale_string(machine, this, arg(args, 0), arg(args, 1))
}
