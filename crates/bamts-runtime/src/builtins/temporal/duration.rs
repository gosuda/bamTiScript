//! `Temporal.Duration`.

use std::cmp::Ordering;

use bamts_native::Value;

use super::super::intl::duration_to_locale_string;
use super::fields::{
    RelativeTo, providers, relative_to_option, to_integer_if_integral, to_partial_duration,
    to_temporal_duration,
};
use super::options::{
    ALL_UNITS, TIME_UNITS, UnitOption, fractional_second_digits_option, get_options_object,
    rounding_increment_option, rounding_mode_option, seconds_precision, unit_argument,
    unit_valued_option, validate_unit_value,
};
use super::{
    Class, OrThrow, arg, construct, create, install_class, number_outcome, range_error,
    require_new, string_outcome, temporal_record, type_error, value_of_throws,
};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::temporal::instant_duration::{
    Duration, Overflow, RoundingMode, Unit, validate_rounding_increment,
};
use crate::temporal::relative::{
    DifferenceRounding, InternalDuration, add_time_duration, compare_with_days, date_duration_days,
    difference_plain_date_time_with_rounding, difference_plain_date_time_with_total,
    difference_zoned_date_time_with_rounding, difference_zoned_date_time_with_total,
    plain_relative_endpoints, round_time_duration, temporal_duration_from_internal,
};
use crate::temporal::zoned_date_time::add_zoned_date_time;
use crate::temporal::{TemporalKind, TemporalObject};
use crate::{EvalFailure, HeapEntry, Host, Machine};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    builtins: &mut BuiltinTable<H>,
    namespace: Value,
) {
    install_class(
        heap,
        atoms,
        builtins,
        namespace,
        &Class {
            kind: TemporalKind::Duration,
            name: "Duration",
            tag: "Temporal.Duration",
            length: 0,
            constructor: constructor::<H>,
            statics: &[("from", 1, from::<H>), ("compare", 2, compare::<H>)],
            getters: &[
                ("years", "get years", years::<H>),
                ("months", "get months", months::<H>),
                ("weeks", "get weeks", weeks::<H>),
                ("days", "get days", days::<H>),
                ("hours", "get hours", hours::<H>),
                ("minutes", "get minutes", minutes::<H>),
                ("seconds", "get seconds", seconds::<H>),
                ("milliseconds", "get milliseconds", milliseconds::<H>),
                ("microseconds", "get microseconds", microseconds::<H>),
                ("nanoseconds", "get nanoseconds", nanoseconds::<H>),
                ("sign", "get sign", sign::<H>),
                ("blank", "get blank", blank::<H>),
            ],
            methods: &[
                ("with", 1, with::<H>),
                ("negated", 0, negated::<H>),
                ("abs", 0, abs::<H>),
                ("add", 1, add::<H>),
                ("subtract", 1, subtract::<H>),
                ("round", 1, round::<H>),
                ("total", 1, total::<H>),
                ("toString", 0, to_string::<H>),
                ("toJSON", 0, to_json::<H>),
                ("toLocaleString", 0, to_locale_string::<H>),
                ("valueOf", 0, value_of_throws::<H>),
            ],
        },
    );
}

fn this_duration<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
) -> Result<Duration, EvalFailure> {
    match temporal_record(machine, this)? {
        Some(TemporalObject::Duration(value)) => Ok(value),
        _ => Err(type_error(machine, "receiver is not a Temporal.Duration")),
    }
}

fn duration_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Duration,
) -> Result<BuiltinOutcome, EvalFailure> {
    create(machine, TemporalObject::Duration(value)).map(BuiltinOutcome::Value)
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_new(machine, constructing, "Duration")?;
    let mut fields = [0_i128; 10];
    for (index, field) in fields.iter_mut().enumerate() {
        let value = arg(args, index);
        if value != Value::UNDEFINED {
            *field = to_integer_if_integral(machine, value)?;
        }
    }
    let value = Duration::new(fields).or_throw(machine)?;
    construct(machine, TemporalObject::Duration(value))
}

fn from<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = to_temporal_duration(machine, arg(args, 0))?;
    duration_outcome(machine, value)
}

fn compare<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let one = to_temporal_duration(machine, arg(args, 0))?;
    let two = to_temporal_duration(machine, arg(args, 1))?;
    let options = get_options_object(machine, arg(args, 2))?;
    let relative_to = relative_to_option(machine, options)?;
    if one == two {
        return number_outcome(0.0);
    }
    let largest_one = one.default_largest_unit();
    let largest_two = two.default_largest_unit();
    let internal_one = InternalDuration::from_duration(&one);
    let internal_two = InternalDuration::from_duration(&two);
    if let RelativeTo::Zoned(zoned) = &relative_to
        && (largest_one <= Unit::Day || largest_two <= Unit::Day)
    {
        let core = providers();
        let after = |internal| {
            add_zoned_date_time(
                &core,
                zoned.to_instant(),
                zoned.time_zone_id(),
                zoned.calendar_id(),
                internal,
                Overflow::Constrain,
            )
        };
        let after_one = after(internal_one).or_throw(machine)?;
        let after_two = after(internal_two).or_throw(machine)?;
        return ordering_outcome(after_one.cmp(&after_two));
    }
    let (days_one, days_two) = if largest_one < Unit::Day || largest_two < Unit::Day {
        let RelativeTo::Plain(date, calendar) = &relative_to else {
            return Err(range_error(
                machine,
                "comparing calendar units requires relativeTo",
            ));
        };
        let core = providers();
        (
            date_duration_days(&core, &internal_one.date, *date, calendar).or_throw(machine)?,
            date_duration_days(&core, &internal_two.date, *date, calendar).or_throw(machine)?,
        )
    } else {
        (one.days, two.days)
    };
    let ordering =
        compare_with_days(&internal_one, days_one, &internal_two, days_two).or_throw(machine)?;
    ordering_outcome(ordering)
}

fn ordering_outcome(ordering: Ordering) -> Result<BuiltinOutcome, EvalFailure> {
    number_outcome(match ordering {
        Ordering::Less => -1.0,
        Ordering::Equal => 0.0,
        Ordering::Greater => 1.0,
    })
}

macro_rules! field_getter {
    ($($name:ident),+) => {
        $(fn $name<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            number_outcome(this_duration(machine, this)?.$name as f64)
        })+
    };
}

field_getter!(
    years,
    months,
    weeks,
    days,
    hours,
    minutes,
    seconds,
    milliseconds,
    microseconds,
    nanoseconds
);

fn sign<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    number_outcome(this_duration(machine, this)?.sign() as f64)
}

fn blank<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = this_duration(machine, this)?;
    Ok(BuiltinOutcome::Value(Value::boolean(value.is_zero())))
}

fn with<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = this_duration(machine, this)?;
    let partial = to_partial_duration(machine, arg(args, 0))?;
    let mut fields = value.fields();
    for (field, replacement) in fields.iter_mut().zip(partial) {
        if let Some(replacement) = replacement {
            *field = replacement;
        }
    }
    let result = Duration::new(fields).or_throw(machine)?;
    duration_outcome(machine, result)
}

fn negated<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = this_duration(machine, this)?.negated();
    duration_outcome(machine, value)
}

fn abs<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = this_duration(machine, this)?.abs();
    duration_outcome(machine, value)
}

/// AddDurations: only durations of time and days can be summed without a
/// starting point, and days count as 24 hours.
fn add_durations<H: Host>(
    machine: &mut Machine<'_, H>,
    one: Duration,
    other: Value,
    subtract: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let mut two = to_temporal_duration(machine, other)?;
    if subtract {
        two = two.negated();
    }
    let largest_unit = one
        .default_largest_unit()
        .larger(two.default_largest_unit());
    if largest_unit < Unit::Day {
        return Err(range_error(
            machine,
            "adding calendar units requires a starting point",
        ));
    }
    let time = add_time_duration(
        one.total_nanoseconds_with_24_hour_days(),
        two.total_nanoseconds_with_24_hour_days(),
    )
    .or_throw(machine)?;
    let result = temporal_duration_from_internal(
        InternalDuration::new(Duration::default(), time),
        largest_unit,
    )
    .or_throw(machine)?;
    duration_outcome(machine, result)
}

fn add<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = this_duration(machine, this)?;
    add_durations(machine, value, arg(args, 0), false)
}

fn subtract<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = this_duration(machine, this)?;
    add_durations(machine, value, arg(args, 0), true)
}

fn round<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let duration = this_duration(machine, this)?;
    let round_to = unit_argument(machine, arg(args, 0))?;
    let options = round_to.options;
    let largest = unit_valued_option(machine, options, "largestUnit")?;
    let relative_to = relative_to_option(machine, options)?;
    let increment = rounding_increment_option(machine, options)?;
    let mode = rounding_mode_option(machine, options, RoundingMode::HalfExpand)?;
    let smallest = round_to.unit(machine, "smallestUnit")?;
    validate_unit_value(machine, largest, ALL_UNITS, Some(UnitOption::Auto))?;
    validate_unit_value(machine, smallest, ALL_UNITS, None)?;
    let smallest_present = smallest != UnitOption::Unset;
    let smallest_unit = match smallest {
        UnitOption::Unit(unit) => unit,
        _ => Unit::Nanosecond,
    };
    let existing_largest = duration.default_largest_unit();
    let default_largest = existing_largest.larger(smallest_unit);
    let largest_present = largest != UnitOption::Unset;
    let largest_unit = match largest {
        UnitOption::Unit(unit) => unit,
        _ => default_largest,
    };
    if !smallest_present && !largest_present {
        return Err(range_error(
            machine,
            "at least one of smallestUnit or largestUnit is required",
        ));
    }
    if largest_unit.larger(smallest_unit) != largest_unit {
        return Err(range_error(
            machine,
            "smallestUnit must not be larger than largestUnit",
        ));
    }
    if smallest_unit.max_rounding_increment().is_some() {
        validate_rounding_increment(smallest_unit, increment, false).or_throw(machine)?;
    }
    if increment > 1 && largest_unit != smallest_unit && smallest_unit <= Unit::Day {
        return Err(range_error(
            machine,
            "roundingIncrement above 1 requires smallestUnit to equal largestUnit \
             for a date unit",
        ));
    }
    let rounding = DifferenceRounding {
        largest_unit,
        smallest_unit,
        increment,
        mode,
    };
    let core = providers();
    let result = match relative_to {
        RelativeTo::Zoned(zoned) => {
            let origin = zoned.epoch_nanoseconds();
            let target = add_zoned_date_time(
                &core,
                zoned.to_instant(),
                zoned.time_zone_id(),
                zoned.calendar_id(),
                InternalDuration::from_duration(&duration),
                Overflow::Constrain,
            )
            .or_throw(machine)?;
            let internal = difference_zoned_date_time_with_rounding(
                &core,
                origin,
                target.epoch_nanoseconds(),
                zoned.time_zone_id(),
                zoned.calendar_id(),
                rounding,
            )
            .or_throw(machine)?;
            let balance_to = if largest_unit <= Unit::Day {
                Unit::Hour
            } else {
                largest_unit
            };
            temporal_duration_from_internal(internal, balance_to)
        }
        RelativeTo::Plain(date, calendar) => {
            let (start, target) =
                plain_relative_endpoints(&core, date, &calendar, &duration).or_throw(machine)?;
            let internal =
                difference_plain_date_time_with_rounding(&core, start, target, &calendar, rounding)
                    .or_throw(machine)?;
            temporal_duration_from_internal(internal, largest_unit)
        }
        RelativeTo::None => {
            if existing_largest < Unit::Day || largest_unit < Unit::Day {
                return Err(range_error(
                    machine,
                    "rounding calendar units requires relativeTo",
                ));
            }
            duration.round(smallest_unit, largest_unit, increment, mode)
        }
    }
    .or_throw(machine)?;
    duration_outcome(machine, result)
}

fn total<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let duration = this_duration(machine, this)?;
    let total_of = unit_argument(machine, arg(args, 0))?;
    let relative_to = relative_to_option(machine, total_of.options)?;
    let unit = total_of.required_unit(machine, "unit")?;
    validate_unit_value(machine, unit, ALL_UNITS, None)?;
    let UnitOption::Unit(unit) = unit else {
        return Err(range_error(machine, "unit is required"));
    };
    let core = providers();
    let result = match relative_to {
        RelativeTo::Zoned(zoned) => {
            let origin = zoned.epoch_nanoseconds();
            let target = add_zoned_date_time(
                &core,
                zoned.to_instant(),
                zoned.time_zone_id(),
                zoned.calendar_id(),
                InternalDuration::from_duration(&duration),
                Overflow::Constrain,
            )
            .or_throw(machine)?;
            difference_zoned_date_time_with_total(
                &core,
                origin,
                target.epoch_nanoseconds(),
                zoned.time_zone_id(),
                zoned.calendar_id(),
                unit,
            )
        }
        RelativeTo::Plain(date, calendar) => {
            let (start, target) =
                plain_relative_endpoints(&core, date, &calendar, &duration).or_throw(machine)?;
            difference_plain_date_time_with_total(&core, start, target, &calendar, unit)
        }
        RelativeTo::None => duration.total_as_f64(unit),
    }
    .or_throw(machine)?;
    number_outcome(result)
}

fn to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let duration = this_duration(machine, this)?;
    let options = get_options_object(machine, arg(args, 0))?;
    let digits = fractional_second_digits_option(machine, options)?;
    let mode = rounding_mode_option(machine, options, RoundingMode::Trunc)?;
    let smallest = unit_valued_option(machine, options, "smallestUnit")?;
    validate_unit_value(machine, smallest, TIME_UNITS, None)?;
    if matches!(smallest, UnitOption::Unit(Unit::Hour | Unit::Minute)) {
        return Err(range_error(
            machine,
            "smallestUnit must be second or smaller",
        ));
    }
    let precision = seconds_precision(machine, smallest, digits)?;
    if precision.unit == Unit::Nanosecond && precision.increment == 1 {
        return string_outcome(
            machine,
            &duration.format_with_precision(precision.precision),
        );
    }
    let internal = InternalDuration::from_duration(&duration);
    let time = round_time_duration(internal.time, precision.increment, precision.unit, mode)
        .or_throw(machine)?;
    let rounded = temporal_duration_from_internal(
        InternalDuration::new(internal.date, time),
        duration.default_largest_unit().larger(Unit::Second),
    )
    .or_throw(machine)?;
    string_outcome(machine, &rounded.format_with_precision(precision.precision))
}

fn to_json<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let text = this_duration(machine, this)?.format();
    string_outcome(machine, &text)
}

fn to_locale_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let duration = this_duration(machine, this)?;
    duration_to_locale_string(machine, &duration, arg(args, 0), arg(args, 1))
}
