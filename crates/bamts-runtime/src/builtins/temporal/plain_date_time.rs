//! `Temporal.PlainDateTime`.

use bamts_native::Value;

use super::fields::{
    CalendarFields, FieldNames, calendar_argument, date_time_from_fields, iso_year,
    prepare_partial_fields, providers, require_partial_temporal_object, to_calendar_identifier,
    to_integer_with_truncation, to_temporal_date_time, to_temporal_duration, to_temporal_time,
    to_time_zone_identifier,
};
use super::options::{
    ALL_UNITS, DifferencePolicy, TIME_UNITS, UnitOption, difference_settings,
    disambiguation_option, fractional_second_digits_option, get_options_object, overflow_option,
    rounding_increment_option, rounding_mode_option, show_calendar_option, unit_argument,
    unit_valued_option, validate_unit_value,
};
use super::{
    Class, Getter, OrThrow, arg, construct, create, install_class, number_outcome, range_error,
    require_new, string_outcome, temporal_record, type_error, value_of_throws,
};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::temporal::instant_duration::{
    Overflow, Precision, RoundingMode, Unit, validate_rounding_increment,
};
use crate::temporal::now_rounding::{
    ShowCalendar, ToStringRoundingOptions, serialize_plain_date_time,
};
use crate::temporal::plain_types::{PlainDate, PlainDateTime, PlainTime};
use crate::temporal::zoned_date_time::{CalendarId, ResolveOptions, ZonedDateTime};
use crate::temporal::{TemporalKind, TemporalObject};
use crate::{EvalFailure, HeapEntry, Host, Machine};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    builtins: &mut BuiltinTable<H>,
    namespace: Value,
) {
    let date_getters: [Getter<H>; 16] = date_getter_table!(H);
    let time_getters: [Getter<H>; 6] = [
        ("hour", "get hour", hour::<H>),
        ("minute", "get minute", minute::<H>),
        ("second", "get second", second::<H>),
        ("millisecond", "get millisecond", millisecond::<H>),
        ("microsecond", "get microsecond", microsecond::<H>),
        ("nanosecond", "get nanosecond", nanosecond::<H>),
    ];
    let getters: Vec<Getter<H>> = date_getters.iter().chain(&time_getters).copied().collect();
    install_class(
        heap,
        builtins,
        namespace,
        &Class {
            kind: TemporalKind::PlainDateTime,
            name: "PlainDateTime",
            tag: "Temporal.PlainDateTime",
            length: 3,
            constructor: constructor::<H>,
            statics: &[("from", 1, from::<H>), ("compare", 2, compare::<H>)],
            getters: &getters,
            methods: &[
                ("with", 1, with::<H>),
                ("withPlainTime", 0, with_plain_time::<H>),
                ("withCalendar", 1, with_calendar::<H>),
                ("add", 1, add::<H>),
                ("subtract", 1, subtract::<H>),
                ("until", 1, until::<H>),
                ("since", 1, since::<H>),
                ("round", 1, round::<H>),
                ("equals", 1, equals::<H>),
                ("toString", 0, to_string::<H>),
                ("toLocaleString", 0, to_json::<H>),
                ("toJSON", 0, to_json::<H>),
                ("valueOf", 0, value_of_throws::<H>),
                ("toZonedDateTime", 1, to_zoned_date_time::<H>),
                ("toPlainDate", 0, to_plain_date::<H>),
                ("toPlainTime", 0, to_plain_time::<H>),
            ],
        },
    );
}

fn this_date_time<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
) -> Result<(PlainDateTime, CalendarId), EvalFailure> {
    match temporal_record(machine, this)? {
        Some(TemporalObject::PlainDateTime { value, calendar }) => Ok((value, calendar)),
        _ => Err(type_error(
            machine,
            "receiver is not a Temporal.PlainDateTime",
        )),
    }
}

/// The date behind the shared calendar accessors.
fn accessor_date<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
) -> Result<(PlainDate, CalendarId), EvalFailure> {
    let (value, calendar) = this_date_time(machine, this)?;
    Ok((value.date, calendar))
}

date_accessors!(accessor_date);

macro_rules! time_getter {
    ($($name:ident),+) => {
        $(fn $name<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            number_outcome(f64::from(this_date_time(machine, this)?.0.time.$name))
        })+
    };
}

time_getter!(hour, minute, second, millisecond, microsecond, nanosecond);

fn date_time_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    value: PlainDateTime,
    calendar: CalendarId,
) -> Result<BuiltinOutcome, EvalFailure> {
    create(machine, TemporalObject::PlainDateTime { value, calendar }).map(BuiltinOutcome::Value)
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_new(machine, constructing, "PlainDateTime")?;
    let year = to_integer_with_truncation(machine, arg(args, 0))?;
    let month = to_integer_with_truncation(machine, arg(args, 1))?;
    let day = to_integer_with_truncation(machine, arg(args, 2))?;
    let mut time = [0_f64; 6];
    for (index, field) in time.iter_mut().enumerate() {
        let value = arg(args, index + 3);
        if value != Value::UNDEFINED {
            *field = to_integer_with_truncation(machine, value)?;
        }
    }
    let calendar = calendar_argument(machine, arg(args, 9))?;
    let year = iso_year(machine, year)?;
    let value = PlainDateTime::new(
        year,
        month as i64,
        day as i64,
        time.map(|field| field as i64),
        Overflow::Reject,
    )
    .or_throw(machine)?;
    construct(machine, TemporalObject::PlainDateTime { value, calendar })
}

fn from<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = to_temporal_date_time(machine, arg(args, 0), arg(args, 1))?;
    date_time_outcome(machine, value, calendar)
}

fn compare<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (one, _) = to_temporal_date_time(machine, arg(args, 0), Value::UNDEFINED)?;
    let (two, _) = to_temporal_date_time(machine, arg(args, 1), Value::UNDEFINED)?;
    number_outcome(f64::from(one.cmp(&two) as i8))
}

fn with<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date_time, calendar) = this_date_time(machine, this)?;
    let like = arg(args, 0);
    require_partial_temporal_object(machine, like)?;
    let names = FieldNames::DATE.with(FieldNames::TIME);
    let partial = prepare_partial_fields(machine, like, names)?;
    let fields = CalendarFields::from_date(date_time.date)
        .with_time(date_time.time)
        .merged_with(partial);
    let options = get_options_object(machine, arg(args, 1))?;
    let overflow = overflow_option(machine, options)?;
    let value = date_time_from_fields(machine, &fields, overflow)?;
    let value = PlainDateTime::from_parts(value.date, value.time).or_throw(machine)?;
    date_time_outcome(machine, value, calendar)
}

fn with_plain_time<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date_time, calendar) = this_date_time(machine, this)?;
    let like = arg(args, 0);
    let time = if like == Value::UNDEFINED {
        PlainTime::midnight()
    } else {
        to_temporal_time(machine, like, Value::UNDEFINED)?
    };
    let value = PlainDateTime::from_parts(date_time.date, time).or_throw(machine)?;
    date_time_outcome(machine, value, calendar)
}

fn with_calendar<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date_time, _) = this_date_time(machine, this)?;
    let calendar = to_calendar_identifier(machine, arg(args, 0))?;
    date_time_outcome(machine, date_time, calendar)
}

/// AddDurationToDateTime.
fn add_duration<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    subtract: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date_time, calendar) = this_date_time(machine, this)?;
    let duration = to_temporal_duration(machine, arg(args, 0))?;
    let options = get_options_object(machine, arg(args, 1))?;
    let overflow = overflow_option(machine, options)?;
    let value = if subtract {
        date_time.subtract(&duration, overflow)
    } else {
        date_time.add(&duration, overflow)
    }
    .or_throw(machine)?;
    date_time_outcome(machine, value, calendar)
}

fn add<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    add_duration(machine, this, args, false)
}

fn subtract<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    add_duration(machine, this, args, true)
}

/// DifferenceTemporalPlainDateTime.
fn difference<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    since: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date_time, calendar) = this_date_time(machine, this)?;
    let (other, other_calendar) = to_temporal_date_time(machine, arg(args, 0), Value::UNDEFINED)?;
    if calendar != other_calendar {
        return Err(range_error(machine, "calendars must match"));
    }
    let options = get_options_object(machine, arg(args, 1))?;
    let settings = difference_settings(
        machine,
        since,
        options,
        DifferencePolicy {
            group: ALL_UNITS,
            disallowed: &[],
            fallback_smallest: Unit::Nanosecond,
            smallest_largest_default: Unit::Day,
        },
    )?;
    let value = date_time
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
    difference(machine, this, args, false)
}

fn since<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    difference(machine, this, args, true)
}

fn round<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date_time, calendar) = this_date_time(machine, this)?;
    let round_to = unit_argument(machine, arg(args, 0))?;
    let increment = rounding_increment_option(machine, round_to.options)?;
    let mode = rounding_mode_option(machine, round_to.options, RoundingMode::HalfExpand)?;
    let smallest = round_to.required_unit(machine, "smallestUnit")?;
    validate_unit_value(
        machine,
        smallest,
        TIME_UNITS,
        Some(UnitOption::Unit(Unit::Day)),
    )?;
    let UnitOption::Unit(unit) = smallest else {
        return Err(range_error(machine, "smallestUnit is required"));
    };
    if unit == Unit::Day {
        if increment != 1 {
            return Err(range_error(
                machine,
                "roundingIncrement must be 1 when rounding to day",
            ));
        }
    } else {
        validate_rounding_increment(unit, increment, false).or_throw(machine)?;
    }
    let value = date_time.round(unit, increment, mode).or_throw(machine)?;
    date_time_outcome(machine, value, calendar)
}

fn equals<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date_time, calendar) = this_date_time(machine, this)?;
    let (other, other_calendar) = to_temporal_date_time(machine, arg(args, 0), Value::UNDEFINED)?;
    let equal = date_time == other && calendar == other_calendar;
    Ok(BuiltinOutcome::Value(Value::boolean(equal)))
}

fn to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date_time, calendar) = this_date_time(machine, this)?;
    let options = get_options_object(machine, arg(args, 0))?;
    let show = show_calendar_option(machine, options)?;
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
    let text = serialize_plain_date_time(
        &date_time,
        calendar.as_str(),
        show,
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
    let (date_time, calendar) = this_date_time(machine, this)?;
    let text = crate::temporal::now_rounding::format_calendar_annotation(
        calendar.as_str(),
        ShowCalendar::Auto,
    )
    .or_throw(machine)?;
    let text = format!("{}{text}", date_time.format(Precision::Auto));
    string_outcome(machine, &text)
}

fn to_zoned_date_time<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date_time, calendar) = this_date_time(machine, this)?;
    let time_zone = to_time_zone_identifier(machine, arg(args, 0))?;
    let options = get_options_object(machine, arg(args, 1))?;
    let disambiguation = disambiguation_option(machine, options)?;
    let value = ZonedDateTime::from_local(
        &providers(),
        date_time,
        time_zone,
        calendar,
        None,
        ResolveOptions {
            disambiguation,
            ..ResolveOptions::default()
        },
    )
    .or_throw(machine)?;
    create(machine, TemporalObject::ZonedDateTime(value)).map(BuiltinOutcome::Value)
}

fn to_plain_date<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date_time, calendar) = this_date_time(machine, this)?;
    create(
        machine,
        TemporalObject::PlainDate {
            value: date_time.to_plain_date(),
            calendar,
        },
    )
    .map(BuiltinOutcome::Value)
}

fn to_plain_time<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date_time, _) = this_date_time(machine, this)?;
    create(
        machine,
        TemporalObject::PlainTime(date_time.to_plain_time()),
    )
    .map(BuiltinOutcome::Value)
}
