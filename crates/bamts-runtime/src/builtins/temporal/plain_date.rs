//! `Temporal.PlainDate`.

use bamts_native::Value;

use super::fields::{
    CalendarFields, FieldNames, calendar_argument, iso_year, prepare_partial_fields,
    require_partial_temporal_object, resolved_date_fields, to_calendar_identifier,
    to_integer_with_truncation, to_temporal_date, to_temporal_duration, to_temporal_time,
    to_time_zone_identifier,
};
use super::options::{
    DATE_UNITS, DifferencePolicy, difference_settings, get_options_object, overflow_option,
    show_calendar_option,
};
use super::{
    Class, OrThrow, arg, construct, create, install_class, is_object, number_outcome, range_error,
    require_new, string_outcome, temporal_record, type_error, value_of_throws,
};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::temporal::instant_duration::{Instant, Overflow, Unit};
use crate::temporal::now_rounding::{ShowCalendar, format_calendar_annotation};
use crate::temporal::plain_types::{PlainDate, PlainDateTime, PlainTime};
use crate::temporal::relative::date_duration_without_time;
use crate::temporal::zoned_date_time::{
    CalendarId, FixedOffsetTimeZones, ZonedDateTime, epoch_nanoseconds_for, start_of_day,
};
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
            kind: TemporalKind::PlainDate,
            name: "PlainDate",
            tag: "Temporal.PlainDate",
            length: 3,
            constructor: constructor::<H>,
            statics: &[("from", 1, from::<H>), ("compare", 2, compare::<H>)],
            getters: &date_getter_table!(H),
            methods: &[
                ("toPlainYearMonth", 0, to_plain_year_month::<H>),
                ("toPlainMonthDay", 0, to_plain_month_day::<H>),
                ("add", 1, add::<H>),
                ("subtract", 1, subtract::<H>),
                ("with", 1, with::<H>),
                ("withCalendar", 1, with_calendar::<H>),
                ("until", 1, until::<H>),
                ("since", 1, since::<H>),
                ("equals", 1, equals::<H>),
                ("toPlainDateTime", 0, to_plain_date_time::<H>),
                ("toZonedDateTime", 1, to_zoned_date_time::<H>),
                ("toString", 0, to_string::<H>),
                ("toLocaleString", 0, to_json::<H>),
                ("toJSON", 0, to_json::<H>),
                ("valueOf", 0, value_of_throws::<H>),
            ],
        },
    );
}

fn this_date<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
) -> Result<(PlainDate, CalendarId), EvalFailure> {
    match temporal_record(machine, this)? {
        Some(TemporalObject::PlainDate { value, calendar }) => Ok((value, calendar)),
        _ => Err(type_error(machine, "receiver is not a Temporal.PlainDate")),
    }
}

/// The date behind the shared calendar accessors.
fn accessor_date<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
) -> Result<(PlainDate, CalendarId), EvalFailure> {
    this_date(machine, this)
}

date_accessors!(accessor_date);

fn date_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    value: PlainDate,
    calendar: CalendarId,
) -> Result<BuiltinOutcome, EvalFailure> {
    create(machine, TemporalObject::PlainDate { value, calendar }).map(BuiltinOutcome::Value)
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_new(machine, constructing, "PlainDate")?;
    let year = to_integer_with_truncation(machine, arg(args, 0))?;
    let month = to_integer_with_truncation(machine, arg(args, 1))?;
    let day = to_integer_with_truncation(machine, arg(args, 2))?;
    let calendar = calendar_argument(machine, arg(args, 3))?;
    let year = iso_year(machine, year)?;
    let value =
        PlainDate::new(year, month as i64, day as i64, Overflow::Reject).or_throw(machine)?;
    construct(machine, TemporalObject::PlainDate { value, calendar })
}

fn from<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = to_temporal_date(machine, arg(args, 0), arg(args, 1))?;
    date_outcome(machine, value, calendar)
}

fn compare<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (one, _) = to_temporal_date(machine, arg(args, 0), Value::UNDEFINED)?;
    let (two, _) = to_temporal_date(machine, arg(args, 1), Value::UNDEFINED)?;
    number_outcome(f64::from(one.cmp(&two) as i8))
}

fn to_plain_year_month<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date, calendar) = this_date(machine, this)?;
    let value = date.to_plain_year_month();
    create(machine, TemporalObject::PlainYearMonth { value, calendar }).map(BuiltinOutcome::Value)
}

fn to_plain_month_day<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date, calendar) = this_date(machine, this)?;
    let value = date.to_plain_month_day();
    create(machine, TemporalObject::PlainMonthDay { value, calendar }).map(BuiltinOutcome::Value)
}

/// AddDurationToDate: time folds into whole days first.
fn add_duration<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    subtract: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date, calendar) = this_date(machine, this)?;
    let duration = to_temporal_duration(machine, arg(args, 0))?;
    let date_duration = date_duration_without_time(&duration).or_throw(machine)?;
    let options = get_options_object(machine, arg(args, 1))?;
    let overflow = overflow_option(machine, options)?;
    let value = if subtract {
        date.subtract(&date_duration, overflow)
    } else {
        date.add(&date_duration, overflow)
    }
    .or_throw(machine)?;
    date_outcome(machine, value, calendar)
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

fn with<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date, calendar) = this_date(machine, this)?;
    let like = arg(args, 0);
    require_partial_temporal_object(machine, like)?;
    let partial = prepare_partial_fields(machine, like, FieldNames::DATE)?;
    let fields = CalendarFields::from_date(date).merged_with(partial);
    let options = get_options_object(machine, arg(args, 1))?;
    let overflow = overflow_option(machine, options)?;
    let (year, month, day) = resolved_date_fields(machine, &fields)?;
    let value = date
        .with(Some(year), Some(month), Some(day), overflow)
        .or_throw(machine)?;
    date_outcome(machine, value, calendar)
}

fn with_calendar<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date, _) = this_date(machine, this)?;
    let calendar = to_calendar_identifier(machine, arg(args, 0))?;
    date_outcome(machine, date, calendar)
}

/// DifferenceTemporalPlainDate.
fn difference<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    since: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date, calendar) = this_date(machine, this)?;
    let (other, other_calendar) = to_temporal_date(machine, arg(args, 0), Value::UNDEFINED)?;
    if calendar != other_calendar {
        return Err(range_error(machine, "calendars must match"));
    }
    let options = get_options_object(machine, arg(args, 1))?;
    let settings = difference_settings(
        machine,
        since,
        options,
        DifferencePolicy {
            group: DATE_UNITS,
            disallowed: &[],
            fallback_smallest: Unit::Day,
            smallest_largest_default: Unit::Day,
        },
    )?;
    let value = date
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

fn equals<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date, calendar) = this_date(machine, this)?;
    let (other, other_calendar) = to_temporal_date(machine, arg(args, 0), Value::UNDEFINED)?;
    let equal = date == other && calendar == other_calendar;
    Ok(BuiltinOutcome::Value(Value::boolean(equal)))
}

fn to_plain_date_time<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date, calendar) = this_date(machine, this)?;
    let time = arg(args, 0);
    let time = if time == Value::UNDEFINED {
        PlainTime::midnight()
    } else {
        to_temporal_time(machine, time, Value::UNDEFINED)?
    };
    let value = date.to_plain_date_time(time).or_throw(machine)?;
    create(machine, TemporalObject::PlainDateTime { value, calendar }).map(BuiltinOutcome::Value)
}

fn to_zoned_date_time<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date, calendar) = this_date(machine, this)?;
    let item = arg(args, 0);
    let mut plain_time = Value::UNDEFINED;
    let time_zone = if is_object(machine, item)? {
        let like = machine.get_named_property(item, "timeZone")?;
        if like == Value::UNDEFINED {
            to_time_zone_identifier(machine, item)?
        } else {
            let time_zone = to_time_zone_identifier(machine, like)?;
            plain_time = machine.get_named_property(item, "plainTime")?;
            time_zone
        }
    } else {
        to_time_zone_identifier(machine, item)?
    };
    let instant = if plain_time == Value::UNDEFINED {
        start_of_day(&FixedOffsetTimeZones, &time_zone, date).or_throw(machine)?
    } else {
        let time = to_temporal_time(machine, plain_time, Value::UNDEFINED)?;
        let local = PlainDateTime::from_parts(date, time).or_throw(machine)?;
        let nanoseconds =
            epoch_nanoseconds_for(&FixedOffsetTimeZones, &time_zone, local).or_throw(machine)?;
        Instant::from_epoch_nanoseconds(nanoseconds).or_throw(machine)?
    };
    let value = ZonedDateTime::from_instant(instant, time_zone, calendar);
    create(machine, TemporalObject::ZonedDateTime(value)).map(BuiltinOutcome::Value)
}

fn date_text<H: Host>(
    machine: &mut Machine<'_, H>,
    date: PlainDate,
    calendar: &CalendarId,
    show: ShowCalendar,
) -> Result<String, EvalFailure> {
    let annotation = format_calendar_annotation(calendar.as_str(), show).or_throw(machine)?;
    Ok(format!("{}{annotation}", date.format()))
}

fn to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date, calendar) = this_date(machine, this)?;
    let options = get_options_object(machine, arg(args, 0))?;
    let show = show_calendar_option(machine, options)?;
    let text = date_text(machine, date, &calendar, show)?;
    string_outcome(machine, &text)
}

fn to_json<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (date, calendar) = this_date(machine, this)?;
    let text = date_text(machine, date, &calendar, ShowCalendar::Auto)?;
    string_outcome(machine, &text)
}
