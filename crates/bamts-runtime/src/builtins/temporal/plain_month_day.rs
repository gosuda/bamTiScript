//! `Temporal.PlainMonthDay`.

use bamts_native::Value;

use super::super::intl::temporal_to_locale_string;
use super::fields::{
    CalendarFields, FieldNames, calendar_argument, calendar_date, date_from_fields, iso_year,
    month_day_from_fields, prepare_calendar_fields, prepare_partial_fields,
    require_partial_temporal_object, to_integer_with_truncation, to_temporal_month_day,
};
use super::options::{get_options_object, overflow_option, show_calendar_option};
use super::{
    Class, OrThrow, arg, construct, create, install_class, is_object, number_outcome, require_new,
    string_outcome, temporal_record, type_error, value_of_throws,
};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::temporal::instant_duration::{Overflow, format_iso_date};
use crate::temporal::now_rounding::{ShowCalendar, format_calendar_annotation};
use crate::temporal::plain_types::{MONTH_DAY_REFERENCE_YEAR, PlainMonthDay};
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
            kind: TemporalKind::PlainMonthDay,
            name: "PlainMonthDay",
            tag: "Temporal.PlainMonthDay",
            length: 2,
            constructor: constructor::<H>,
            statics: &[("from", 1, from::<H>)],
            getters: &[
                ("calendarId", "get calendarId", calendar_id::<H>),
                ("monthCode", "get monthCode", month_code::<H>),
                ("day", "get day", day::<H>),
            ],
            methods: &[
                ("with", 1, with::<H>),
                ("equals", 1, equals::<H>),
                ("toString", 0, to_string::<H>),
                ("toLocaleString", 0, to_locale_string::<H>),
                ("toJSON", 0, to_json::<H>),
                ("valueOf", 0, value_of_throws::<H>),
                ("toPlainDate", 1, to_plain_date::<H>),
            ],
        },
    );
}

fn this_month_day<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
) -> Result<(PlainMonthDay, CalendarId), EvalFailure> {
    match temporal_record(machine, this)? {
        Some(TemporalObject::PlainMonthDay { value, calendar }) => Ok((value, calendar)),
        _ => Err(type_error(
            machine,
            "receiver is not a Temporal.PlainMonthDay",
        )),
    }
}

fn month_day_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    value: PlainMonthDay,
    calendar: CalendarId,
) -> Result<BuiltinOutcome, EvalFailure> {
    create(machine, TemporalObject::PlainMonthDay { value, calendar }).map(BuiltinOutcome::Value)
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_new(machine, constructing, "PlainMonthDay")?;
    let month = to_integer_with_truncation(machine, arg(args, 0))?;
    let day = to_integer_with_truncation(machine, arg(args, 1))?;
    let calendar = calendar_argument(machine, arg(args, 2))?;
    let reference = arg(args, 3);
    let year = if reference == Value::UNDEFINED {
        f64::from(MONTH_DAY_REFERENCE_YEAR)
    } else {
        to_integer_with_truncation(machine, reference)?
    };
    let year = iso_year(machine, year)?;
    let value =
        PlainMonthDay::with_reference_year(month as i64, day as i64, year, Overflow::Reject)
            .or_throw(machine)?;
    construct(machine, TemporalObject::PlainMonthDay { value, calendar })
}

fn from<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = to_temporal_month_day(machine, arg(args, 0), arg(args, 1))?;
    month_day_outcome(machine, value, calendar)
}

fn calendar_id<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, calendar) = this_month_day(machine, this)?;
    string_outcome(machine, calendar.as_str())
}

fn month_code<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = this_month_day(machine, this)?;
    if calendar.is_iso8601() {
        return string_outcome(machine, &value.month_code());
    }
    let fields = calendar_date(machine, &calendar, value.iso_date())?;
    string_outcome(machine, &fields.month_code)
}

fn day<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = this_month_day(machine, this)?;
    let fields = calendar_date(machine, &calendar, value.iso_date())?;
    number_outcome(f64::from(fields.day))
}

fn with<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = this_month_day(machine, this)?;
    let like = arg(args, 0);
    require_partial_temporal_object(machine, like)?;
    let partial = prepare_partial_fields(machine, &calendar, like, FieldNames::DATE)?;
    let fields = CalendarFields::from_month_day(machine, &calendar, value)?.merged_with(partial);
    let options = get_options_object(machine, arg(args, 1))?;
    let overflow = overflow_option(machine, options)?;
    let result = month_day_from_fields(machine, &calendar, &fields, overflow)?;
    month_day_outcome(machine, result, calendar)
}

fn equals<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = this_month_day(machine, this)?;
    let (other, other_calendar) = to_temporal_month_day(machine, arg(args, 0), Value::UNDEFINED)?;
    let equal = value.equals(&other) && calendar == other_calendar;
    Ok(BuiltinOutcome::Value(Value::boolean(equal)))
}

/// TemporalMonthDayToString: the reference year is only shown when a calendar
/// annotation makes it part of the round trip.
fn month_day_text<H: Host>(
    machine: &mut Machine<'_, H>,
    value: PlainMonthDay,
    calendar: &CalendarId,
    show: ShowCalendar,
) -> Result<String, EvalFailure> {
    let body = if matches!(show, ShowCalendar::Always | ShowCalendar::Critical)
        || !calendar.is_iso8601()
    {
        format_iso_date(value.reference_year(), value.month, value.day)
    } else {
        value.format()
    };
    let annotation = format_calendar_annotation(calendar.as_str(), show).or_throw(machine)?;
    Ok(format!("{body}{annotation}"))
}

fn to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = this_month_day(machine, this)?;
    let options = get_options_object(machine, arg(args, 0))?;
    let show = show_calendar_option(machine, options)?;
    let text = month_day_text(machine, value, &calendar, show)?;
    string_outcome(machine, &text)
}

fn to_json<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = this_month_day(machine, this)?;
    let text = month_day_text(machine, value, &calendar, ShowCalendar::Auto)?;
    string_outcome(machine, &text)
}

fn to_plain_date<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = this_month_day(machine, this)?;
    let item = arg(args, 0);
    if !is_object(machine, item)? {
        return Err(type_error(machine, "argument must be an object"));
    }
    let input =
        prepare_calendar_fields(machine, &calendar, item, FieldNames::YEAR, FieldNames::NONE)?;
    let date = if calendar.is_iso8601() {
        let Some(year) = input.year else {
            return Err(type_error(machine, "year is required"));
        };
        let year = iso_year(machine, year)?;
        value
            .to_plain_date(year, Overflow::Constrain)
            .or_throw(machine)?
    } else {
        let fields = CalendarFields::from_month_day(machine, &calendar, value)?.merged_with(input);
        date_from_fields(machine, &calendar, &fields, Overflow::Constrain)?
    };
    create(
        machine,
        TemporalObject::PlainDate {
            value: date,
            calendar,
        },
    )
    .map(BuiltinOutcome::Value)
}

fn to_locale_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    this_month_day(machine, this)?;
    temporal_to_locale_string(machine, this, arg(args, 0), arg(args, 1))
}
