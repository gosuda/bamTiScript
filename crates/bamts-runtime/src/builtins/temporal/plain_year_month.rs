//! `Temporal.PlainYearMonth`.

use bamts_native::Value;

use super::super::intl::temporal_to_locale_string;
use super::fields::{
    CalendarFields, FieldNames, calendar_argument, calendar_date, date_from_fields, iso_year,
    prepare_calendar_fields, prepare_partial_fields, providers, require_partial_temporal_object,
    to_integer_with_truncation, to_temporal_duration, to_temporal_year_month,
    year_month_from_fields,
};
use super::options::{
    DATE_UNITS, DifferencePolicy, difference_settings, get_options_object, overflow_option,
    show_calendar_option,
};
use super::{
    Class, OrThrow, arg, construct, create, install_class, is_object, number_outcome,
    optional_number_outcome, optional_string_outcome, range_error, require_new, string_outcome,
    temporal_record, type_error, value_of_throws,
};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::temporal::calendar::{self, Calendar};
use crate::temporal::instant_duration::{Duration, Overflow, Unit, format_iso_date};
use crate::temporal::now_rounding::{ShowCalendar, format_calendar_annotation};
use crate::temporal::plain_types::PlainYearMonth;
use crate::temporal::relative::{DifferenceRounding, difference_plain_year_month};
use crate::temporal::zoned_date_time::{CalendarDateFields, CalendarId};
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
            kind: TemporalKind::PlainYearMonth,
            name: "PlainYearMonth",
            tag: "Temporal.PlainYearMonth",
            length: 2,
            constructor: constructor::<H>,
            statics: &[("from", 1, from::<H>), ("compare", 2, compare::<H>)],
            getters: &[
                ("calendarId", "get calendarId", calendar_id::<H>),
                ("era", "get era", era::<H>),
                ("eraYear", "get eraYear", era_year::<H>),
                ("year", "get year", year::<H>),
                ("month", "get month", month::<H>),
                ("monthCode", "get monthCode", month_code::<H>),
                ("daysInYear", "get daysInYear", days_in_year::<H>),
                ("daysInMonth", "get daysInMonth", days_in_month::<H>),
                ("monthsInYear", "get monthsInYear", months_in_year::<H>),
                ("inLeapYear", "get inLeapYear", in_leap_year::<H>),
            ],
            methods: &[
                ("with", 1, with::<H>),
                ("add", 1, add::<H>),
                ("subtract", 1, subtract::<H>),
                ("until", 1, until::<H>),
                ("since", 1, since::<H>),
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

fn this_year_month<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
) -> Result<(PlainYearMonth, CalendarId), EvalFailure> {
    match temporal_record(machine, this)? {
        Some(TemporalObject::PlainYearMonth { value, calendar }) => Ok((value, calendar)),
        _ => Err(type_error(
            machine,
            "receiver is not a Temporal.PlainYearMonth",
        )),
    }
}

fn year_month_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    value: PlainYearMonth,
    calendar: CalendarId,
) -> Result<BuiltinOutcome, EvalFailure> {
    create(machine, TemporalObject::PlainYearMonth { value, calendar }).map(BuiltinOutcome::Value)
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_new(machine, constructing, "PlainYearMonth")?;
    let year = to_integer_with_truncation(machine, arg(args, 0))?;
    let month = to_integer_with_truncation(machine, arg(args, 1))?;
    let calendar = calendar_argument(machine, arg(args, 2))?;
    let reference = arg(args, 3);
    let day = if reference == Value::UNDEFINED {
        1.0
    } else {
        to_integer_with_truncation(machine, reference)?
    };
    let year = iso_year(machine, year)?;
    if !(1.0..=12.0).contains(&month) || !(1.0..=31.0).contains(&day) {
        return Err(range_error(machine, "invalid ISO month or reference day"));
    }
    let value =
        PlainYearMonth::with_reference_day(year, month as u8, day as u8).or_throw(machine)?;
    construct(machine, TemporalObject::PlainYearMonth { value, calendar })
}

fn from<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = to_temporal_year_month(machine, arg(args, 0), arg(args, 1))?;
    year_month_outcome(machine, value, calendar)
}

fn compare<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (one, _) = to_temporal_year_month(machine, arg(args, 0), Value::UNDEFINED)?;
    let (two, _) = to_temporal_year_month(machine, arg(args, 1), Value::UNDEFINED)?;
    number_outcome(f64::from(one.cmp(&two) as i8))
}

fn calendar_id<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (_, calendar) = this_year_month(machine, this)?;
    string_outcome(machine, calendar.as_str())
}

/// The calendar's view of the receiver's date.
fn calendar_fields<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
) -> Result<CalendarDateFields, EvalFailure> {
    let (value, calendar) = this_year_month(machine, this)?;
    calendar_date(machine, &calendar, value.iso_date())
}

fn era<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let fields = calendar_fields(machine, this)?;
    optional_string_outcome(machine, fields.era.as_deref())
}

fn era_year<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let fields = calendar_fields(machine, this)?;
    optional_number_outcome(fields.era_year.map(f64::from))
}

fn month_code<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let fields = calendar_fields(machine, this)?;
    string_outcome(machine, &fields.month_code)
}

fn in_leap_year<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let fields = calendar_fields(machine, this)?;
    Ok(BuiltinOutcome::Value(Value::boolean(fields.in_leap_year)))
}

macro_rules! number_getter {
    ($($name:ident: |$fields:ident| $number:expr),+ $(,)?) => {
        $(fn $name<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let $fields = calendar_fields(machine, this)?;
            number_outcome($number)
        })+
    };
}

number_getter! {
    year: |fields| f64::from(fields.year),
    month: |fields| f64::from(fields.month),
    days_in_year: |fields| f64::from(fields.days_in_year),
    months_in_year: |fields| f64::from(fields.months_in_year),
}

fn days_in_month<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = this_year_month(machine, this)?;
    if calendar.is_iso8601() {
        return number_outcome(f64::from(value.days_in_month()));
    }
    let fields = calendar_date(machine, &calendar, value.iso_date())?;
    number_outcome(f64::from(fields.days_in_month))
}

fn with<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = this_year_month(machine, this)?;
    let like = arg(args, 0);
    require_partial_temporal_object(machine, like)?;
    let partial = prepare_partial_fields(machine, &calendar, like, FieldNames::YEAR_MONTH)?;
    let fields = CalendarFields::from_year_month(machine, &calendar, value)?.merged_with(partial);
    let options = get_options_object(machine, arg(args, 1))?;
    let overflow = overflow_option(machine, options)?;
    let result = year_month_from_fields(machine, &calendar, &fields, overflow)?;
    year_month_outcome(machine, result, calendar)
}

/// AddDurationToYearMonth.
fn add_duration<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    subtract: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = this_year_month(machine, this)?;
    let duration = to_temporal_duration(machine, arg(args, 0))?;
    let options = get_options_object(machine, arg(args, 1))?;
    let overflow = overflow_option(machine, options)?;
    let result = match Calendar::from_id(&calendar) {
        Some(kind) if subtract => {
            calendar::add_to_year_month(kind, value, &duration.negated(), overflow)
        }
        Some(kind) => calendar::add_to_year_month(kind, value, &duration, overflow),
        None if subtract => value.subtract(&duration, overflow),
        None => value.add(&duration, overflow),
    }
    .or_throw(machine)?;
    year_month_outcome(machine, result, calendar)
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

/// DifferenceTemporalPlainYearMonth.
fn difference<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    since: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = this_year_month(machine, this)?;
    let (other, other_calendar) = to_temporal_year_month(machine, arg(args, 0), Value::UNDEFINED)?;
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
            disallowed: &[Unit::Week, Unit::Day],
            fallback_smallest: Unit::Month,
            smallest_largest_default: Unit::Year,
        },
    )?;
    let result = match Calendar::from_id(&calendar) {
        Some(_) if value == other => Ok(Duration::default()),
        Some(kind) => calendar::first_of_month(kind, value).and_then(|one| {
            difference_plain_year_month(
                &providers(),
                one,
                calendar::first_of_month(kind, other)?,
                &calendar,
                DifferenceRounding {
                    largest_unit: settings.largest_unit,
                    smallest_unit: settings.smallest_unit,
                    increment: settings.rounding_increment,
                    mode: settings.rounding_mode,
                },
            )
        }),
        None => value.until(
            other,
            settings.largest_unit,
            settings.smallest_unit,
            settings.rounding_increment,
            settings.rounding_mode,
        ),
    }
    .or_throw(machine)?;
    let result = if since { result.negated() } else { result };
    create(machine, TemporalObject::Duration(result)).map(BuiltinOutcome::Value)
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
    let (value, calendar) = this_year_month(machine, this)?;
    let (other, other_calendar) = to_temporal_year_month(machine, arg(args, 0), Value::UNDEFINED)?;
    let equal = value == other && calendar == other_calendar;
    Ok(BuiltinOutcome::Value(Value::boolean(equal)))
}

/// TemporalYearMonthToString: the reference day is only shown when a calendar
/// annotation makes it part of the round trip.
fn year_month_text<H: Host>(
    machine: &mut Machine<'_, H>,
    value: PlainYearMonth,
    calendar: &CalendarId,
    show: ShowCalendar,
) -> Result<String, EvalFailure> {
    let body = if matches!(show, ShowCalendar::Always | ShowCalendar::Critical)
        || !calendar.is_iso8601()
    {
        format_iso_date(value.year, value.month, value.reference_day())
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
    let (value, calendar) = this_year_month(machine, this)?;
    let options = get_options_object(machine, arg(args, 0))?;
    let show = show_calendar_option(machine, options)?;
    let text = year_month_text(machine, value, &calendar, show)?;
    string_outcome(machine, &text)
}

fn to_json<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = this_year_month(machine, this)?;
    let text = year_month_text(machine, value, &calendar, ShowCalendar::Auto)?;
    string_outcome(machine, &text)
}

fn to_plain_date<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, calendar) = this_year_month(machine, this)?;
    let item = arg(args, 0);
    if !is_object(machine, item)? {
        return Err(type_error(machine, "argument must be an object"));
    }
    let input =
        prepare_calendar_fields(machine, &calendar, item, FieldNames::DAY, FieldNames::NONE)?;
    let date = if calendar.is_iso8601() {
        let Some(day) = input.day else {
            return Err(type_error(machine, "day is required"));
        };
        value
            .to_plain_date(day as i64, Overflow::Constrain)
            .or_throw(machine)?
    } else {
        let fields = CalendarFields::from_year_month(machine, &calendar, value)?.merged_with(input);
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
    this_year_month(machine, this)?;
    temporal_to_locale_string(machine, this, arg(args, 0), arg(args, 1))
}
