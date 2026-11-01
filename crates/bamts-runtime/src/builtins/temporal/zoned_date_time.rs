//! `Temporal.ZonedDateTime`.

use bamts_native::Value;

use super::super::bigint::to_bigint;
use super::super::intl::temporal_to_locale_string;
use super::fields::{
    CalendarFields, FieldNames, OffsetBehaviour, calendar_argument, date_time_from_fields,
    interpret_offset, prepare_partial_fields, providers, require_partial_temporal_object,
    to_calendar_identifier, to_temporal_duration, to_temporal_time, to_temporal_zoned_date_time,
    to_time_zone_identifier,
};
use super::options::{
    ALL_UNITS, DifferencePolicy, TIME_UNITS, UnitOption, difference_settings, direction_option,
    disambiguation_option, fractional_second_digits_option, get_options_object, offset_option,
    overflow_option, rounding_increment_option, rounding_mode_option, seconds_precision,
    show_calendar_option, show_offset_option, show_time_zone_option, unit_argument,
    unit_valued_option, validate_unit_value,
};
use super::{
    Class, Getter, OrThrow, arg, bigint_outcome, bigint_to_i128, construct, create, install_class,
    number_outcome, range_error, require_new, string_outcome, temporal_record, type_error,
    value_of_throws,
};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::temporal::instant_duration::{
    Instant, NS_PER_HOUR, RoundingMode, Unit, UnitCategory, exact_ratio_to_f64,
    validate_rounding_increment,
};
use crate::temporal::parse::parse_time_zone_identifier;
use crate::temporal::plain_types::{PlainDate, PlainDateTime};
use crate::temporal::zoned_date_time::{
    ArithmeticOptions, CalendarId, DifferenceOptions, FixedOffsetTimeZones, OffsetMatch,
    OffsetOption, ResolveOptions, RoundOptions, TimeZoneId, ToStringOptions, TransitionDirection,
    ZonedDateTime, epoch_nanoseconds_for, format_utc_offset, start_of_day,
};
use crate::temporal::{TemporalKind, TemporalObject};
use crate::{EvalFailure, HeapEntry, Host, Machine};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    builtins: &mut BuiltinTable<H>,
    namespace: Value,
) {
    let date_getters: [Getter<H>; 16] = date_getter_table!(H);
    let other_getters: [Getter<H>; 11] = [
        ("timeZoneId", "get timeZoneId", time_zone_id::<H>),
        ("hour", "get hour", hour::<H>),
        ("minute", "get minute", minute::<H>),
        ("second", "get second", second::<H>),
        ("millisecond", "get millisecond", millisecond::<H>),
        ("microsecond", "get microsecond", microsecond::<H>),
        ("nanosecond", "get nanosecond", nanosecond::<H>),
        (
            "epochMilliseconds",
            "get epochMilliseconds",
            epoch_milliseconds::<H>,
        ),
        (
            "epochNanoseconds",
            "get epochNanoseconds",
            epoch_nanoseconds::<H>,
        ),
        ("hoursInDay", "get hoursInDay", hours_in_day::<H>),
        (
            "offsetNanoseconds",
            "get offsetNanoseconds",
            offset_nanoseconds::<H>,
        ),
    ];
    let offset: Getter<H> = ("offset", "get offset", offset::<H>);
    let getters: Vec<Getter<H>> = date_getters
        .iter()
        .chain(&other_getters)
        .chain(std::iter::once(&offset))
        .copied()
        .collect();
    install_class(
        heap,
        builtins,
        namespace,
        &Class {
            kind: TemporalKind::ZonedDateTime,
            name: "ZonedDateTime",
            tag: "Temporal.ZonedDateTime",
            length: 2,
            constructor: constructor::<H>,
            statics: &[("from", 1, from::<H>), ("compare", 2, compare::<H>)],
            getters: &getters,
            methods: &[
                ("with", 1, with::<H>),
                ("withPlainTime", 0, with_plain_time::<H>),
                ("withTimeZone", 1, with_time_zone::<H>),
                ("withCalendar", 1, with_calendar::<H>),
                ("add", 1, add::<H>),
                ("subtract", 1, subtract::<H>),
                ("until", 1, until::<H>),
                ("since", 1, since::<H>),
                ("round", 1, round::<H>),
                ("equals", 1, equals::<H>),
                ("toString", 0, to_string::<H>),
                ("toLocaleString", 0, to_locale_string::<H>),
                ("toJSON", 0, to_json::<H>),
                ("valueOf", 0, value_of_throws::<H>),
                ("startOfDay", 0, start_of_day_method::<H>),
                ("getTimeZoneTransition", 1, get_time_zone_transition::<H>),
                ("toInstant", 0, to_instant::<H>),
                ("toPlainDate", 0, to_plain_date::<H>),
                ("toPlainTime", 0, to_plain_time::<H>),
                ("toPlainDateTime", 0, to_plain_date_time::<H>),
            ],
        },
    );
}

fn this_zoned<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
) -> Result<ZonedDateTime, EvalFailure> {
    match temporal_record(machine, this)? {
        Some(TemporalObject::ZonedDateTime(value)) => Ok(value),
        _ => Err(type_error(
            machine,
            "receiver is not a Temporal.ZonedDateTime",
        )),
    }
}

fn zoned_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    value: ZonedDateTime,
) -> Result<BuiltinOutcome, EvalFailure> {
    create(machine, TemporalObject::ZonedDateTime(value)).map(BuiltinOutcome::Value)
}

fn local_date_time<H: Host>(
    machine: &mut Machine<'_, H>,
    zoned: &ZonedDateTime,
) -> Result<PlainDateTime, EvalFailure> {
    zoned
        .to_plain_date_time(&FixedOffsetTimeZones)
        .or_throw(machine)
}

/// The date behind the shared calendar accessors.
fn accessor_date<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
) -> Result<(PlainDate, CalendarId), EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let local = local_date_time(machine, &zoned)?;
    Ok((local.date, zoned.calendar_id().clone()))
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
            let zoned = this_zoned(machine, this)?;
            let fields = zoned.fields(&providers()).or_throw(machine)?;
            number_outcome(f64::from(fields.$name()))
        })+
    };
}

time_getter!(hour, minute, second, millisecond, microsecond, nanosecond);

/// The zone argument of the constructor, which must be exactly an identifier;
/// the ISO strings `ToTemporalTimeZoneIdentifier` accepts are not allowed here.
fn time_zone_argument<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<TimeZoneId, EvalFailure> {
    let Some(text) = machine.string_value(value) else {
        return Err(type_error(machine, "time zone must be a string"));
    };
    let parsed = parse_time_zone_identifier(&text.to_utf8_lossy()).or_throw(machine)?;
    TimeZoneId::from_parsed(parsed).or_throw(machine)
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_new(machine, constructing, "ZonedDateTime")?;
    let bigint = to_bigint(machine, arg(args, 0))?;
    let nanoseconds = bigint_to_i128(machine, bigint)?;
    let instant = Instant::from_epoch_nanoseconds(nanoseconds).or_throw(machine)?;
    let time_zone = time_zone_argument(machine, arg(args, 1))?;
    let calendar = calendar_argument(machine, arg(args, 2))?;
    construct(
        machine,
        TemporalObject::ZonedDateTime(ZonedDateTime::from_instant(instant, time_zone, calendar)),
    )
}

fn from<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = to_temporal_zoned_date_time(machine, arg(args, 0), arg(args, 1))?;
    zoned_outcome(machine, value)
}

fn compare<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let one = to_temporal_zoned_date_time(machine, arg(args, 0), Value::UNDEFINED)?;
    let two = to_temporal_zoned_date_time(machine, arg(args, 1), Value::UNDEFINED)?;
    number_outcome(f64::from(ZonedDateTime::compare(&one, &two) as i8))
}

fn time_zone_id<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    string_outcome(machine, zoned.time_zone_id().as_str())
}

fn epoch_milliseconds<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    number_outcome(this_zoned(machine, this)?.epoch_milliseconds() as f64)
}

fn epoch_nanoseconds<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = this_zoned(machine, this)?.epoch_nanoseconds();
    bigint_outcome(machine, value)
}

fn hours_in_day<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let length = zoned
        .day_length_nanoseconds(&providers())
        .or_throw(machine)?;
    number_outcome(exact_ratio_to_f64(length, NS_PER_HOUR))
}

fn current_offset<H: Host>(
    machine: &mut Machine<'_, H>,
    zoned: &ZonedDateTime,
) -> Result<crate::temporal::zoned_date_time::UtcOffsetNanoseconds, EvalFailure> {
    let fields = zoned.fields(&providers()).or_throw(machine)?;
    Ok(fields.offset)
}

fn offset_nanoseconds<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let offset = current_offset(machine, &zoned)?;
    number_outcome(offset.get() as f64)
}

fn offset<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let offset = current_offset(machine, &zoned)?;
    string_outcome(machine, &format_utc_offset(offset))
}

fn with<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let like = arg(args, 0);
    require_partial_temporal_object(machine, like)?;
    let local = local_date_time(machine, &zoned)?;
    let current = current_offset(machine, &zoned)?;
    let mut base = CalendarFields::from_date(local.date).with_time(local.time);
    base.offset = Some(i128::from(current.get()));
    let names = FieldNames::DATE
        .with(FieldNames::TIME)
        .with(FieldNames::OFFSET);
    let partial = prepare_partial_fields(machine, like, names)?;
    let fields = base.merged_with(partial);
    let options = get_options_object(machine, arg(args, 1))?;
    let disambiguation = disambiguation_option(machine, options)?;
    let offset = offset_option(machine, options, OffsetOption::Prefer)?;
    let overflow = overflow_option(machine, options)?;
    let resolved = date_time_from_fields(machine, &fields, overflow)?;
    let value = interpret_offset(
        machine,
        resolved,
        OffsetBehaviour::Option(fields.offset.unwrap_or(0)),
        zoned.time_zone_id().clone(),
        zoned.calendar_id().clone(),
        ResolveOptions {
            disambiguation,
            offset,
            offset_match: OffsetMatch::Exactly,
        },
    )?;
    zoned_outcome(machine, value)
}

fn with_plain_time<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let like = arg(args, 0);
    let local = local_date_time(machine, &zoned)?;
    let time_zone = zoned.time_zone_id().clone();
    let calendar = zoned.calendar_id().clone();
    let instant = if like == Value::UNDEFINED {
        start_of_day(&FixedOffsetTimeZones, &time_zone, local.date).or_throw(machine)?
    } else {
        let time = to_temporal_time(machine, like, Value::UNDEFINED)?;
        let target = PlainDateTime::from_parts(local.date, time).or_throw(machine)?;
        let nanoseconds =
            epoch_nanoseconds_for(&FixedOffsetTimeZones, &time_zone, target).or_throw(machine)?;
        Instant::from_epoch_nanoseconds(nanoseconds).or_throw(machine)?
    };
    zoned_outcome(
        machine,
        ZonedDateTime::from_instant(instant, time_zone, calendar),
    )
}

fn with_time_zone<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let time_zone = to_time_zone_identifier(machine, arg(args, 0))?;
    zoned_outcome(machine, zoned.with_time_zone(time_zone))
}

fn with_calendar<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let calendar = to_calendar_identifier(machine, arg(args, 0))?;
    zoned_outcome(machine, zoned.with_calendar(calendar))
}

/// AddDurationToZonedDateTime.
fn add_duration<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    subtract: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let duration = to_temporal_duration(machine, arg(args, 0))?;
    let options = get_options_object(machine, arg(args, 1))?;
    let overflow = overflow_option(machine, options)?;
    let core = providers();
    let arithmetic = ArithmeticOptions { overflow };
    let value = if subtract {
        zoned.subtract(&core, &duration, arithmetic)
    } else {
        zoned.add(&core, &duration, arithmetic)
    }
    .or_throw(machine)?;
    zoned_outcome(machine, value)
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

/// DifferenceTemporalZonedDateTime. The settings are read with `since` false
/// because `ZonedDateTime::since` negates the rounding mode itself.
fn difference<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    since: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let other = to_temporal_zoned_date_time(machine, arg(args, 0), Value::UNDEFINED)?;
    if zoned.calendar_id() != other.calendar_id() {
        return Err(range_error(machine, "calendars must match"));
    }
    let options = get_options_object(machine, arg(args, 1))?;
    let settings = difference_settings(
        machine,
        false,
        options,
        DifferencePolicy {
            group: ALL_UNITS,
            disallowed: &[],
            fallback_smallest: Unit::Nanosecond,
            smallest_largest_default: Unit::Hour,
        },
    )?;
    if settings.largest_unit.category() == UnitCategory::Date
        && zoned.time_zone_id() != other.time_zone_id()
    {
        return Err(range_error(
            machine,
            "date units require matching time zones",
        ));
    }
    let core = providers();
    let difference_options = DifferenceOptions {
        largest_unit: settings.largest_unit,
        smallest_unit: settings.smallest_unit,
        rounding_increment: settings.rounding_increment,
        rounding_mode: settings.rounding_mode,
    };
    let value = if since {
        zoned.since(&core, &other, difference_options)
    } else {
        zoned.until(&core, &other, difference_options)
    }
    .or_throw(machine)?;
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
    let zoned = this_zoned(machine, this)?;
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
    if unit == Unit::Nanosecond && increment == 1 {
        return zoned_outcome(machine, zoned);
    }
    let value = zoned
        .round(
            &providers(),
            RoundOptions {
                smallest_unit: unit,
                rounding_increment: increment,
                rounding_mode: mode,
            },
        )
        .or_throw(machine)?;
    zoned_outcome(machine, value)
}

fn equals<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let other = to_temporal_zoned_date_time(machine, arg(args, 0), Value::UNDEFINED)?;
    Ok(BuiltinOutcome::Value(Value::boolean(zoned.equals(&other))))
}

fn to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let options = get_options_object(machine, arg(args, 0))?;
    let show_calendar = show_calendar_option(machine, options)?;
    let digits = fractional_second_digits_option(machine, options)?;
    let show_offset = show_offset_option(machine, options)?;
    let mode = rounding_mode_option(machine, options, RoundingMode::Trunc)?;
    let smallest = unit_valued_option(machine, options, "smallestUnit")?;
    let show_time_zone = show_time_zone_option(machine, options)?;
    validate_unit_value(machine, smallest, TIME_UNITS, None)?;
    if smallest == UnitOption::Unit(Unit::Hour) {
        return Err(range_error(machine, "smallestUnit must not be hour"));
    }
    let precision = seconds_precision(machine, smallest, digits)?;
    let text = zoned
        .format(
            &providers(),
            ToStringOptions {
                precision: precision.precision,
                show_calendar,
                show_time_zone,
                show_offset,
                round: Some(RoundOptions {
                    smallest_unit: precision.unit,
                    rounding_increment: precision.increment,
                    rounding_mode: mode,
                }),
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
    let text = this_zoned(machine, this)?
        .to_json(&providers())
        .or_throw(machine)?;
    string_outcome(machine, &text)
}

fn start_of_day_method<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let value = zoned.start_of_day(&providers()).or_throw(machine)?;
    zoned_outcome(machine, value)
}

fn get_time_zone_transition<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let direction = unit_argument(machine, arg(args, 0))?;
    let direction = match direction.shorthand() {
        Some(text) => direction_text(machine, text)?,
        None => direction_option(machine, direction.options)?,
    };
    let direction = if direction == "next" {
        TransitionDirection::Next
    } else {
        TransitionDirection::Previous
    };
    let transition = zoned
        .get_time_zone_transition(&FixedOffsetTimeZones, direction)
        .or_throw(machine)?;
    match transition {
        Some(value) => zoned_outcome(machine, value),
        None => Ok(BuiltinOutcome::Value(Value::NULL)),
    }
}

fn direction_text<H: Host>(
    machine: &mut Machine<'_, H>,
    text: &str,
) -> Result<String, EvalFailure> {
    if matches!(text, "next" | "previous") {
        Ok(text.to_owned())
    } else {
        Err(range_error(machine, format!("{text} is not a direction")))
    }
}

fn to_instant<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = this_zoned(machine, this)?.to_instant();
    create(machine, TemporalObject::Instant(value)).map(BuiltinOutcome::Value)
}

fn to_plain_date<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let value = zoned
        .to_plain_date(&FixedOffsetTimeZones)
        .or_throw(machine)?;
    let calendar = zoned.calendar_id().clone();
    create(machine, TemporalObject::PlainDate { value, calendar }).map(BuiltinOutcome::Value)
}

fn to_plain_time<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let value = zoned
        .to_plain_time(&FixedOffsetTimeZones)
        .or_throw(machine)?;
    create(machine, TemporalObject::PlainTime(value)).map(BuiltinOutcome::Value)
}

fn to_plain_date_time<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let zoned = this_zoned(machine, this)?;
    let value = local_date_time(machine, &zoned)?;
    let calendar = zoned.calendar_id().clone();
    create(machine, TemporalObject::PlainDateTime { value, calendar }).map(BuiltinOutcome::Value)
}

fn to_locale_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    this_zoned(machine, this)?;
    temporal_to_locale_string(machine, this, arg(args, 0), arg(args, 1))
}
