//! `Temporal.Instant`.

use bamts_native::Value;

use super::super::bigint::to_bigint;
use super::super::intl::temporal_to_locale_string;
use super::super::value_number;
use super::fields::{
    providers, to_temporal_duration, to_temporal_instant, to_time_zone_identifier,
};
use super::options::{
    DifferencePolicy, Options, TIME_UNITS, UnitOption, difference_settings,
    fractional_second_digits_option, get_options_object, rounding_increment_option,
    rounding_mode_option, seconds_precision, unit_argument, unit_valued_option, validate_increment,
    validate_unit_value,
};
use super::{
    Class, OrThrow, arg, bigint_outcome, bigint_to_i128, construct, create, install_class,
    number_outcome, range_error, require_new, string_outcome, temporal_record, type_error,
    value_of_throws,
};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::temporal::instant_duration::{Instant, NS_PER_DAY, RoundingMode, Unit};
use crate::temporal::now_rounding::{
    format_iso_date_time, format_utc_offset_rounded, round_epoch_nanoseconds,
};
use crate::temporal::zoned_date_time::{
    CalendarId, TimeZoneId, ZonedDateTime, iso_date_time_for_instant,
};
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
            kind: TemporalKind::Instant,
            name: "Instant",
            tag: "Temporal.Instant",
            length: 1,
            constructor: constructor::<H>,
            statics: &[
                ("from", 1, from::<H>),
                ("fromEpochMilliseconds", 1, from_epoch_milliseconds::<H>),
                ("fromEpochNanoseconds", 1, from_epoch_nanoseconds::<H>),
                ("compare", 2, compare::<H>),
            ],
            getters: &[
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
            ],
            methods: &[
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
                ("toZonedDateTimeISO", 1, to_zoned_date_time_iso::<H>),
            ],
        },
    );
}

fn this_instant<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
) -> Result<Instant, EvalFailure> {
    match temporal_record(machine, this)? {
        Some(TemporalObject::Instant(value)) => Ok(value),
        _ => Err(type_error(machine, "receiver is not a Temporal.Instant")),
    }
}

fn instant_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Instant,
) -> Result<BuiltinOutcome, EvalFailure> {
    create(machine, TemporalObject::Instant(value)).map(BuiltinOutcome::Value)
}

/// ToBigInt, then the range check of CreateTemporalInstant.
fn instant_from_bigint<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<Instant, EvalFailure> {
    let bigint = to_bigint(machine, value)?;
    let nanoseconds = bigint_to_i128(machine, bigint)?;
    Instant::from_epoch_nanoseconds(nanoseconds).or_throw(machine)
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_new(machine, constructing, "Instant")?;
    let value = instant_from_bigint(machine, arg(args, 0))?;
    construct(machine, TemporalObject::Instant(value))
}

fn from<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = to_temporal_instant(machine, arg(args, 0))?;
    instant_outcome(machine, value)
}

fn from_epoch_milliseconds<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let number = value_number(machine.coerce_number_observable(arg(args, 0))?);
    if !number.is_finite() || number.trunc() != number {
        return Err(range_error(
            machine,
            "epoch milliseconds must be an integer",
        ));
    }
    // A saturated value is still out of range, as the original was.
    let value = Instant::from_epoch_milliseconds(number as i64).or_throw(machine)?;
    instant_outcome(machine, value)
}

fn from_epoch_nanoseconds<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = instant_from_bigint(machine, arg(args, 0))?;
    instant_outcome(machine, value)
}

fn compare<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let one = to_temporal_instant(machine, arg(args, 0))?;
    let two = to_temporal_instant(machine, arg(args, 1))?;
    number_outcome(f64::from(one.cmp(&two) as i8))
}

fn epoch_milliseconds<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    number_outcome(this_instant(machine, this)?.epoch_milliseconds() as f64)
}

fn epoch_nanoseconds<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = this_instant(machine, this)?.epoch_nanoseconds();
    bigint_outcome(machine, value)
}

fn add_duration<H: Host>(
    machine: &mut Machine<'_, H>,
    instant: Instant,
    other: Value,
    subtract: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let duration = to_temporal_duration(machine, other)?;
    let value = if subtract {
        instant.subtract(&duration)
    } else {
        instant.add(&duration)
    }
    .or_throw(machine)?;
    instant_outcome(machine, value)
}

fn add<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let instant = this_instant(machine, this)?;
    add_duration(machine, instant, arg(args, 0), false)
}

fn subtract<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let instant = this_instant(machine, this)?;
    add_duration(machine, instant, arg(args, 0), true)
}

/// DifferenceTemporalInstant.
fn difference<H: Host>(
    machine: &mut Machine<'_, H>,
    since: bool,
    instant: Instant,
    other: Value,
    options: Value,
) -> Result<BuiltinOutcome, EvalFailure> {
    let other = to_temporal_instant(machine, other)?;
    let options = get_options_object(machine, options)?;
    let settings = difference_settings(
        machine,
        since,
        options,
        DifferencePolicy {
            group: TIME_UNITS,
            disallowed: &[],
            fallback_smallest: Unit::Nanosecond,
            smallest_largest_default: Unit::Second,
        },
    )?;
    let value = instant
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
    let instant = this_instant(machine, this)?;
    difference(machine, false, instant, arg(args, 0), arg(args, 1))
}

fn since<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let instant = this_instant(machine, this)?;
    difference(machine, true, instant, arg(args, 0), arg(args, 1))
}

fn round<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let instant = this_instant(machine, this)?;
    let round_to = unit_argument(machine, arg(args, 0))?;
    let increment = rounding_increment_option(machine, round_to.options)?;
    let mode = rounding_mode_option(machine, round_to.options, RoundingMode::HalfExpand)?;
    let smallest = round_to.required_unit(machine, "smallestUnit")?;
    validate_unit_value(machine, smallest, TIME_UNITS, None)?;
    let UnitOption::Unit(unit) = smallest else {
        return Err(range_error(machine, "smallestUnit is required"));
    };
    let unit_ns = unit.ns_per().unwrap_or(1);
    validate_increment(machine, increment, NS_PER_DAY / unit_ns, true)?;
    let value = instant.round(unit, increment, mode).or_throw(machine)?;
    instant_outcome(machine, value)
}

fn equals<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let instant = this_instant(machine, this)?;
    let other = to_temporal_instant(machine, arg(args, 0))?;
    Ok(BuiltinOutcome::Value(Value::boolean(instant == other)))
}

/// TemporalInstantToString: `Z` without a zone, else the zone's rounded offset.
fn instant_text<H: Host>(
    machine: &mut Machine<'_, H>,
    instant: Instant,
    time_zone: Option<&TimeZoneId>,
    precision: crate::temporal::instant_duration::Precision,
) -> Result<String, EvalFailure> {
    let Some(time_zone) = time_zone else {
        return Ok(instant.format(precision));
    };
    let core = providers();
    let local = iso_date_time_for_instant(core.time_zone, time_zone, instant.epoch_nanoseconds())
        .or_throw(machine)?;
    let offset = core
        .time_zone
        .offset_nanoseconds_for(time_zone, instant)
        .or_throw(machine)?;
    let offset = format_utc_offset_rounded(offset).or_throw(machine)?;
    Ok(format!(
        "{}{offset}",
        format_iso_date_time(&local, precision)
    ))
}

fn to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let instant = this_instant(machine, this)?;
    let options: Options = get_options_object(machine, arg(args, 0))?;
    let digits = fractional_second_digits_option(machine, options)?;
    let mode = rounding_mode_option(machine, options, RoundingMode::Trunc)?;
    let smallest = unit_valued_option(machine, options, "smallestUnit")?;
    let time_zone = match options {
        Some(object) => machine.get_named_property(object, "timeZone")?,
        None => Value::UNDEFINED,
    };
    validate_unit_value(machine, smallest, TIME_UNITS, None)?;
    if smallest == UnitOption::Unit(Unit::Hour) {
        return Err(range_error(machine, "smallestUnit must not be hour"));
    }
    let time_zone = if time_zone == Value::UNDEFINED {
        None
    } else {
        Some(to_time_zone_identifier(machine, time_zone)?)
    };
    let precision = seconds_precision(machine, smallest, digits)?;
    let rounded = round_epoch_nanoseconds(
        instant.epoch_nanoseconds(),
        precision.unit,
        precision.increment,
        mode,
    )
    .and_then(Instant::from_epoch_nanoseconds)
    .or_throw(machine)?;
    let text = instant_text(machine, rounded, time_zone.as_ref(), precision.precision)?;
    string_outcome(machine, &text)
}

fn to_json<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let text = this_instant(machine, this)?.to_string();
    string_outcome(machine, &text)
}

fn to_zoned_date_time_iso<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let instant = this_instant(machine, this)?;
    let time_zone = to_time_zone_identifier(machine, arg(args, 0))?;
    let value = ZonedDateTime::from_instant(instant, time_zone, CalendarId::iso8601());
    create(machine, TemporalObject::ZonedDateTime(value)).map(BuiltinOutcome::Value)
}

fn to_locale_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    this_instant(machine, this)?;
    temporal_to_locale_string(machine, this, arg(args, 0), arg(args, 1))
}
