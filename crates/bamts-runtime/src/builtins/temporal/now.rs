//! `Temporal.Now`.

use std::convert::Infallible;

use bamts_native::Value;

use super::super::{define_data, install_function};
use super::fields::to_time_zone_identifier;
use super::{Method, arg, create, string_outcome, throw};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::temporal::TemporalObject;
use crate::temporal::instant_duration::{Instant, NS_PER_MILLISECOND, TemporalError};
use crate::temporal::now_rounding::{
    CalendarProjectionProvider, ClockSnapshot, HostClock, NowError, NowTimeZoneProvider,
    TemporalNow, UtcOffsetNanoseconds,
};
use crate::temporal::parse::parse_time_zone_identifier;
use crate::temporal::plain_types::PlainDate;
use crate::temporal::zoned_date_time::{
    CalendarId, FixedOffsetTimeZones, TimeZoneId, TimeZoneProvider, ZonedDateTime,
};
use crate::{EvalFailure, HeapEntry, Host, Machine};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    builtins: &mut BuiltinTable<H>,
    namespace: Value,
) {
    let now = super::super::super::ordinary_prototype(heap, builtins.object_prototype());
    let methods: [Method<H>; 6] = [
        ("instant", 0, instant::<H>),
        ("timeZoneId", 0, time_zone_id::<H>),
        ("zonedDateTimeISO", 0, zoned_date_time_iso::<H>),
        ("plainDateTimeISO", 0, plain_date_time_iso::<H>),
        ("plainDateISO", 0, plain_date_iso::<H>),
        ("plainTimeISO", 0, plain_time_iso::<H>),
    ];
    for (name, length, handler) in methods {
        let function = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name,
                length,
                handler,
            },
        );
        define_data(heap, atoms, shapes, now, name, function);
    }
    let tag_symbol = builtins.symbol_to_string_tag();
    super::super::define_to_string_tag(heap, shapes, now, tag_symbol, "Temporal.Now");
    define_data(heap, atoms, shapes, namespace, "Now", now);
}

/// One reading of the host clock. The host has millisecond resolution.
struct HostReading(ClockSnapshot);

impl HostClock for HostReading {
    type Error = Infallible;

    fn snapshot(&mut self) -> Result<ClockSnapshot, Infallible> {
        Ok(self.0)
    }
}

/// The host's zone, and the offsets of every zone available without a database.
struct AvailableZones {
    system: TimeZoneId,
}

impl NowTimeZoneProvider for AvailableZones {
    type Error = TemporalError;
    type Identifier = TimeZoneId;

    fn system_time_zone_id(&mut self) -> Result<TimeZoneId, TemporalError> {
        Ok(self.system.clone())
    }

    fn offset_nanoseconds(
        &mut self,
        time_zone: &TimeZoneId,
        instant: Instant,
    ) -> Result<UtcOffsetNanoseconds, TemporalError> {
        FixedOffsetTimeZones.offset_nanoseconds_for(time_zone, instant)
    }
}

/// `Temporal.Now` produces ISO values, whose projection is the ISO date itself.
struct IsoProjection;

impl CalendarProjectionProvider for IsoProjection {
    type Error = Infallible;
    type Identifier = CalendarId;
    type Projection = PlainDate;

    fn iso8601_identifier(&self) -> CalendarId {
        CalendarId::iso8601()
    }

    fn project_iso_date(
        &mut self,
        _calendar: &CalendarId,
        iso_date: PlainDate,
    ) -> Result<PlainDate, Infallible> {
        Ok(iso_date)
    }
}

type HostNow = TemporalNow<HostReading, AvailableZones, IsoProjection>;

/// SystemTimeZoneIdentifier. A host zone needing a time zone database cannot
/// be represented here, and the proposal's answer for an implementation that
/// only knows UTC is `UTC`.
fn system_time_zone<H: Host>(machine: &Machine<'_, H>) -> TimeZoneId {
    machine
        .host
        .env("TZ")
        .and_then(|zone| parse_time_zone_identifier(zone).ok())
        .and_then(|zone| TimeZoneId::from_parsed(zone).ok())
        .unwrap_or_else(TimeZoneId::utc)
}

fn host_now<H: Host>(machine: &mut Machine<'_, H>) -> HostNow {
    let nanoseconds = i128::from(machine.host.now_ms()) * NS_PER_MILLISECOND;
    TemporalNow::new(
        HostReading(ClockSnapshot::clamped(nanoseconds)),
        AvailableZones {
            system: system_time_zone(machine),
        },
        IsoProjection,
    )
}

fn now_failure<H: Host>(
    machine: &mut Machine<'_, H>,
    failure: NowError<Infallible, TemporalError, Infallible>,
) -> EvalFailure {
    match failure {
        NowError::Temporal(error) | NowError::TimeZone(error) => throw(machine, error),
        NowError::Clock(never) | NowError::Calendar(never) => match never {},
    }
}

/// The zone argument of the `*ISO` methods: absent means the host's.
fn time_zone_argument<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<Option<TimeZoneId>, EvalFailure> {
    if value == Value::UNDEFINED {
        Ok(None)
    } else {
        to_time_zone_identifier(machine, value).map(Some)
    }
}

fn instant<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = host_now(machine)
        .instant()
        .map_err(|failure| now_failure(machine, failure))?;
    create(machine, TemporalObject::Instant(value)).map(BuiltinOutcome::Value)
}

fn time_zone_id<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time_zone = host_now(machine)
        .time_zone_id()
        .map_err(|failure| now_failure(machine, failure))?;
    string_outcome(machine, time_zone.as_str())
}

fn zoned_date_time_iso<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time_zone = time_zone_argument(machine, arg(args, 0))?;
    let projected = host_now(machine)
        .zoned_date_time_iso(time_zone)
        .map_err(|failure| now_failure(machine, failure))?;
    let value = ZonedDateTime::from_instant(
        projected.instant(),
        projected.time_zone_id().clone(),
        projected.calendar_id().clone(),
    );
    create(machine, TemporalObject::ZonedDateTime(value)).map(BuiltinOutcome::Value)
}

fn plain_date_time_iso<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time_zone = time_zone_argument(machine, arg(args, 0))?;
    let value = host_now(machine)
        .plain_date_time_iso(time_zone)
        .map_err(|failure| now_failure(machine, failure))?;
    create(
        machine,
        TemporalObject::PlainDateTime {
            value,
            calendar: CalendarId::iso8601(),
        },
    )
    .map(BuiltinOutcome::Value)
}

fn plain_date_iso<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time_zone = time_zone_argument(machine, arg(args, 0))?;
    let mut now = host_now(machine);
    let projected = now
        .zoned_date_time_iso(time_zone)
        .map_err(|failure| now_failure(machine, failure))?;
    let calendar = projected.calendar_id().clone();
    let value = now
        .project_calendar(&projected, &calendar)
        .map_err(|failure| now_failure(machine, failure))?;
    create(machine, TemporalObject::PlainDate { value, calendar }).map(BuiltinOutcome::Value)
}

fn plain_time_iso<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let time_zone = time_zone_argument(machine, arg(args, 0))?;
    let value = host_now(machine)
        .plain_time_iso(time_zone)
        .map_err(|failure| now_failure(machine, failure))?;
    create(machine, TemporalObject::PlainTime(value)).map(BuiltinOutcome::Value)
}
