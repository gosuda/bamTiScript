//! ECMA-402 Temporal primitives.

pub mod calendar;
pub mod instant_duration;
pub mod now_rounding;
pub mod parse;
pub mod plain_types;
pub mod relative;
pub mod zoned_date_time;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum TemporalKind {
    Instant,
    Duration,
    PlainDate,
    PlainTime,
    PlainDateTime,
    PlainYearMonth,
    PlainMonthDay,
    ZonedDateTime,
}

impl TemporalKind {
    pub(crate) const COUNT: usize = 8;

    pub(crate) const ALL: [Self; Self::COUNT] = [
        Self::Instant,
        Self::Duration,
        Self::PlainDate,
        Self::PlainTime,
        Self::PlainDateTime,
        Self::PlainYearMonth,
        Self::PlainMonthDay,
        Self::ZonedDateTime,
    ];

    pub(crate) const fn index(self) -> usize {
        self as usize
    }
}

#[derive(Clone, Debug)]
pub enum TemporalObject {
    Instant(instant_duration::Instant),
    Duration(instant_duration::Duration),
    PlainDate {
        value: plain_types::PlainDate,
        calendar: zoned_date_time::CalendarId,
    },
    PlainTime(plain_types::PlainTime),
    PlainDateTime {
        value: plain_types::PlainDateTime,
        calendar: zoned_date_time::CalendarId,
    },
    PlainYearMonth {
        value: plain_types::PlainYearMonth,
        calendar: zoned_date_time::CalendarId,
    },
    PlainMonthDay {
        value: plain_types::PlainMonthDay,
        calendar: zoned_date_time::CalendarId,
    },
    ZonedDateTime(zoned_date_time::ZonedDateTime),
}

impl TemporalObject {
    /// The `[[Calendar]]` slot, for the classes that have one.
    pub(crate) fn calendar(&self) -> Option<zoned_date_time::CalendarId> {
        match self {
            Self::Instant(_) | Self::Duration(_) | Self::PlainTime(_) => None,
            Self::PlainDate { calendar, .. }
            | Self::PlainDateTime { calendar, .. }
            | Self::PlainYearMonth { calendar, .. }
            | Self::PlainMonthDay { calendar, .. } => Some(calendar.clone()),
            Self::ZonedDateTime(value) => Some(value.calendar_id().clone()),
        }
    }

    pub(crate) const fn kind(&self) -> TemporalKind {
        match self {
            Self::Instant(_) => TemporalKind::Instant,
            Self::Duration(_) => TemporalKind::Duration,
            Self::PlainDate { .. } => TemporalKind::PlainDate,
            Self::PlainTime(_) => TemporalKind::PlainTime,
            Self::PlainDateTime { .. } => TemporalKind::PlainDateTime,
            Self::PlainYearMonth { .. } => TemporalKind::PlainYearMonth,
            Self::PlainMonthDay { .. } => TemporalKind::PlainMonthDay,
            Self::ZonedDateTime(_) => TemporalKind::ZonedDateTime,
        }
    }
}
