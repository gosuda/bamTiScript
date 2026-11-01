//! The JavaScript binding of the `Temporal` proposal.
//!
//! Algorithms live in `crate::temporal`; this module owns what only JavaScript
//! can observe: argument conversion, the order options and properties are read
//! in, receiver checks, and the shape of the installed objects.

/// Defines the calendar accessors shared by the classes that hold a date.
/// `$this` reads the receiver's date and calendar, and is the brand check.
macro_rules! date_accessors {
    ($this:ident) => {
        fn calendar_id<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let (_, calendar) = $this(machine, this)?;
            string_outcome(machine, calendar.as_str())
        }

        /// The ISO calendar has no eras.
        fn no_era<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            $this(machine, this)?;
            Ok(BuiltinOutcome::Value(Value::UNDEFINED))
        }

        fn month_code<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let (date, _) = $this(machine, this)?;
            string_outcome(machine, &format!("M{:02}", date.month))
        }

        fn in_leap_year<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let (date, _) = $this(machine, this)?;
            Ok(BuiltinOutcome::Value(Value::boolean(date.in_leap_year())))
        }

        date_number_accessors! {
            $this,
            year: |date| f64::from(date.year),
            month: |date| f64::from(date.month),
            day: |date| f64::from(date.day),
            day_of_week: |date| f64::from(date.day_of_week()),
            day_of_year: |date| f64::from(date.day_of_year()),
            week_of_year: |date| f64::from(date.week_of_year().1),
            year_of_week: |date| f64::from(date.week_of_year().0),
            days_in_week: |_date| 7.0,
            days_in_month: |date| f64::from(date.days_in_month()),
            days_in_year: |date| f64::from(date.days_in_year()),
            months_in_year: |date| f64::from(date.months_in_year()),
        }
    };
}

macro_rules! date_number_accessors {
    ($this:ident, $($name:ident: |$date:ident| $value:expr),+ $(,)?) => {
        $(fn $name<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let ($date, _) = $this(machine, this)?;
            number_outcome($value)
        })+
    };
}

/// The accessor table `date_accessors!` defines the functions for.
macro_rules! date_getter_table {
    ($H:ident) => {
        [
            ("calendarId", "get calendarId", calendar_id::<$H>),
            ("era", "get era", no_era::<$H>),
            ("eraYear", "get eraYear", no_era::<$H>),
            ("year", "get year", year::<$H>),
            ("month", "get month", month::<$H>),
            ("monthCode", "get monthCode", month_code::<$H>),
            ("day", "get day", day::<$H>),
            ("dayOfWeek", "get dayOfWeek", day_of_week::<$H>),
            ("dayOfYear", "get dayOfYear", day_of_year::<$H>),
            ("weekOfYear", "get weekOfYear", week_of_year::<$H>),
            ("yearOfWeek", "get yearOfWeek", year_of_week::<$H>),
            ("daysInWeek", "get daysInWeek", days_in_week::<$H>),
            ("daysInMonth", "get daysInMonth", days_in_month::<$H>),
            ("daysInYear", "get daysInYear", days_in_year::<$H>),
            ("monthsInYear", "get monthsInYear", months_in_year::<$H>),
            ("inLeapYear", "get inLeapYear", in_leap_year::<$H>),
        ]
    };
}

mod duration;
mod fields;
mod instant;
mod options;
mod plain_date;
mod plain_date_time;
mod plain_month_day;
mod plain_time;
mod plain_year_month;

use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::Value;

use super::{allocate_string, define_data, install_constructor_function, install_function};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::temporal::instant_duration::{TemporalError, TemporalErrorKind};
use crate::temporal::{TemporalKind, TemporalObject};
use crate::{EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap};

/// Name, `length`, and implementation of one installed function.
pub(super) type Method<H> = (&'static str, u32, BuiltinHandler<H>);

/// Property name, function name, and implementation of one accessor.
pub(super) type Getter<H> = (&'static str, &'static str, BuiltinHandler<H>);

/// The installed shape of one Temporal class.
struct Class<'a, H: Host> {
    kind: TemporalKind,
    name: &'static str,
    tag: &'static str,
    length: u32,
    constructor: BuiltinHandler<H>,
    statics: &'a [Method<H>],
    getters: &'a [Getter<H>],
    methods: &'a [Method<H>],
}

fn install_class<H: Host>(
    heap: &mut Vec<HeapEntry>,
    builtins: &mut BuiltinTable<H>,
    namespace: Value,
    class: &Class<'_, H>,
) {
    let prototype = builtins.temporal_prototype(class.kind);
    let constructor =
        install_constructor_function(heap, builtins, class.name, class.length, class.constructor);
    builtins.set_constructor_prototype(heap, constructor, prototype);
    for &(name, length, handler) in class.statics {
        let function = install_function(heap, builtins, name, length, handler);
        define_data(heap, constructor, name, function);
    }
    for &(property, name, handler) in class.getters {
        let getter = install_function(heap, builtins, name, 0, handler);
        define_getter(heap, prototype, property, getter);
    }
    for &(name, length, handler) in class.methods {
        let function = install_function(heap, builtins, name, length, handler);
        define_data(heap, prototype, name, function);
    }
    let tag_symbol = builtins.symbol_to_string_tag();
    super::define_to_string_tag(heap, prototype, tag_symbol, class.tag);
    define_data(heap, namespace, class.name, constructor);
}

fn define_getter(heap: &mut [HeapEntry], object: Value, name: &str, getter: Value) {
    let Some(bamts_native::Decoded::HeapRef(id)) = object.decode() else {
        panic!("accessor target is a heap object");
    };
    let HeapEntry::Object { properties, .. } = &mut heap[id.slot() as usize - 1] else {
        panic!("accessor target is an ordinary object");
    };
    properties.insert(
        PropertyKey::Named(EcmaString::encode(name)),
        Property::Accessor {
            getter: Some(getter),
            setter: None,
            enumerable: false,
            configurable: true,
        },
    );
}

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let namespace = super::super::ordinary_prototype(heap, builtins.object_prototype());
    let tag_symbol = builtins.symbol_to_string_tag();
    super::define_to_string_tag(heap, namespace, tag_symbol, "Temporal");
    // Classes refer to each other's instances, so every prototype exists before
    // any class is populated.
    for kind in TemporalKind::ALL {
        let prototype = super::super::ordinary_prototype(heap, builtins.object_prototype());
        builtins.set_temporal_prototype(kind, prototype);
    }
    duration::install(heap, builtins, namespace);
    instant::install(heap, builtins, namespace);
    plain_time::install(heap, builtins, namespace);
    plain_date::install(heap, builtins, namespace);
    plain_date_time::install(heap, builtins, namespace);
    plain_year_month::install(heap, builtins, namespace);
    plain_month_day::install(heap, builtins, namespace);
    globals.insert(EcmaString::encode("Temporal"), namespace);
}

/// Maps a core error to the ECMAScript exception it stands for. Grammar
/// failures are `RangeError`s, and every message survives to the catch site.
pub(super) fn throw<H: Host>(machine: &mut Machine<'_, H>, error: TemporalError) -> EvalFailure {
    let name = match error.kind {
        TemporalErrorKind::Type => "TypeError",
        TemporalErrorKind::Range | TemporalErrorKind::Syntax => "RangeError",
    };
    let id = machine
        .intrinsics
        .builtins
        .id_named(name)
        .expect("error constructor is installed");
    machine.throw_error(id, error.message)
}

/// Lifts a core result into the binding's error channel.
pub(super) trait OrThrow<T> {
    fn or_throw<H: Host>(self, machine: &mut Machine<'_, H>) -> Result<T, EvalFailure>;
}

impl<T> OrThrow<T> for Result<T, TemporalError> {
    fn or_throw<H: Host>(self, machine: &mut Machine<'_, H>) -> Result<T, EvalFailure> {
        self.map_err(|error| throw(machine, error))
    }
}

pub(super) fn range_error<H: Host>(
    machine: &mut Machine<'_, H>,
    message: impl Into<String>,
) -> EvalFailure {
    throw(machine, TemporalError::range(message))
}

pub(super) fn type_error<H: Host>(
    machine: &mut Machine<'_, H>,
    message: impl Into<String>,
) -> EvalFailure {
    throw(machine, TemporalError::type_error(message))
}

/// `Type(value) is Object`. `Machine::is_object` also answers true for a
/// Symbol, which every Temporal "must be an object" check has to reject.
pub(super) fn is_object<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<bool, EvalFailure> {
    Ok(!machine.coercion_is_primitive(value)?)
}

/// The Temporal record `value` carries, if it is a Temporal instance.
pub(super) fn temporal_record<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<Option<TemporalObject>, EvalFailure> {
    let Some(index) = machine.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
        return Ok(None);
    };
    Ok(match &machine.heap[index] {
        HeapEntry::Temporal { value, .. } => Some((**value).clone()),
        _ => None,
    })
}

/// Allocates an instance with the class's own prototype.
pub(super) fn create<H: Host>(
    machine: &mut Machine<'_, H>,
    value: TemporalObject,
) -> Result<Value, EvalFailure> {
    let prototype = machine.intrinsics.builtins.temporal_prototype(value.kind());
    allocate(machine, value, prototype)
}

/// Allocates the result of `new`, honouring `new.target`. The proposal reads
/// `prototype` last, after every argument has been validated, and an object
/// whose `prototype` is not an object gets the class's own prototype rather
/// than `Object.prototype`.
pub(super) fn construct<H: Host>(
    machine: &mut Machine<'_, H>,
    value: TemporalObject,
) -> Result<BuiltinOutcome, EvalFailure> {
    let new_target = machine.current_new_target();
    let prototype = machine.get_named_property(new_target, "prototype")?;
    let prototype = if is_object(machine, prototype)? {
        prototype
    } else {
        machine.intrinsics.builtins.temporal_prototype(value.kind())
    };
    allocate(machine, value, prototype).map(BuiltinOutcome::Value)
}

fn allocate<H: Host>(
    machine: &mut Machine<'_, H>,
    value: TemporalObject,
    prototype: Value,
) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::Temporal {
            value: Box::new(value),
            properties: PropertyMap::default(),
            prototype: Some(prototype),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)
}

/// Throws unless this call came through `new`.
pub(super) fn require_new<H: Host>(
    machine: &mut Machine<'_, H>,
    constructing: bool,
    name: &str,
) -> Result<(), EvalFailure> {
    if constructing {
        Ok(())
    } else {
        Err(type_error(
            machine,
            format!("Temporal.{name} constructor requires new"),
        ))
    }
}

pub(super) fn string_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    text: &str,
) -> Result<BuiltinOutcome, EvalFailure> {
    allocate_string(machine, EcmaString::encode(text)).map(BuiltinOutcome::Value)
}

pub(super) fn number_outcome(value: f64) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(crate::number_value(value)))
}

/// `valueOf` on every Temporal class: comparison must be explicit.
pub(super) fn value_of_throws<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Err(type_error(
        machine,
        "Temporal objects are not comparable with valueOf; use compare or equals",
    ))
}

/// The value of a BigInt the caller has already produced with ToBigInt. One
/// too large for `i128` is out of every Temporal range.
pub(super) fn bigint_to_i128<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<i128, EvalFailure> {
    let text = super::bigint::bigint_from_value(machine, value)?
        .expect("ToBigInt produces a BigInt")
        .to_string_radix(10);
    text.parse()
        .map_err(|_| range_error(machine, "BigInt outside the Temporal range"))
}

pub(super) fn bigint_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    value: i128,
) -> Result<BuiltinOutcome, EvalFailure> {
    machine
        .allocate(HeapEntry::BigInt(value.to_string()))
        .map(BuiltinOutcome::Value)
        .map_err(EvalFailure::Runtime)
}

/// The argument at `index`, `undefined` when absent.
pub(super) fn arg(args: &[Value], index: usize) -> Value {
    args.get(index).copied().unwrap_or(Value::UNDEFINED)
}
