//! `Intl.RelativeTimeFormat`.

use bamts_native::{Decoded, Value};

use super::super::allocate_array;
use super::options::{
    canonicalize_locale_list, coerce_options_to_object, locale_matcher_option, matcher_name,
    string_option,
};
use super::{
    Class, allocate, arg, define_field, install_class, instance_prototype, intl_record,
    is_type_sequence, new_object, part_object, range_error, require_new, service_failure,
    string_outcome, string_value, supported_locales_outcome, type_error,
};
use crate::intl::locale_data::{DATA, IntlData};
use crate::intl::number_data::NoHostLocale;
use crate::intl::plural_rules::{
    NumberPartKind, RelativeTimeFormat, RelativeTimeFormatOptions, RelativeTimePartKind,
};
use crate::intl::{IntlKind, IntlObject};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
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
            kind: IntlKind::RelativeTimeFormat,
            name: "RelativeTimeFormat",
            tag: "Intl.RelativeTimeFormat",
            length: 0,
            constructor: constructor::<H>,
            statics: &[("supportedLocalesOf", 1, supported_locales_of::<H>)],
            getters: &[],
            methods: &[
                ("format", 2, format::<H>),
                ("formatToParts", 2, format_to_parts::<H>),
                ("resolvedOptions", 0, resolved_options::<H>),
            ],
        },
    );
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_new(machine, constructing, "RelativeTimeFormat")?;
    let prototype = instance_prototype(machine, IntlKind::RelativeTimeFormat, constructing)?;
    let requested = canonicalize_locale_list(machine, arg(args, 0))?;
    let options = coerce_options_to_object(machine, arg(args, 1))?;
    let matcher = locale_matcher_option(machine, options)?;
    let numbering_system = string_option(machine, options, "numberingSystem", &[])?;
    if let Some(name) = &numbering_system
        && !is_type_sequence(name)
    {
        let message = format!("{name} is not a valid numbering system");
        return Err(range_error(machine, message));
    }
    let style = string_option(machine, options, "style", &["long", "short", "narrow"])?;
    let numeric = string_option(machine, options, "numeric", &["always", "auto"])?;
    let resolved = RelativeTimeFormatOptions {
        locale_matcher: Some(matcher_name(matcher).to_owned()),
        numeric,
        style,
        numbering_system,
    };
    let data: &'static IntlData = &DATA;
    let format = RelativeTimeFormat::try_new(&requested, &resolved, data, &NoHostLocale)
        .map_err(|error| service_failure(machine, &error))?;
    allocate(machine, IntlObject::RelativeTimeFormat(format), prototype).map(BuiltinOutcome::Value)
}

fn supported_locales_of<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    supported_locales_outcome(machine, args)
}

fn this_format<'a, H: Host>(
    machine: &'a Machine<'_, H>,
    this: Value,
) -> Result<Option<&'a RelativeTimeFormat<'static>>, EvalFailure> {
    Ok(match intl_record(machine, this)? {
        Some(IntlObject::RelativeTimeFormat(format)) => Some(format),
        _ => None,
    })
}

fn not_a_relative_time_format<H: Host>(machine: &mut Machine<'_, H>) -> EvalFailure {
    type_error(machine, "receiver is not an Intl.RelativeTimeFormat")
}

/// The argument conversions `format` and `formatToParts` share.
fn value_and_unit<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
) -> Result<(f64, String), EvalFailure> {
    if this_format(machine, this)?.is_none() {
        return Err(not_a_relative_time_format(machine));
    }
    let number = machine.coerce_number_observable(arg(args, 0))?;
    let number = match number.decode() {
        Some(Decoded::Int32(number)) => f64::from(number as i32),
        Some(Decoded::Number(number)) => number,
        _ => f64::NAN,
    };
    let unit = machine
        .coerce_string_observable(arg(args, 1))?
        .to_utf8_lossy();
    Ok((number, unit))
}

fn format<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, unit) = value_and_unit(machine, this, args)?;
    let Some(format) = this_format(machine, this)? else {
        return Err(not_a_relative_time_format(machine));
    };
    let text = format.format(value, &unit);
    let text = text.map_err(|error| service_failure(machine, &error))?;
    string_outcome(machine, &text)
}

const fn number_part_type(kind: NumberPartKind) -> &'static str {
    match kind {
        NumberPartKind::Integer => "integer",
        NumberPartKind::Group => "group",
        NumberPartKind::Decimal => "decimal",
        NumberPartKind::Fraction => "fraction",
        NumberPartKind::PlusSign => "plusSign",
        NumberPartKind::MinusSign => "minusSign",
        NumberPartKind::Nan => "nan",
        NumberPartKind::Infinity => "infinity",
        NumberPartKind::ExponentSeparator => "exponentSeparator",
        NumberPartKind::ExponentMinusSign => "exponentMinusSign",
        NumberPartKind::ExponentInteger => "exponentInteger",
        NumberPartKind::Compact => "compact",
        NumberPartKind::PercentSign => "percentSign",
        NumberPartKind::Currency => "currency",
        NumberPartKind::Unit => "unit",
        NumberPartKind::Literal => "literal",
    }
}

fn format_to_parts<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (value, unit) = value_and_unit(machine, this, args)?;
    let Some(format) = this_format(machine, this)? else {
        return Err(not_a_relative_time_format(machine));
    };
    let parts = format.format_to_parts(value, &unit);
    let parts = parts.map_err(|error| service_failure(machine, &error))?;
    let mut elements = Vec::with_capacity(parts.len());
    for part in &parts {
        let part_type = match part.kind {
            RelativeTimePartKind::Literal => "literal",
            RelativeTimePartKind::Number(kind) => number_part_type(kind),
        };
        let extra = part.unit.map(|unit| ("unit", unit.as_str()));
        elements.push(part_object(machine, part_type, &part.value, extra)?);
    }
    allocate_array(machine, elements).map(BuiltinOutcome::Value)
}

fn resolved_options<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let Some(format) = this_format(machine, this)? else {
        return Err(not_a_relative_time_format(machine));
    };
    let resolved = format.resolved_options();
    let result = new_object(machine)?;
    for (name, text) in [
        ("locale", resolved.locale.as_str()),
        ("style", resolved.style.as_str()),
        ("numeric", resolved.numeric.as_str()),
        ("numberingSystem", resolved.numbering_system.as_str()),
    ] {
        let value = string_value(machine, text)?;
        define_field(machine, result, name, value)?;
    }
    Ok(BuiltinOutcome::Value(result))
}
