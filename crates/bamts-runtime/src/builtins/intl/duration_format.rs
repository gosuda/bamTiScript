//! `Intl.DurationFormat`.

use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::Value;

use super::super::{allocate_array, allocate_string};
use super::super::temporal::to_temporal_duration;
use super::options::{
    Options, canonicalize_locale_list, get_options_object, locale_matcher_option, number_option,
    string_option,
};
use super::{
    Class, allocate, arg, define_field, install_class, instance_prototype, intl_record,
    is_type_sequence, new_object, part_object, range_error, require_new, string_value,
    supported_locales_outcome, type_error,
};
use crate::intl::duration_format::{
    DurationFormat, DurationPart, UNITS, UnitOptions, UnitStyle, default_unit_options,
    is_valid_unit_style, settled_unit_style,
};
use crate::intl::locale_data::{DATA, IntlData};
use crate::intl::locale_negotiation::resolve_locale;
use crate::intl::{IntlKind, IntlObject};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::temporal::instant_duration::Duration;
use crate::{EvalFailure, HeapEntry, Host, Machine};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    builtins: &mut BuiltinTable<H>,
    namespace: Value,
) {
    install_class(
        heap,
        atoms,
        shapes,
        builtins,
        namespace,
        &Class {
            kind: IntlKind::DurationFormat,
            name: "DurationFormat",
            tag: "Intl.DurationFormat",
            length: 0,
            constructor: constructor::<H>,
            statics: &[("supportedLocalesOf", 1, supported_locales_of::<H>)],
            getters: &[],
            methods: &[
                ("format", 1, format::<H>),
                ("formatToParts", 1, format_to_parts::<H>),
                ("resolvedOptions", 0, resolved_options::<H>),
            ],
        },
    );
}

/// GetDurationUnitOptions for the unit at `index`.
fn unit_options<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    index: usize,
    base: &str,
    previous: Option<UnitStyle>,
) -> Result<UnitOptions, EvalFailure> {
    const DATE_STYLES: &[&str] = &["long", "short", "narrow"];
    const TIME_STYLES: &[&str] = &["long", "short", "narrow", "numeric", "2-digit"];
    const SUBSECOND_STYLES: &[&str] = &["long", "short", "narrow", "numeric"];
    let allowed = match index {
        0..=3 => DATE_STYLES,
        4..=6 => TIME_STYLES,
        _ => SUBSECOND_STYLES,
    };
    let unit = UNITS[index];
    let requested = string_option(machine, options, unit, allowed)?;
    let base_style = if base == "digital" {
        UnitStyle::Short
    } else {
        UnitStyle::parse(base)
    };
    let (mut style, mut always) = match requested {
        Some(style) => (UnitStyle::parse(&style), true),
        None => default_unit_options(index, base == "digital", base_style, previous),
    };
    if style == UnitStyle::Numeric && index > 6 {
        style = UnitStyle::Fractional;
        always = false;
    }
    let display = string_option(
        machine,
        options,
        &format!("{unit}Display"),
        &["auto", "always"],
    )?;
    let always = display.map_or(always, |display| display == "always");
    if !is_valid_unit_style(style, always, previous) {
        return Err(range_error(
            machine,
            format!("{unit} cannot use this style here"),
        ));
    }
    Ok(UnitOptions {
        style: settled_unit_style(index, style, previous),
        always,
    })
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_new(machine, constructing, "DurationFormat")?;
    let prototype = instance_prototype(machine, IntlKind::DurationFormat, constructing)?;
    let format = create_duration_format(machine, arg(args, 0), arg(args, 1))?;
    allocate(
        machine,
        IntlObject::DurationFormat(Box::new(format)),
        prototype,
    )
    .map(BuiltinOutcome::Value)
}

/// The body of the constructor, which `toLocaleString` shares.
pub(super) fn create_duration_format<H: Host>(
    machine: &mut Machine<'_, H>,
    locales: Value,
    options: Value,
) -> Result<DurationFormat, EvalFailure> {
    let requested = canonicalize_locale_list(machine, locales)?;
    let options = get_options_object(machine, options)?;
    let matcher = locale_matcher_option(machine, options)?;
    let numbering_system = string_option(machine, options, "numberingSystem", &[])?;
    let mut locale_options = BTreeMap::new();
    if let Some(name) = numbering_system {
        if !is_type_sequence(&name) {
            let message = format!("{name} is not a valid numbering system");
            return Err(range_error(machine, message));
        }
        locale_options.insert(String::from("nu"), name.to_ascii_lowercase());
    }
    let resolved = resolve_locale(
        &requested,
        &locale_options,
        &[String::from("nu")],
        matcher,
        &*DATA,
    )
    .map_err(|error| range_error(machine, error.to_string()))?;
    let style = string_option(
        machine,
        options,
        "style",
        &["long", "short", "narrow", "digital"],
    )?
    .unwrap_or_else(|| String::from("short"));
    let mut units = [UnitOptions {
        style: UnitStyle::Short,
        always: false,
    }; 10];
    let mut previous = None;
    for (index, slot) in units.iter_mut().enumerate() {
        let unit = unit_options(machine, options, index, &style, previous)?;
        *slot = unit;
        previous = Some(unit.style);
    }
    let fractional_digits =
        number_option(machine, options, "fractionalDigits", 0.0, 9.0)?.map(|digits| digits as u8);
    Ok(DurationFormat {
        locale: resolved.locale,
        numbering_system: resolved.values.get("nu").cloned().unwrap_or_default(),
        style,
        units,
        fractional_digits,
    })
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
) -> Result<Option<&'a DurationFormat>, EvalFailure> {
    Ok(match intl_record(machine, this)? {
        Some(IntlObject::DurationFormat(format)) => Some(format),
        _ => None,
    })
}

fn not_a_duration_format<H: Host>(machine: &mut Machine<'_, H>) -> EvalFailure {
    type_error(machine, "receiver is not an Intl.DurationFormat")
}

/// ToDurationRecord, then the partition.
fn parts<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    duration: Value,
) -> Result<Vec<DurationPart>, EvalFailure> {
    if this_format(machine, this)?.is_none() {
        return Err(not_a_duration_format(machine));
    }
    let duration = to_temporal_duration(machine, duration)?;
    let Some(format) = this_format(machine, this)? else {
        return Err(not_a_duration_format(machine));
    };
    let format = format.clone();
    duration_parts(machine, &format, &duration)
}

/// PartitionDurationFormatPattern.
pub(super) fn duration_parts<H: Host>(
    machine: &mut Machine<'_, H>,
    format: &DurationFormat,
    duration: &Duration,
) -> Result<Vec<DurationPart>, EvalFailure> {
    let fields = [
        duration.years,
        duration.months,
        duration.weeks,
        duration.days,
        duration.hours,
        duration.minutes,
        duration.seconds,
        duration.milliseconds,
        duration.microseconds,
        duration.nanoseconds,
    ];
    let data: &'static IntlData = &DATA;
    let result = format.partition(&fields, data);
    result.map_err(|error| range_error(machine, error.to_string()))
}

fn format<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let parts = parts(machine, this, arg(args, 0))?;
    let mut text = Vec::new();
    for part in &parts {
        text.extend_from_slice(part.value.as_units());
    }
    allocate_string(machine, EcmaString::from_units(&text)).map(BuiltinOutcome::Value)
}

fn format_to_parts<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let parts = parts(machine, this, arg(args, 0))?;
    let mut elements = Vec::with_capacity(parts.len());
    for part in &parts {
        let extra = part.unit.map(|unit| ("unit", unit));
        elements.push(part_object(machine, part.part_type, part.value.clone(), extra)?);
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
        return Err(not_a_duration_format(machine));
    };
    let format = format.clone();
    let result = new_object(machine)?;
    for (name, text) in [
        ("locale", format.locale.as_str()),
        ("numberingSystem", format.numbering_system.as_str()),
        ("style", format.style.as_str()),
    ] {
        let value = string_value(machine, text)?;
        define_field(machine, result, name, value)?;
    }
    for (unit, options) in UNITS.iter().zip(format.units) {
        let value = string_value(machine, options.style.as_str())?;
        define_field(machine, result, unit, value)?;
        let display = if options.always { "always" } else { "auto" };
        let value = string_value(machine, display)?;
        define_field(machine, result, &format!("{unit}Display"), value)?;
    }
    if let Some(digits) = format.fractional_digits {
        define_field(
            machine,
            result,
            "fractionalDigits",
            crate::number_value(f64::from(digits)),
        )?;
    }
    Ok(BuiltinOutcome::Value(result))
}
