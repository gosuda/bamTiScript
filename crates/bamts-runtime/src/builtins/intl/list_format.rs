//! `Intl.ListFormat`.

use bamts_native::Value;

use super::super::allocate_array;
use super::options::{
    canonicalize_locale_list, get_options_object, locale_matcher_option, matcher_name,
    string_option,
};
use super::{
    Class, allocate, arg, define_field, install_class, instance_prototype, intl_record, new_object,
    part_object, require_new, service_failure, string_iterable_to_list, string_outcome,
    string_value, supported_locales_outcome, type_error,
};
use crate::intl::locale_data::{DATA, IntlData};
use crate::intl::number_data::NoHostLocale;
use crate::intl::plural_rules::{ListFormat, ListFormatOptions, ListPartKind};
use crate::intl::{IntlKind, IntlObject};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
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
            kind: IntlKind::ListFormat,
            name: "ListFormat",
            tag: "Intl.ListFormat",
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

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_new(machine, constructing, "ListFormat")?;
    let prototype = instance_prototype(machine, IntlKind::ListFormat, constructing)?;
    let requested = canonicalize_locale_list(machine, arg(args, 0))?;
    let options = get_options_object(machine, arg(args, 1))?;
    let matcher = locale_matcher_option(machine, options)?;
    let list_type = string_option(
        machine,
        options,
        "type",
        &["conjunction", "disjunction", "unit"],
    )?;
    let style = string_option(machine, options, "style", &["long", "short", "narrow"])?;
    let resolved = ListFormatOptions {
        locale_matcher: Some(matcher_name(matcher).to_owned()),
        list_type,
        style,
    };
    let data: &'static IntlData = &DATA;
    let format = ListFormat::try_new(&requested, &resolved, data, &NoHostLocale)
        .map_err(|error| service_failure(machine, &error))?;
    allocate(machine, IntlObject::ListFormat(format), prototype).map(BuiltinOutcome::Value)
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
) -> Result<Option<&'a ListFormat<'static>>, EvalFailure> {
    Ok(match intl_record(machine, this)? {
        Some(IntlObject::ListFormat(format)) => Some(format),
        _ => None,
    })
}

fn not_a_list_format<H: Host>(machine: &mut Machine<'_, H>) -> EvalFailure {
    type_error(machine, "receiver is not an Intl.ListFormat")
}

fn format<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if this_format(machine, this)?.is_none() {
        return Err(not_a_list_format(machine));
    }
    let elements = string_iterable_to_list(machine, arg(args, 0))?;
    let Some(format) = this_format(machine, this)? else {
        return Err(not_a_list_format(machine));
    };
    let text = format.format(&elements);
    let text = text.map_err(|error| service_failure(machine, &error))?;
    string_outcome(machine, &text)
}

fn format_to_parts<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if this_format(machine, this)?.is_none() {
        return Err(not_a_list_format(machine));
    }
    let elements = string_iterable_to_list(machine, arg(args, 0))?;
    let Some(format) = this_format(machine, this)? else {
        return Err(not_a_list_format(machine));
    };
    let parts = format.format_to_parts(&elements);
    let parts = parts.map_err(|error| service_failure(machine, &error))?;
    let mut elements = Vec::with_capacity(parts.len());
    for part in &parts {
        let part_type = match part.kind {
            ListPartKind::Element => "element",
            ListPartKind::Literal => "literal",
        };
        elements.push(part_object(machine, part_type, &part.value, None)?);
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
        return Err(not_a_list_format(machine));
    };
    let resolved = format.resolved_options();
    let result = new_object(machine)?;
    for (name, text) in [
        ("locale", resolved.locale.as_str()),
        ("type", resolved.list_type.as_str()),
        ("style", resolved.style.as_str()),
    ] {
        let value = string_value(machine, text)?;
        define_field(machine, result, name, value)?;
    }
    Ok(BuiltinOutcome::Value(result))
}
