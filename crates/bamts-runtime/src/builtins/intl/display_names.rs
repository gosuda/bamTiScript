//! `Intl.DisplayNames`.

use bamts_native::Value;

use super::options::{
    canonicalize_locale_list, get_options_object, locale_matcher_option, matcher_name,
    string_option,
};
use super::{
    Class, allocate, arg, define_field, install_class, instance_prototype, intl_record, new_object,
    optional_string_outcome, require_new, service_failure, string_value, supported_locales_outcome,
    type_error,
};
use crate::intl::locale_data::{DATA, IntlData};
use crate::intl::number_data::NoHostLocale;
use crate::intl::plural_rules::{DisplayNames, DisplayNamesOptions, DisplayNamesType};
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
            kind: IntlKind::DisplayNames,
            name: "DisplayNames",
            tag: "Intl.DisplayNames",
            length: 2,
            constructor: constructor::<H>,
            statics: &[("supportedLocalesOf", 1, supported_locales_of::<H>)],
            getters: &[],
            methods: &[
                ("of", 1, of::<H>),
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
    require_new(machine, constructing, "DisplayNames")?;
    let prototype = instance_prototype(machine, IntlKind::DisplayNames, constructing)?;
    let requested = canonicalize_locale_list(machine, arg(args, 0))?;
    if arg(args, 1) == Value::UNDEFINED {
        return Err(type_error(machine, "options are required"));
    }
    let options = get_options_object(machine, arg(args, 1))?;
    let matcher = locale_matcher_option(machine, options)?;
    let style = string_option(machine, options, "style", &["narrow", "short", "long"])?;
    let name_type = string_option(
        machine,
        options,
        "type",
        &[
            "language",
            "region",
            "script",
            "currency",
            "calendar",
            "dateTimeField",
        ],
    )?;
    if name_type.is_none() {
        return Err(type_error(machine, "type is required"));
    }
    let fallback = string_option(machine, options, "fallback", &["code", "none"])?;
    let language_display = string_option(
        machine,
        options,
        "languageDisplay",
        &["dialect", "standard"],
    )?;
    let resolved = DisplayNamesOptions {
        locale_matcher: Some(matcher_name(matcher).to_owned()),
        name_type,
        style,
        fallback,
        language_display,
    };
    let data: &'static IntlData = &DATA;
    let names = DisplayNames::try_new(&requested, &resolved, data, &NoHostLocale)
        .map_err(|error| service_failure(machine, &error))?;
    allocate(machine, IntlObject::DisplayNames(names), prototype).map(BuiltinOutcome::Value)
}

fn supported_locales_of<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    supported_locales_outcome(machine, args)
}

fn this_names<'a, H: Host>(
    machine: &'a Machine<'_, H>,
    this: Value,
) -> Result<Option<&'a DisplayNames<'static>>, EvalFailure> {
    Ok(match intl_record(machine, this)? {
        Some(IntlObject::DisplayNames(names)) => Some(names),
        _ => None,
    })
}

fn not_display_names<H: Host>(machine: &mut Machine<'_, H>) -> EvalFailure {
    type_error(machine, "receiver is not an Intl.DisplayNames")
}

fn of<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if this_names(machine, this)?.is_none() {
        return Err(not_display_names(machine));
    }
    let code = machine
        .coerce_string_observable(arg(args, 0))?
        .to_utf8_lossy();
    let Some(names) = this_names(machine, this)? else {
        return Err(not_display_names(machine));
    };
    let name = names.of(&code);
    let name = name.map_err(|error| service_failure(machine, &error))?;
    optional_string_outcome(machine, name.as_deref())
}

fn resolved_options<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let Some(names) = this_names(machine, this)? else {
        return Err(not_display_names(machine));
    };
    let resolved = names.resolved_options();
    let result = new_object(machine)?;
    let mut fields = vec![
        ("locale", resolved.locale.as_str()),
        ("style", resolved.style.as_str()),
        ("type", resolved.name_type.as_str()),
        ("fallback", resolved.fallback.as_str()),
    ];
    if resolved.name_type == DisplayNamesType::Language {
        fields.push(("languageDisplay", resolved.language_display.as_str()));
    }
    for (name, text) in fields {
        let value = string_value(machine, text)?;
        define_field(machine, result, name, value)?;
    }
    Ok(BuiltinOutcome::Value(result))
}
