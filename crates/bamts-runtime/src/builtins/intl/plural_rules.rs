//! `Intl.PluralRules`.

use bamts_native::{Decoded, Value};

use super::options::{
    canonicalize_locale_list, coerce_options_to_object, digit_options, locale_matcher_option,
    matcher_name, string_option,
};
use super::{
    Class, allocate, arg, define_field, install_class, instance_prototype, intl_record, new_object,
    range_error, require_new, service_failure, string_array, string_outcome, string_value,
    supported_locales_outcome, type_error,
};
use crate::intl::locale_data::{DATA, IntlData};
use crate::intl::number_data::NoHostLocale;
use crate::intl::plural_rules::{PluralRules, PluralRulesOptions};
use crate::intl::{IntlKind, IntlObject};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
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
            kind: IntlKind::PluralRules,
            name: "PluralRules",
            tag: "Intl.PluralRules",
            length: 0,
            constructor: constructor::<H>,
            statics: &[("supportedLocalesOf", 1, supported_locales_of::<H>)],
            getters: &[],
            methods: &[
                ("resolvedOptions", 0, resolved_options::<H>),
                ("select", 1, select::<H>),
                ("selectRange", 2, select_range::<H>),
            ],
        },
    );
}

fn to_u8(value: Option<f64>) -> Option<u8> {
    value.map(|value| value as u8)
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_new(machine, constructing, "PluralRules")?;
    let prototype = instance_prototype(machine, IntlKind::PluralRules, constructing)?;
    let requested = canonicalize_locale_list(machine, arg(args, 0))?;
    let options = coerce_options_to_object(machine, arg(args, 1))?;
    let matcher = locale_matcher_option(machine, options)?;
    let plural_type = string_option(machine, options, "type", &["cardinal", "ordinal"])?;
    let notation = string_option(
        machine,
        options,
        "notation",
        &["standard", "scientific", "engineering", "compact"],
    )?;
    let compact_display = string_option(machine, options, "compactDisplay", &["short", "long"])?;
    let compact = notation.as_deref() == Some("compact");
    let digits = digit_options(machine, options, compact)?;
    let resolved = PluralRulesOptions {
        locale_matcher: Some(matcher_name(matcher).to_owned()),
        plural_type,
        minimum_integer_digits: to_u8(digits.minimum_integer_digits),
        minimum_fraction_digits: to_u8(digits.minimum_fraction_digits),
        maximum_fraction_digits: to_u8(digits.maximum_fraction_digits),
        minimum_significant_digits: to_u8(digits.minimum_significant_digits),
        maximum_significant_digits: to_u8(digits.maximum_significant_digits),
        rounding_priority: digits.rounding_priority,
        rounding_increment: digits.rounding_increment.map(|value| value as u16),
        rounding_mode: digits.rounding_mode,
        trailing_zero_display: digits.trailing_zero_display,
        notation,
        compact_display,
    };
    let data: &'static IntlData = &DATA;
    let rules = PluralRules::try_new(&requested, &resolved, data, &NoHostLocale)
        .map_err(|error| service_failure(machine, &error))?;
    allocate(machine, IntlObject::PluralRules(rules), prototype).map(BuiltinOutcome::Value)
}

fn supported_locales_of<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    supported_locales_outcome(machine, args)
}

fn this_rules<'a, H: Host>(
    machine: &'a Machine<'_, H>,
    this: Value,
) -> Result<Option<&'a PluralRules<'static>>, EvalFailure> {
    Ok(match intl_record(machine, this)? {
        Some(IntlObject::PluralRules(rules)) => Some(rules),
        _ => None,
    })
}

fn not_plural_rules<H: Host>(machine: &mut Machine<'_, H>) -> EvalFailure {
    type_error(machine, "receiver is not an Intl.PluralRules")
}

fn to_number<H: Host>(machine: &mut Machine<'_, H>, value: Value) -> Result<f64, EvalFailure> {
    let number = machine.coerce_number_observable(value)?;
    Ok(match number.decode() {
        Some(Decoded::Int32(number)) => f64::from(number as i32),
        Some(Decoded::Number(number)) => number,
        _ => f64::NAN,
    })
}

fn select<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if this_rules(machine, this)?.is_none() {
        return Err(not_plural_rules(machine));
    }
    let number = to_number(machine, arg(args, 0))?;
    let Some(rules) = this_rules(machine, this)? else {
        return Err(not_plural_rules(machine));
    };
    let category = rules.select(number);
    let category = category.map_err(|error| service_failure(machine, &error))?;
    string_outcome(machine, category.as_str())
}

fn select_range<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if this_rules(machine, this)?.is_none() {
        return Err(not_plural_rules(machine));
    }
    let (start, end) = (arg(args, 0), arg(args, 1));
    if start == Value::UNDEFINED || end == Value::UNDEFINED {
        return Err(type_error(machine, "a range needs two ends"));
    }
    let start = to_number(machine, start)?;
    let end = to_number(machine, end)?;
    if start.is_nan() || end.is_nan() {
        return Err(range_error(machine, "a range end is not a number"));
    }
    let Some(rules) = this_rules(machine, this)? else {
        return Err(not_plural_rules(machine));
    };
    let category = rules.select_range(start, end);
    let category = category.map_err(|error| service_failure(machine, &error))?;
    string_outcome(machine, category.as_str())
}

fn resolved_options<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let Some(rules) = this_rules(machine, this)? else {
        return Err(not_plural_rules(machine));
    };
    let resolved = rules.resolved_options();
    let result = new_object(machine)?;
    let text = |machine: &mut Machine<'_, H>, name: &str, value: &str| {
        let value = string_value(machine, value)?;
        define_field(machine, result, name, value)
    };
    let number = |machine: &mut Machine<'_, H>, name: &str, value: u16| {
        define_field(machine, result, name, crate::number_value(f64::from(value)))
    };
    text(machine, "locale", &resolved.locale)?;
    text(machine, "type", resolved.plural_type.as_str())?;
    text(machine, "notation", &resolved.notation)?;
    if let Some(display) = &resolved.compact_display {
        text(machine, "compactDisplay", display)?;
    }
    number(
        machine,
        "minimumIntegerDigits",
        u16::from(resolved.minimum_integer_digits),
    )?;
    for (name, value) in [
        ("minimumFractionDigits", resolved.minimum_fraction_digits),
        ("maximumFractionDigits", resolved.maximum_fraction_digits),
        (
            "minimumSignificantDigits",
            resolved.minimum_significant_digits,
        ),
        (
            "maximumSignificantDigits",
            resolved.maximum_significant_digits,
        ),
    ] {
        if let Some(value) = value {
            number(machine, name, u16::from(value))?;
        }
    }
    let categories: Vec<String> = resolved
        .plural_categories
        .iter()
        .map(|category| category.as_str().to_owned())
        .collect();
    let categories = string_array(machine, &categories)?;
    define_field(machine, result, "pluralCategories", categories)?;
    number(machine, "roundingIncrement", resolved.rounding_increment)?;
    text(machine, "roundingMode", resolved.rounding_mode.as_str())?;
    text(
        machine,
        "roundingPriority",
        resolved.rounding_priority.as_str(),
    )?;
    text(
        machine,
        "trailingZeroDisplay",
        resolved.trailing_zero_display.as_str(),
    )?;
    Ok(BuiltinOutcome::Value(result))
}
