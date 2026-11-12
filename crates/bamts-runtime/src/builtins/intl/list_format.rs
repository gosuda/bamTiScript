//! `Intl.ListFormat`.

use bamts_native::Value;

use super::super::{allocate_array, allocate_string};
use super::options::{
    canonicalize_locale_list, get_options_object, locale_matcher_option, matcher_name,
    string_option,
};
use super::{
    Class, allocate, arg, define_field, install_class, instance_prototype, intl_record, new_object,
    part_object, require_new, service_failure, string_iterable_to_list, string_value,
    supported_locales_outcome, type_error,
};
use crate::intl::locale_data::{DATA, IntlData};
use crate::intl::number_data::NoHostLocale;
use crate::intl::plural_rules::{ListFormat, ListFormatOptions, ListPartKind};
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
    allocate_string(machine, text).map(BuiltinOutcome::Value)
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
        elements.push(part_object(machine, part_type, part.value.clone(), None)?);
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

#[cfg(test)]
mod tests {
    use super::super::super::allocate_string;
    use super::super::super::test_support::{TestHost, blank_program};
    use super::*;
    use crate::Limits;
    use bamts_bytecode::EcmaString;

    const LONE_SURROGATE_UNITS: [[u16; 1]; 2] = [[0xD800], [0xDC00]];
    const TYPES: [(&str, &str); 2] = [("conjunction", ", and "), ("disjunction", ", or ")];

    fn list_format(machine: &mut Machine<'_, TestHost>, list_type: &str) -> Value {
        let intl = machine.intrinsics.global("Intl").expect("Intl");
        let constructor = machine
            .get_named_property(intl, "ListFormat")
            .expect("Intl.ListFormat");
        let options = super::new_object(machine).expect("options object");
        let type_name = super::string_value(machine, list_type).expect("type string");
        super::define_field(machine, options, "type", type_name).expect("type option");
        let locales = super::string_value(machine, "en").expect("locales string");
        machine
            .construct_value(constructor, &[locales, options])
            .expect("a list format")
    }

    fn element_array(machine: &mut Machine<'_, TestHost>, elements: &[&[u16]]) -> Value {
        let mut values = Vec::with_capacity(elements.len());
        for element in elements {
            values.push(
                allocate_string(machine, EcmaString::from_units(element)).expect("element string"),
            );
        }
        allocate_array(machine, values).expect("element array")
    }

    fn formatted_units(
        machine: &mut Machine<'_, TestHost>,
        format: Value,
        elements: &[&[u16]],
    ) -> Vec<u16> {
        let list = element_array(machine, elements);
        let method = machine
            .get_named_property(format, "format")
            .expect("format method");
        let text = machine.call_value(method, format, &[list]).expect("text");
        machine.string_value(text).expect("a string").as_units().to_vec()
    }

    fn part_units(
        machine: &mut Machine<'_, TestHost>,
        format: Value,
        elements: &[&[u16]],
    ) -> Vec<(&'static str, Vec<u16>)> {
        let list = element_array(machine, elements);
        let method = machine
            .get_named_property(format, "formatToParts")
            .expect("formatToParts method");
        let parts = machine.call_value(method, format, &[list]).expect("parts");
        let parts = machine
            .array_elements(parts)
            .expect("an array")
            .expect("an array");
        parts
            .into_iter()
            .map(|part| {
                let kind = machine
                    .get_named_property(part, "type")
                    .expect("type property");
                let kind = if machine.string_value(kind).expect("a string").eq_ascii("element") {
                    "element"
                } else {
                    "literal"
                };
                let value = machine
                    .get_named_property(part, "value")
                    .expect("value property");
                let value = machine.string_value(value).expect("a string");
                (kind, value.as_units().to_vec())
            })
            .collect()
    }

    fn joined_units(elements: &[Vec<u16>], separators: &[&str]) -> Vec<u16> {
        let mut joined = Vec::new();
        for (element, separator) in elements.iter().zip(separators) {
            joined.extend(separator.encode_utf16());
            joined.extend_from_slice(element);
        }
        joined
    }

    fn elements_with(lone: [u16; 1], position: usize) -> Vec<Vec<u16>> {
        let mut elements: Vec<Vec<u16>> = ["a", "b", "c"]
            .iter()
            .map(|text| text.encode_utf16().collect())
            .collect();
        elements[position] = lone.to_vec();
        elements
    }

    fn borrowed(elements: &[Vec<u16>]) -> Vec<&[u16]> {
        elements.iter().map(Vec::as_slice).collect()
    }

    fn element_values(parts: &[(&'static str, Vec<u16>)]) -> Vec<Vec<u16>> {
        parts
            .iter()
            .filter(|(kind, _)| *kind == "element")
            .map(|(_, value)| value.clone())
            .collect()
    }

    fn literal_values(parts: &[(&'static str, Vec<u16>)]) -> Vec<Vec<u16>> {
        parts
            .iter()
            .filter(|(kind, _)| *kind == "literal")
            .map(|(_, value)| value.clone())
            .collect()
    }

    #[test]
    fn a_lone_surrogate_element_keeps_its_code_unit_in_formatted_text() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        for (list_type, separator) in TYPES {
            let format = list_format(&mut machine, list_type);
            let separators = ["", ", ", separator];
            for lone in LONE_SURROGATE_UNITS {
                for position in 0..3 {
                    let elements = elements_with(lone, position);
                    let text = formatted_units(&mut machine, format, &borrowed(&elements));
                    assert_eq!(text, joined_units(&elements, &separators));
                }
            }
        }
    }

    #[test]
    fn a_lone_surrogate_element_keeps_its_code_unit_in_every_part() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        for (list_type, separator) in TYPES {
            let format = list_format(&mut machine, list_type);
            let literals = vec![
                ", ".encode_utf16().collect::<Vec<u16>>(),
                separator.encode_utf16().collect::<Vec<u16>>(),
            ];
            for lone in LONE_SURROGATE_UNITS {
                for position in 0..3 {
                    let elements = elements_with(lone, position);
                    let parts = part_units(&mut machine, format, &borrowed(&elements));
                    assert_eq!(element_values(&parts), elements);
                    assert_eq!(literal_values(&parts), literals);
                }
            }
        }
    }
}
