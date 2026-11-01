//! Option reading. Every function here performs exactly the property reads and
//! conversions its abstract operation does; callers sequence them in the order
//! ECMA-402 lists them, which test262 observes through getters and Proxies.

use bamts_native::Value;

use super::{is_object, locale_record, range_error, type_error};
use crate::intl::locale_data::DATA;
use crate::intl::locale_negotiation::{LocaleMatcher, canonicalize_unicode_locale_id};
use crate::intrinsics::builtins::array_es2023::{index_key, length_of_array_like};
use crate::{EvalFailure, Host, Machine};

/// A resolved options argument. `None` stands for the empty null-prototype
/// object of `undefined`, which no read can observe.
pub(super) type Options = Option<Value>;

/// CoerceOptionsToObject.
pub(super) fn coerce_options_to_object<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<Options, EvalFailure> {
    if value == Value::UNDEFINED {
        Ok(None)
    } else {
        machine.value_to_object(value).map(Some)
    }
}

/// The value of one option, `undefined` when absent.
pub(super) fn read<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    name: &str,
) -> Result<Value, EvalFailure> {
    match options {
        Some(object) => machine.get_named_property(object, name),
        None => Ok(Value::UNDEFINED),
    }
}

/// GetOption with type string and no default. An empty `allowed` accepts any
/// value.
pub(super) fn string_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    name: &str,
    allowed: &[&str],
) -> Result<Option<String>, EvalFailure> {
    let value = read(machine, options, name)?;
    if value == Value::UNDEFINED {
        return Ok(None);
    }
    let text = machine.coerce_string_observable(value)?.to_utf8_lossy();
    if allowed.is_empty() || allowed.contains(&text.as_str()) {
        Ok(Some(text))
    } else {
        Err(range_error(
            machine,
            format!("{text} is not a valid value for {name}"),
        ))
    }
}

/// GetOption with type boolean and no default.
pub(super) fn boolean_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
    name: &str,
) -> Result<Option<bool>, EvalFailure> {
    let value = read(machine, options, name)?;
    if value == Value::UNDEFINED {
        Ok(None)
    } else {
        Ok(Some(machine.to_boolean(value)))
    }
}

/// The `localeMatcher` option every constructor reads.
pub(super) fn locale_matcher_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Options,
) -> Result<LocaleMatcher, EvalFailure> {
    let value = string_option(machine, options, "localeMatcher", &["lookup", "best fit"])?;
    Ok(if value.as_deref() == Some("lookup") {
        LocaleMatcher::Lookup
    } else {
        LocaleMatcher::BestFit
    })
}

/// CanonicalizeLocaleList. Elements are read and validated one at a time, so
/// an invalid tag stops the walk before any later element is touched.
pub(super) fn canonicalize_locale_list<H: Host>(
    machine: &mut Machine<'_, H>,
    locales: Value,
) -> Result<Vec<String>, EvalFailure> {
    let mut seen = Vec::new();
    if locales == Value::UNDEFINED {
        return Ok(seen);
    }
    if machine.string_value(locales).is_some() || locale_record(machine, locales)?.is_some() {
        add_locale(machine, &mut seen, locales)?;
        return Ok(seen);
    }
    let object = machine.value_to_object(locales)?;
    let length = length_of_array_like(machine, object)?;
    for index in 0..length {
        let key = index_key(index);
        if !machine.internal_has_property(object, &key)? {
            continue;
        }
        let element = machine.get_property_key(object, &key)?;
        if machine.string_value(element).is_none() && !is_object(machine, element)? {
            return Err(type_error(
                machine,
                "a locale must be a string or an object",
            ));
        }
        add_locale(machine, &mut seen, element)?;
    }
    Ok(seen)
}

fn add_locale<H: Host>(
    machine: &mut Machine<'_, H>,
    seen: &mut Vec<String>,
    element: Value,
) -> Result<(), EvalFailure> {
    let tag = match locale_record(machine, element)? {
        Some(tag) => tag.to_string(),
        None => machine.coerce_string_observable(element)?.to_utf8_lossy(),
    };
    let canonical = canonicalize_unicode_locale_id(&tag, &*DATA)
        .map_err(|error| range_error(machine, error.to_string()))?;
    if !seen.contains(&canonical) {
        seen.push(canonical);
    }
    Ok(())
}
