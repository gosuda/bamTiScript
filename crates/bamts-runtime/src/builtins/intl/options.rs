//! Option reading. Every function here performs exactly the property reads and
//! conversions its abstract operation does; callers sequence them in the order
//! ECMA-402 lists them, which test262 observes through getters and Proxies.

use bamts_native::Value;

use super::range_error;
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
