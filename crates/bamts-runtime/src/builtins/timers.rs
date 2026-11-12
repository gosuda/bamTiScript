//! Node-compatible `setTimeout`/`clearTimeout` and `setInterval`/`clearInterval`,
//! installed only when the host exposes a [`crate::TimerProvider`]. The builtins
//! validate and coerce their arguments; the machine owns the live timer table,
//! ordering, and identifiers. An interval re-arms itself after each fire until
//! its handle is cleared.

use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::Value;

use super::install_function;
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, ThrowOrigin};

pub(crate) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let set_timeout = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "setTimeout",
            length: 2,
            handler: set_timeout::<H>,
        },
    );
    globals.insert(EcmaString::encode("setTimeout"), set_timeout);
    let clear_timeout = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "clearTimeout",
            length: 1,
            handler: clear_timeout::<H>,
        },
    );
    globals.insert(EcmaString::encode("clearTimeout"), clear_timeout);
    let set_interval = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "setInterval",
            length: 2,
            handler: set_interval::<H>,
        },
    );
    globals.insert(EcmaString::encode("setInterval"), set_interval);
    let clear_interval = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "clearInterval",
            length: 1,
            handler: clear_interval::<H>,
        },
    );
    globals.insert(EcmaString::encode("clearInterval"), clear_interval);
}

fn set_timeout<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "setTimeout is not a constructor",
        }));
    }
    let callback = args.first().copied().unwrap_or(Value::UNDEFINED);
    // Callable validation precedes delay coercion so a coercion side effect
    // cannot arm a timer for a non-callable callback.
    if !machine.is_callable(callback)? {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "setTimeout callback is not a function",
        }));
    }
    let delay_arg = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let delay_number = super::value_number(machine.coerce_number_observable(delay_arg)?);
    let delay_ms = clamp_delay(delay_number);
    let forwarded = args.get(2..).unwrap_or(&[]).to_vec();
    let handle = machine.schedule_timeout(callback, delay_ms, forwarded)?;
    Ok(BuiltinOutcome::Value(handle))
}

fn clear_timeout<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "clearTimeout is not a constructor",
        }));
    }
    let handle = args.first().copied().unwrap_or(Value::UNDEFINED);
    machine.clear_timeout(handle)?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn set_interval<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "setInterval is not a constructor",
        }));
    }
    let callback = args.first().copied().unwrap_or(Value::UNDEFINED);
    // Callable validation precedes delay coercion so a coercion side effect
    // cannot arm a timer for a non-callable callback.
    if !machine.is_callable(callback)? {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "setInterval callback is not a function",
        }));
    }
    let delay_arg = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let delay_number = super::value_number(machine.coerce_number_observable(delay_arg)?);
    let delay_ms = clamp_delay(delay_number);
    let forwarded = args.get(2..).unwrap_or(&[]).to_vec();
    let handle = machine.schedule_interval(callback, delay_ms, forwarded)?;
    Ok(BuiltinOutcome::Value(handle))
}

fn clear_interval<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "clearInterval is not a constructor",
        }));
    }
    let handle = args.first().copied().unwrap_or(Value::UNDEFINED);
    // Intervals and timeouts share the same handle/id space, so the same
    // machine-level clear path disposes either.
    machine.clear_timeout(handle)?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

/// Node 24 delay coercion: `NaN`, values below `1`, and values above
/// `2_147_483_647` clamp to `1`; every other value truncates toward zero to an
/// integer millisecond count.
fn clamp_delay(delay: f64) -> u32 {
    if !(1.0..=2_147_483_647.0).contains(&delay) {
        1
    } else {
        delay.trunc() as u32
    }
}
