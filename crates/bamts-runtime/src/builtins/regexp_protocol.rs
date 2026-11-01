//! The observable accessors of `%RegExp.prototype%`.

use bamts_bytecode::{EcmaString, EcmaStringBuilder};
use bamts_native::Value;

use super::regexp::regexp_parts;
use super::{allocate_string, type_error};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine};

fn require_object<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
    operation: &'static str,
) -> Result<(), EvalFailure> {
    if machine.is_object(value) {
        Ok(())
    } else {
        Err(type_error(operation))
    }
}

fn contains_flag(flags: &EcmaString, flag: u8) -> bool {
    flags.as_units().contains(&u16::from(flag))
}

/// Whether a RegExp receiver owns flag `flag`, for the flag accessors. The
/// prototype itself answers `undefined`, which is what makes it inspectable.
fn has_flag<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    flag: u8,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_object(machine, this, "RegExp flag getter requires an object")?;
    if let Some((_, flags)) = regexp_parts(machine, this) {
        return Ok(BuiltinOutcome::Value(Value::boolean(contains_flag(
            &flags, flag,
        ))));
    }
    if this == machine.intrinsics.regexp_prototype() {
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    }
    Err(type_error("RegExp flag getter requires a RegExp"))
}

macro_rules! flag_getter {
    ($name:ident, $flag:literal) => {
        fn $name<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            has_flag(machine, this, $flag)
        }
    };
}
flag_getter!(dot_all, b's');
flag_getter!(global, b'g');
flag_getter!(has_indices, b'd');
flag_getter!(ignore_case, b'i');
flag_getter!(multiline, b'm');
flag_getter!(sticky, b'y');
flag_getter!(unicode, b'u');
flag_getter!(unicode_sets, b'v');

/// `get RegExp.prototype.flags`: built from the individual accessors, in
/// `dgimsuvy` order, so each one is an observable `Get`.
pub(super) fn flags_getter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_object(
        machine,
        this,
        "RegExp.prototype.flags getter requires an object",
    )?;
    let mut flags = EcmaStringBuilder::new();
    for (name, flag) in [
        ("hasIndices", b'd'),
        ("global", b'g'),
        ("ignoreCase", b'i'),
        ("multiline", b'm'),
        ("dotAll", b's'),
        ("unicode", b'u'),
        ("unicodeSets", b'v'),
        ("sticky", b'y'),
    ] {
        let value = machine.get_named_property(this, name)?;
        if machine.to_boolean(value) {
            flags.push_unit(u16::from(flag));
        }
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        flags.finish(),
    )?))
}

/// Installs the flag accessors.
pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    builtins: &mut BuiltinTable<H>,
    prototype: Value,
) {
    use super::install_function;
    use crate::intrinsics::BuiltinHandler;

    for (property, getter_name, handler) in [
        ("dotAll", "get dotAll", dot_all::<H> as BuiltinHandler<H>),
        ("global", "get global", global::<H>),
        ("hasIndices", "get hasIndices", has_indices::<H>),
        ("ignoreCase", "get ignoreCase", ignore_case::<H>),
        ("multiline", "get multiline", multiline::<H>),
        ("sticky", "get sticky", sticky::<H>),
        ("unicode", "get unicode", unicode::<H>),
        ("unicodeSets", "get unicodeSets", unicode_sets::<H>),
    ] {
        let getter = install_function(heap, builtins, getter_name, 0, handler);
        super::regexp::define_getter(heap, prototype, property, getter);
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::{Limits, ThrowOrigin};

    fn regexp(machine: &mut Machine<'_, TestHost>, pattern: &str, flags: &str) -> Value {
        let constructor = machine.intrinsics.global("RegExp").unwrap();
        let pattern = allocate_string(machine, EcmaString::encode(pattern)).unwrap();
        let flags = allocate_string(machine, EcmaString::encode(flags)).unwrap();
        machine
            .construct_value(constructor, &[pattern, flags])
            .unwrap()
    }

    #[test]
    fn flag_accessors_answer_for_regexps_and_the_prototype_only() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let value = regexp(&mut machine, "x", "gi");
        assert_eq!(
            machine.get_named_property(value, "global").unwrap(),
            Value::TRUE
        );
        assert_eq!(
            machine.get_named_property(value, "sticky").unwrap(),
            Value::FALSE
        );
        let key = crate::PropertyKey::Named(EcmaString::encode("global"));
        assert_eq!(
            machine.own_descriptor(value, &key).unwrap(),
            None,
            "a flag is an accessor on the prototype, not an own property"
        );
        let prototype = machine.intrinsics.regexp_prototype();
        assert_eq!(
            machine.get_named_property(prototype, "global").unwrap(),
            Value::UNDEFINED
        );
        let object = ordinary_object(&mut machine);
        machine
            .internal_set_prototype_of(object, Some(prototype))
            .unwrap();
        assert!(matches!(
            machine.get_named_property(object, "global"),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn flags_reads_each_accessor_so_an_override_is_seen() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let object = ordinary_object(&mut machine);
        for (name, value) in [("global", Value::TRUE), ("sticky", Value::int32(1))] {
            machine.set_data_property(object, name, value).unwrap();
        }
        let BuiltinOutcome::Value(flags) = flags_getter(&mut machine, object, &[], false).unwrap()
        else {
            panic!("the flags getter returns a value");
        };
        assert!(machine.string_value(flags).unwrap().eq_ascii("gy"));
        assert!(matches!(
            flags_getter(&mut machine, Value::int32(1), &[], false),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }
}
