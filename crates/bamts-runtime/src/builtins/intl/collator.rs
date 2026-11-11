//! `Intl.Collator`.

use bamts_native::Value;

use super::options::{Options, canonicalize_locale_list, coerce_options_to_object, read};
use super::{
    Class, allocate, arg, bound_function, define_field, install_class, instance_prototype,
    intl_record, new_object, register_hidden, string_value, supported_locales_outcome, type_error,
};
use crate::intl::collator::{
    CoercedCollatorOption, Collator, CollatorError, CollatorErrorKind, CollatorOptionType,
    CollatorOptionsSource,
};
use crate::intl::locale_data::DATA;
use crate::intl::{IntlKind, IntlObject};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine};

const COMPARE: &str = "Intl.Collator compare";

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    builtins: &mut BuiltinTable<H>,
    namespace: Value,
) {
    register_hidden(builtins, COMPARE, 2, compare_strings::<H>);
    install_class(
        heap,
        atoms,
        shapes,
        builtins,
        namespace,
        &Class {
            kind: IntlKind::Collator,
            name: "Collator",
            tag: "Intl.Collator",
            length: 0,
            constructor: constructor::<H>,
            statics: &[("supportedLocalesOf", 1, supported_locales_of::<H>)],
            getters: &[("compare", "get compare", compare_getter::<H>)],
            methods: &[("resolvedOptions", 0, resolved_options::<H>)],
        },
    );
}

/// The library reads options itself, in specification order, through this
/// adapter. A JavaScript failure cannot cross its error type, so it waits
/// here for the constructor to rethrow.
struct LiveOptions<'a, 'm, H: Host> {
    machine: &'a mut Machine<'m, H>,
    options: Options,
    failure: Option<EvalFailure>,
}

impl<H: Host> LiveOptions<'_, '_, H> {
    fn fail(&mut self, failure: EvalFailure) -> CollatorError {
        self.failure = Some(failure);
        CollatorError::type_error("option read failed")
    }
}

impl<H: Host> CollatorOptionsSource for LiveOptions<'_, '_, H> {
    fn coerce_options_to_object(&mut self) -> Result<(), CollatorError> {
        Ok(())
    }

    fn get_option(
        &mut self,
        property: &'static str,
        option_type: CollatorOptionType,
    ) -> Result<Option<CoercedCollatorOption>, CollatorError> {
        let value = match read(self.machine, self.options, property) {
            Ok(value) => value,
            Err(failure) => return Err(self.fail(failure)),
        };
        if value == Value::UNDEFINED {
            return Ok(None);
        }
        match option_type {
            CollatorOptionType::Boolean => Ok(Some(CoercedCollatorOption::Boolean(
                self.machine.to_boolean(value),
            ))),
            CollatorOptionType::String => match self.machine.coerce_string_observable(value) {
                Ok(text) => Ok(Some(CoercedCollatorOption::String(text.to_utf8_lossy()))),
                Err(failure) => Err(self.fail(failure)),
            },
        }
    }
}

fn collator_failure<H: Host>(machine: &mut Machine<'_, H>, error: CollatorError) -> EvalFailure {
    match error.kind {
        CollatorErrorKind::TypeError => type_error(machine, error.message),
        CollatorErrorKind::RangeError => super::range_error(machine, error.message),
    }
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let prototype = instance_prototype(machine, IntlKind::Collator, constructing)?;
    let collator = create_collator(machine, arg(args, 0), arg(args, 1))?;
    allocate(machine, IntlObject::Collator(collator), prototype).map(BuiltinOutcome::Value)
}

/// InitializeCollator without the object it initializes.
pub(super) fn create_collator<H: Host>(
    machine: &mut Machine<'_, H>,
    locales: Value,
    options: Value,
) -> Result<Collator, EvalFailure> {
    let requested = canonicalize_locale_list(machine, locales)?;
    let options = coerce_options_to_object(machine, options)?;
    let mut live = LiveOptions {
        machine,
        options,
        failure: None,
    };
    let source: Option<&mut dyn CollatorOptionsSource> = if options.is_some() {
        Some(&mut live)
    } else {
        None
    };
    let result = Collator::new(&requested, source, &*DATA);
    let LiveOptions {
        machine, failure, ..
    } = live;
    match (result, failure) {
        (_, Some(failure)) => Err(failure),
        (Ok(collator), None) => Ok(collator),
        (Err(error), None) => Err(collator_failure(machine, error)),
    }
}

fn supported_locales_of<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    supported_locales_outcome(machine, args)
}

fn compare_getter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !matches!(intl_record(machine, this)?, Some(IntlObject::Collator(_))) {
        return Err(type_error(machine, "receiver is not an Intl.Collator"));
    }
    bound_function(machine, this, COMPARE, 2)
}

/// The function `compare` hands out, bound to its collator.
fn compare_strings<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let left = machine.coerce_string_observable(arg(args, 0))?;
    let right = machine.coerce_string_observable(arg(args, 1))?;
    let Some(IntlObject::Collator(collator)) = intl_record(machine, this)? else {
        return Err(type_error(machine, "receiver is not an Intl.Collator"));
    };
    let result = collator.compare(&*DATA, left.as_units(), right.as_units());
    Ok(BuiltinOutcome::Value(crate::number_value(f64::from(
        result,
    ))))
}

fn resolved_options<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let Some(IntlObject::Collator(collator)) = intl_record(machine, this)? else {
        return Err(type_error(machine, "receiver is not an Intl.Collator"));
    };
    let resolved = collator.resolved_options();
    let locale = resolved.locale.to_owned();
    let usage = resolved.usage.as_str();
    let sensitivity = resolved.sensitivity.as_str();
    let ignore_punctuation = resolved.ignore_punctuation;
    let collation = resolved.collation.to_owned();
    let numeric = resolved.numeric;
    let case_first = resolved.case_first.as_str();
    let result = new_object(machine)?;
    for (name, text) in [
        ("locale", locale.as_str()),
        ("usage", usage),
        ("sensitivity", sensitivity),
    ] {
        let value = string_value(machine, text)?;
        define_field(machine, result, name, value)?;
    }
    define_field(
        machine,
        result,
        "ignorePunctuation",
        Value::boolean(ignore_punctuation),
    )?;
    let value = string_value(machine, &collation)?;
    define_field(machine, result, "collation", value)?;
    define_field(machine, result, "numeric", Value::boolean(numeric))?;
    let value = string_value(machine, case_first)?;
    define_field(machine, result, "caseFirst", value)?;
    Ok(BuiltinOutcome::Value(result))
}
