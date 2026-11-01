use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, Value};

use super::{define_data, define_to_string_tag, install_constructor_function, install_function};
use crate::intrinsics::BuiltinOutcome;
use crate::intrinsics::BuiltinTable;
use crate::{
    EvalFailure, HeapEntry, Host, IteratorKind, Machine, PropertyKey, PropertyMap, ThrowOrigin,
};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = crate::intrinsics::push(
        heap,
        HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(builtins.object_prototype()),
            boxed_primitive: None,
            extensible: true,
        },
    );
    builtins.set_promise_prototype(prototype);
    let resolve_target = install_function(
        heap,
        builtins,
        "Promise resolve target",
        1,
        resolve_target::<H>,
    );
    let reject_target = install_function(
        heap,
        builtins,
        "Promise reject target",
        1,
        reject_target::<H>,
    );
    builtins.set_promise_resolver_targets(resolve_target, reject_target);
    let all_fulfill = install_function(heap, builtins, "Promise all fulfill", 1, all_fulfill::<H>);
    builtins.set_promise_all_target(all_fulfill);
    let capability_executor = install_function(
        heap,
        builtins,
        "Promise capability executor",
        2,
        capability_executor::<H>,
    );
    let finally_value = install_function(
        heap,
        builtins,
        "Promise finally value",
        1,
        finally_value::<H>,
    );
    let finally_throw = install_function(
        heap,
        builtins,
        "Promise finally throw",
        1,
        finally_throw::<H>,
    );
    let species = install_function(heap, builtins, "get [Symbol.species]", 0, species::<H>);
    let finally_return = install_function(
        heap,
        builtins,
        "Promise finally return",
        0,
        finally_return::<H>,
    );
    let finally_rethrow = install_function(
        heap,
        builtins,
        "Promise finally rethrow",
        0,
        finally_rethrow::<H>,
    );
    let then_fulfill = install_function(
        heap,
        builtins,
        "Promise capability fulfill",
        1,
        then_fulfill::<H>,
    );
    let then_reject = install_function(
        heap,
        builtins,
        "Promise capability reject",
        1,
        then_reject::<H>,
    );

    let constructor = install_constructor_function(heap, builtins, "Promise", 1, constructor::<H>);
    builtins.set_constructor_prototype(heap, constructor, prototype);
    globals.insert(EcmaString::encode("Promise"), constructor);
    let queue_microtask =
        install_function(heap, builtins, "queueMicrotask", 1, queue_microtask::<H>);
    globals.insert(EcmaString::encode("queueMicrotask"), queue_microtask);

    let resolve = install_function(heap, builtins, "resolve", 1, resolve::<H>);
    let reject = install_function(heap, builtins, "reject", 1, reject::<H>);
    let all = install_function(heap, builtins, "all", 1, all::<H>);
    let race = install_function(heap, builtins, "race", 1, race::<H>);
    let all_settled = install_function(heap, builtins, "allSettled", 1, all_settled::<H>);
    let any = install_function(heap, builtins, "any", 1, any::<H>);
    let try_method = install_function(heap, builtins, "try", 1, promise_try::<H>);
    let with_resolvers = install_function(heap, builtins, "withResolvers", 0, with_resolvers::<H>);
    define_static(heap, constructor, "resolve", resolve);
    define_static(heap, constructor, "reject", reject);
    define_static(heap, constructor, "all", all);
    define_static(heap, constructor, "race", race);
    define_static(heap, constructor, "allSettled", all_settled);
    define_static(heap, constructor, "any", any);
    define_static(heap, constructor, "try", try_method);
    define_static(heap, constructor, "withResolvers", with_resolvers);
    builtins.set_promise_capability_executor(capability_executor);
    builtins.set_promise_finally_value(finally_value);
    builtins.set_promise_finally_throw(finally_throw);
    builtins.set_promise_finally_return(finally_return);
    builtins.set_promise_finally_rethrow(finally_rethrow);
    builtins.set_promise_then_fulfill(then_fulfill);
    builtins.set_promise_then_reject(then_reject);
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[super::heap_index(constructor)]
    else {
        unreachable!("Promise constructor is native")
    };
    properties.insert(
        PropertyKey::Symbol(super::heap_index(builtins.symbol_species()) as u32),
        crate::Property::Accessor {
            getter: Some(species),
            setter: None,
            enumerable: false,
            configurable: true,
        },
    );
    let then = install_function(heap, builtins, "then", 2, then::<H>);
    let catch = install_function(heap, builtins, "catch", 1, catch::<H>);
    let finally = install_function(heap, builtins, "finally", 1, finally::<H>);
    define_data(heap, prototype, "constructor", constructor);
    define_data(heap, prototype, "then", then);
    define_data(heap, prototype, "catch", catch);
    define_data(heap, prototype, "finally", finally);
    define_to_string_tag(heap, prototype, builtins.symbol_to_string_tag(), "Promise");
}

fn define_static(heap: &mut [HeapEntry], constructor: Value, name: &str, value: Value) {
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[super::heap_index(constructor)]
    else {
        panic!("Promise constructor must be native")
    };
    properties.insert(
        PropertyKey::Named(EcmaString::encode(name)),
        super::builtin_property(value),
    );
}

struct PromiseCapability {
    promise: Value,
    resolve: Value,
    reject: Value,
}

fn new_promise_capability<H: Host>(
    machine: &mut Machine<'_, H>,
    constructor: Value,
) -> Result<PromiseCapability, EvalFailure> {
    if !machine.is_callable(constructor)? {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise constructor",
        }));
    }
    let record = super::ordinary_runtime(machine, None)?;
    let target = machine.intrinsics.builtins.promise_capability_executor();
    let executor = machine.create_promise_resolver_function(target, record)?;
    let promise = machine.construct_value(constructor, &[executor])?;
    let resolve = machine.get_named_property(record, "resolve")?;
    let reject = machine.get_named_property(record, "reject")?;
    if !machine.is_callable(resolve)? || !machine.is_callable(reject)? {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise capability executor",
        }));
    }
    Ok(PromiseCapability {
        promise,
        resolve,
        reject,
    })
}

fn promise_resolve_with_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    constructor: Value,
    value: Value,
) -> Result<Value, EvalFailure> {
    if matches!(
        machine.runtime_slot(value).map_err(EvalFailure::Runtime)?,
        Some(index) if matches!(machine.heap[index], HeapEntry::Promise { .. })
    ) {
        let value_constructor = machine.get_named_property(value, "constructor")?;
        if value_constructor == constructor {
            return Ok(value);
        }
    }
    let capability = new_promise_capability(machine, constructor)?;
    machine.call_value(capability.resolve, Value::UNDEFINED, &[value])?;
    Ok(capability.promise)
}

fn reject_capability_failure<H: Host>(
    machine: &mut Machine<'_, H>,
    capability: &PromiseCapability,
    failure: EvalFailure,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (reason, _) = machine.promise_rejection_value(failure)?;
    machine.call_value(capability.reject, Value::UNDEFINED, &[reason])?;
    Ok(BuiltinOutcome::Value(capability.promise))
}

fn capability_executor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise capability executor",
        }));
    }
    let record = args.first().copied().unwrap_or(Value::UNDEFINED);
    if machine.get_named_property(record, "resolve")? != Value::UNDEFINED
        || machine.get_named_property(record, "reject")? != Value::UNDEFINED
    {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise capability executor",
        }));
    }
    machine.set_data_property(
        record,
        "resolve",
        args.get(1).copied().unwrap_or(Value::UNDEFINED),
    )?;
    machine.set_data_property(
        record,
        "reject",
        args.get(2).copied().unwrap_or(Value::UNDEFINED),
    )?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn species<H: Host>(
    _machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise Symbol.species",
        }));
    }
    Ok(BuiltinOutcome::Value(this))
}

fn species_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
) -> Result<Value, EvalFailure> {
    // The default constructor is the original Promise constructor.  Resolve
    // it from the immutable prototype slot in the intrinsics table, not from
    // the script-mutable global map, so reassigning the global `Promise`
    // cannot change the species fallback.
    let prototype = machine.intrinsics.builtins.promise_prototype();
    let default = machine.get_named_property(prototype, "constructor")?;
    let constructor = machine.get_named_property(object, "constructor")?;
    if matches!(constructor.decode(), Some(bamts_native::Decoded::Undefined)) {
        return Ok(default);
    }
    if !machine.is_object(constructor) {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise constructor",
        }));
    }
    let species_symbol = machine.intrinsics.builtins.symbol_species();
    let species_key = machine.to_property_key(species_symbol)?;
    let species = machine.get_property_key(constructor, &species_key)?;
    if matches!(
        species.decode(),
        Some(bamts_native::Decoded::Undefined | bamts_native::Decoded::Null)
    ) {
        return Ok(default);
    }
    if !machine.is_callable(species)? {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise Symbol.species",
        }));
    }
    Ok(species)
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise constructor",
        }));
    }
    let executor = args.first().copied().unwrap_or(Value::UNDEFINED);
    if !machine.is_callable(executor)? {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise executor",
        }));
    }

    let promise = machine.create_promise()?;
    let new_target = machine.current_new_target();
    if new_target != Value::UNDEFINED {
        let default_prototype = machine.intrinsics.builtins.promise_prototype();
        let prototype = machine
            .constructed_prototype(new_target)
            .unwrap_or(default_prototype);
        if prototype != default_prototype
            && !machine.internal_set_prototype_of(promise, Some(prototype))?
        {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "cannot set promise prototype",
            }));
        }
    }
    let record = machine.create_promise_resolver(promise)?;
    let (resolve_target, reject_target) = machine.intrinsics.builtins.promise_resolver_targets();
    let resolve = machine.create_promise_resolver_function(resolve_target, record)?;
    let reject = machine.create_promise_resolver_function(reject_target, record)?;
    if let Err(failure) = machine.call_value(executor, Value::UNDEFINED, &[resolve, reject]) {
        machine.reject_promise_resolver_failure(record, failure)?;
    }
    Ok(BuiltinOutcome::Value(promise))
}

fn resolve_target<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise resolve",
        }));
    }
    let record = args
        .first()
        .copied()
        .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise resolver",
        }))?;
    machine.resolve_promise_resolver(record, args.get(1).copied().unwrap_or(Value::UNDEFINED))?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn reject_target<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise reject",
        }));
    }
    let record = args
        .first()
        .copied()
        .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise resolver",
        }))?;
    machine.reject_promise_resolver(record, args.get(1).copied().unwrap_or(Value::UNDEFINED))?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn then<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise.prototype.then",
        }));
    }
    if !matches!(
        machine.runtime_slot(this).map_err(EvalFailure::Runtime)?,
        Some(index) if matches!(machine.heap[index], HeapEntry::Promise { .. })
    ) {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise.prototype.then",
        }));
    }
    let constructor = species_constructor(machine, this)?;
    let capability = new_promise_capability(machine, constructor)?;
    let record = super::ordinary_runtime(machine, None)?;
    machine.set_data_property(
        record,
        "onFulfilled",
        args.first().copied().unwrap_or(Value::UNDEFINED),
    )?;
    machine.set_data_property(
        record,
        "onRejected",
        args.get(1).copied().unwrap_or(Value::UNDEFINED),
    )?;
    machine.set_data_property(record, "resolve", capability.resolve)?;
    machine.set_data_property(record, "reject", capability.reject)?;
    let fulfill_target = machine.intrinsics.builtins.promise_then_fulfill();
    let reject_target = machine.intrinsics.builtins.promise_then_reject();
    let fulfill = machine.create_promise_resolver_function(fulfill_target, record)?;
    let reject = machine.create_promise_resolver_function(reject_target, record)?;
    let ignored = machine.promise_then(this, fulfill, reject)?;
    let _ = ignored;
    Ok(BuiltinOutcome::Value(capability.promise))
}

fn resolve<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise.resolve",
        }));
    }
    let value = args.first().copied().unwrap_or(Value::UNDEFINED);
    Ok(BuiltinOutcome::Value(promise_resolve_with_constructor(
        machine, this, value,
    )?))
}

fn reject<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise.reject",
        }));
    }
    let capability = new_promise_capability(machine, this)?;
    machine.call_value(
        capability.reject,
        Value::UNDEFINED,
        &[args.first().copied().unwrap_or(Value::UNDEFINED)],
    )?;
    Ok(BuiltinOutcome::Value(capability.promise))
}

/// `Promise.try(callback, ...args)`: a synchronous throw rejects the result
/// rather than reaching the caller. The capability stays rooted across the
/// callback, which can run arbitrary code.
fn promise_try<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !machine.is_constructor(this)? {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise.try",
        }));
    }
    let capability = new_promise_capability(machine, this)?;
    let depth = machine.native_roots.len();
    machine.push_native_roots(
        depth,
        &[capability.promise, capability.resolve, capability.reject],
    );
    let callback = args.first().copied().unwrap_or(Value::UNDEFINED);
    let callback_args = args.get(1..).unwrap_or_default();
    let outcome = match machine.call_value(callback, Value::UNDEFINED, callback_args) {
        Ok(value) => machine
            .call_value(capability.resolve, Value::UNDEFINED, &[value])
            .map(|_| BuiltinOutcome::Value(capability.promise)),
        Err(failure) => reject_capability_failure(machine, &capability, failure),
    };
    machine.pop_native_roots(depth);
    outcome
}

/// `Promise.withResolvers()`: a capability exposed as an ordinary object.
fn with_resolvers<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !machine.is_constructor(this)? {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise.withResolvers",
        }));
    }
    let capability = new_promise_capability(machine, this)?;
    let prototype = machine.intrinsics.object_prototype;
    let result = super::ordinary_runtime(machine, Some(prototype))?;
    for (name, value) in [
        ("promise", capability.promise),
        ("resolve", capability.resolve),
        ("reject", capability.reject),
    ] {
        let key = PropertyKey::Named(EcmaString::encode(name));
        machine.create_data_property_key(result, key, value)?;
    }
    Ok(BuiltinOutcome::Value(result))
}

fn all<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise.all",
        }));
    }
    let capability = new_promise_capability(machine, this)?;
    let resolve = match machine.get_named_property(this, "resolve") {
        Ok(resolve) if machine.is_callable(resolve)? => resolve,
        Ok(_) => {
            return reject_capability_failure(
                machine,
                &capability,
                EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "Promise.all resolve",
                }),
            );
        }
        Err(failure) => return reject_capability_failure(machine, &capability, failure),
    };
    let iterable = args.first().copied().unwrap_or(Value::UNDEFINED);
    machine.promise_all_with_resolve(
        iterable,
        resolve,
        this,
        capability.resolve,
        capability.reject,
    )?;
    Ok(BuiltinOutcome::Value(capability.promise))
}

fn race<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise.race",
        }));
    }
    let capability = new_promise_capability(machine, this)?;
    let resolve = match constructor_resolve(machine, this, "Promise.race resolve") {
        Ok(resolve) => resolve,
        Err(failure) => return reject_capability_failure(machine, &capability, failure),
    };
    let iterable = args.first().copied().unwrap_or(Value::UNDEFINED);
    let iterator = match machine.create_iterator(iterable, IteratorKind::Sync) {
        Ok(iterator) => iterator,
        Err(failure) => return reject_capability_failure(machine, &capability, failure),
    };
    loop {
        let value = match machine.iterator_next(iterator) {
            Ok((true, _)) => break,
            Ok((false, value)) => value,
            Err(failure) => return reject_capability_failure(machine, &capability, failure),
        };
        let resolved = match machine.call_value(resolve, this, &[value]) {
            Ok(resolved) => resolved,
            Err(failure) => {
                return reject_iterator_failure(machine, &capability, iterator, failure);
            }
        };
        let then = match machine.get_named_property(resolved, "then") {
            Ok(then) => then,
            Err(failure) => {
                return reject_iterator_failure(machine, &capability, iterator, failure);
            }
        };
        if let Err(failure) =
            machine.call_value(then, resolved, &[capability.resolve, capability.reject])
        {
            return reject_iterator_failure(machine, &capability, iterator, failure);
        }
    }
    Ok(BuiltinOutcome::Value(capability.promise))
}

fn all_settled<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    aggregate_static(machine, this, args, constructing, AggregateKind::AllSettled)
}

fn any<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    aggregate_static(machine, this, args, constructing, AggregateKind::Any)
}

#[derive(Clone, Copy)]
enum AggregateKind {
    AllSettled,
    Any,
}

fn aggregate_static<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
    kind: AggregateKind,
) -> Result<BuiltinOutcome, EvalFailure> {
    let operation = match kind {
        AggregateKind::AllSettled => "Promise.allSettled",
        AggregateKind::Any => "Promise.any",
    };
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError { operation }));
    }
    let capability = new_promise_capability(machine, this)?;
    let resolve = match constructor_resolve(machine, this, operation) {
        Ok(resolve) => resolve,
        Err(failure) => return reject_capability_failure(machine, &capability, failure),
    };
    let iterable = args.first().copied().unwrap_or(Value::UNDEFINED);
    perform_ordered_aggregate(machine, iterable, resolve, this, &capability, kind)?;
    Ok(BuiltinOutcome::Value(capability.promise))
}

fn constructor_resolve<H: Host>(
    machine: &mut Machine<'_, H>,
    constructor: Value,
    operation: &'static str,
) -> Result<Value, EvalFailure> {
    let resolve = machine.get_named_property(constructor, "resolve")?;
    if machine.is_callable(resolve)? {
        Ok(resolve)
    } else {
        Err(EvalFailure::Throw(ThrowOrigin::TypeError { operation }))
    }
}

fn perform_ordered_aggregate<H: Host>(
    machine: &mut Machine<'_, H>,
    iterable: Value,
    resolve_method: Value,
    receiver: Value,
    capability: &PromiseCapability,
    kind: AggregateKind,
) -> Result<(), EvalFailure> {
    let aggregate_resolve = match kind {
        AggregateKind::AllSettled => {
            let record = completion_record(
                machine,
                ReactionKind::AllSettledComplete,
                capability.resolve,
                capability.reject,
            )?;
            machine.create_promise_resolver_function(
                machine.intrinsics.builtins.promise_all_target(),
                record,
            )?
        }
        AggregateKind::Any => {
            let constructor =
                machine
                    .intrinsics
                    .global("AggregateError")
                    .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "Promise.any AggregateError",
                    }))?;
            let record = reaction_record(
                machine,
                ReactionKind::AnyComplete,
                Value::UNDEFINED,
                Some(capability.reject),
            )?;
            machine.create_data_property_key(
                record,
                PropertyKey::Named(EcmaString::encode("constructor")),
                constructor,
            )?;
            machine.create_promise_resolver_function(
                machine.intrinsics.builtins.promise_all_target(),
                record,
            )?
        }
    };
    let aggregate = machine
        .allocate(HeapEntry::PromiseAll {
            resolve: aggregate_resolve,
            reject: capability.reject,
            values: Vec::new(),
            remaining: 1,
            settled: false,
        })
        .map_err(EvalFailure::Runtime)?;
    let iterator = match machine.create_iterator(iterable, IteratorKind::Sync) {
        Ok(iterator) => iterator,
        Err(failure) => {
            machine.mark_promise_all_settled(aggregate)?;
            return reject_failure(machine, capability.reject, failure);
        }
    };
    loop {
        let value = match machine.iterator_next(iterator) {
            Ok((true, _)) => break,
            Ok((false, value)) => value,
            Err(failure) => {
                machine.mark_promise_all_settled(aggregate)?;
                return reject_failure(machine, capability.reject, failure);
            }
        };
        let index = match machine.add_promise_all_element(aggregate) {
            Ok(index) => index,
            Err(failure) => {
                return reject_aggregate_failure(
                    machine,
                    aggregate,
                    capability.reject,
                    iterator,
                    failure,
                );
            }
        };
        let element = match machine
            .allocate(HeapEntry::PromiseAllElement {
                aggregate,
                index,
                called: false,
            })
            .map_err(EvalFailure::Runtime)
        {
            Ok(element) => element,
            Err(failure) => {
                return reject_aggregate_failure(
                    machine,
                    aggregate,
                    capability.reject,
                    iterator,
                    failure,
                );
            }
        };
        let callbacks = match aggregate_callbacks(machine, kind, element, capability) {
            Ok(callbacks) => callbacks,
            Err(failure) => {
                return reject_aggregate_failure(
                    machine,
                    aggregate,
                    capability.reject,
                    iterator,
                    failure,
                );
            }
        };
        let resolved = match machine.call_value(resolve_method, receiver, &[value]) {
            Ok(resolved) => resolved,
            Err(failure) => {
                return reject_aggregate_failure(
                    machine,
                    aggregate,
                    capability.reject,
                    iterator,
                    failure,
                );
            }
        };
        let then = match machine.get_named_property(resolved, "then") {
            Ok(then) => then,
            Err(failure) => {
                return reject_aggregate_failure(
                    machine,
                    aggregate,
                    capability.reject,
                    iterator,
                    failure,
                );
            }
        };
        if let Err(failure) = machine.call_value(then, resolved, &[callbacks.0, callbacks.1]) {
            return reject_aggregate_failure(
                machine,
                aggregate,
                capability.reject,
                iterator,
                failure,
            );
        }
    }
    if machine.finish_promise_all(aggregate)? {
        let values = machine.move_promise_all_values_to_array(aggregate)?;
        if let Err(failure) = machine.call_value(aggregate_resolve, Value::UNDEFINED, &[values]) {
            reject_failure(machine, capability.reject, failure)?;
        }
    }
    Ok(())
}

fn aggregate_callbacks<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: AggregateKind,
    element: Value,
    capability: &PromiseCapability,
) -> Result<(Value, Value), EvalFailure> {
    let target = machine.intrinsics.builtins.promise_all_target();
    match kind {
        AggregateKind::AllSettled => {
            let fulfilled =
                reaction_record(machine, ReactionKind::AllSettledFulfilled, element, None)?;
            let rejected =
                reaction_record(machine, ReactionKind::AllSettledRejected, element, None)?;
            Ok((
                machine.create_promise_resolver_function(target, fulfilled)?,
                machine.create_promise_resolver_function(target, rejected)?,
            ))
        }
        AggregateKind::Any => {
            let on_fulfilled = completion_record(
                machine,
                ReactionKind::AnyFulfilled,
                capability.resolve,
                capability.reject,
            )?;
            let rejected = reaction_record(machine, ReactionKind::AnyRejected, element, None)?;
            Ok((
                machine.create_promise_resolver_function(target, on_fulfilled)?,
                machine.create_promise_resolver_function(target, rejected)?,
            ))
        }
    }
}

#[repr(i32)]
#[derive(Clone, Copy)]
enum ReactionKind {
    AllSettledFulfilled = 0,
    AllSettledRejected = 1,
    AnyRejected = 2,
    AnyComplete = 3,
    AllSettledComplete = 4,
    AnyFulfilled = 5,
}

fn reaction_record<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: ReactionKind,
    element: Value,
    reject: Option<Value>,
) -> Result<Value, EvalFailure> {
    let record = super::ordinary_runtime(machine, None)?;
    machine.create_data_property_key(
        record,
        PropertyKey::Named(EcmaString::encode("kind")),
        Value::int32(kind as u32),
    )?;
    machine.create_data_property_key(
        record,
        PropertyKey::Named(EcmaString::encode("element")),
        element,
    )?;
    if let Some(reject) = reject {
        machine.create_data_property_key(
            record,
            PropertyKey::Named(EcmaString::encode("reject")),
            reject,
        )?;
    }
    Ok(record)
}

fn completion_record<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: ReactionKind,
    resolve: Value,
    reject: Value,
) -> Result<Value, EvalFailure> {
    let record = reaction_record(machine, kind, Value::UNDEFINED, Some(reject))?;
    machine.create_data_property_key(
        record,
        PropertyKey::Named(EcmaString::encode("resolve")),
        resolve,
    )?;
    Ok(record)
}

fn reject_iterator_failure<H: Host>(
    machine: &mut Machine<'_, H>,
    capability: &PromiseCapability,
    iterator: Value,
    failure: EvalFailure,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (close, _) = machine.close_iterator_raw(iterator);
    if let Err(EvalFailure::Runtime(kind)) = close {
        return Err(EvalFailure::Runtime(kind));
    }
    reject_capability_failure(machine, capability, failure)
}

fn reject_aggregate_failure<H: Host>(
    machine: &mut Machine<'_, H>,
    aggregate: Value,
    reject: Value,
    iterator: Value,
    failure: EvalFailure,
) -> Result<(), EvalFailure> {
    machine.mark_promise_all_settled(aggregate)?;
    let (close, _) = machine.close_iterator_raw(iterator);
    if let Err(EvalFailure::Runtime(kind)) = close {
        return Err(EvalFailure::Runtime(kind));
    }
    reject_failure(machine, reject, failure)
}

fn reject_failure<H: Host>(
    machine: &mut Machine<'_, H>,
    reject: Value,
    failure: EvalFailure,
) -> Result<(), EvalFailure> {
    let (reason, _) = machine.promise_rejection_value(failure)?;
    machine.call_value(reject, Value::UNDEFINED, &[reason])?;
    Ok(())
}

fn catch<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise.prototype.catch",
        }));
    }
    let then = machine.get_named_property(this, "then")?;
    Ok(BuiltinOutcome::Value(machine.call_value(
        then,
        this,
        &[
            Value::UNDEFINED,
            args.first().copied().unwrap_or(Value::UNDEFINED),
        ],
    )?))
}

fn finally<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise.prototype.finally",
        }));
    }
    if !machine.is_object(this) {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise.prototype.finally",
        }));
    }
    let species = species_constructor(machine, this)?;
    let handler = args.first().copied().unwrap_or(Value::UNDEFINED);
    let (on_fulfilled, on_rejected) = if machine.is_callable(handler)? {
        let record = super::ordinary_runtime(machine, None)?;
        machine.set_data_property(record, "handler", handler)?;
        machine.set_data_property(record, "constructor", species)?;
        let fulfill = machine.intrinsics.builtins.promise_finally_value();
        let reject = machine.intrinsics.builtins.promise_finally_throw();
        (
            machine.create_promise_resolver_function(fulfill, record)?,
            machine.create_promise_resolver_function(reject, record)?,
        )
    } else {
        (handler, handler)
    };
    let then = machine.get_named_property(this, "then")?;
    Ok(BuiltinOutcome::Value(machine.call_value(
        then,
        this,
        &[on_fulfilled, on_rejected],
    )?))
}

fn reject_reaction_failure<H: Host>(
    machine: &mut Machine<'_, H>,
    record: Value,
    failure: EvalFailure,
) -> Result<(), EvalFailure> {
    let (reason, _) = machine.promise_rejection_value(failure)?;
    let reject = machine.get_named_property(record, "reject")?;
    machine.call_value(reject, Value::UNDEFINED, &[reason])?;
    Ok(())
}

fn then_fulfill<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise reaction",
        }));
    }
    let record = args.first().copied().unwrap_or(Value::UNDEFINED);
    let value = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let handler = machine.get_named_property(record, "onFulfilled")?;
    let result = if machine.is_callable(handler)? {
        match machine.call_value(handler, Value::UNDEFINED, &[value]) {
            Ok(result) => result,
            Err(failure) => {
                reject_reaction_failure(machine, record, failure)?;
                return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
            }
        }
    } else {
        value
    };
    let resolve = machine.get_named_property(record, "resolve")?;
    machine.call_value(resolve, Value::UNDEFINED, &[result])?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn then_reject<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise reaction",
        }));
    }
    let record = args.first().copied().unwrap_or(Value::UNDEFINED);
    let reason = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let handler = machine.get_named_property(record, "onRejected")?;
    if machine.is_callable(handler)? {
        match machine.call_value(handler, Value::UNDEFINED, &[reason]) {
            Ok(result) => {
                let resolve = machine.get_named_property(record, "resolve")?;
                machine.call_value(resolve, Value::UNDEFINED, &[result])?;
            }
            Err(failure) => reject_reaction_failure(machine, record, failure)?,
        }
    } else {
        let reject = machine.get_named_property(record, "reject")?;
        machine.call_value(reject, Value::UNDEFINED, &[reason])?;
    }
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn finally_wait<H: Host>(
    machine: &mut Machine<'_, H>,
    record: Value,
    original: Value,
    rejected: bool,
) -> Result<Value, EvalFailure> {
    let handler = machine.get_named_property(record, "handler")?;
    let result = machine.call_value(handler, Value::UNDEFINED, &[])?;
    let constructor = machine.get_named_property(record, "constructor")?;
    let promise = promise_resolve_with_constructor(machine, constructor, result)?;
    let continuation_record = super::ordinary_runtime(machine, None)?;
    machine.set_data_property(continuation_record, "value", original)?;
    let target = if rejected {
        machine.intrinsics.builtins.promise_finally_rethrow()
    } else {
        machine.intrinsics.builtins.promise_finally_return()
    };
    let continuation = machine.create_promise_resolver_function(target, continuation_record)?;
    let then = machine.get_named_property(promise, "then")?;
    machine.call_value(then, promise, &[continuation, Value::UNDEFINED])
}

fn finally_value<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise finally callback",
        }));
    }
    let record = args.first().copied().unwrap_or(Value::UNDEFINED);
    let original = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    Ok(BuiltinOutcome::Value(finally_wait(
        machine, record, original, false,
    )?))
}

fn finally_throw<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise finally callback",
        }));
    }
    let record = args.first().copied().unwrap_or(Value::UNDEFINED);
    let original = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    Ok(BuiltinOutcome::Value(finally_wait(
        machine, record, original, true,
    )?))
}

fn finally_return<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise finally continuation",
        }));
    }
    let record = args.first().copied().unwrap_or(Value::UNDEFINED);
    Ok(BuiltinOutcome::Value(
        machine.get_named_property(record, "value")?,
    ))
}

fn finally_rethrow<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise finally continuation",
        }));
    }
    let record = args.first().copied().unwrap_or(Value::UNDEFINED);
    Err(EvalFailure::ThrowValue(
        machine.get_named_property(record, "value")?,
    ))
}

fn all_fulfill<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise all target",
        }));
    }
    let record = args
        .first()
        .copied()
        .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise all target",
        }))?;
    let value = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let index = machine
        .runtime_slot(record)
        .map_err(EvalFailure::Runtime)?
        .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "Promise all target",
        }))?;
    if matches!(machine.heap[index], HeapEntry::PromiseAllElement { .. }) {
        machine.resolve_promise_all_element(record, value)?;
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    }
    let kind = match machine.get_named_property(record, "kind")?.decode() {
        Some(Decoded::Int32(raw)) => raw as i32,
        _ => {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Promise aggregate target",
            }));
        }
    };
    match kind {
        raw if raw == ReactionKind::AllSettledFulfilled as i32 => {
            let element = machine.get_named_property(record, "element")?;
            let result = settlement_result(machine, "fulfilled", "value", value)?;
            machine.resolve_promise_all_element(element, result)?;
        }
        raw if raw == ReactionKind::AllSettledRejected as i32 => {
            let element = machine.get_named_property(record, "element")?;
            let result = settlement_result(machine, "rejected", "reason", value)?;
            machine.resolve_promise_all_element(element, result)?;
        }
        raw if raw == ReactionKind::AnyRejected as i32 => {
            let element = machine.get_named_property(record, "element")?;
            machine.resolve_promise_all_element(element, value)?;
        }
        raw if raw == ReactionKind::AnyComplete as i32 => {
            let reject = machine.get_named_property(record, "reject")?;
            let constructor = machine.get_named_property(record, "constructor")?;
            let error = machine.construct_value(constructor, &[value])?;
            machine.call_value(reject, Value::UNDEFINED, &[error])?;
        }
        raw if raw == ReactionKind::AllSettledComplete as i32
            || raw == ReactionKind::AnyFulfilled as i32 =>
        {
            let resolve = machine.get_named_property(record, "resolve")?;
            machine.call_value(resolve, Value::UNDEFINED, &[value])?;
        }
        _ => {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Promise aggregate target",
            }));
        }
    }
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn settlement_result<H: Host>(
    machine: &mut Machine<'_, H>,
    status: &str,
    field: &str,
    value: Value,
) -> Result<Value, EvalFailure> {
    let result = super::ordinary_runtime(machine, None)?;
    let status = machine
        .allocate(HeapEntry::String(EcmaString::encode(status)))
        .map_err(EvalFailure::Runtime)?;
    machine.create_data_property_key(
        result,
        PropertyKey::Named(EcmaString::encode("status")),
        status,
    )?;
    machine.create_data_property_key(
        result,
        PropertyKey::Named(EcmaString::encode(field)),
        value,
    )?;
    Ok(result)
}

fn queue_microtask<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "queueMicrotask",
        }));
    }
    let callback = args.first().copied().unwrap_or(Value::UNDEFINED);
    if !machine.is_callable(callback)? {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "queueMicrotask callback",
        }));
    }
    machine.enqueue_microtask_callback(callback)?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program, custom_iterable};
    use super::*;
    use crate::intrinsics::BuiltinHandler;
    use crate::{Limits, PromiseState};

    fn promise_state<'m>(machine: &'m Machine<'_, TestHost>, promise: Value) -> &'m PromiseState {
        let index = machine.runtime_slot(promise).unwrap().unwrap();
        let HeapEntry::Promise { state, .. } = &machine.heap[index] else {
            panic!("expected a promise");
        };
        state
    }

    fn static_method(machine: &mut Machine<'_, TestHost>, name: &str) -> (Value, Value) {
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let method = machine.get_named_property(constructor, name).unwrap();
        (constructor, method)
    }

    #[test]
    fn promise_try_rejects_a_synchronous_throw_instead_of_propagating_it() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let (constructor, method) = static_method(&mut machine, "try");
        let thrower = callback(&mut machine, "thrower", throw_99);
        let promise = machine
            .call_value(method, constructor, &[thrower])
            .expect("the throw is captured by the promise");
        assert!(matches!(
            promise_state(&machine, promise),
            PromiseState::Rejected { .. }
        ));
    }

    #[test]
    fn promise_try_and_with_resolvers_require_a_constructor() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let parse_int = machine.intrinsics.global("parseInt").unwrap();
        for name in ["try", "withResolvers"] {
            let (_, method) = static_method(&mut machine, name);
            for receiver in [Value::UNDEFINED, parse_int] {
                assert!(matches!(
                    machine.call_value(method, receiver, &[]),
                    Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
                ));
            }
        }
    }

    #[test]
    fn with_resolvers_exposes_a_working_capability() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let (constructor, method) = static_method(&mut machine, "withResolvers");
        let record = machine.call_value(method, constructor, &[]).unwrap();
        let promise = machine.get_named_property(record, "promise").unwrap();
        let resolve = machine.get_named_property(record, "resolve").unwrap();
        machine.get_named_property(record, "reject").unwrap();
        assert!(matches!(
            promise_state(&machine, promise),
            PromiseState::Pending { .. }
        ));
        machine
            .call_value(resolve, Value::UNDEFINED, &[Value::int32(1)])
            .unwrap();
        assert!(matches!(
            promise_state(&machine, promise),
            PromiseState::Fulfilled { .. }
        ));
    }

    fn callback(
        machine: &mut Machine<'_, TestHost>,
        name: &'static str,
        handler: BuiltinHandler<TestHost>,
    ) -> Value {
        install_function(
            &mut machine.heap,
            &mut machine.intrinsics.builtins,
            name,
            0,
            handler,
        )
    }

    fn return_undefined(
        _machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    fn throw_99(
        _machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(EvalFailure::ThrowValue(Value::int32(99)))
    }

    fn return_hostile_thenable(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(
            machine
                .test_global("hostileThenable")
                .expect("test installs hostile thenable"),
        ))
    }

    fn fulfill_then_reject(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let fulfill = args.first().copied().unwrap_or(Value::UNDEFINED);
        let reject = args.get(1).copied().unwrap_or(Value::UNDEFINED);
        machine.call_value(fulfill, Value::UNDEFINED, &[Value::int32(1)])?;
        machine.call_value(reject, Value::UNDEFINED, &[Value::int32(99)])?;
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    fn record_capability_reject(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.test_set_global(
            "capabilityRejectReason",
            args.first().copied().unwrap_or(Value::UNDEFINED),
        );
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    fn count_capability_resolve_then_throw(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let count = machine
            .test_global("capabilityResolveCount")
            .and_then(Value::decode)
            .and_then(|value| match value {
                bamts_native::Decoded::Int32(raw) => Some(raw),
                _ => None,
            })
            .unwrap_or(0);
        machine.test_set_global("capabilityResolveCount", Value::int32(count + 1));
        Err(EvalFailure::ThrowValue(Value::int32(99)))
    }

    fn throwing_capability_constructor(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        args: &[Value],
        constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        if !constructing {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "test Promise constructor",
            }));
        }
        let executor = args.first().copied().unwrap_or(Value::UNDEFINED);
        let promise = super::super::ordinary_runtime(machine, None)?;
        let resolve = callback(
            machine,
            "throwing capability resolve",
            count_capability_resolve_then_throw,
        );
        let reject = callback(
            machine,
            "record capability reject",
            record_capability_reject,
        );
        machine.call_value(executor, Value::UNDEFINED, &[resolve, reject])?;
        machine.test_set_global("capabilityPromise", promise);
        Ok(BuiltinOutcome::Value(promise))
    }

    fn return_fulfilled_builtin_promise(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let promise = machine.create_promise()?;
        machine
            .resolve_promise(promise, args.first().copied().unwrap_or(Value::UNDEFINED))
            .map_err(EvalFailure::Runtime)?;
        Ok(BuiltinOutcome::Value(promise))
    }

    fn return_rejected_builtin_promise(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let promise = machine.create_promise()?;
        machine
            .reject_promise(
                promise,
                args.first().copied().unwrap_or(Value::UNDEFINED),
                ThrowOrigin::Bytecode,
            )
            .map_err(EvalFailure::Runtime)?;
        Ok(BuiltinOutcome::Value(promise))
    }

    fn count_capability_reject_then_throw(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let count = machine
            .test_global("capabilityRejectCount")
            .and_then(Value::decode)
            .and_then(|value| match value {
                bamts_native::Decoded::Int32(raw) => Some(raw),
                _ => None,
            })
            .unwrap_or(0);
        machine.test_set_global("capabilityRejectCount", Value::int32(count + 1));
        Err(EvalFailure::ThrowValue(Value::int32(99)))
    }

    fn throwing_reject_capability_constructor(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        args: &[Value],
        constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        if !constructing {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "test Promise constructor",
            }));
        }
        let executor = args.first().copied().unwrap_or(Value::UNDEFINED);
        let promise = super::super::ordinary_runtime(machine, None)?;
        let resolve = callback(machine, "unused capability resolve", return_undefined);
        let reject = callback(
            machine,
            "counting throwing capability reject",
            count_capability_reject_then_throw,
        );
        machine.call_value(executor, Value::UNDEFINED, &[resolve, reject])?;
        Ok(BuiltinOutcome::Value(promise))
    }

    fn resolve_88(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.test_set_global("thenSeen", Value::int32(2));
        machine.call_value(
            args.first().copied().unwrap_or(Value::UNDEFINED),
            Value::UNDEFINED,
            &[Value::int32(88)],
        )?;
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    fn return_thenable(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.test_set_global("handlerSeen", Value::int32(1));
        Ok(BuiltinOutcome::Value(
            machine
                .test_global("thenable")
                .expect("test installs thenable"),
        ))
    }

    fn iterator_method(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(
            machine
                .test_global("testIterator")
                .expect("test installs iterator"),
        ))
    }

    fn iterator_next_once(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let seen = machine.test_global("nextSeen").is_some();
        machine.test_set_global("nextSeen", Value::TRUE);
        Ok(BuiltinOutcome::Value(
            machine.iterator_result(Value::int32(1), seen)?,
        ))
    }

    fn iterator_return(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.test_set_global("iteratorClosed", Value::TRUE);
        Ok(BuiltinOutcome::Value(this))
    }

    fn throwing_resolve(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.test_set_global("resolveReceiver", this);
        Err(EvalFailure::ThrowValue(Value::int32(99)))
    }

    fn resolve_getter(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let count = machine
            .test_global("resolveGetCount")
            .and_then(Value::decode)
            .and_then(|value| match value {
                bamts_native::Decoded::Int32(raw) => Some(raw),
                _ => None,
            })
            .unwrap_or(0);
        machine.test_set_global("resolveGetCount", Value::int32(count + 1));
        Ok(BuiltinOutcome::Value(
            machine
                .test_global("throwingResolve")
                .expect("test installs throwing resolve"),
        ))
    }

    fn self_capability_constructor(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        args: &[Value],
        constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        if !constructing {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Promise constructor",
            }));
        }
        let executor = args.first().copied().unwrap_or(Value::UNDEFINED);
        let built_in = machine
            .intrinsics
            .global("Promise")
            .expect("Promise global is installed");
        let promise = machine.construct_value(built_in, &[executor])?;
        let throwing_then = callback(machine, "self then", throw_then_observed);
        machine.set_data_property(promise, "then", throwing_then)?;
        machine.test_set_global("selfCapabilityPromise", promise);
        Ok(BuiltinOutcome::Value(promise))
    }

    fn resolve_returns_capability(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(
            machine
                .test_global("selfCapabilityPromise")
                .expect("constructor set capability promise"),
        ))
    }

    fn throw_then_observed(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.test_set_global("thenObserved", Value::TRUE);
        Err(EvalFailure::ThrowValue(Value::int32(77)))
    }

    fn one_value_iterable(machine: &mut Machine<'_, TestHost>) -> Value {
        let iterator = super::super::ordinary_runtime(machine, None).unwrap();
        let next = callback(machine, "test iterator next", iterator_next_once);
        let close = callback(machine, "test iterator return", iterator_return);
        machine.set_data_property(iterator, "next", next).unwrap();
        machine
            .set_data_property(iterator, "return", close)
            .unwrap();
        machine.test_set_global("testIterator", iterator);

        let iterable = super::super::ordinary_runtime(machine, None).unwrap();
        let method = callback(machine, "test iterator method", iterator_method);
        let symbol = machine.intrinsics.builtins.symbol_iterator();
        let key = machine.to_property_key(symbol).unwrap();
        machine
            .set_data_property_key(iterable, key, method)
            .unwrap();
        iterable
    }

    #[test]
    fn all_calls_receiver_resolve_and_closes_on_abrupt_completion() {
        let module = blank_program("<promise-all-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let resolve = callback(&mut machine, "throwing resolve", throwing_resolve);
        machine.test_set_global("throwingResolve", resolve);
        let getter = callback(&mut machine, "resolve getter", resolve_getter);
        machine
            .define_accessor(
                constructor,
                PropertyKey::Named(EcmaString::encode("resolve")),
                getter,
                crate::AccessorKind::Getter,
            )
            .unwrap();
        let iterable = one_value_iterable(&mut machine);
        let all = machine.get_named_property(constructor, "all").unwrap();

        let promise = machine
            .call_value(all, constructor, &[iterable])
            .expect("Promise.all returns its rejected capability");
        machine.drain_microtasks().unwrap();

        assert_eq!(
            machine.test_global("resolveGetCount"),
            Some(Value::int32(1))
        );
        assert_eq!(machine.test_global("resolveReceiver"), Some(constructor));
        assert_eq!(machine.test_global("iteratorClosed"), Some(Value::TRUE));
        assert!(
            matches!(state(&machine, promise), PromiseState::Rejected { reason, .. } if reason == Value::int32(99))
        );
    }

    #[test]
    fn all_does_not_read_mutable_promise_prototype_then() {
        let module = blank_program("<promise-all-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let prototype = machine.intrinsics.builtins.promise_prototype();
        let throwing_getter = callback(&mut machine, "throwing then getter", throw_99);
        machine
            .define_accessor(
                prototype,
                PropertyKey::Named(EcmaString::encode("then")),
                throwing_getter,
                crate::AccessorKind::Getter,
            )
            .unwrap();
        let iterable = super::super::allocate_array(&mut machine, Vec::new()).unwrap();
        let all = machine.get_named_property(constructor, "all").unwrap();

        let promise = machine
            .call_value(all, constructor, &[iterable])
            .expect("Promise.all returns its capability");

        assert!(matches!(
            state(&machine, promise),
            PromiseState::Fulfilled { .. }
        ));
    }

    #[test]
    fn all_retains_capability_callbacks_until_pending_input_settles() {
        let module = blank_program("<promise-all-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let source = machine.create_promise().unwrap();
        let iterable = super::super::allocate_array(&mut machine, vec![source]).unwrap();
        let all = machine.get_named_property(constructor, "all").unwrap();

        let promise = machine
            .call_value(all, constructor, &[iterable])
            .expect("Promise.all returns its capability");
        assert!(matches!(
            state(&machine, promise),
            PromiseState::Pending { .. }
        ));

        machine.push_native_roots(0, &[source, promise]);
        machine.collect_garbage();
        machine.fulfill_promise(source, Value::int32(7)).unwrap();
        machine.drain_microtasks().unwrap();
        machine.pop_native_roots(0);

        assert!(matches!(
            state(&machine, promise),
            PromiseState::Fulfilled { .. }
        ));
    }

    #[test]
    fn all_rejects_when_hostile_thenable_fulfills_then_rejects() {
        let module = blank_program("<promise-all-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let thenable = super::super::ordinary_runtime(&mut machine, None).unwrap();
        let then = callback(&mut machine, "fulfill then reject", fulfill_then_reject);
        machine.set_data_property(thenable, "then", then).unwrap();
        machine.test_set_global("hostileThenable", thenable);
        let resolve = callback(
            &mut machine,
            "return hostile thenable",
            return_hostile_thenable,
        );
        machine
            .set_data_property(constructor, "resolve", resolve)
            .unwrap();
        let iterable = super::super::allocate_array(&mut machine, vec![Value::int32(1)]).unwrap();
        let all = machine.get_named_property(constructor, "all").unwrap();

        let promise = machine.call_value(all, constructor, &[iterable]).unwrap();

        assert!(matches!(
            state(&machine, promise),
            PromiseState::Rejected { reason, .. } if reason == Value::int32(99)
        ));
    }

    #[test]
    fn all_rejects_when_empty_capability_resolve_throws() {
        let module = blank_program("<promise-all-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let promise_constructor = machine.intrinsics.global("Promise").unwrap();
        let all = machine
            .get_named_property(promise_constructor, "all")
            .unwrap();
        let constructor = callback(
            &mut machine,
            "throwing capability constructor",
            throwing_capability_constructor,
        );
        let resolve = callback(&mut machine, "unused resolve", return_undefined);
        machine
            .set_data_property(constructor, "resolve", resolve)
            .unwrap();
        let iterable = super::super::allocate_array(&mut machine, Vec::new()).unwrap();

        let promise = machine.call_value(all, constructor, &[iterable]).unwrap();

        assert_eq!(machine.test_global("capabilityPromise"), Some(promise));
        assert_eq!(
            machine.test_global("capabilityRejectReason"),
            Some(Value::int32(99))
        );
    }

    fn state(machine: &Machine<'_, TestHost>, promise: Value) -> PromiseState {
        let index = machine.runtime_slot(promise).unwrap().unwrap();
        let HeapEntry::Promise { state, .. } = &machine.heap[index] else {
            panic!("expected promise");
        };
        state.clone()
    }

    #[test]
    fn finally_preserves_fulfillment_and_rejection_and_replaces_with_throw() {
        let module = blank_program("<promise-finally-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let pass = callback(&mut machine, "pass finally", return_undefined);
        let throw = callback(&mut machine, "throw finally", throw_99);

        let fulfilled = machine.create_promise().unwrap();
        let finally = machine.get_named_property(fulfilled, "finally").unwrap();
        let preserved = machine.call_value(finally, fulfilled, &[pass]).unwrap();
        machine.fulfill_promise(fulfilled, Value::int32(7)).unwrap();
        machine.drain_microtasks().unwrap();
        assert!(
            matches!(state(&machine, preserved), PromiseState::Fulfilled { value } if value == Value::int32(7))
        );

        let rejected = machine.create_promise().unwrap();
        let preserved = machine.call_value(finally, rejected, &[pass]).unwrap();
        machine
            .reject_promise(rejected, Value::int32(8), ThrowOrigin::Bytecode)
            .unwrap();
        machine.drain_microtasks().unwrap();
        assert!(
            matches!(state(&machine, preserved), PromiseState::Rejected { reason, .. } if reason == Value::int32(8))
        );

        let source = machine.create_promise().unwrap();
        let replaced = machine.call_value(finally, source, &[throw]).unwrap();
        machine.fulfill_promise(source, Value::int32(7)).unwrap();
        machine.drain_microtasks().unwrap();
        assert!(
            matches!(state(&machine, replaced), PromiseState::Rejected { reason, .. } if reason == Value::int32(99))
        );
    }

    #[test]
    fn finally_awaits_thenable_before_preserving_completion() {
        let module = blank_program("<promise-finally-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let then = callback(&mut machine, "thenable then", resolve_88);
        let handler = callback(&mut machine, "return thenable", return_thenable);
        let thenable = super::super::ordinary_runtime(&mut machine, None).unwrap();
        machine.set_data_property(thenable, "then", then).unwrap();
        machine.test_set_global("thenable", thenable);

        let source = machine.create_promise().unwrap();
        let finally = machine.get_named_property(source, "finally").unwrap();
        let derived = machine.call_value(finally, source, &[handler]).unwrap();
        machine.fulfill_promise(source, Value::int32(7)).unwrap();
        machine.drain_microtasks().unwrap();

        assert_eq!(machine.test_global("handlerSeen"), Some(Value::int32(1)));
        assert_eq!(machine.test_global("thenSeen"), Some(Value::int32(2)));
        assert!(
            matches!(state(&machine, derived), PromiseState::Fulfilled { value } if value == Value::int32(7))
        );
    }

    #[test]
    fn constructor_honors_new_target_for_subclass_prototype() {
        let module = blank_program("<promise-subclass-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let promise_constructor = machine.intrinsics.global("Promise").unwrap();
        let promise_prototype = machine.intrinsics.builtins.promise_prototype();

        // Build a subclass prototype that inherits from Promise.prototype.
        let subclass_prototype =
            super::super::ordinary_runtime(&mut machine, Some(promise_prototype)).unwrap();
        machine
            .set_data_property(subclass_prototype, "myMethod", Value::int32(42))
            .unwrap();

        // Build a new_target whose .prototype is the subclass prototype.
        let new_target = super::super::ordinary_runtime(&mut machine, None).unwrap();
        machine
            .set_data_property(new_target, "prototype", subclass_prototype)
            .unwrap();

        let promise_id = machine.intrinsics.builtins.id_named("Promise").unwrap();
        let executor = callback(&mut machine, "resolve immediately", return_undefined);
        let BuiltinOutcome::Value(promise) = machine
            .call_builtin_with_new_target(
                promise_id,
                Value::UNDEFINED,
                &[executor],
                true,
                new_target,
            )
            .unwrap()
        else {
            panic!("Promise construct returns a value");
        };

        // The promise must inherit from the subclass prototype, not
        // Promise.prototype directly.
        assert_eq!(
            machine.internal_get_prototype_of(promise).unwrap(),
            Some(subclass_prototype)
        );
        // Subclass methods are visible on the instance.
        assert_eq!(
            machine.get_named_property(promise, "myMethod").unwrap(),
            Value::int32(42)
        );
        // And it is still a real promise.
        assert!(matches!(
            state(&machine, promise),
            PromiseState::Pending { .. }
        ));
        let _ = promise_constructor;
    }

    #[test]
    fn then_rejects_non_promise_receiver_without_observable_getter() {
        let module = blank_program("<promise-then-brand-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        // A spy object with a `constructor` getter that would be observed
        // if the brand check did not short-circuit first.
        let spy = super::super::ordinary_runtime(&mut machine, None).unwrap();
        let getter = callback(&mut machine, "constructor getter", constructor_getter);
        machine
            .define_accessor(
                spy,
                PropertyKey::Named(EcmaString::encode("constructor")),
                getter,
                crate::AccessorKind::Getter,
            )
            .unwrap();

        let then = machine
            .get_named_property(machine.intrinsics.builtins.promise_prototype(), "then")
            .unwrap();
        let result = machine.call_value(then, spy, &[Value::UNDEFINED]);

        // Must throw a TypeError.
        assert!(matches!(
            result,
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        // The constructor getter must NOT have been invoked.
        assert_eq!(machine.test_global("constructorGetCount"), None);
    }

    fn constructor_getter(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let count = machine
            .test_global("constructorGetCount")
            .and_then(Value::decode)
            .and_then(|value| match value {
                bamts_native::Decoded::Int32(raw) => Some(raw),
                _ => None,
            })
            .unwrap_or(0);
        machine.test_set_global("constructorGetCount", Value::int32(count + 1));
        Ok(BuiltinOutcome::Value(
            machine.intrinsics.global("Promise").unwrap(),
        ))
    }

    fn record_value(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.test_set_global(
            "recordedValue",
            args.first().copied().unwrap_or(Value::UNDEFINED),
        );
        Ok(BuiltinOutcome::Value(
            args.first().copied().unwrap_or(Value::UNDEFINED),
        ))
    }

    #[test]
    fn then_survives_global_promise_reassignment() {
        let module = blank_program("<promise-global-reassign>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        // Create and fulfill a promise before clobbering the global.
        let promise = machine.create_promise().unwrap();
        machine.fulfill_promise(promise, Value::int32(42)).unwrap();

        // Simulate script code reassigning the global `Promise`.  Before the
        // fix, `intrinsic_target` and `species_constructor` re-read this global
        // to resolve internal target functions, so the reassignment would
        // redirect those lookups and break `then`.
        machine
            .intrinsics
            .globals
            .insert(EcmaString::encode("Promise"), Value::UNDEFINED);

        let then = machine.get_named_property(promise, "then").unwrap();
        let on_fulfilled = callback(&mut machine, "record value", record_value);
        let derived = machine.call_value(then, promise, &[on_fulfilled]).unwrap();
        machine.drain_microtasks().unwrap();

        // The fulfillment reaction ran and forwarded the value.
        assert_eq!(machine.test_global("recordedValue"), Some(Value::int32(42)));
        let derived_state = state(&machine, derived);
        assert!(
            matches!(derived_state, PromiseState::Fulfilled { value } if value == Value::int32(42)),
            "derived promise should be fulfilled with 42, got {derived_state:?}"
        );
    }

    #[test]
    fn promise_has_no_nul_prefixed_own_keys() {
        // The 7 internal target functions must live in BuiltinTable, not as
        // script-reachable \0-prefixed properties on %Promise% or its prototype.
        let module = blank_program("<promise-nul-keys>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let promise_ctor = machine.intrinsics.global("Promise").unwrap();
        let idx = machine
            .runtime_slot(promise_ctor)
            .expect("Promise has slot")
            .expect("slot exists");
        let HeapEntry::NativeFunction { properties, .. } = &machine.heap[idx] else {
            panic!("Promise constructor is native");
        };
        for (key, _) in properties.iter() {
            if let PropertyKey::Named(name) = key {
                assert!(
                    !name.as_units().starts_with(&[0]),
                    "Promise should have no NUL-prefixed own keys, found {:?}",
                    name
                );
            }
        }
        // Also check prototype
        let proto = machine.intrinsics.builtins.promise_prototype();
        let proto_idx = machine
            .runtime_slot(proto)
            .expect("prototype has slot")
            .expect("slot exists");
        let HeapEntry::Object { properties, .. } = &machine.heap[proto_idx] else {
            panic!("Promise prototype is object");
        };
        for (key, _) in properties.iter() {
            if let PropertyKey::Named(name) = key {
                assert!(
                    !name.as_units().starts_with(&[0]),
                    "Promise.prototype should have no NUL-prefixed own keys, found {:?}",
                    name
                );
            }
        }
        // And verify capability/then/finally still work via BuiltinTable
        let promise = machine.create_promise().unwrap();
        machine.fulfill_promise(promise, Value::int32(1)).unwrap();
        let then = machine.get_named_property(promise, "then").unwrap();
        let on_fulfilled = callback(&mut machine, "noop", return_undefined);
        let derived = machine.call_value(then, promise, &[on_fulfilled]).unwrap();
        machine.drain_microtasks().unwrap();
        assert!(matches!(
            state(&machine, derived),
            PromiseState::Fulfilled { .. }
        ));
    }

    // ── Static presence and length ─────────────────────────────────────

    #[test]
    fn race_all_settled_any_are_installed_statics_with_length_1() {
        let module = blank_program("<promise-statics>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        for name in ["race", "allSettled", "any"] {
            let method = machine.get_named_property(constructor, name).unwrap();
            assert!(
                machine.is_callable(method).unwrap(),
                "Promise.{name} must be callable"
            );
            let length = machine.get_named_property(method, "length").unwrap();
            assert_eq!(length, Value::int32(1), "Promise.{name} length must be 1");
        }
    }

    // ── race ───────────────────────────────────────────────────────────

    #[test]
    fn race_fulfills_with_first_settled_promise() {
        let module = blank_program("<promise-race-fulfill>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let slow = machine.create_promise().unwrap();
        let fast = machine.create_promise().unwrap();
        let iterable = super::super::allocate_array(&mut machine, vec![slow, fast]).unwrap();
        let race = machine.get_named_property(constructor, "race").unwrap();

        let promise = machine.call_value(race, constructor, &[iterable]).unwrap();
        assert!(matches!(
            state(&machine, promise),
            PromiseState::Pending { .. }
        ));

        machine.fulfill_promise(fast, Value::int32(42)).unwrap();
        machine.drain_microtasks().unwrap();

        assert!(
            matches!(state(&machine, promise), PromiseState::Fulfilled { value } if value == Value::int32(42)),
            "race should fulfill with the first settled promise"
        );
    }

    #[test]
    fn race_rejects_with_first_rejected_promise() {
        let module = blank_program("<promise-race-reject>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let slow = machine.create_promise().unwrap();
        let fast = machine.create_promise().unwrap();
        let iterable = super::super::allocate_array(&mut machine, vec![slow, fast]).unwrap();
        let race = machine.get_named_property(constructor, "race").unwrap();

        let promise = machine.call_value(race, constructor, &[iterable]).unwrap();
        machine
            .reject_promise(fast, Value::int32(7), ThrowOrigin::Bytecode)
            .unwrap();
        machine.drain_microtasks().unwrap();

        assert!(
            matches!(state(&machine, promise), PromiseState::Rejected { reason, .. } if reason == Value::int32(7)),
            "race should reject with the first rejected promise"
        );
    }

    #[test]
    fn race_empty_iterable_stays_pending() {
        let module = blank_program("<promise-race-empty>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let iterable = super::super::allocate_array(&mut machine, Vec::new()).unwrap();
        let race = machine.get_named_property(constructor, "race").unwrap();

        let promise = machine.call_value(race, constructor, &[iterable]).unwrap();
        assert!(
            matches!(state(&machine, promise), PromiseState::Pending { .. }),
            "race with empty iterable must stay pending"
        );
    }

    #[test]
    fn race_mixed_fulfilled_and_rejected_settles_with_first() {
        let module = blank_program("<promise-race-mixed>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let fulfilled = machine.create_promise().unwrap();
        let rejected = machine.create_promise().unwrap();
        let iterable =
            super::super::allocate_array(&mut machine, vec![fulfilled, rejected]).unwrap();
        let race = machine.get_named_property(constructor, "race").unwrap();

        let promise = machine.call_value(race, constructor, &[iterable]).unwrap();
        machine
            .fulfill_promise(fulfilled, Value::int32(11))
            .unwrap();
        machine
            .reject_promise(rejected, Value::int32(22), ThrowOrigin::Bytecode)
            .unwrap();
        machine.drain_microtasks().unwrap();

        assert!(
            matches!(state(&machine, promise), PromiseState::Fulfilled { value } if value == Value::int32(11)),
            "race mixed should settle with whichever settles first"
        );
    }

    // ── allSettled ─────────────────────────────────────────────────────

    #[test]
    fn all_settled_empty_resolves_with_empty_array() {
        let module = blank_program("<promise-all-settled-empty>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let iterable = super::super::allocate_array(&mut machine, Vec::new()).unwrap();
        let all_settled = machine
            .get_named_property(constructor, "allSettled")
            .unwrap();

        let promise = machine
            .call_value(all_settled, constructor, &[iterable])
            .unwrap();
        machine.drain_microtasks().unwrap();

        match state(&machine, promise) {
            PromiseState::Fulfilled { value } => {
                let elements = machine
                    .array_elements(value)
                    .unwrap()
                    .expect("result is an array");
                assert!(elements.is_empty(), "empty allSettled resolves with []");
            }
            other => panic!("empty allSettled should fulfill, got {other:?}"),
        }
    }

    #[test]
    fn all_settled_mixed_produces_ordered_records() {
        let module = blank_program("<promise-all-settled-mixed>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let p0 = machine.create_promise().unwrap();
        let p1 = machine.create_promise().unwrap();
        let iterable = super::super::allocate_array(&mut machine, vec![p0, p1]).unwrap();
        let all_settled = machine
            .get_named_property(constructor, "allSettled")
            .unwrap();

        let promise = machine
            .call_value(all_settled, constructor, &[iterable])
            .unwrap();
        // Settle out of order: p1 first (rejected), then p0 (fulfilled).
        machine
            .reject_promise(p1, Value::int32(99), ThrowOrigin::Bytecode)
            .unwrap();
        machine.fulfill_promise(p0, Value::int32(42)).unwrap();
        machine.drain_microtasks().unwrap();

        match state(&machine, promise) {
            PromiseState::Fulfilled { value } => {
                let elements = machine
                    .array_elements(value)
                    .unwrap()
                    .expect("result is an array");
                assert_eq!(elements.len(), 2, "two inputs → two records");
                // Index 0: fulfilled with 42
                let status0 = machine.get_named_property(elements[0], "status").unwrap();
                assert_eq!(
                    machine.string_value(status0).unwrap(),
                    EcmaString::encode("fulfilled")
                );
                let val0 = machine.get_named_property(elements[0], "value").unwrap();
                assert_eq!(val0, Value::int32(42));
                // Index 1: rejected with 99
                let status1 = machine.get_named_property(elements[1], "status").unwrap();
                assert_eq!(
                    machine.string_value(status1).unwrap(),
                    EcmaString::encode("rejected")
                );
                let reason1 = machine.get_named_property(elements[1], "reason").unwrap();
                assert_eq!(reason1, Value::int32(99));
            }
            other => panic!("mixed allSettled should fulfill, got {other:?}"),
        }
    }

    // ── any ────────────────────────────────────────────────────────────

    #[test]
    fn any_fulfills_with_first_fulfilled_promise() {
        let module = blank_program("<promise-any-fulfill>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let rejected = machine.create_promise().unwrap();
        let fulfilled = machine.create_promise().unwrap();
        let iterable =
            super::super::allocate_array(&mut machine, vec![rejected, fulfilled]).unwrap();
        let any = machine.get_named_property(constructor, "any").unwrap();

        let promise = machine.call_value(any, constructor, &[iterable]).unwrap();
        machine
            .reject_promise(rejected, Value::int32(10), ThrowOrigin::Bytecode)
            .unwrap();
        machine
            .fulfill_promise(fulfilled, Value::int32(77))
            .unwrap();
        machine.drain_microtasks().unwrap();

        assert!(
            matches!(state(&machine, promise), PromiseState::Fulfilled { value } if value == Value::int32(77)),
            "any should fulfill with the first fulfilled promise"
        );
    }

    #[test]
    fn any_all_rejected_rejects_with_aggregate_error() {
        let module = blank_program("<promise-any-all-rejected>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let p0 = machine.create_promise().unwrap();
        let p1 = machine.create_promise().unwrap();
        let iterable = super::super::allocate_array(&mut machine, vec![p0, p1]).unwrap();
        let any = machine.get_named_property(constructor, "any").unwrap();

        let promise = machine.call_value(any, constructor, &[iterable]).unwrap();
        machine
            .reject_promise(p0, Value::int32(10), ThrowOrigin::Bytecode)
            .unwrap();
        machine
            .reject_promise(p1, Value::int32(20), ThrowOrigin::Bytecode)
            .unwrap();
        machine.drain_microtasks().unwrap();

        match state(&machine, promise) {
            PromiseState::Rejected { reason, .. } => {
                // The reason must be an AggregateError whose `errors` array
                // contains the rejection reasons in iteration order.
                let errors = machine.get_named_property(reason, "errors").unwrap();
                let elements = machine
                    .array_elements(errors)
                    .unwrap()
                    .expect("AggregateError.errors is an array");
                assert_eq!(elements.len(), 2, "two rejections → two errors");
                assert_eq!(elements[0], Value::int32(10));
                assert_eq!(elements[1], Value::int32(20));
            }
            other => panic!("all-rejected any should reject with AggregateError, got {other:?}"),
        }
    }

    #[test]
    fn any_empty_iterable_rejects_with_aggregate_error() {
        let module = blank_program("<promise-any-empty>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let iterable = super::super::allocate_array(&mut machine, Vec::new()).unwrap();
        let any = machine.get_named_property(constructor, "any").unwrap();

        let promise = machine.call_value(any, constructor, &[iterable]).unwrap();
        machine.drain_microtasks().unwrap();

        match state(&machine, promise) {
            PromiseState::Rejected { reason, .. } => {
                let errors = machine.get_named_property(reason, "errors").unwrap();
                let elements = machine
                    .array_elements(errors)
                    .unwrap()
                    .expect("AggregateError.errors is an array");
                assert!(
                    elements.is_empty(),
                    "empty any → AggregateError with empty errors"
                );
            }
            other => panic!("empty any should reject with AggregateError, got {other:?}"),
        }
    }

    // ── Abrupt iterator / setup rejection ──────────────────────────────

    #[test]
    fn race_rejects_when_iterator_creation_throws() {
        let module = blank_program("<promise-race-bad-iter>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let race = machine.get_named_property(constructor, "race").unwrap();

        let promise = machine
            .call_value(race, constructor, &[Value::int32(0)])
            .unwrap();

        assert!(
            matches!(state(&machine, promise), PromiseState::Rejected { .. }),
            "race with non-iterable must reject the capability"
        );
    }

    #[test]
    fn all_settled_rejects_when_iterator_creation_throws() {
        let module = blank_program("<promise-all-settled-bad-iter>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let all_settled = machine
            .get_named_property(constructor, "allSettled")
            .unwrap();

        let promise = machine
            .call_value(all_settled, constructor, &[Value::int32(0)])
            .unwrap();

        assert!(
            matches!(state(&machine, promise), PromiseState::Rejected { .. }),
            "allSettled with non-iterable must reject the capability"
        );
    }

    #[test]
    fn any_rejects_when_iterator_creation_throws() {
        let module = blank_program("<promise-any-bad-iter>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        let any = machine.get_named_property(constructor, "any").unwrap();

        let promise = machine
            .call_value(any, constructor, &[Value::int32(0)])
            .unwrap();

        assert!(
            matches!(state(&machine, promise), PromiseState::Rejected { .. }),
            "any with non-iterable must reject the capability"
        );
    }

    #[test]
    fn all_settled_rejects_when_constructor_resolve_is_not_callable() {
        let module = blank_program("<promise-all-settled-bad-resolve>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Promise").unwrap();
        machine
            .set_data_property(constructor, "resolve", Value::int32(0))
            .unwrap();
        let all_settled = machine
            .get_named_property(constructor, "allSettled")
            .unwrap();
        let iterable = super::super::allocate_array(&mut machine, Vec::new()).unwrap();

        let promise = machine
            .call_value(all_settled, constructor, &[iterable])
            .unwrap();

        assert!(
            matches!(state(&machine, promise), PromiseState::Rejected { .. }),
            "allSettled with non-callable resolve must reject the capability"
        );
    }

    // ── Self-capability promise then observation ───────────────────────

    #[test]
    fn all_settled_observes_then_on_self_capability_promise() {
        let module = blank_program("<promise-all-settled-self-then>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let built_in = machine.intrinsics.global("Promise").unwrap();
        let constructor = callback(
            &mut machine,
            "self constructor",
            self_capability_constructor,
        );
        let resolve = callback(&mut machine, "self resolve", resolve_returns_capability);
        machine
            .set_data_property(constructor, "resolve", resolve)
            .unwrap();
        let all_settled = machine.get_named_property(built_in, "allSettled").unwrap();

        let iterable = custom_iterable(&mut machine, vec![Value::int32(1)]);
        let promise = machine
            .call_value(all_settled, constructor, &[iterable])
            .expect("allSettled returns its capability");
        machine.drain_microtasks().unwrap();

        assert_eq!(
            machine.test_global("thenObserved"),
            Some(Value::TRUE),
            "allSettled must observe the self-capability's own .then"
        );
        assert!(
            matches!(
                state(&machine, promise),
                PromiseState::Rejected { reason, .. } if reason == Value::int32(77)
            ),
            "allSettled must reject the capability when the self-capability's .then throws"
        );
    }

    #[test]
    fn any_observes_then_on_self_capability_promise() {
        let module = blank_program("<promise-any-self-then>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let built_in = machine.intrinsics.global("Promise").unwrap();
        let constructor = callback(
            &mut machine,
            "self constructor",
            self_capability_constructor,
        );
        let resolve = callback(&mut machine, "self resolve", resolve_returns_capability);
        machine
            .set_data_property(constructor, "resolve", resolve)
            .unwrap();
        let any = machine.get_named_property(built_in, "any").unwrap();

        let iterable = custom_iterable(&mut machine, vec![Value::int32(1)]);
        let promise = machine
            .call_value(any, constructor, &[iterable])
            .expect("any returns its capability");
        machine.drain_microtasks().unwrap();

        assert_eq!(
            machine.test_global("thenObserved"),
            Some(Value::TRUE),
            "any must observe the self-capability's own .then"
        );
        assert!(
            matches!(
                state(&machine, promise),
                PromiseState::Rejected { reason, .. } if reason == Value::int32(77)
            ),
            "any must reject the capability when the self-capability's .then throws"
        );
    }

    #[test]
    fn race_observes_then_on_self_capability_promise() {
        let module = blank_program("<promise-race-self-then>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let built_in = machine.intrinsics.global("Promise").unwrap();
        let constructor = callback(
            &mut machine,
            "self constructor",
            self_capability_constructor,
        );
        let resolve = callback(&mut machine, "self resolve", resolve_returns_capability);
        machine
            .set_data_property(constructor, "resolve", resolve)
            .unwrap();
        let race = machine.get_named_property(built_in, "race").unwrap();

        let iterable = custom_iterable(&mut machine, vec![Value::int32(1)]);
        let promise = machine
            .call_value(race, constructor, &[iterable])
            .expect("race returns its capability");
        machine.drain_microtasks().unwrap();

        assert_eq!(
            machine.test_global("thenObserved"),
            Some(Value::TRUE),
            "race must observe the self-capability's own .then"
        );
        assert!(
            matches!(
                state(&machine, promise),
                PromiseState::Rejected { reason, .. } if reason == Value::int32(77)
            ),
            "race must reject the capability when the self-capability's .then throws"
        );
    }

    // ── Post-capability error escape ───────────────────────────────────

    #[test]
    fn all_settled_routes_final_resolve_error_to_capability_reject() {
        let module = blank_program("<promise-all-settled-resolve-throws>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let promise_constructor = machine.intrinsics.global("Promise").unwrap();
        let all_settled = machine
            .get_named_property(promise_constructor, "allSettled")
            .unwrap();
        let constructor = callback(
            &mut machine,
            "throwing capability constructor",
            throwing_capability_constructor,
        );
        let resolve = callback(&mut machine, "unused resolve", return_undefined);
        machine
            .set_data_property(constructor, "resolve", resolve)
            .unwrap();
        let iterable = super::super::allocate_array(&mut machine, Vec::new()).unwrap();

        let promise = machine
            .call_value(all_settled, constructor, &[iterable])
            .unwrap();

        assert_eq!(machine.test_global("capabilityPromise"), Some(promise));
        assert_eq!(
            machine.test_global("capabilityRejectReason"),
            Some(Value::int32(99)),
            "allSettled empty with throwing capability resolve must route 99 to capability reject"
        );
    }

    #[test]
    fn all_settled_fulfillment_resolve_error_stays_on_derived_reaction() {
        let module = blank_program("<promise-all-settled-derived-resolve-throws>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let built_in = machine.intrinsics.global("Promise").unwrap();
        let all_settled = machine.get_named_property(built_in, "allSettled").unwrap();
        let constructor = callback(
            &mut machine,
            "throwing capability constructor",
            throwing_capability_constructor,
        );
        let resolve = callback(
            &mut machine,
            "return fulfilled built-in promise",
            return_fulfilled_builtin_promise,
        );
        machine
            .set_data_property(constructor, "resolve", resolve)
            .unwrap();
        let iterable = super::super::allocate_array(&mut machine, vec![Value::int32(1)]).unwrap();

        let promise = machine
            .call_value(all_settled, constructor, &[iterable])
            .unwrap();
        machine.drain_microtasks().unwrap();

        assert_eq!(machine.test_global("capabilityPromise"), Some(promise));
        assert_eq!(
            machine.test_global("capabilityResolveCount"),
            Some(Value::int32(1)),
            "allSettled must invoke the outer capability resolve once"
        );
        assert_eq!(
            machine.test_global("capabilityRejectReason"),
            None,
            "allSettled reaction resolve failure must not invoke the outer capability reject"
        );
    }

    #[test]
    fn any_fulfillment_resolve_error_stays_on_derived_reaction() {
        let module = blank_program("<promise-any-derived-resolve-throws>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let built_in = machine.intrinsics.global("Promise").unwrap();
        let any = machine.get_named_property(built_in, "any").unwrap();
        let constructor = callback(
            &mut machine,
            "throwing capability constructor",
            throwing_capability_constructor,
        );
        let resolve = callback(
            &mut machine,
            "return fulfilled built-in promise",
            return_fulfilled_builtin_promise,
        );
        machine
            .set_data_property(constructor, "resolve", resolve)
            .unwrap();
        let iterable = super::super::allocate_array(&mut machine, vec![Value::int32(1)]).unwrap();

        let promise = machine.call_value(any, constructor, &[iterable]).unwrap();
        machine.drain_microtasks().unwrap();

        assert_eq!(machine.test_global("capabilityPromise"), Some(promise));
        assert_eq!(
            machine.test_global("capabilityResolveCount"),
            Some(Value::int32(1)),
            "Promise.any must invoke the outer capability resolve once"
        );
        assert_eq!(
            machine.test_global("capabilityRejectReason"),
            None,
            "any reaction resolve failure must not invoke the outer capability reject"
        );
    }

    #[test]
    fn any_all_rejected_calls_throwing_capability_reject_once() {
        let module = blank_program("<promise-any-reject-once>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let built_in = machine.intrinsics.global("Promise").unwrap();
        let any = machine.get_named_property(built_in, "any").unwrap();
        let constructor = callback(
            &mut machine,
            "throwing reject capability constructor",
            throwing_reject_capability_constructor,
        );
        let resolve = callback(
            &mut machine,
            "return rejected built-in promise",
            return_rejected_builtin_promise,
        );
        machine
            .set_data_property(constructor, "resolve", resolve)
            .unwrap();
        let iterable =
            super::super::allocate_array(&mut machine, vec![Value::int32(11), Value::int32(22)])
                .unwrap();

        machine.call_value(any, constructor, &[iterable]).unwrap();
        machine.drain_microtasks().unwrap();

        assert_eq!(
            machine.test_global("capabilityRejectCount"),
            Some(Value::int32(1)),
            "Promise.any must invoke a throwing aggregate reject exactly once"
        );
    }
}
