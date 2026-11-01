use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, Value};

use super::property_descriptor::{PropertyDescriptor, from_property_descriptor, same_value};
use super::{allocate_array, allocate_string, install_function, keep_root, type_error, with_roots};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap};

/// Installs the complete ES2025 `Object` constructor static surface.
///
/// The caller owns `%Object%` construction and passes its cached constructor;
/// this leaf neither performs a global lookup nor installs prototype methods.
pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    builtins: &mut BuiltinTable<H>,
    constructor: Value,
) {
    for (name, length, handler) in [
        ("assign", 2, assign::<H> as BuiltinHandler<H>),
        ("create", 2, super::object::create::<H>),
        ("defineProperties", 2, super::object::define_properties::<H>),
        ("defineProperty", 3, super::object::define_property::<H>),
        ("entries", 1, entries::<H>),
        ("freeze", 1, freeze::<H>),
        ("fromEntries", 1, from_entries::<H>),
        (
            "getOwnPropertyDescriptor",
            2,
            get_own_property_descriptor::<H>,
        ),
        (
            "getOwnPropertyDescriptors",
            1,
            get_own_property_descriptors::<H>,
        ),
        ("getOwnPropertyNames", 1, get_own_property_names::<H>),
        ("getOwnPropertySymbols", 1, get_own_property_symbols::<H>),
        ("getPrototypeOf", 1, get_prototype_of::<H>),
        ("groupBy", 2, group_by::<H>),
        ("hasOwn", 2, has_own::<H>),
        ("is", 2, object_is::<H>),
        ("isExtensible", 1, is_extensible_method::<H>),
        ("isFrozen", 1, is_frozen::<H>),
        ("isSealed", 1, is_sealed::<H>),
        ("keys", 1, keys::<H>),
        ("preventExtensions", 1, prevent_extensions::<H>),
        ("seal", 1, seal::<H>),
        ("setPrototypeOf", 2, set_prototype_of::<H>),
        ("values", 1, values::<H>),
    ] {
        let function = install_function(heap, builtins, name, length, handler);
        define_static(heap, constructor, name, function);
    }
}

fn define_static(heap: &mut [HeapEntry], constructor: Value, name: &str, value: Value) {
    let index = super::heap_index(constructor);
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[index] else {
        panic!("Object constructor must be a native function");
    };
    properties.insert(
        PropertyKey::Named(EcmaString::encode(name)),
        super::builtin_property(value),
    );
}

fn argument(args: &[Value], index: usize) -> Value {
    args.get(index).copied().unwrap_or(Value::UNDEFINED)
}

fn require_object_coercible(value: Value, operation: &'static str) -> Result<(), EvalFailure> {
    if matches!(value.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        Err(type_error(operation))
    } else {
        Ok(())
    }
}

fn to_object<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    operation: &'static str,
) -> Result<Value, EvalFailure> {
    require_object_coercible(value, operation)?;
    machine.value_to_object(value)
}

fn ordinary_object<H: Host>(
    machine: &mut Machine<'_, H>,
    prototype: Option<Value>,
) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype,
            extensible: true,
            boxed_primitive: None,
        })
        .map_err(EvalFailure::Runtime)
}

fn create_data_property<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    key: PropertyKey,
    value: Value,
) -> Result<(), EvalFailure> {
    machine.define_descriptor(
        object,
        key,
        Property::Data {
            value,
            writable: true,
            enumerable: true,
            configurable: true,
        },
    )
}

fn symbol_value(index: u32) -> Value {
    Value::heap_ref(
        bamts_native::SlotId::from_parts(crate::RUNTIME_HEAP_SEGMENT, index + 1)
            .expect("property symbol is a valid runtime heap slot"),
    )
}

/// `ToObject` is represented by raw primitive values on several runtime paths.
/// String exotic own keys therefore need their virtual indices and `length`
/// merged with stored keys before the ES `[[OwnPropertyKeys]]` consumers run.
/// The ordinary `[[OwnPropertyKeys]]` core, including the string-exotic
/// virtual-index merge for (boxed) strings. Invoked BY
/// `Machine::internal_own_property_keys`; user-facing callers must go through
/// the canonical method.
pub(super) fn own_keys<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
) -> Result<Vec<PropertyKey>, EvalFailure> {
    if let Some(index) = machine.runtime_slot(object).map_err(EvalFailure::Runtime)? {
        machine.reify_function_properties(index)?;
    }
    let stored = machine.own_property_keys(object)?;
    let primitive = machine.unbox_primitive_or_self(object)?;
    let Some(index) = machine
        .runtime_slot(primitive)
        .map_err(EvalFailure::Runtime)?
    else {
        return Ok(stored);
    };
    let HeapEntry::String(text) = &machine.heap[index] else {
        return Ok(stored);
    };

    let mut indices = BTreeMap::new();
    for offset in 0..text.len_units() {
        indices.insert(
            offset as u32,
            PropertyKey::Named(EcmaString::encode(&offset.to_string())),
        );
    }
    let mut strings = Vec::new();
    let mut symbols = Vec::new();
    for key in stored {
        match &key {
            PropertyKey::Named(name) => {
                if let Some(offset) = crate::array_index(name) {
                    indices.insert(offset, key);
                } else if !name.eq_ascii("length") {
                    strings.push(key);
                }
            }
            PropertyKey::Symbol(_) => symbols.push(key),
            PropertyKey::Private(_) => {}
        }
    }
    Ok(indices
        .into_values()
        .chain(std::iter::once(PropertyKey::Named(EcmaString::encode(
            "length",
        ))))
        .chain(strings)
        .chain(symbols)
        .collect())
}

/// `[[GetOwnProperty]]` seam: every Object-static descriptor read dispatches
/// through the canonical method (trap-bearing for proxies).
fn own_descriptor<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    key: &PropertyKey,
) -> Result<Option<PropertyDescriptor>, EvalFailure> {
    machine.internal_get_own_property(object, key)
}

/// `EnumerableOwnProperties`, reading each key's descriptor immediately before
/// its value. `item` builds the list entry from the name and that value.
fn enumerable_own_properties<H: Host>(
    machine: &mut Machine<'_, H>,
    source: Value,
    item: impl Fn(&mut Machine<'_, H>, EcmaString, Value) -> Result<Value, EvalFailure>,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_object_coercible(source, "Cannot convert undefined or null to object")?;
    let object = machine.value_to_object(source)?;
    with_roots(machine, &[object], |machine, depth| {
        let mut items = Vec::new();
        for key in machine.internal_own_property_keys(object)? {
            let PropertyKey::Named(name) = &key else {
                continue;
            };
            if !own_descriptor(machine, object, &key)?
                .is_some_and(|descriptor| descriptor.enumerable == Some(true))
            {
                continue;
            }
            let value = machine.get_property_key(object, &key)?;
            let entry = item(machine, name.clone(), value)?;
            keep_root(machine, depth, entry);
            items.push(entry);
        }
        allocate_array(machine, items).map(BuiltinOutcome::Value)
    })
}

fn assign<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let target = to_object(
        machine,
        argument(args, 0),
        "Cannot convert undefined or null to object",
    )?;
    for source in args.iter().copied().skip(1) {
        if matches!(source.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            continue;
        }
        let source = machine.value_to_object(source)?;
        for key in machine.internal_own_property_keys(source)? {
            if !machine
                .internal_get_own_property(source, &key)?
                .is_some_and(|descriptor| descriptor.enumerable == Some(true))
            {
                continue;
            }
            let value = machine.get_property_key(source, &key)?;
            machine.set_data_property_key(target, key, value)?;
        }
    }
    Ok(BuiltinOutcome::Value(target))
}

fn keys<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = argument(args, 0);
    require_object_coercible(object, "Cannot convert undefined or null to object")?;
    let object = machine.value_to_object(object)?;
    with_roots(machine, &[object], |machine, depth| {
        let mut names = Vec::new();
        for key in machine.internal_own_property_keys(object)? {
            if let PropertyKey::Named(name) = &key
                && own_descriptor(machine, object, &key)?
                    .is_some_and(|descriptor| descriptor.enumerable == Some(true))
            {
                let name = allocate_string(machine, name.clone())?;
                keep_root(machine, depth, name);
                names.push(name);
            }
        }
        allocate_array(machine, names).map(BuiltinOutcome::Value)
    })
}

fn values<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    enumerable_own_properties(machine, argument(args, 0), |_, _, value| Ok(value))
}

fn entries<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    enumerable_own_properties(machine, argument(args, 0), |machine, name, value| {
        let key = allocate_string(machine, name)?;
        allocate_array(machine, vec![key, value])
    })
}

fn get_own_property_descriptor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = argument(args, 0);
    require_object_coercible(source, "Cannot convert undefined or null to object")?;
    let source = machine.value_to_object(source)?;
    let key = machine.observable_property_key(argument(args, 1))?;
    let descriptor = own_descriptor(machine, source, &key)?;
    Ok(BuiltinOutcome::Value(from_property_descriptor(
        machine, descriptor,
    )?))
}

fn get_own_property_descriptors<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = argument(args, 0);
    require_object_coercible(source, "Cannot convert undefined or null to object")?;
    let source = machine.value_to_object(source)?;
    let keys = machine.internal_own_property_keys(source)?;
    let result = ordinary_object(machine, Some(machine.intrinsics.object_prototype))?;
    for key in keys {
        let descriptor = own_descriptor(machine, source, &key)?;
        let reified = from_property_descriptor(machine, descriptor)?;
        if reified != Value::UNDEFINED {
            create_data_property(machine, result, key, reified)?;
        }
    }
    Ok(BuiltinOutcome::Value(result))
}

fn get_own_property_names<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = argument(args, 0);
    require_object_coercible(source, "Cannot convert undefined or null to object")?;
    let mut names = Vec::new();
    for key in machine.internal_own_property_keys(source)? {
        if let PropertyKey::Named(name) = key {
            names.push(allocate_string(machine, name)?);
        }
    }
    Ok(BuiltinOutcome::Value(allocate_array(machine, names)?))
}

fn get_own_property_symbols<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = argument(args, 0);
    require_object_coercible(source, "Cannot convert undefined or null to object")?;
    let symbols = machine
        .internal_own_property_keys(source)?
        .into_iter()
        .filter_map(|key| match key {
            PropertyKey::Symbol(index) => Some(symbol_value(index)),
            PropertyKey::Named(_) | PropertyKey::Private(_) => None,
        })
        .collect();
    Ok(BuiltinOutcome::Value(allocate_array(machine, symbols)?))
}

fn get_prototype_of<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(
        machine,
        argument(args, 0),
        "Cannot convert undefined or null to object",
    )?;
    Ok(BuiltinOutcome::Value(
        machine
            .internal_get_prototype_of(object)?
            .unwrap_or(Value::NULL),
    ))
}

fn has_own<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = argument(args, 0);
    require_object_coercible(source, "Cannot convert undefined or null to object")?;
    let key = machine.observable_property_key(argument(args, 1))?;
    Ok(BuiltinOutcome::Value(Value::boolean(
        own_descriptor(machine, source, &key)?.is_some(),
    )))
}

fn object_is<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(Value::boolean(same_value(
        machine,
        argument(args, 0),
        argument(args, 1),
    ))))
}

fn is_extensible_method<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = argument(args, 0);
    let result = machine.is_object(value) && machine.internal_is_extensible(value)?;
    Ok(BuiltinOutcome::Value(Value::boolean(result)))
}

#[derive(Clone, Copy)]
enum IntegrityLevel {
    Sealed,
    Frozen,
}

fn prevent_extensions_object<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
) -> Result<bool, EvalFailure> {
    machine.internal_prevent_extensions(object)
}

fn set_integrity_level<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    level: IntegrityLevel,
) -> Result<bool, EvalFailure> {
    if !prevent_extensions_object(machine, object)? {
        return Ok(false);
    }
    let keys = machine.internal_own_property_keys(object)?;
    for key in keys {
        let mut descriptor = PropertyDescriptor {
            configurable: Some(false),
            ..PropertyDescriptor::default()
        };
        if matches!(level, IntegrityLevel::Frozen)
            && own_descriptor(machine, object, &key)?.is_some_and(|descriptor| descriptor.is_data())
        {
            descriptor.writable = Some(false);
        }
        if !machine.internal_define_own_property(object, key, descriptor)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn test_integrity_level<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    level: IntegrityLevel,
) -> Result<bool, EvalFailure> {
    if machine.internal_is_extensible(object)? {
        return Ok(false);
    }
    for key in machine.internal_own_property_keys(object)? {
        let Some(descriptor) = own_descriptor(machine, object, &key)? else {
            continue;
        };
        if descriptor.configurable == Some(true)
            || (matches!(level, IntegrityLevel::Frozen)
                && descriptor.is_data()
                && descriptor.writable == Some(true))
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn freeze<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = argument(args, 0);
    if machine.is_object(object) && !set_integrity_level(machine, object, IntegrityLevel::Frozen)? {
        return Err(type_error("Object.freeze failed"));
    }
    Ok(BuiltinOutcome::Value(object))
}

fn seal<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = argument(args, 0);
    if machine.is_object(object) && !set_integrity_level(machine, object, IntegrityLevel::Sealed)? {
        return Err(type_error("Object.seal failed"));
    }
    Ok(BuiltinOutcome::Value(object))
}

fn prevent_extensions<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = argument(args, 0);
    if machine.is_object(object) && !prevent_extensions_object(machine, object)? {
        return Err(type_error("Object.preventExtensions failed"));
    }
    Ok(BuiltinOutcome::Value(object))
}

fn is_frozen<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = argument(args, 0);
    let result = !machine.is_object(object)
        || test_integrity_level(machine, object, IntegrityLevel::Frozen)?;
    Ok(BuiltinOutcome::Value(Value::boolean(result)))
}

fn is_sealed<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = argument(args, 0);
    let result = !machine.is_object(object)
        || test_integrity_level(machine, object, IntegrityLevel::Sealed)?;
    Ok(BuiltinOutcome::Value(Value::boolean(result)))
}

fn set_prototype_of<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = argument(args, 0);
    require_object_coercible(object, "Object.setPrototypeOf called on null or undefined")?;
    let prototype = argument(args, 1);
    if prototype != Value::NULL && !machine.is_object(prototype) {
        return Err(type_error("Object prototype may only be an Object or null"));
    }
    if !machine.is_object(object) {
        return Ok(BuiltinOutcome::Value(object));
    }
    if !machine
        .internal_set_prototype_of(object, (prototype != Value::NULL).then_some(prototype))?
    {
        return Err(type_error("Cannot set prototype: object is not extensible"));
    }
    Ok(BuiltinOutcome::Value(object))
}

fn get_sync_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    iterable: Value,
) -> Result<Value, EvalFailure> {
    let key = machine.to_property_key(machine.intrinsics.builtins.symbol_iterator())?;
    let method = machine.get_property_key(iterable, &key)?;
    if !machine.is_callable(method)? {
        return Err(type_error("value is not iterable"));
    }
    let target = machine.call_value(method, iterable, &[])?;
    if !machine.is_object(target) {
        return Err(type_error("iterator method returned a non-object"));
    }
    let next = machine.get_named_property(target, "next")?;
    machine.create_protocol_iterator(target, next)
}

fn close_after_abrupt<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator: Value,
    failure: EvalFailure,
) -> EvalFailure {
    // ES2025 IteratorClose preserves an existing throw even when `return`
    // lookup/call throws; an engine failure still prevents safe continuation.
    // https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-iteratorclose
    match machine.close_iterator_raw(iterator).0 {
        Err(EvalFailure::Runtime(kind)) => EvalFailure::Runtime(kind),
        Ok(_)
        | Err(
            EvalFailure::Throw(_)
            | EvalFailure::ThrowValue(_)
            | EvalFailure::ThrowValueOrigin { .. },
        ) => failure,
    }
}

fn from_entries<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let iterable = argument(args, 0);
    require_object_coercible(iterable, "Object.fromEntries requires an iterable")?;
    let object = ordinary_object(machine, Some(machine.intrinsics.object_prototype))?;
    let depth = machine.native_roots.len();
    machine.push_native_roots(depth, &[object, iterable]);
    let result: Result<(), EvalFailure> = (|| {
        let iterator = get_sync_iterator(machine, iterable)?;
        machine.refresh_native_roots(depth, &[object, iterator]);
        loop {
            // Failures from iterator stepping are not IteratorClose sites.
            let result = machine.iterator_step(iterator)?;
            let (done, entry) = machine.iterator_result_parts(result)?;
            if done {
                break;
            }
            machine.refresh_native_roots(depth, &[object, iterator, entry]);
            let inserted = (|| {
                if !machine.is_object(entry) {
                    return Err(type_error("Iterator value is not an entry object"));
                }
                let key_value = machine.get_named_property(entry, "0")?;
                machine.refresh_native_roots(depth, &[object, iterator, entry, key_value]);
                let value = machine.get_named_property(entry, "1")?;
                machine.refresh_native_roots(depth, &[object, iterator, entry, key_value, value]);
                let key = machine.observable_property_key(key_value)?;
                create_data_property(machine, object, key, value)
            })();
            if let Err(failure) = inserted {
                match &failure {
                    EvalFailure::ThrowValue(value)
                    | EvalFailure::ThrowValueOrigin { value, .. } => {
                        machine.refresh_native_roots(depth, &[object, iterator, *value]);
                    }
                    EvalFailure::Throw(_) | EvalFailure::Runtime(_) => {
                        machine.refresh_native_roots(depth, &[object, iterator]);
                    }
                }
                return Err(close_after_abrupt(machine, iterator, failure));
            }
        }
        Ok(())
    })();
    machine.pop_native_roots(depth);
    result?;
    Ok(BuiltinOutcome::Value(object))
}

struct Group {
    key: PropertyKey,
    values: Vec<Value>,
}

fn group_by<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let items = argument(args, 0);
    require_object_coercible(items, "Object.groupBy requires an iterable")?;
    let callback = argument(args, 1);
    if !machine.is_callable(callback)? {
        return Err(type_error("Object.groupBy callback is not callable"));
    }
    let iterator = get_sync_iterator(machine, items)?;
    // Group records keep first-encounter order and SameValueZero-free key
    // equality through PropertyKey's Ord, with equal integer-index keys
    // merged after ToPropertyKey canonicalization.
    let mut groups: Vec<Group> = Vec::new();
    let mut group_indices: BTreeMap<PropertyKey, usize> = BTreeMap::new();
    let mut index = 0_u64;
    loop {
        // GroupBy checks the safe-integer bound before advancing the iterator.
        // https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-groupby
        if index >= 9_007_199_254_740_991 {
            return Err(close_after_abrupt(
                machine,
                iterator,
                type_error("Object.groupBy iteration count exceeds safe integer range"),
            ));
        }
        let result = machine.iterator_step(iterator)?;
        let (done, value) = machine.iterator_result_parts(result)?;
        if done {
            break;
        }
        let key_value = match machine.call_value(
            callback,
            Value::UNDEFINED,
            &[value, crate::number_value(index as f64)],
        ) {
            Ok(key) => key,
            Err(failure) => return Err(close_after_abrupt(machine, iterator, failure)),
        };
        let key = match machine.observable_property_key(key_value) {
            Ok(key) => key,
            Err(failure) => return Err(close_after_abrupt(machine, iterator, failure)),
        };
        if let Some(group) = group_indices.get(&key).copied() {
            groups[group].values.push(value);
        } else {
            group_indices.insert(key.clone(), groups.len());
            groups.push(Group {
                key,
                values: vec![value],
            });
        }
        index += 1;
    }

    let result = ordinary_object(machine, None)?;
    for group in groups {
        let values = allocate_array(machine, group.values)?;
        create_data_property(machine, result, group.key, values)?;
    }
    Ok(BuiltinOutcome::Value(result))
}

#[cfg(test)]
mod tests {
    use bamts_native::Value;

    use super::super::test_support::{
        TestHost, blank_program, custom_iterable, ordinary_object as test_object,
    };
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, ThrowOrigin};

    fn with_machine(test: impl FnOnce(&mut Machine<'_, TestHost>)) {
        let program = blank_program("object statics");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        test(&mut machine);
    }

    fn value(outcome: BuiltinOutcome) -> Value {
        let BuiltinOutcome::Value(value) = outcome else {
            panic!("Object static completed without a value")
        };
        value
    }

    fn array(machine: &Machine<'_, TestHost>, value: Value) -> Vec<Value> {
        machine
            .array_elements(value)
            .expect("array lookup succeeds")
            .expect("result is an array")
    }

    #[test]
    fn object_is_uses_same_value() {
        with_machine(|machine| {
            let nan = value(
                object_is(
                    machine,
                    Value::UNDEFINED,
                    &[Value::number(f64::NAN), Value::number(f64::NAN)],
                    false,
                )
                .unwrap(),
            );
            let signed_zero = value(
                object_is(
                    machine,
                    Value::UNDEFINED,
                    &[Value::number(0.0), Value::number(-0.0)],
                    false,
                )
                .unwrap(),
            );
            assert_eq!(nan, Value::TRUE);
            assert_eq!(signed_zero, Value::FALSE);
        });
    }

    #[test]
    fn freeze_and_seal_apply_descriptor_invariants() {
        with_machine(|machine| {
            let frozen = test_object(machine);
            machine
                .define_descriptor(
                    frozen,
                    PropertyKey::Named(EcmaString::encode("data")),
                    Property::Data {
                        value: Value::int32(1),
                        writable: true,
                        enumerable: true,
                        configurable: true,
                    },
                )
                .unwrap();
            value(freeze(machine, Value::UNDEFINED, &[frozen], false).unwrap());
            assert!(!machine.internal_is_extensible(frozen).unwrap());
            assert!(matches!(
                machine
                    .own_descriptor(frozen, &PropertyKey::Named(EcmaString::encode("data")))
                    .unwrap(),
                Some(Property::Data {
                    writable: false,
                    configurable: false,
                    ..
                })
            ));
            assert_eq!(
                value(is_frozen(machine, Value::UNDEFINED, &[frozen], false).unwrap()),
                Value::TRUE
            );

            let sealed = test_object(machine);
            machine
                .define_descriptor(
                    sealed,
                    PropertyKey::Named(EcmaString::encode("data")),
                    Property::Data {
                        value: Value::int32(2),
                        writable: true,
                        enumerable: true,
                        configurable: true,
                    },
                )
                .unwrap();
            value(seal(machine, Value::UNDEFINED, &[sealed], false).unwrap());
            assert!(matches!(
                machine
                    .own_descriptor(sealed, &PropertyKey::Named(EcmaString::encode("data")))
                    .unwrap(),
                Some(Property::Data {
                    writable: true,
                    configurable: false,
                    ..
                })
            ));
            assert_eq!(
                value(is_sealed(machine, Value::UNDEFINED, &[sealed], false).unwrap()),
                Value::TRUE
            );
            assert_eq!(
                value(is_frozen(machine, Value::UNDEFINED, &[sealed], false).unwrap()),
                Value::FALSE
            );
        });
    }

    fn parity<H: Host>(
        _machine: &mut Machine<'_, H>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let number = match args.first().and_then(|value| value.decode()) {
            Some(Decoded::Int32(number)) => number,
            _ => 0,
        };
        Ok(BuiltinOutcome::Value(Value::int32(number % 2)))
    }

    #[test]
    fn group_by_returns_null_prototype_and_stable_groups() {
        with_machine(|machine| {
            let iterable = custom_iterable(
                machine,
                vec![Value::int32(1), Value::int32(2), Value::int32(3)],
            );
            let callback_id = machine.intrinsics.builtins.register(BuiltinDef {
                name: "parity",
                length: 2,
                handler: parity::<TestHost>,
            });
            let callback = native_function(&mut machine.heap, callback_id, "parity", 2);
            let grouped =
                value(group_by(machine, Value::UNDEFINED, &[iterable, callback], false).unwrap());
            assert_eq!(machine.internal_get_prototype_of(grouped).unwrap(), None);
            let odd = machine.get_named_property(grouped, "1").unwrap();
            let even = machine.get_named_property(grouped, "0").unwrap();
            assert_eq!(array(machine, odd), vec![Value::int32(1), Value::int32(3)]);
            assert_eq!(array(machine, even), vec![Value::int32(2)]);
        });
    }

    fn throwing_getter<H: Host>(
        _machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "entry key",
        }))
    }

    fn mark_closed<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "closed", Value::TRUE)?;
        Ok(BuiltinOutcome::Value(test_object(machine)))
    }

    fn yield_once<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let yielded = machine.get_named_property(this, "yielded")?;
        if yielded == Value::TRUE {
            return Ok(BuiltinOutcome::Value(
                machine.iterator_result(Value::UNDEFINED, true)?,
            ));
        }
        machine.set_data_property(this, "yielded", Value::TRUE)?;
        let entry = machine.get_named_property(this, "entry")?;
        Ok(BuiltinOutcome::Value(
            machine.iterator_result(entry, false)?,
        ))
    }

    fn iterator_self<H: Host>(
        _machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(this))
    }

    #[test]
    fn from_entries_closes_after_entry_abrupt_completion() {
        with_machine(|machine| {
            let entry = test_object(machine);
            let getter_id = machine.intrinsics.builtins.register(BuiltinDef {
                name: "throw key",
                length: 0,
                handler: throwing_getter::<TestHost>,
            });
            let getter = native_function(&mut machine.heap, getter_id, "throw key", 0);
            machine
                .define_descriptor(
                    entry,
                    PropertyKey::Named(EcmaString::encode("0")),
                    Property::Accessor {
                        getter: Some(getter),
                        setter: None,
                        enumerable: true,
                        configurable: true,
                    },
                )
                .unwrap();

            let iterator = test_object(machine);
            machine.set_data_property(iterator, "entry", entry).unwrap();
            machine
                .set_data_property(iterator, "yielded", Value::FALSE)
                .unwrap();
            machine
                .set_data_property(iterator, "closed", Value::FALSE)
                .unwrap();
            for (name, handler) in [
                ("next", yield_once::<TestHost> as BuiltinHandler<TestHost>),
                ("return", mark_closed::<TestHost>),
            ] {
                let id = machine.intrinsics.builtins.register(BuiltinDef {
                    name,
                    length: 0,
                    handler,
                });
                let function = native_function(&mut machine.heap, id, name, 0);
                machine.set_data_property(iterator, name, function).unwrap();
            }
            let iterator_id = machine.intrinsics.builtins.register(BuiltinDef {
                name: "iterator",
                length: 0,
                handler: iterator_self::<TestHost>,
            });
            let iterator_function = native_function(&mut machine.heap, iterator_id, "iterator", 0);
            let iterator_key = machine
                .to_property_key(machine.intrinsics.builtins.symbol_iterator())
                .unwrap();
            machine
                .set_data_property_key(iterator, iterator_key, iterator_function)
                .unwrap();

            assert!(from_entries(machine, Value::UNDEFINED, &[iterator], false).is_err());
            assert_eq!(
                machine.get_named_property(iterator, "closed").unwrap(),
                Value::TRUE
            );
        });
    }

    #[test]
    fn own_key_methods_keep_ecmascript_order_and_symbols() {
        with_machine(|machine| {
            let object = test_object(machine);
            let symbol = machine
                .allocate(HeapEntry::Symbol {
                    description: EcmaString::encode("s"),
                })
                .unwrap();
            let symbol_key = machine.to_property_key(symbol).unwrap();
            for (name, value) in [("b", 1), ("2", 2), ("1", 3), ("a", 4)] {
                create_data_property(
                    machine,
                    object,
                    PropertyKey::Named(EcmaString::encode(name)),
                    Value::int32(value),
                )
                .unwrap();
            }
            create_data_property(machine, object, symbol_key, Value::int32(5)).unwrap();

            let names =
                value(get_own_property_names(machine, Value::UNDEFINED, &[object], false).unwrap());
            let names: Vec<EcmaString> = array(machine, names)
                .into_iter()
                .map(|value| machine.string_value(value).unwrap())
                .collect();
            assert_eq!(names, ["1", "2", "b", "a"].map(EcmaString::encode));
            let symbols = value(
                get_own_property_symbols(machine, Value::UNDEFINED, &[object], false).unwrap(),
            );
            assert_eq!(array(machine, symbols), vec![symbol]);
        });
    }

    #[test]
    fn installed_methods_have_builtin_descriptors() {
        with_machine(|machine| {
            let constructor = machine.intrinsics.global("Object").unwrap();
            install(
                &mut machine.heap,
                &mut machine.intrinsics.builtins,
                constructor,
            );
            for (name, length) in [
                ("assign", 2),
                ("getOwnPropertyDescriptors", 1),
                ("groupBy", 2),
                ("seal", 1),
            ] {
                let method = machine.get_named_property(constructor, name).unwrap();
                assert!(matches!(
                    machine.own_descriptor(constructor, &PropertyKey::Named(EcmaString::encode(name))).unwrap(),
                    Some(Property::Data { value, writable: true, enumerable: false, configurable: true }) if value == method
                ));
                assert_eq!(
                    machine.get_named_property(method, "length").unwrap(),
                    crate::number_value(length as f64)
                );
                let installed_name = machine.get_named_property(method, "name").unwrap();
                assert_eq!(
                    machine.string_value(installed_name).unwrap(),
                    EcmaString::encode(name)
                );
            }
        });
    }
    fn capture_assignment<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "assigned", argument(args, 0))?;
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    #[test]
    fn assign_uses_set_and_invokes_inherited_setter() {
        with_machine(|machine| {
            let target = test_object(machine);
            let prototype = test_object(machine);
            let setter_id = machine.intrinsics.builtins.register(BuiltinDef {
                name: "capture assignment",
                length: 1,
                handler: capture_assignment::<TestHost>,
            });
            let setter = native_function(&mut machine.heap, setter_id, "capture assignment", 1);
            machine
                .define_descriptor(
                    prototype,
                    PropertyKey::Named(EcmaString::encode("x")),
                    Property::Accessor {
                        getter: None,
                        setter: Some(setter),
                        enumerable: true,
                        configurable: true,
                    },
                )
                .unwrap();
            machine
                .internal_set_prototype_of(target, Some(prototype))
                .unwrap();
            let source = test_object(machine);
            machine
                .set_data_property(source, "x", Value::int32(42))
                .unwrap();

            value(assign(machine, Value::UNDEFINED, &[target, source], false).unwrap());

            assert_eq!(
                machine.get_named_property(target, "assigned").unwrap(),
                Value::int32(42)
            );
            assert!(
                machine
                    .own_descriptor(target, &PropertyKey::Named(EcmaString::encode("x")))
                    .unwrap()
                    .is_none()
            );
        });
    }

    fn key_to_string<H: Host>(
        machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(
            machine
                .allocate(HeapEntry::String(EcmaString::encode("x")))
                .map_err(EvalFailure::Runtime)?,
        ))
    }

    #[test]
    fn public_key_arguments_use_observable_to_property_key() {
        with_machine(|machine| {
            let target = test_object(machine);
            let key_object = test_object(machine);
            let to_string_id = machine.intrinsics.builtins.register(BuiltinDef {
                name: "key toString",
                length: 0,
                handler: key_to_string::<TestHost>,
            });
            let to_string = native_function(&mut machine.heap, to_string_id, "key toString", 0);
            machine
                .set_data_property(key_object, "toString", to_string)
                .unwrap();
            let descriptor = test_object(machine);
            machine
                .set_data_property(descriptor, "value", Value::int32(7))
                .unwrap();

            value(
                super::super::object::define_property(
                    machine,
                    Value::UNDEFINED,
                    &[target, key_object, descriptor],
                    false,
                )
                .unwrap(),
            );
            assert_eq!(
                value(has_own(machine, Value::UNDEFINED, &[target, key_object], false).unwrap()),
                Value::TRUE
            );
            assert_eq!(
                machine.get_named_property(target, "x").unwrap(),
                Value::int32(7)
            );
        });
    }
}
