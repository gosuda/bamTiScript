use std::collections::BTreeSet;

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, SlotId, Value};

use super::property_descriptor::{
    PropertyDescriptor, complete_property_descriptor, from_property_descriptor,
    is_compatible_property_descriptor, to_property_descriptor,
};
use super::{
    allocate_array, allocate_string, define_data, install_function, to_integer_or_infinity,
    type_error,
};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::{
    EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap, RUNTIME_HEAP_SEGMENT,
};

/// The live/revoked state is one enum so a revoked proxy cannot retain either
/// target or handler. This mirrors ValidateNonRevokedProxy and makes the two GC
/// edges disappear in the same transition.
#[derive(Clone, Debug)]
enum ProxyState {
    Live { target: Value, handler: Value },
    Revoked,
}

/// Payload owned by `HeapEntry::Proxy`.
///
/// Callability and constructability are fixed by ProxyCreate. They remain on a
/// revoked proxy because revocation changes what invocation does, not whether
/// the value has the corresponding internal method.
#[derive(Clone, Debug)]
pub(crate) struct ProxyRecord {
    state: ProxyState,
    callable: bool,
    constructable: bool,
}

impl ProxyRecord {
    pub(crate) fn is_callable(&self) -> bool {
        self.callable
    }

    pub(crate) fn is_constructor(&self) -> bool {
        self.constructable
    }

    /// The target of a live proxy; a revoked proxy has none.
    pub(crate) fn live_target(&self) -> Option<Value> {
        match self.state {
            ProxyState::Live { target, .. } => Some(target),
            ProxyState::Revoked => None,
        }
    }

    pub(crate) fn for_each_value(&self, mut visit: impl FnMut(Value)) {
        if let ProxyState::Live { target, handler } = &self.state {
            visit(*target);
            visit(*handler);
        }
    }

    fn live(&self) -> Result<(Value, Value), EvalFailure> {
        match &self.state {
            ProxyState::Live { target, handler } => Ok((*target, *handler)),
            ProxyState::Revoked => Err(type_error("operation on revoked Proxy")),
        }
    }

    fn revoke(&mut self) {
        self.state = ProxyState::Revoked;
    }
}
/// Per-revoker state. `take` makes revocation idempotent and releases the
/// revoker's GC edge before any user-observable operation can re-enter.
#[derive(Clone, Debug)]
pub(crate) struct ProxyRevokerRecord {
    proxy: Option<Value>,
}

impl ProxyRevokerRecord {
    pub(crate) fn for_each_value(&self, mut visit: impl FnMut(Value)) {
        if let Some(proxy) = self.proxy {
            visit(proxy);
        }
    }
}

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut std::collections::BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let constructor = install_function(heap, builtins, "Proxy", 2, constructor::<H>);
    let revocable = install_function(heap, builtins, "revocable", 2, revocable::<H>);
    define_data(heap, constructor, "revocable", revocable);
    globals.insert(EcmaString::encode("Proxy"), constructor);
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !constructing {
        return Err(type_error("Proxy constructor requires new"));
    }
    Ok(BuiltinOutcome::Value(create(
        machine,
        args.first().copied().unwrap_or(Value::UNDEFINED),
        args.get(1).copied().unwrap_or(Value::UNDEFINED),
    )?))
}

fn revocable<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(type_error("Proxy.revocable is not a constructor"));
    }
    let proxy = create(
        machine,
        args.first().copied().unwrap_or(Value::UNDEFINED),
        args.get(1).copied().unwrap_or(Value::UNDEFINED),
    )?;
    let revoker = proxy_revoker(machine, proxy)?;
    let result = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)?;
    for (name, value) in [("proxy", proxy), ("revoke", revoker)] {
        machine.define_descriptor(
            result,
            PropertyKey::Named(EcmaString::encode(name)),
            Property::Data {
                value,
                writable: true,
                enumerable: true,
                configurable: true,
            },
        )?;
    }
    Ok(BuiltinOutcome::Value(result))
}

fn proxy_revoker<H: Host>(
    machine: &mut Machine<'_, H>,
    proxy: Value,
) -> Result<Value, EvalFailure> {
    let name = allocate_string(machine, EcmaString::default())?;
    let mut properties = PropertyMap::default();
    properties.insert(
        PropertyKey::Named(EcmaString::encode("length")),
        Property::Data {
            value: Value::int32(0),
            writable: false,
            enumerable: false,
            configurable: true,
        },
    );
    properties.insert(
        PropertyKey::Named(EcmaString::encode("name")),
        Property::Data {
            value: name,
            writable: false,
            enumerable: false,
            configurable: true,
        },
    );
    machine
        .allocate(HeapEntry::ProxyRevoker {
            record: ProxyRevokerRecord { proxy: Some(proxy) },
            properties,
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)
}

pub(crate) fn call_revoker<H: Host>(
    machine: &mut Machine<'_, H>,
    revoker: Value,
) -> Result<Value, EvalFailure> {
    let Some(revoker_index) = machine
        .runtime_slot(revoker)
        .map_err(EvalFailure::Runtime)?
    else {
        return Err(type_error("Proxy revoker receiver is invalid"));
    };
    let proxy = {
        let HeapEntry::ProxyRevoker { record, .. } = &mut machine.heap[revoker_index] else {
            return Err(type_error("Proxy revoker receiver is invalid"));
        };
        record.proxy.take()
    };
    let Some(proxy) = proxy else {
        return Ok(Value::UNDEFINED);
    };
    let Some(proxy_index) = machine.runtime_slot(proxy).map_err(EvalFailure::Runtime)? else {
        return Ok(Value::UNDEFINED);
    };
    if let HeapEntry::Proxy { record } = &mut machine.heap[proxy_index] {
        record.revoke();
    }
    Ok(Value::UNDEFINED)
}

/// ECMA-262 ProxyCreate.
/// https://tc39.es/ecma262/#sec-proxycreate
pub(crate) fn create<H: Host>(
    machine: &mut Machine<'_, H>,
    target: Value,
    handler: Value,
) -> Result<Value, EvalFailure> {
    if !machine.is_object(target) {
        return Err(type_error("Proxy target must be an object"));
    }
    if !machine.is_object(handler) {
        return Err(type_error("Proxy handler must be an object"));
    }
    let callable = machine.is_callable(target)?;
    let constructable = machine.is_constructor(target)?;
    machine
        .allocate(HeapEntry::Proxy {
            record: ProxyRecord {
                state: ProxyState::Live { target, handler },
                callable,
                constructable,
            },
        })
        .map_err(EvalFailure::Runtime)
}

fn record<H: Host>(machine: &Machine<'_, H>, proxy: Value) -> Result<ProxyRecord, EvalFailure> {
    let Some(index) = machine.runtime_slot(proxy).map_err(EvalFailure::Runtime)? else {
        return Err(type_error("Proxy internal method receiver is not a Proxy"));
    };
    match &machine.heap[index] {
        HeapEntry::Proxy { record } => Ok(record.clone()),
        _ => Err(type_error("Proxy internal method receiver is not a Proxy")),
    }
}

fn live<H: Host>(machine: &Machine<'_, H>, proxy: Value) -> Result<(Value, Value), EvalFailure> {
    record(machine, proxy)?.live()
}

fn get_method<H: Host>(
    machine: &mut Machine<'_, H>,
    handler: Value,
    name: &'static str,
) -> Result<Option<Value>, EvalFailure> {
    let key = PropertyKey::Named(EcmaString::encode(name));
    let method = machine.internal_get(handler, &key, handler)?;
    if matches!(method.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        return Ok(None);
    }
    if !machine.is_callable(method)? {
        return Err(type_error("Proxy handler trap is not callable"));
    }
    Ok(Some(method))
}

fn key_value<H: Host>(
    machine: &mut Machine<'_, H>,
    key: &PropertyKey,
) -> Result<Value, EvalFailure> {
    match key {
        PropertyKey::Named(name) => allocate_string(machine, name.clone()),
        PropertyKey::Symbol(index) | PropertyKey::Private(index) => Ok(Value::heap_ref(
            SlotId::from_parts(RUNTIME_HEAP_SEGMENT, index + 1)
                .expect("property-key heap slots are nonzero"),
        )),
    }
}

fn proxy_key<H: Host>(machine: &Machine<'_, H>, value: Value) -> Result<PropertyKey, EvalFailure> {
    let Some(index) = machine.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
        return Err(type_error("Proxy ownKeys trap returned a non-property key"));
    };
    match &machine.heap[index] {
        HeapEntry::String(name) => Ok(PropertyKey::Named(name.clone())),
        HeapEntry::Symbol { .. } => Ok(PropertyKey::Symbol(index as u32)),
        _ => Err(type_error("Proxy ownKeys trap returned a non-property key")),
    }
}

fn trap_property_key_list<H: Host>(
    machine: &mut Machine<'_, H>,
    source: Value,
) -> Result<Vec<PropertyKey>, EvalFailure> {
    if !machine.is_object(source) {
        return Err(type_error("Proxy ownKeys trap result is not an object"));
    }
    let length_key = PropertyKey::Named(EcmaString::encode("length"));
    let length_value = machine.internal_get(source, &length_key, source)?;
    let length = to_integer_or_infinity(machine, length_value)?.clamp(0.0, 9_007_199_254_740_991.0);
    if length > f64::from(machine.limits.max_argument_count) {
        return Err(crate::EvalFailure::Runtime(
            crate::RuntimeErrorKind::ArgumentLimitExceeded {
                limit: machine.limits.max_argument_count,
                requested: length.min(f64::from(u32::MAX)) as u32,
            },
        ));
    }
    let mut keys = Vec::with_capacity(length as usize);
    let mut seen = BTreeSet::new();
    for index in 0..length as usize {
        let index_key = PropertyKey::Named(EcmaString::encode(&index.to_string()));
        let value = machine.internal_get(source, &index_key, source)?;
        let key = proxy_key(machine, value)?;
        if !seen.insert(key.clone()) {
            return Err(type_error("Proxy ownKeys trap returned duplicate keys"));
        }
        keys.push(key);
    }
    Ok(keys)
}

pub(crate) fn get_prototype_of<H: Host>(
    machine: &mut Machine<'_, H>,
    proxy: Value,
) -> Result<Option<Value>, EvalFailure> {
    let (target, handler) = live(machine, proxy)?;
    let Some(trap) = get_method(machine, handler, "getPrototypeOf")? else {
        return machine.internal_get_prototype_of(target);
    };
    let result = machine.call_value(trap, handler, &[target])?;
    let result = if matches!(result.decode(), Some(Decoded::Null)) {
        None
    } else if machine.is_object(result) {
        Some(result)
    } else {
        return Err(type_error(
            "Proxy getPrototypeOf trap returned invalid prototype",
        ));
    };
    if machine.internal_is_extensible(target)? {
        return Ok(result);
    }
    if machine.internal_get_prototype_of(target)? != result {
        return Err(type_error("Proxy getPrototypeOf violated target invariant"));
    }
    Ok(result)
}

pub(crate) fn set_prototype_of<H: Host>(
    machine: &mut Machine<'_, H>,
    proxy: Value,
    prototype: Option<Value>,
) -> Result<bool, EvalFailure> {
    let (target, handler) = live(machine, proxy)?;
    let Some(trap) = get_method(machine, handler, "setPrototypeOf")? else {
        return machine.internal_set_prototype_of(target, prototype);
    };
    let prototype_value = prototype.unwrap_or(Value::NULL);
    let result = machine.call_value(trap, handler, &[target, prototype_value])?;
    if !machine.to_boolean(result) {
        return Ok(false);
    }
    if !machine.internal_is_extensible(target)?
        && machine.internal_get_prototype_of(target)? != prototype
    {
        return Err(type_error("Proxy setPrototypeOf violated target invariant"));
    }
    Ok(true)
}

pub(crate) fn is_extensible<H: Host>(
    machine: &mut Machine<'_, H>,
    proxy: Value,
) -> Result<bool, EvalFailure> {
    let (target, handler) = live(machine, proxy)?;
    let Some(trap) = get_method(machine, handler, "isExtensible")? else {
        return machine.internal_is_extensible(target);
    };
    let trap_result = machine.call_value(trap, handler, &[target])?;
    let trap_result = machine.to_boolean(trap_result);
    if trap_result != machine.internal_is_extensible(target)? {
        return Err(type_error("Proxy isExtensible contradicted target"));
    }
    Ok(trap_result)
}

pub(crate) fn prevent_extensions<H: Host>(
    machine: &mut Machine<'_, H>,
    proxy: Value,
) -> Result<bool, EvalFailure> {
    let (target, handler) = live(machine, proxy)?;
    let Some(trap) = get_method(machine, handler, "preventExtensions")? else {
        return machine.internal_prevent_extensions(target);
    };
    let trap_result = machine.call_value(trap, handler, &[target])?;
    let trap_result = machine.to_boolean(trap_result);
    if trap_result && machine.internal_is_extensible(target)? {
        return Err(type_error("Proxy preventExtensions left target extensible"));
    }
    Ok(trap_result)
}

pub(crate) fn get_own_property<H: Host>(
    machine: &mut Machine<'_, H>,
    proxy: Value,
    key: &PropertyKey,
) -> Result<Option<PropertyDescriptor>, EvalFailure> {
    let (target, handler) = live(machine, proxy)?;
    let Some(trap) = get_method(machine, handler, "getOwnPropertyDescriptor")? else {
        return machine.internal_get_own_property(target, key);
    };
    let key_value = key_value(machine, key)?;
    let trap_result = machine.call_value(trap, handler, &[target, key_value])?;
    if trap_result != Value::UNDEFINED && !machine.is_object(trap_result) {
        return Err(type_error(
            "Proxy getOwnPropertyDescriptor trap returned invalid value",
        ));
    }
    let target_descriptor = machine.internal_get_own_property(target, key)?;
    if trap_result == Value::UNDEFINED {
        let Some(target_descriptor) = target_descriptor else {
            return Ok(None);
        };
        if target_descriptor.configurable == Some(false)
            || !machine.internal_is_extensible(target)?
        {
            return Err(type_error(
                "Proxy getOwnPropertyDescriptor hid a fixed property",
            ));
        }
        return Ok(None);
    }
    let extensible = machine.internal_is_extensible(target)?;
    let result_descriptor =
        complete_property_descriptor(to_property_descriptor(machine, trap_result)?);
    if !is_compatible_property_descriptor(
        machine,
        extensible,
        result_descriptor,
        target_descriptor.as_ref(),
    ) {
        return Err(type_error(
            "Proxy getOwnPropertyDescriptor returned incompatible descriptor",
        ));
    }
    if result_descriptor.configurable == Some(false) {
        let Some(target_descriptor) = target_descriptor.as_ref() else {
            return Err(type_error("Proxy reported a new non-configurable property"));
        };
        if target_descriptor.configurable == Some(true) {
            return Err(type_error("Proxy reported a new non-configurable property"));
        }
        if result_descriptor.writable == Some(false) && target_descriptor.writable == Some(true) {
            return Err(type_error(
                "Proxy reported non-writable for writable non-configurable property",
            ));
        }
    }
    Ok(Some(result_descriptor))
}

pub(crate) fn define_own_property<H: Host>(
    machine: &mut Machine<'_, H>,
    proxy: Value,
    key: PropertyKey,
    descriptor: PropertyDescriptor,
) -> Result<bool, EvalFailure> {
    let (target, handler) = live(machine, proxy)?;
    let Some(trap) = get_method(machine, handler, "defineProperty")? else {
        return machine.internal_define_own_property(target, key, descriptor);
    };
    let key_value = key_value(machine, &key)?;
    let descriptor_object = from_property_descriptor(machine, Some(descriptor))?;
    let trap_result = machine.call_value(trap, handler, &[target, key_value, descriptor_object])?;
    let trap_result = machine.to_boolean(trap_result);
    if !trap_result {
        return Ok(false);
    }
    let target_descriptor = machine.internal_get_own_property(target, &key)?;
    let extensible = machine.internal_is_extensible(target)?;
    let setting_config_false = descriptor.configurable == Some(false);
    match target_descriptor.as_ref() {
        None if !extensible => {
            return Err(type_error(
                "Proxy defineProperty added property to fixed target",
            ));
        }
        None if setting_config_false => {
            return Err(type_error(
                "Proxy defineProperty invented non-configurable property",
            ));
        }
        Some(current)
            if !is_compatible_property_descriptor(
                machine,
                extensible,
                descriptor,
                Some(current),
            ) =>
        {
            return Err(type_error(
                "Proxy defineProperty accepted incompatible descriptor",
            ));
        }
        Some(current) if setting_config_false && current.configurable == Some(true) => {
            return Err(type_error(
                "Proxy defineProperty fixed configurable target property",
            ));
        }
        Some(current)
            if current.configurable == Some(false)
                && current.writable == Some(true)
                && descriptor.writable == Some(false) =>
        {
            return Err(type_error(
                "Proxy defineProperty reported writable property as non-writable",
            ));
        }
        _ => {}
    }
    Ok(true)
}

pub(crate) fn has_property<H: Host>(
    machine: &mut Machine<'_, H>,
    proxy: Value,
    key: &PropertyKey,
) -> Result<bool, EvalFailure> {
    let (target, handler) = live(machine, proxy)?;
    let Some(trap) = get_method(machine, handler, "has")? else {
        return machine.internal_has_property(target, key);
    };
    let key_value = key_value(machine, key)?;
    let trap_result = machine.call_value(trap, handler, &[target, key_value])?;
    let trap_result = machine.to_boolean(trap_result);
    if trap_result {
        return Ok(true);
    }
    if let Some(target_descriptor) = machine.internal_get_own_property(target, key)?
        && (target_descriptor.configurable == Some(false)
            || !machine.internal_is_extensible(target)?)
    {
        return Err(type_error("Proxy has trap hid a fixed property"));
    }
    Ok(false)
}

pub(crate) fn get<H: Host>(
    machine: &mut Machine<'_, H>,
    proxy: Value,
    key: &PropertyKey,
    receiver: Value,
) -> Result<Value, EvalFailure> {
    let (target, handler) = live(machine, proxy)?;
    let Some(trap) = get_method(machine, handler, "get")? else {
        return machine.internal_get(target, key, receiver);
    };
    let key_value = key_value(machine, key)?;
    let trap_result = machine.call_value(trap, handler, &[target, key_value, receiver])?;
    if let Some(target_descriptor) = machine.internal_get_own_property(target, key)? {
        if target_descriptor.configurable == Some(false)
            && target_descriptor.writable == Some(false)
            && !is_compatible_property_descriptor(
                machine,
                true,
                PropertyDescriptor {
                    value: Some(trap_result),
                    ..PropertyDescriptor::default()
                },
                Some(&target_descriptor),
            )
        {
            return Err(type_error(
                "Proxy get trap changed frozen data property value",
            ));
        }
        if target_descriptor.configurable == Some(false)
            && target_descriptor.is_accessor()
            && target_descriptor.getter == Some(Value::UNDEFINED)
            && trap_result != Value::UNDEFINED
        {
            return Err(type_error(
                "Proxy get trap supplied value for getterless property",
            ));
        }
    }
    Ok(trap_result)
}

pub(crate) fn set<H: Host>(
    machine: &mut Machine<'_, H>,
    proxy: Value,
    key: PropertyKey,
    value: Value,
    receiver: Value,
) -> Result<bool, EvalFailure> {
    let (target, handler) = live(machine, proxy)?;
    let Some(trap) = get_method(machine, handler, "set")? else {
        return machine.internal_set(target, key, value, receiver);
    };
    let key_value = key_value(machine, &key)?;
    let trap_result = machine.call_value(trap, handler, &[target, key_value, value, receiver])?;
    let trap_result = machine.to_boolean(trap_result);
    if !trap_result {
        return Ok(false);
    }
    if let Some(target_descriptor) = machine.internal_get_own_property(target, &key)?
        && target_descriptor.configurable == Some(false)
    {
        if target_descriptor.writable == Some(false)
            && !is_compatible_property_descriptor(
                machine,
                true,
                PropertyDescriptor {
                    value: Some(value),
                    ..PropertyDescriptor::default()
                },
                Some(&target_descriptor),
            )
        {
            return Err(type_error(
                "Proxy set trap changed frozen data property value",
            ));
        }
        if target_descriptor.is_accessor() && target_descriptor.setter == Some(Value::UNDEFINED) {
            return Err(type_error("Proxy set trap accepted setterless property"));
        }
    }
    Ok(true)
}

pub(crate) fn delete<H: Host>(
    machine: &mut Machine<'_, H>,
    proxy: Value,
    key: &PropertyKey,
) -> Result<bool, EvalFailure> {
    let (target, handler) = live(machine, proxy)?;
    let Some(trap) = get_method(machine, handler, "deleteProperty")? else {
        return machine.internal_delete(target, key);
    };
    let key_value = key_value(machine, key)?;
    let trap_result = machine.call_value(trap, handler, &[target, key_value])?;
    let trap_result = machine.to_boolean(trap_result);
    if !trap_result {
        return Ok(false);
    }
    if let Some(target_descriptor) = machine.internal_get_own_property(target, key)?
        && (target_descriptor.configurable == Some(false)
            || !machine.internal_is_extensible(target)?)
    {
        return Err(type_error("Proxy deleteProperty trap hid a fixed property"));
    }
    Ok(true)
}

pub(crate) fn own_property_keys<H: Host>(
    machine: &mut Machine<'_, H>,
    proxy: Value,
) -> Result<Vec<PropertyKey>, EvalFailure> {
    let (target, handler) = live(machine, proxy)?;
    let Some(trap) = get_method(machine, handler, "ownKeys")? else {
        return machine.internal_own_property_keys(target);
    };
    let trap_result = machine.call_value(trap, handler, &[target])?;
    let trap_keys = trap_property_key_list(machine, trap_result)?;
    let extensible = machine.internal_is_extensible(target)?;
    let target_keys = machine.internal_own_property_keys(target)?;

    let trap_set: BTreeSet<_> = trap_keys.iter().cloned().collect();
    for key in &target_keys {
        let descriptor = machine.internal_get_own_property(target, key)?;
        if descriptor
            .as_ref()
            .is_some_and(|descriptor| descriptor.configurable == Some(false))
            && !trap_set.contains(key)
        {
            return Err(type_error(
                "Proxy ownKeys omitted non-configurable property",
            ));
        }
    }
    if !extensible {
        let target_set: BTreeSet<_> = target_keys.into_iter().collect();
        if trap_set != target_set {
            return Err(type_error("Proxy ownKeys disagreed with fixed target keys"));
        }
    }
    Ok(trap_keys)
}

pub(crate) fn call<H: Host>(
    machine: &mut Machine<'_, H>,
    proxy: Value,
    this_argument: Value,
    arguments: &[Value],
) -> Result<Value, EvalFailure> {
    let proxy_record = record(machine, proxy)?;
    if !proxy_record.is_callable() {
        return Err(type_error("Proxy target is not callable"));
    }
    let (target, handler) = proxy_record.live()?;
    let Some(trap) = get_method(machine, handler, "apply")? else {
        return machine.call_value(target, this_argument, arguments);
    };
    let argument_array = allocate_array(machine, arguments.to_vec())?;
    machine.call_value(trap, handler, &[target, this_argument, argument_array])
}

pub(crate) fn construct<H: Host>(
    machine: &mut Machine<'_, H>,
    proxy: Value,
    arguments: &[Value],
    new_target: Value,
) -> Result<Value, EvalFailure> {
    let proxy_record = record(machine, proxy)?;
    if !proxy_record.is_constructor() {
        return Err(type_error("Proxy target is not a constructor"));
    }
    let (target, handler) = proxy_record.live()?;
    let Some(trap) = get_method(machine, handler, "construct")? else {
        return machine.internal_construct(target, arguments, new_target);
    };
    let argument_array = allocate_array(machine, arguments.to_vec())?;
    let result = machine.call_value(trap, handler, &[target, argument_array, new_target])?;
    if !machine.is_object(result) {
        return Err(type_error("Proxy construct trap returned a non-object"));
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtins::test_support::{TestHost, blank_program, ordinary_object};
    use crate::intrinsics::{BuiltinDef, BuiltinHandler, native_function};
    use crate::{Limits, ThrowOrigin};

    fn with_machine(test: impl FnOnce(&mut Machine<'_, TestHost>)) {
        let program = blank_program("<proxy-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        test(&mut machine);
    }

    fn native(
        machine: &mut Machine<'_, TestHost>,
        name: &'static str,
        length: u32,
        handler: BuiltinHandler<TestHost>,
    ) -> Value {
        let id = machine
            .intrinsics
            .builtins
            .register_constructor(BuiltinDef {
                name,
                length,
                handler,
            });
        native_function(&mut machine.heap, id, name, length)
    }

    fn key(name: &str) -> PropertyKey {
        PropertyKey::Named(EcmaString::encode(name))
    }

    fn is_type_error<T>(result: Result<T, EvalFailure>) -> bool {
        matches!(
            result,
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        )
    }

    fn return_two(
        _: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(Value::int32(2)))
    }

    fn return_true(
        _: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(Value::TRUE))
    }

    fn return_result(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(
            machine.get_named_property(this, "result")?,
        ))
    }

    fn abrupt(
        _: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(type_error("abrupt Proxy trap getter"))
    }

    fn receiver_get(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        args: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "seenReceiver", args[2])?;
        Ok(BuiltinOutcome::Value(Value::int32(9)))
    }

    fn receiver_set(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        args: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "seenReceiver", args[3])?;
        Ok(BuiltinOutcome::Value(Value::TRUE))
    }

    fn apply_trap(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        args: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "seenThis", args[1])?;
        machine.set_data_property(this, "seenArgs", args[2])?;
        Ok(BuiltinOutcome::Value(Value::int32(77)))
    }

    fn construct_trap(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        args: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "seenArgs", args[1])?;
        machine.set_data_property(this, "seenNewTarget", args[2])?;
        Ok(BuiltinOutcome::Value(
            machine.get_named_property(this, "result")?,
        ))
    }

    fn inert_callable(
        _: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    #[test]
    fn constructor_is_new_only_and_revokers_are_independent() {
        with_machine(|machine| {
            let constructor = machine.intrinsics.global("Proxy").unwrap();
            let target_a = ordinary_object(machine);
            let target_b = ordinary_object(machine);
            let handler_a = ordinary_object(machine);
            let handler_b = ordinary_object(machine);
            assert!(is_type_error(machine.call_value(
                constructor,
                Value::UNDEFINED,
                &[target_a, handler_a],
            )));
            let constructed = machine
                .construct_value(constructor, &[target_a, handler_a])
                .unwrap();
            assert!(machine.is_object(constructed));

            let revocable = machine
                .get_named_property(constructor, "revocable")
                .unwrap();
            let result_a = machine
                .call_value(revocable, constructor, &[target_a, handler_a])
                .unwrap();
            let result_b = machine
                .call_value(revocable, constructor, &[target_b, handler_b])
                .unwrap();
            let proxy_a = machine.get_named_property(result_a, "proxy").unwrap();
            let proxy_b = machine.get_named_property(result_b, "proxy").unwrap();
            let revoker_a = machine.get_named_property(result_a, "revoke").unwrap();
            let revoker_b = machine.get_named_property(result_b, "revoke").unwrap();
            assert_eq!(
                machine
                    .call_value(revoker_a, Value::UNDEFINED, &[])
                    .unwrap(),
                Value::UNDEFINED
            );
            assert_eq!(
                machine
                    .call_value(revoker_a, Value::UNDEFINED, &[])
                    .unwrap(),
                Value::UNDEFINED
            );
            assert!(is_type_error(get(machine, proxy_a, &key("x"), proxy_a,)));
            assert_eq!(
                get(machine, proxy_b, &key("x"), proxy_b).unwrap(),
                Value::UNDEFINED
            );
            assert_eq!(
                machine
                    .call_value(revoker_b, Value::UNDEFINED, &[])
                    .unwrap(),
                Value::UNDEFINED
            );
            assert!(is_type_error(get(machine, proxy_b, &key("x"), proxy_b,)));
        });
    }

    #[test]
    fn every_internal_method_rejects_revoked_proxy() {
        with_machine(|machine| {
            let target = native(machine, "target", 0, inert_callable);
            let handler = ordinary_object(machine);
            let proxy = create(machine, target, handler).unwrap();
            let revoker = proxy_revoker(machine, proxy).unwrap();
            call_revoker(machine, revoker).unwrap();
            let x = key("x");
            let descriptor = PropertyDescriptor::default();

            assert!(is_type_error(get_prototype_of(machine, proxy)));
            assert!(is_type_error(set_prototype_of(machine, proxy, None)));
            assert!(is_type_error(is_extensible(machine, proxy)));
            assert!(is_type_error(prevent_extensions(machine, proxy)));
            assert!(is_type_error(get_own_property(machine, proxy, &x)));
            assert!(is_type_error(define_own_property(
                machine,
                proxy,
                x.clone(),
                descriptor
            )));
            assert!(is_type_error(has_property(machine, proxy, &x)));
            assert!(is_type_error(get(machine, proxy, &x, proxy)));
            assert!(is_type_error(set(
                machine,
                proxy,
                x.clone(),
                Value::int32(1),
                proxy
            )));
            assert!(is_type_error(delete(machine, proxy, &x)));
            assert!(is_type_error(own_property_keys(machine, proxy)));
            assert!(is_type_error(call(machine, proxy, Value::UNDEFINED, &[])));
            assert!(is_type_error(construct(machine, proxy, &[], proxy)));
        });
    }

    #[test]
    fn frozen_data_and_setterless_invariants_are_enforced() {
        with_machine(|machine| {
            let target = ordinary_object(machine);
            machine
                .define_descriptor(
                    target,
                    key("x"),
                    Property::Data {
                        value: Value::int32(1),
                        writable: false,
                        enumerable: true,
                        configurable: false,
                    },
                )
                .unwrap();
            machine
                .define_descriptor(
                    target,
                    key("y"),
                    Property::Accessor {
                        getter: None,
                        setter: None,
                        enumerable: true,
                        configurable: false,
                    },
                )
                .unwrap();
            let handler = ordinary_object(machine);
            let get_trap = native(machine, "get trap", 3, return_two);
            let set_trap = native(machine, "set trap", 4, return_true);
            machine.set_data_property(handler, "get", get_trap).unwrap();
            machine.set_data_property(handler, "set", set_trap).unwrap();
            let proxy = create(machine, target, handler).unwrap();

            assert!(is_type_error(get(machine, proxy, &key("x"), proxy)));
            assert!(is_type_error(set(
                machine,
                proxy,
                key("x"),
                Value::int32(2),
                proxy,
            )));
            assert!(is_type_error(get(machine, proxy, &key("y"), proxy)));
            assert!(is_type_error(set(
                machine,
                proxy,
                key("y"),
                Value::int32(1),
                proxy,
            )));
        });
    }

    #[test]
    fn own_keys_rejects_duplicates_missing_fixed_and_extra_fixed_keys() {
        with_machine(|machine| {
            let target = ordinary_object(machine);
            machine
                .define_descriptor(
                    target,
                    key("fixed"),
                    Property::Data {
                        value: Value::int32(1),
                        writable: true,
                        enumerable: true,
                        configurable: false,
                    },
                )
                .unwrap();
            let handler = ordinary_object(machine);
            let trap = native(machine, "ownKeys trap", 1, return_result);
            machine.set_data_property(handler, "ownKeys", trap).unwrap();
            let proxy = create(machine, target, handler).unwrap();

            let fixed_a = allocate_string(machine, EcmaString::encode("fixed")).unwrap();
            let fixed_b = allocate_string(machine, EcmaString::encode("fixed")).unwrap();
            let duplicate = allocate_array(machine, vec![fixed_a, fixed_b]).unwrap();
            machine
                .set_data_property(handler, "result", duplicate)
                .unwrap();
            assert!(is_type_error(own_property_keys(machine, proxy)));

            let missing = allocate_array(machine, vec![]).unwrap();
            machine
                .set_data_property(handler, "result", missing)
                .unwrap();
            assert!(is_type_error(own_property_keys(machine, proxy)));

            machine.internal_prevent_extensions(target).unwrap();
            let fixed = allocate_string(machine, EcmaString::encode("fixed")).unwrap();
            let extra = allocate_string(machine, EcmaString::encode("extra")).unwrap();
            let extra_result = allocate_array(machine, vec![fixed, extra]).unwrap();
            machine
                .set_data_property(handler, "result", extra_result)
                .unwrap();
            assert!(is_type_error(own_property_keys(machine, proxy)));
        });
    }

    #[test]
    fn get_and_set_forward_the_original_receiver() {
        with_machine(|machine| {
            let target = ordinary_object(machine);
            let handler = ordinary_object(machine);
            let get_trap = native(machine, "receiver get", 3, receiver_get);
            let set_trap = native(machine, "receiver set", 4, receiver_set);
            machine.set_data_property(handler, "get", get_trap).unwrap();
            machine.set_data_property(handler, "set", set_trap).unwrap();
            let proxy = create(machine, target, handler).unwrap();
            let receiver = ordinary_object(machine);

            assert_eq!(
                get(machine, proxy, &key("x"), receiver).unwrap(),
                Value::int32(9)
            );
            assert_eq!(
                machine.get_named_property(handler, "seenReceiver").unwrap(),
                receiver
            );
            assert!(set(machine, proxy, key("x"), Value::int32(4), receiver).unwrap());
            assert_eq!(
                machine.get_named_property(handler, "seenReceiver").unwrap(),
                receiver
            );
        });
    }

    #[test]
    fn apply_and_construct_preserve_argument_and_new_target_identity() {
        with_machine(|machine| {
            let target = native(machine, "callable target", 0, inert_callable);
            let handler = ordinary_object(machine);
            let apply = native(machine, "apply trap", 3, apply_trap);
            let construct_method = native(machine, "construct trap", 3, construct_trap);
            let result_object = ordinary_object(machine);
            machine.set_data_property(handler, "apply", apply).unwrap();
            machine
                .set_data_property(handler, "construct", construct_method)
                .unwrap();
            machine
                .set_data_property(handler, "result", result_object)
                .unwrap();
            let proxy = create(machine, target, handler).unwrap();
            let this_argument = ordinary_object(machine);

            assert_eq!(
                call(machine, proxy, this_argument, &[Value::int32(3)]).unwrap(),
                Value::int32(77)
            );
            assert_eq!(
                machine.get_named_property(handler, "seenThis").unwrap(),
                this_argument
            );
            let apply_args = machine.get_named_property(handler, "seenArgs").unwrap();
            assert_eq!(
                machine.array_elements(apply_args).unwrap().unwrap(),
                vec![Value::int32(3)]
            );

            assert_eq!(
                construct(machine, proxy, &[Value::int32(5)], target).unwrap(),
                result_object
            );
            assert_eq!(
                machine
                    .get_named_property(handler, "seenNewTarget")
                    .unwrap(),
                target
            );
            let construct_args = machine.get_named_property(handler, "seenArgs").unwrap();
            assert_eq!(
                machine.array_elements(construct_args).unwrap().unwrap(),
                vec![Value::int32(5)]
            );
        });
    }

    #[test]
    fn abrupt_trap_getter_propagates_before_target_observation() {
        with_machine(|machine| {
            let target = ordinary_object(machine);
            let handler = ordinary_object(machine);
            let getter = native(machine, "abrupt getter", 0, abrupt);
            machine
                .define_descriptor(
                    handler,
                    key("get"),
                    Property::Accessor {
                        getter: Some(getter),
                        setter: None,
                        enumerable: true,
                        configurable: true,
                    },
                )
                .unwrap();
            let proxy = create(machine, target, handler).unwrap();
            assert!(matches!(
                get(machine, proxy, &key("x"), proxy),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "abrupt Proxy trap getter"
                }))
            ));
        });
    }
}
