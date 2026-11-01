use super::{
    arraybuffer::{ArrayBufferHandle, SharedBlock},
    type_error,
};
use crate::{
    CollectionIndex, CollectionKind, EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey,
    PropertyMap, intrinsics::BuiltinOutcome,
};
use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, Value};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    sync::Arc,
};
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DataCloneError {
    Callable,
    Symbol,
    WeakReference,
    HostObject,
    DetachedArrayBuffer,
    DuplicateTransfer,
    NonTransferable,
    ArrayBufferDetachKey,
    UnsupportedBinaryView,
}
impl DataCloneError {
    fn operation(self) -> &'static str {
        match self {
            Self::Callable => "DataCloneError: callable value",
            Self::Symbol => "DataCloneError: symbol value",
            Self::WeakReference => "DataCloneError: weak reference",
            Self::HostObject => "DataCloneError: host or runtime exotic object",
            Self::DetachedArrayBuffer => "DataCloneError: detached ArrayBuffer",
            Self::DuplicateTransfer => "DataCloneError: duplicate transferable",
            Self::NonTransferable => "DataCloneError: value is not transferable",
            Self::ArrayBufferDetachKey => "DataCloneError: ArrayBuffer has a detach key",
            Self::UnsupportedBinaryView => "DataCloneError: unsupported binary view",
        }
    }
    fn into_eval_failure(self) -> EvalFailure {
        type_error(self.operation())
    }
}
#[derive(Debug)]
pub(crate) enum StructuredCloneFailure {
    DataClone(DataCloneError),
    Evaluation(EvalFailure),
}
impl From<DataCloneError> for StructuredCloneFailure {
    fn from(error: DataCloneError) -> Self {
        Self::DataClone(error)
    }
}
impl From<EvalFailure> for StructuredCloneFailure {
    fn from(error: EvalFailure) -> Self {
        Self::Evaluation(error)
    }
}
#[derive(Clone, Copy, Debug)]
enum EncodedValue {
    Immediate(Value),
    Node(usize),
}
#[derive(Clone, Debug)]
struct PlannedProperty {
    key: PropertyKey,
    value: EncodedValue,
    writable: bool,
    enumerable: bool,
    configurable: bool,
}
#[derive(Clone, Debug)]
enum PlannedNode {
    Pending(Value),
    String(EcmaString),
    BigInt(String),
    Object {
        prototype: Option<Value>,
        boxed_primitive: Option<EncodedValue>,
        properties: Vec<PlannedProperty>,
    },
    Array {
        length: usize,
        elements: Vec<(usize, EncodedValue)>,
        properties: Vec<PlannedProperty>,
    },
    Date {
        time: f64,
        properties: Vec<PlannedProperty>,
    },
    RegExp {
        pattern: EcmaString,
        flags: EcmaString,
        source: EncodedValue,
        canonical_flags: EncodedValue,
        properties: Vec<PlannedProperty>,
    },
    Map {
        entries: Vec<(EncodedValue, EncodedValue)>,
        properties: Vec<PlannedProperty>,
        prototype: Option<Value>,
    },
    Set {
        values: Vec<EncodedValue>,
        properties: Vec<PlannedProperty>,
        prototype: Option<Value>,
    },
    ArrayBuffer {
        bytes: Vec<u8>,
        max_byte_length: Option<usize>,
        properties: Vec<PlannedProperty>,
    },
    SharedArrayBuffer {
        data: Arc<SharedBlock>,
        properties: Vec<PlannedProperty>,
        prototype: Option<Value>,
    },
}
struct ClonePlan {
    root: EncodedValue,
    nodes: Vec<PlannedNode>,
    source_to_node: BTreeMap<usize, usize>,
    pending: VecDeque<usize>,
    transfers: Vec<ArrayBufferHandle>,
}
impl ClonePlan {
    fn new(transfers: Vec<ArrayBufferHandle>) -> Self {
        Self {
            root: EncodedValue::Immediate(Value::UNDEFINED),
            nodes: Vec::new(),
            source_to_node: BTreeMap::new(),
            pending: VecDeque::new(),
            transfers,
        }
    }
    fn encode<H: Host>(
        &mut self,
        machine: &Machine<'_, H>,
        value: Value,
    ) -> Result<EncodedValue, StructuredCloneFailure> {
        let Some(Decoded::HeapRef(_)) = value.decode() else {
            return Ok(EncodedValue::Immediate(value));
        };
        let Some(source_slot) = machine.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
            return Err(DataCloneError::HostObject.into());
        };
        if let Some(node) = self.source_to_node.get(&source_slot) {
            return Ok(EncodedValue::Node(*node));
        }
        let node = self.nodes.len();
        self.source_to_node.insert(source_slot, node);
        self.nodes.push(PlannedNode::Pending(value));
        self.pending.push_back(node);
        Ok(EncodedValue::Node(node))
    }
}
#[derive(Clone, Copy)]
struct HeapCheckpoint {
    heap_len: usize,
    slot_bytes_len: usize,
    heap_bytes: usize,
    vacant_count: usize,
}
impl HeapCheckpoint {
    fn capture<H: Host>(machine: &Machine<'_, H>) -> Self {
        Self {
            heap_len: machine.heap.len(),
            slot_bytes_len: machine.slot_bytes.len(),
            heap_bytes: machine.heap_bytes,
            vacant_count: machine.vacant_count,
        }
    }
    fn rollback<H: Host>(self, machine: &mut Machine<'_, H>) {
        machine.heap.truncate(self.heap_len);
        machine.slot_bytes.truncate(self.slot_bytes_len);
        machine.heap_bytes = self.heap_bytes;
        machine.vacant_count = self.vacant_count;
    }
}
pub(crate) fn clone_value_with_transfer<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    transfer: &[Value],
) -> Result<Value, StructuredCloneFailure> {
    let transfers = validate_transfers(machine, transfer)?;
    let mut plan = ClonePlan::new(transfers);
    plan.root = plan.encode(machine, value)?;
    build_plan(machine, &mut plan)?;
    let checkpoint = HeapCheckpoint::capture(machine);
    match materialize(machine, &plan) {
        Ok(result) => {
            for transfer in &plan.transfers {
                transfer.detach(machine, Value::UNDEFINED)?;
            }
            Ok(result)
        }
        Err(error) => {
            checkpoint.rollback(machine);
            Err(error)
        }
    }
}
/// Builtin entry point for the global `structuredClone` function.
pub(super) fn structured_clone<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = args.first().copied().unwrap_or(Value::UNDEFINED);
    let transfer = transfer_argument(machine, args.get(1).copied())?;
    clone_value_with_transfer(machine, value, &transfer)
        .map(BuiltinOutcome::Value)
        .map_err(|failure| match failure {
            StructuredCloneFailure::DataClone(error) => error.into_eval_failure(),
            StructuredCloneFailure::Evaluation(error) => error,
        })
}
fn transfer_argument<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Option<Value>,
) -> Result<Vec<Value>, EvalFailure> {
    let Some(options) =
        options.filter(|value| !matches!(value.decode(), Some(Decoded::Undefined | Decoded::Null)))
    else {
        return Ok(Vec::new());
    };
    if !machine.is_object(options) {
        return Err(type_error("structuredClone options must be an object"));
    }
    let transfer = machine.get_named_property(options, "transfer")?;
    if transfer == Value::UNDEFINED {
        return Ok(Vec::new());
    }
    machine.iterable_values(transfer)
}
fn validate_transfers<H: Host>(
    machine: &Machine<'_, H>,
    transfer: &[Value],
) -> Result<Vec<ArrayBufferHandle>, StructuredCloneFailure> {
    let mut slots = BTreeSet::new();
    let mut handles = Vec::with_capacity(transfer.len());
    for value in transfer {
        let Some(slot) = machine.runtime_slot(*value).map_err(EvalFailure::Runtime)? else {
            return Err(DataCloneError::NonTransferable.into());
        };
        if !slots.insert(slot) {
            return Err(DataCloneError::DuplicateTransfer.into());
        }
        let handle = ArrayBufferHandle::from_value(machine, *value)
            .map_err(|_| DataCloneError::NonTransferable)?;
        if handle.is_detached(machine) {
            return Err(DataCloneError::DetachedArrayBuffer.into());
        }
        let HeapEntry::ArrayBuffer { data, .. } = &machine.heap[slot] else {
            unreachable!("ArrayBufferHandle validated the transfer brand")
        };
        if data.detach_key() != Value::UNDEFINED {
            return Err(DataCloneError::ArrayBufferDetachKey.into());
        }
        handles.push(handle);
    }
    Ok(handles)
}
fn build_plan<H: Host>(
    machine: &mut Machine<'_, H>,
    plan: &mut ClonePlan,
) -> Result<(), StructuredCloneFailure> {
    while let Some(node_id) = plan.pending.pop_front() {
        let PlannedNode::Pending(source) = plan.nodes[node_id] else {
            unreachable!("only pending nodes enter the graph worklist")
        };
        let source_slot = machine
            .runtime_slot(source)
            .map_err(EvalFailure::Runtime)?
            .expect("planned heap value remains a runtime slot");
        let entry = machine.heap[source_slot].clone();
        let node = match entry {
            HeapEntry::String(text) => PlannedNode::String(text),
            HeapEntry::BigInt(text) => PlannedNode::BigInt(text),
            HeapEntry::Object {
                properties,
                prototype,
                boxed_primitive,
                ..
            } => {
                let error_prototype = prototype.filter(|candidate| {
                    machine
                        .intrinsics
                        .builtins
                        .error_prototypes
                        .iter()
                        .any(|(_, prototype)| prototype == candidate)
                });
                let mut planned = enumerable_properties(machine, plan, source)?;
                if error_prototype.is_some() {
                    append_error_state(machine, plan, source, &properties, &mut planned)?;
                }
                PlannedNode::Object {
                    prototype: error_prototype.or_else(|| {
                        boxed_primitive
                            .is_some()
                            .then_some(prototype)
                            .flatten()
                            .or(Some(machine.intrinsics.object_prototype))
                    }),
                    boxed_primitive: boxed_primitive
                        .map(|value| plan.encode(machine, value))
                        .transpose()?,
                    properties: planned,
                }
            }
            HeapEntry::Array { elements, .. } => {
                let mut element_values = Vec::new();
                let mut properties = Vec::new();
                for property in enumerable_properties(machine, plan, source)? {
                    let Some(name) = property.key.as_string() else {
                        continue;
                    };
                    if let Some(index) = crate::array_index(name) {
                        element_values.push((index as usize, property.value));
                    } else if !name.eq_ascii("length") {
                        properties.push(property);
                    }
                }
                PlannedNode::Array {
                    length: elements.len(),
                    elements: element_values,
                    properties,
                }
            }
            HeapEntry::Date { time, .. } => PlannedNode::Date {
                // Date is a typed carrier: only [[DateValue]] is cloned.
                time,
                properties: Vec::new(),
            },
            HeapEntry::RegExp {
                pattern,
                flags,
                properties,
                ..
            } => {
                let source_value = regexp_property(&properties, "source")?;
                let canonical_flags = regexp_property(&properties, "flags")?;
                PlannedNode::RegExp {
                    pattern,
                    flags,
                    source: plan.encode(machine, source_value)?,
                    canonical_flags: plan.encode(machine, canonical_flags)?,
                    properties: enumerable_properties_excluding(
                        machine,
                        plan,
                        source,
                        &["source", "flags", "lastIndex"],
                    )?,
                }
            }
            HeapEntry::Collection {
                kind,
                entries,
                prototype,
                ..
            } => match kind {
                CollectionKind::Map => PlannedNode::Map {
                    entries: entries
                        .into_iter()
                        .filter(|entry| entry.live)
                        .map(|entry| {
                            Ok((
                                plan.encode(machine, entry.key)?,
                                plan.encode(machine, entry.value)?,
                            ))
                        })
                        .collect::<Result<_, StructuredCloneFailure>>()?,
                    properties: enumerable_properties(machine, plan, source)?,
                    prototype,
                },
                CollectionKind::Set => PlannedNode::Set {
                    values: entries
                        .into_iter()
                        .filter(|entry| entry.live)
                        .map(|entry| plan.encode(machine, entry.key))
                        .collect::<Result<_, _>>()?,
                    properties: enumerable_properties(machine, plan, source)?,
                    prototype: Some(machine.intrinsics.builtins.set_prototype()),
                },
                CollectionKind::WeakMap | CollectionKind::WeakSet => {
                    return Err(DataCloneError::WeakReference.into());
                }
            },
            HeapEntry::ArrayBuffer { .. } => {
                let handle = ArrayBufferHandle::from_value(machine, source)?;
                if handle.is_detached(machine) {
                    return Err(DataCloneError::DetachedArrayBuffer.into());
                }
                let bytes = handle.with_bytes(machine, <[u8]>::to_vec)?;
                let max_byte_length = handle
                    .is_resizable(machine)?
                    .then(|| handle.max_byte_length(machine))
                    .transpose()?;
                PlannedNode::ArrayBuffer {
                    bytes,
                    max_byte_length,
                    properties: enumerable_properties(machine, plan, source)?,
                }
            }
            HeapEntry::SharedArrayBuffer {
                data, prototype, ..
            } => PlannedNode::SharedArrayBuffer {
                data,
                properties: enumerable_properties(machine, plan, source)?,
                prototype,
            },
            HeapEntry::TypedArray { .. } | HeapEntry::DataView { .. } => {
                return Err(DataCloneError::UnsupportedBinaryView.into());
            }
            HeapEntry::Function { .. } | HeapEntry::NativeFunction { .. } => {
                return Err(DataCloneError::Callable.into());
            }
            HeapEntry::Proxy { .. } | HeapEntry::ProxyRevoker { .. } => {
                return Err(DataCloneError::Callable.into());
            }
            HeapEntry::Symbol { .. } | HeapEntry::PrivateName { .. } => {
                return Err(DataCloneError::Symbol.into());
            }
            HeapEntry::WeakRef { .. } | HeapEntry::FinalizationRegistry { .. } => {
                return Err(DataCloneError::WeakReference.into());
            }
            HeapEntry::Vacant => unreachable!("runtime_slot rejects vacant slots"),
            HeapEntry::Script { .. }
            | HeapEntry::ModuleNamespace { .. }
            | HeapEntry::ExternalModuleNamespace { .. }
            | HeapEntry::HashState { .. }
            | HeapEntry::BuiltinIterator { .. }
            | HeapEntry::Iterator { .. }
            | HeapEntry::Generator { .. }
            | HeapEntry::AsyncGenerator { .. }
            | HeapEntry::AsyncFromSync { .. }
            | HeapEntry::DisposableStack { .. }
            | HeapEntry::ProcessEnv { .. }
            | HeapEntry::Temporal { .. }
            | HeapEntry::Intl { .. }
            | HeapEntry::Promise { .. }
            | HeapEntry::Timeout { .. }
            | HeapEntry::PromiseResolver { .. }
            | HeapEntry::PromiseAll { .. }
            | HeapEntry::PromiseAllElement { .. }
            | HeapEntry::AsyncActivation { .. } => {
                return Err(DataCloneError::HostObject.into());
            }
        };
        plan.nodes[node_id] = node;
    }
    Ok(())
}
fn regexp_property(
    properties: &PropertyMap,
    name: &'static str,
) -> Result<Value, StructuredCloneFailure> {
    match properties.get(&PropertyKey::Named(EcmaString::encode(name))) {
        Some(Property::Data { value, .. }) => Ok(*value),
        _ => Err(StructuredCloneFailure::Evaluation(type_error(
            "invalid RegExp internal state",
        ))),
    }
}
fn enumerable_properties<H: Host>(
    machine: &mut Machine<'_, H>,
    plan: &mut ClonePlan,
    source: Value,
) -> Result<Vec<PlannedProperty>, StructuredCloneFailure> {
    enumerable_properties_excluding(machine, plan, source, &[])
}
fn enumerable_properties_excluding<H: Host>(
    machine: &mut Machine<'_, H>,
    plan: &mut ClonePlan,
    source: Value,
    excluded: &[&str],
) -> Result<Vec<PlannedProperty>, StructuredCloneFailure> {
    let keys = machine.own_property_keys(source)?;
    let mut properties = Vec::new();
    for key in keys {
        let PropertyKey::Named(name) = &key else {
            continue;
        };
        if excluded.iter().any(|excluded| name.eq_ascii(excluded))
            || !machine.own_property_is_enumerable(source, &key)?
        {
            continue;
        }
        let value = machine.get_property_key(source, &key)?;
        properties.push(PlannedProperty {
            key,
            value: plan.encode(machine, value)?,
            writable: true,
            enumerable: true,
            configurable: true,
        });
    }
    Ok(properties)
}
fn append_error_state<H: Host>(
    machine: &mut Machine<'_, H>,
    plan: &mut ClonePlan,
    source: Value,
    source_properties: &PropertyMap,
    properties: &mut Vec<PlannedProperty>,
) -> Result<(), StructuredCloneFailure> {
    for name in [
        "name",
        "message",
        "cause",
        "errors",
        "error",
        "suppressed",
        "stack",
    ] {
        let key = PropertyKey::Named(EcmaString::encode(name));
        if properties.iter().any(|property| property.key == key)
            || !source_properties.contains_key(&key)
        {
            continue;
        }
        let value = machine.get_property_key(source, &key)?;
        properties.push(PlannedProperty {
            key,
            value: plan.encode(machine, value)?,
            writable: true,
            enumerable: false,
            configurable: true,
        });
    }
    Ok(())
}
fn materialize<H: Host>(
    machine: &mut Machine<'_, H>,
    plan: &ClonePlan,
) -> Result<Value, StructuredCloneFailure> {
    let mut targets = Vec::with_capacity(plan.nodes.len());
    for node in &plan.nodes {
        let target = match node {
            PlannedNode::Pending(_) => unreachable!("worklist must be exhausted before commit"),
            PlannedNode::String(text) => machine
                .allocate(HeapEntry::String(text.clone()))
                .map_err(EvalFailure::Runtime)?,
            PlannedNode::BigInt(text) => machine
                .allocate(HeapEntry::BigInt(text.clone()))
                .map_err(EvalFailure::Runtime)?,
            PlannedNode::Object { prototype, .. } => machine
                .allocate(HeapEntry::Object {
                    properties: PropertyMap::default(),
                    prototype: *prototype,
                    boxed_primitive: None,
                    extensible: true,
                })
                .map_err(EvalFailure::Runtime)?,
            PlannedNode::Array { length, .. } => machine
                .allocate(HeapEntry::Array {
                    elements: vec![Value::HOLE; *length],
                    properties: PropertyMap::default(),
                    prototype: Some(machine.intrinsics.array_prototype),
                    extensible: true,
                    length_writable: true,
                })
                .map_err(EvalFailure::Runtime)?,
            PlannedNode::Date { time, .. } => machine
                .allocate(HeapEntry::Date {
                    time: *time,
                    properties: PropertyMap::default(),
                    prototype: Some(machine.intrinsics.builtins.date_prototype()),
                    extensible: true,
                })
                .map_err(EvalFailure::Runtime)?,
            PlannedNode::RegExp { pattern, flags, .. } => machine
                .allocate(HeapEntry::RegExp {
                    pattern: pattern.clone(),
                    flags: flags.clone(),
                    properties: PropertyMap::default(),
                    prototype: Some(machine.intrinsics.regexp_prototype()),
                    extensible: true,
                })
                .map_err(EvalFailure::Runtime)?,
            PlannedNode::Map { prototype, .. } => machine
                .allocate(HeapEntry::Collection {
                    kind: CollectionKind::Map,
                    entries: Vec::new(),
                    index: CollectionIndex::default(),
                    size: 0,
                    next_order: 0,
                    properties: PropertyMap::default(),
                    prototype: *prototype,
                    extensible: true,
                })
                .map_err(EvalFailure::Runtime)?,
            PlannedNode::Set { prototype, .. } => machine
                .allocate(HeapEntry::Collection {
                    kind: CollectionKind::Set,
                    entries: Vec::new(),
                    index: CollectionIndex::default(),
                    size: 0,
                    next_order: 0,
                    properties: PropertyMap::default(),
                    prototype: *prototype,
                    extensible: true,
                })
                .map_err(EvalFailure::Runtime)?,
            PlannedNode::ArrayBuffer {
                bytes,
                max_byte_length,
                ..
            } => {
                let handle = ArrayBufferHandle::allocate(machine, bytes.len(), *max_byte_length)?;
                handle.with_bytes_mut(machine, |target| target.copy_from_slice(bytes))?;
                handle.value()
            }
            PlannedNode::SharedArrayBuffer {
                data, prototype, ..
            } => machine
                .allocate(HeapEntry::SharedArrayBuffer {
                    data: Arc::clone(data),
                    properties: PropertyMap::default(),
                    prototype: *prototype,
                    extensible: true,
                })
                .map_err(EvalFailure::Runtime)?,
        };
        targets.push(target);
    }
    for (node_id, node) in plan.nodes.iter().enumerate() {
        let target = targets[node_id];
        match node {
            PlannedNode::Object {
                boxed_primitive,
                properties,
                ..
            } => {
                if let Some(boxed) = boxed_primitive {
                    let target_slot = machine
                        .runtime_slot(target)
                        .map_err(EvalFailure::Runtime)?
                        .expect("object target has a runtime slot");
                    let HeapEntry::Object {
                        boxed_primitive, ..
                    } = &mut machine.heap[target_slot]
                    else {
                        unreachable!("object plan allocated an object")
                    };
                    *boxed_primitive = Some(resolve(*boxed, &targets));
                }
                define_properties(machine, target, properties, &targets)?;
            }
            PlannedNode::Array {
                length,
                elements,
                properties,
            } => {
                let mut values = vec![Value::HOLE; *length];
                for (index, value) in elements {
                    if let Some(slot) = values.get_mut(*index) {
                        *slot = resolve(*value, &targets);
                    }
                }
                machine.replace_array_elements(target, values)?;
                define_properties(machine, target, properties, &targets)?;
            }
            PlannedNode::Date { properties, .. }
            | PlannedNode::ArrayBuffer { properties, .. }
            | PlannedNode::SharedArrayBuffer { properties, .. } => {
                define_properties(machine, target, properties, &targets)?;
            }
            PlannedNode::RegExp {
                source,
                canonical_flags,
                properties,
                ..
            } => {
                for (name, value, writable) in [
                    ("source", resolve(*source, &targets), false),
                    ("flags", resolve(*canonical_flags, &targets), false),
                    ("lastIndex", Value::int32(0), true),
                ] {
                    machine.define_descriptor(
                        target,
                        PropertyKey::Named(EcmaString::encode(name)),
                        Property::Data {
                            value,
                            writable,
                            enumerable: false,
                            configurable: false,
                        },
                    )?;
                }
                define_properties(machine, target, properties, &targets)?;
            }
            PlannedNode::Map {
                entries,
                properties,
                ..
            } => {
                let target_slot = machine
                    .runtime_slot(target)
                    .map_err(EvalFailure::Runtime)?
                    .expect("Map target has a runtime slot");
                for (key, value) in entries {
                    super::collections::append_collection_entry(
                        machine,
                        target_slot,
                        resolve(*key, &targets),
                        resolve(*value, &targets),
                    )?;
                }
                define_properties(machine, target, properties, &targets)?;
            }
            PlannedNode::Set {
                values, properties, ..
            } => {
                let target_slot = machine
                    .runtime_slot(target)
                    .map_err(EvalFailure::Runtime)?
                    .expect("Set target has a runtime slot");
                for value in values {
                    let value = resolve(*value, &targets);
                    super::collections::append_collection_entry(
                        machine,
                        target_slot,
                        value,
                        value,
                    )?;
                }
                define_properties(machine, target, properties, &targets)?;
            }
            PlannedNode::Pending(_) | PlannedNode::String(_) | PlannedNode::BigInt(_) => {}
        }
    }
    Ok(resolve(plan.root, &targets))
}
fn define_properties<H: Host>(
    machine: &mut Machine<'_, H>,
    target: Value,
    properties: &[PlannedProperty],
    targets: &[Value],
) -> Result<(), StructuredCloneFailure> {
    for property in properties {
        machine.define_descriptor(
            target,
            property.key.clone(),
            Property::Data {
                value: resolve(property.value, targets),
                writable: property.writable,
                enumerable: property.enumerable,
                configurable: property.configurable,
            },
        )?;
    }
    Ok(())
}
fn resolve(value: EncodedValue, targets: &[Value]) -> Value {
    match value {
        EncodedValue::Immediate(value) => value,
        EncodedValue::Node(node) => targets[node],
    }
}
#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::Limits;
    fn machine<'a>(
        program: &'a bamts_bytecode::Program<bamts_bytecode::Verified>,
        host: &'a mut TestHost,
    ) -> Machine<'a, TestHost> {
        Machine::new(program, host, Limits::default())
    }
    fn clone(machine: &mut Machine<'_, TestHost>, value: Value) -> Value {
        clone_value_with_transfer(machine, value, &[]).expect("clone succeeds")
    }
    fn slot(machine: &Machine<'_, TestHost>, value: Value) -> usize {
        machine.runtime_slot(value).unwrap().unwrap()
    }
    #[test]
    fn cycles_and_shared_aliases_preserve_identity() {
        let module = blank_program("<structured-clone-cycle>");
        let mut host = TestHost;
        let mut machine = machine(&module, &mut host);
        let root = ordinary_object(&mut machine);
        let child = ordinary_object(&mut machine);
        machine.set_data_property(root, "self", root).unwrap();
        machine.set_data_property(root, "left", child).unwrap();
        machine.set_data_property(root, "right", child).unwrap();
        let cloned = clone(&mut machine, root);
        let self_ref = machine.get_named_property(cloned, "self").unwrap();
        let left = machine.get_named_property(cloned, "left").unwrap();
        let right = machine.get_named_property(cloned, "right").unwrap();
        assert_eq!(slot(&machine, cloned), slot(&machine, self_ref));
        assert_eq!(slot(&machine, left), slot(&machine, right));
        assert_ne!(slot(&machine, child), slot(&machine, left));
    }
    #[test]
    fn sparse_arrays_keep_holes_and_normalize_enumerable_descriptors() {
        let module = blank_program("<structured-clone-sparse>");
        let mut host = TestHost;
        let mut machine = machine(&module, &mut host);
        let array = machine
            .allocate(HeapEntry::Array {
                elements: vec![Value::int32(1), Value::HOLE, Value::int32(3)],
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.array_prototype),
                extensible: true,
                length_writable: true,
            })
            .unwrap();
        machine
            .define_descriptor(
                array,
                PropertyKey::Named(EcmaString::encode("hidden")),
                Property::Data {
                    value: Value::int32(9),
                    writable: false,
                    enumerable: false,
                    configurable: false,
                },
            )
            .unwrap();
        machine
            .define_descriptor(
                array,
                PropertyKey::Named(EcmaString::encode("visible")),
                Property::Data {
                    value: Value::int32(7),
                    writable: false,
                    enumerable: true,
                    configurable: false,
                },
            )
            .unwrap();
        let cloned = clone(&mut machine, array);
        assert_eq!(
            machine.array_elements(cloned).unwrap().unwrap(),
            [Value::int32(1), Value::HOLE, Value::int32(3)]
        );
        assert!(
            !machine
                .has_own_property_key(cloned, &PropertyKey::Named(EcmaString::encode("hidden")))
                .unwrap()
        );
        assert!(matches!(
            machine.own_descriptor(
                cloned,
                &PropertyKey::Named(EcmaString::encode("visible"))
            ).unwrap(),
            Some(Property::Data {
                value,
                writable: true,
                enumerable: true,
                configurable: true,
            }) if value == Value::int32(7)
        ));
    }
    #[test]
    fn map_object_keys_reuse_the_cloned_key_identity() {
        let module = blank_program("<structured-clone-map-key>");
        let mut host = TestHost;
        let mut machine = machine(&module, &mut host);
        let key = ordinary_object(&mut machine);
        let map = machine
            .allocate(HeapEntry::Collection {
                kind: CollectionKind::Map,
                entries: Vec::new(),
                index: CollectionIndex::default(),
                size: 0,
                next_order: 0,
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
            })
            .unwrap();
        let map_slot = slot(&machine, map);
        super::super::collections::append_collection_entry(&mut machine, map_slot, key, key)
            .unwrap();
        let cloned = clone(&mut machine, map);
        let HeapEntry::Collection { entries, .. } = &machine.heap[slot(&machine, cloned)] else {
            panic!("clone remains a Map")
        };
        let entry = entries.iter().find(|entry| entry.live).unwrap();
        assert_eq!(slot(&machine, entry.key), slot(&machine, entry.value));
        assert_ne!(slot(&machine, entry.key), slot(&machine, key));
    }
    #[test]
    fn arraybuffer_copy_and_transfer_have_distinct_source_effects() {
        let module = blank_program("<structured-clone-arraybuffer>");
        let mut host = TestHost;
        let mut machine = machine(&module, &mut host);
        let copied = ArrayBufferHandle::allocate(&mut machine, 3, Some(8)).unwrap();
        copied
            .with_bytes_mut(&mut machine, |bytes| bytes.copy_from_slice(&[1, 2, 3]))
            .unwrap();
        let copied_target = clone(&mut machine, copied.value());
        ArrayBufferHandle::from_value(&machine, copied_target)
            .unwrap()
            .with_bytes_mut(&mut machine, |bytes| bytes[0] = 9)
            .unwrap();
        assert_eq!(
            copied.with_bytes(&machine, <[u8]>::to_vec).unwrap(),
            [1, 2, 3]
        );
        let moved = ArrayBufferHandle::allocate(&mut machine, 2, None).unwrap();
        moved
            .with_bytes_mut(&mut machine, |bytes| bytes.copy_from_slice(&[4, 5]))
            .unwrap();
        let moved_target =
            clone_value_with_transfer(&mut machine, moved.value(), &[moved.value()]).unwrap();
        assert!(moved.is_detached(&machine));
        assert_eq!(
            ArrayBufferHandle::from_value(&machine, moved_target)
                .unwrap()
                .with_bytes(&machine, <[u8]>::to_vec)
                .unwrap(),
            [4, 5]
        );
    }
    #[test]
    fn regexp_state_is_rebuilt_and_last_index_is_reset() {
        let module = blank_program("<structured-clone-regexp>");
        let mut host = TestHost;
        let mut machine = machine(&module, &mut host);
        let source_text = machine
            .allocate(HeapEntry::String(EcmaString::encode("a")))
            .unwrap();
        let flags_text = machine
            .allocate(HeapEntry::String(EcmaString::encode("g")))
            .unwrap();
        let mut properties = PropertyMap::default();
        for (name, value, writable) in [
            ("source", source_text, false),
            ("flags", flags_text, false),
            ("lastIndex", Value::int32(12), true),
        ] {
            properties.insert(
                PropertyKey::Named(EcmaString::encode(name)),
                Property::Data {
                    value,
                    writable,
                    enumerable: false,
                    configurable: false,
                },
            );
        }
        let regexp = machine
            .allocate(HeapEntry::RegExp {
                pattern: EcmaString::encode("a"),
                flags: EcmaString::encode("g"),
                properties,
                prototype: Some(machine.intrinsics.regexp_prototype()),
                extensible: true,
            })
            .unwrap();
        let cloned = clone(&mut machine, regexp);
        let cloned_slot = slot(&machine, cloned);
        let HeapEntry::RegExp {
            pattern,
            flags,
            properties,
            ..
        } = &machine.heap[cloned_slot]
        else {
            panic!("clone remains a RegExp")
        };
        assert!(pattern.eq_ascii("a"));
        assert!(flags.eq_ascii("g"));
        assert!(matches!(
            properties.get(&PropertyKey::Named(EcmaString::encode("lastIndex"))),
            Some(Property::Data {
                value,
                writable: true,
                enumerable: false,
                configurable: false,
            }) if *value == Value::int32(0)
        ));
    }
    #[test]
    fn error_message_cause_and_stack_state_are_cloned() {
        let module = blank_program("<structured-clone-error>");
        let mut host = TestHost;
        let mut machine = machine(&module, &mut host);
        let message = machine
            .allocate(HeapEntry::String(EcmaString::encode("boom")))
            .unwrap();
        let cause = ordinary_object(&mut machine);
        let options = ordinary_object(&mut machine);
        machine.set_data_property(options, "cause", cause).unwrap();
        let constructor = machine.intrinsics.global("Error").unwrap();
        let error = machine
            .call_value(constructor, Value::UNDEFINED, &[message, options])
            .unwrap();
        let cloned = clone(&mut machine, error);
        let cloned_message = machine.get_named_property(cloned, "message").unwrap();
        assert_eq!(
            machine.to_string(cloned_message).unwrap(),
            EcmaString::encode("boom")
        );
        let cloned_cause = machine.get_named_property(cloned, "cause").unwrap();
        assert_ne!(slot(&machine, cloned_cause), slot(&machine, cause));
        assert!(
            machine
                .has_own_property_key(cloned, &PropertyKey::Named(EcmaString::encode("stack")))
                .unwrap()
        );
        assert!(matches!(
            machine
                .own_descriptor(cloned, &PropertyKey::Named(EcmaString::encode("message")))
                .unwrap(),
            Some(Property::Data {
                writable: true,
                enumerable: false,
                configurable: true,
                ..
            })
        ));
    }
    #[test]
    fn invalid_transfer_lists_reject_before_any_detachment() {
        let module = blank_program("<structured-clone-transfer-preflight>");
        let mut host = TestHost;
        let mut machine = machine(&module, &mut host);
        let first = ArrayBufferHandle::allocate(&mut machine, 1, None).unwrap();
        let second = ArrayBufferHandle::allocate(&mut machine, 1, None).unwrap();
        assert!(matches!(
            clone_value_with_transfer(&mut machine, Value::NULL, &[first.value(), first.value()]),
            Err(StructuredCloneFailure::DataClone(
                DataCloneError::DuplicateTransfer
            ))
        ));
        assert!(!first.is_detached(&machine));
        assert!(matches!(
            clone_value_with_transfer(
                &mut machine,
                Value::NULL,
                &[first.value(), Value::int32(1), second.value()]
            ),
            Err(StructuredCloneFailure::DataClone(
                DataCloneError::NonTransferable
            ))
        ));
        assert!(!first.is_detached(&machine));
        assert!(!second.is_detached(&machine));
    }
    #[test]
    fn unsupported_values_have_exact_data_clone_taxonomy() {
        let module = blank_program("<structured-clone-unsupported>");
        let mut host = TestHost;
        let mut machine = machine(&module, &mut host);
        let symbol = machine
            .allocate(HeapEntry::Symbol {
                description: EcmaString::encode("x"),
            })
            .unwrap();
        let weak = machine
            .allocate(HeapEntry::WeakRef {
                target: None,
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
            })
            .unwrap();
        let callable = machine.intrinsics.global("Object").unwrap();
        assert!(matches!(
            clone_value_with_transfer(&mut machine, symbol, &[]),
            Err(StructuredCloneFailure::DataClone(DataCloneError::Symbol))
        ));
        assert!(matches!(
            clone_value_with_transfer(&mut machine, weak, &[]),
            Err(StructuredCloneFailure::DataClone(
                DataCloneError::WeakReference
            ))
        ));
        assert!(matches!(
            clone_value_with_transfer(&mut machine, callable, &[]),
            Err(StructuredCloneFailure::DataClone(DataCloneError::Callable))
        ));
        let bytes =
            {
                let handle = ArrayBufferHandle::allocate(&mut machine, 3, None).unwrap();
                handle
                    .with_bytes_mut(&mut machine, |target| target.copy_from_slice(&[1, 2, 3]))
                    .unwrap();
                machine
                    .allocate(HeapEntry::TypedArray {
                        kind: super::super::typedarray_all::ElementKind::Uint8,
                        buffer: handle.value(),
                        byte_offset: 0,
                        byte_length: super::super::typedarray_all::LengthSlot::Fixed(3),
                        array_length: super::super::typedarray_all::LengthSlot::Fixed(3),
                        properties: PropertyMap::default(),
                        prototype: Some(machine.intrinsics.builtins.typed_array_prototype(
                            super::super::typedarray_all::ElementKind::Uint8,
                        )),
                        extensible: true,
                    })
                    .unwrap()
            };
        assert!(matches!(
            clone_value_with_transfer(&mut machine, bytes, &[]),
            Err(StructuredCloneFailure::DataClone(
                DataCloneError::UnsupportedBinaryView
            ))
        ));
    }

    #[test]
    fn dataview_is_classified_as_an_unsupported_binary_view() {
        let module = blank_program("<structured-clone-dataview>");
        let mut host = TestHost;
        let mut machine = machine(&module, &mut host);
        let buffer = ArrayBufferHandle::allocate(&mut machine, 4, None).unwrap();
        let view = machine
            .allocate(HeapEntry::DataView {
                buffer: buffer.value(),
                byte_offset: 0,
                byte_length: super::super::typedarray_all::LengthSlot::Fixed(4),
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.builtins.dataview_prototype()),
                extensible: true,
            })
            .unwrap();

        assert!(matches!(
            clone_value_with_transfer(&mut machine, view, &[]),
            Err(StructuredCloneFailure::DataClone(
                DataCloneError::UnsupportedBinaryView
            ))
        ));
    }
    #[test]
    fn tight_budget_rolls_back_targets_and_keeps_transfers_attached() {
        let module = blank_program("<structured-clone-budget-rollback>");
        let mut host = TestHost;
        let mut machine = machine(&module, &mut host);
        let buffer = ArrayBufferHandle::allocate(&mut machine, 1, None).unwrap();
        let root = ordinary_object(&mut machine);
        machine
            .set_data_property(root, "buffer", buffer.value())
            .unwrap();
        let heap_len = machine.heap.len();
        let heap_bytes = machine.heap_bytes;
        machine.limits.max_heap_slots = machine.live_runtime_slots() + 1;
        assert!(matches!(
            clone_value_with_transfer(&mut machine, root, &[buffer.value()]),
            Err(StructuredCloneFailure::Evaluation(_))
        ));
        assert_eq!(machine.heap.len(), heap_len);
        assert_eq!(machine.heap_bytes, heap_bytes);
        assert!(!buffer.is_detached(&machine));
        machine.assert_heap_ledger();
    }
}
