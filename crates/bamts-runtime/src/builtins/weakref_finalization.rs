use std::collections::{BTreeMap, VecDeque};
use std::mem::size_of;

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, SlotId, Value};

use super::{
    define_data, define_to_string_tag, install_constructor_function, install_function, type_error,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{
    CallbackException, EvalFailure, HeapEntry, Host, Machine, MicrotaskJob, PropertyMap,
    QueuedMicrotask, RUNTIME_HEAP_SEGMENT, RuntimeErrorKind,
};

/// One active registration. `target` is deliberately excluded from ordinary GC
/// tracing; the other two values are strong edges owned by a live registry.
#[derive(Clone, Copy, Debug)]
pub(crate) struct FinalizationCell {
    pub(crate) target: Value,
    pub(crate) held_value: Value,
    pub(crate) unregister_token: Option<Value>,
}

impl FinalizationCell {
    pub(crate) const BYTES: usize = size_of::<Self>();
}

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let weak_ref_prototype = ordinary(heap, Some(builtins.object_prototype()));
    let weak_ref = install_constructor_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "WeakRef",
            length: 1,
            handler: weak_ref_constructor::<H>,
        },
    );
    builtins.set_constructor_prototype(heap, atoms, shapes, weak_ref, weak_ref_prototype);
    builtins.set_weak_ref_prototype(weak_ref_prototype);
    let deref = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "deref",
            length: 0,
            handler: weak_ref_deref::<H>,
        },
    );
    define_data(heap, atoms, shapes, weak_ref_prototype, "deref", deref);
    define_to_string_tag(
        heap,
        shapes,
        weak_ref_prototype,
        builtins.symbol_to_string_tag(),
        "WeakRef",
    );
    globals.insert(EcmaString::encode("WeakRef"), weak_ref);

    let registry_prototype = ordinary(heap, Some(builtins.object_prototype()));
    let registry = install_constructor_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "FinalizationRegistry",
            length: 1,
            handler: finalization_registry_constructor::<H>,
        },
    );
    builtins.set_constructor_prototype(heap, atoms, shapes, registry, registry_prototype);
    builtins.set_finalization_registry_prototype(registry_prototype);
    for (name, length, handler) in [
        (
            "register",
            2,
            finalization_registry_register::<H> as BuiltinHandler<H>,
        ),
        ("unregister", 1, finalization_registry_unregister::<H>),
    ] {
        let function = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name,
                length,
                handler,
            },
        );
        define_data(heap, atoms, shapes, registry_prototype, name, function);
    }
    define_to_string_tag(
        heap,
        shapes,
        registry_prototype,
        builtins.symbol_to_string_tag(),
        "FinalizationRegistry",
    );
    globals.insert(EcmaString::encode("FinalizationRegistry"), registry);
}

fn weak_ref_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !constructing {
        return Err(type_error("WeakRef constructor requires 'new'"));
    }
    let target = args.first().copied().unwrap_or(Value::UNDEFINED);
    require_weakly_holdable(
        machine,
        target,
        "WeakRef target must be an object or symbol",
    )?;
    let prototype =
        constructor_prototype(machine, machine.intrinsics.builtins.weak_ref_prototype())?;
    let weak_ref = machine
        .allocate(HeapEntry::WeakRef {
            target: Some(target),
            properties: PropertyMap::default(),
            prototype: Some(prototype),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)?;
    machine.keep_alive_for_job(target)?;
    Ok(BuiltinOutcome::Value(weak_ref))
}

fn weak_ref_deref<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let slot = weak_ref_slot(machine, this)?;
    let HeapEntry::WeakRef { target, .. } = machine.heap[slot] else {
        unreachable!("WeakRef brand was checked")
    };
    let Some(target) = target else {
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    };
    machine.keep_alive_for_job(target)?;
    Ok(BuiltinOutcome::Value(target))
}

fn finalization_registry_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !constructing {
        return Err(type_error(
            "FinalizationRegistry constructor requires 'new'",
        ));
    }
    let cleanup_callback = args.first().copied().unwrap_or(Value::UNDEFINED);
    if !machine.is_callable(cleanup_callback)? {
        return Err(type_error(
            "FinalizationRegistry cleanup callback must be callable",
        ));
    }
    let prototype = constructor_prototype(
        machine,
        machine
            .intrinsics
            .builtins
            .finalization_registry_prototype(),
    )?;
    let registry = machine
        .allocate(HeapEntry::FinalizationRegistry {
            cleanup_callback,
            cells: Vec::new(),
            pending_holdings: VecDeque::new(),
            cleanup_scheduled: false,
            properties: PropertyMap::default(),
            prototype: Some(prototype),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)?;
    Ok(BuiltinOutcome::Value(registry))
}

fn finalization_registry_register<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let slot = finalization_registry_slot(machine, this)?;
    let target = args.first().copied().unwrap_or(Value::UNDEFINED);
    let held_value = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let unregister_token = args
        .get(2)
        .copied()
        .filter(|value| *value != Value::UNDEFINED);

    require_weakly_holdable(
        machine,
        target,
        "FinalizationRegistry target must be an object or symbol",
    )?;
    if target == held_value {
        return Err(type_error(
            "FinalizationRegistry target and holdings must differ",
        ));
    }
    if let Some(token) = unregister_token {
        require_weakly_holdable(
            machine,
            token,
            "FinalizationRegistry unregister token must be an object or symbol",
        )?;
    }

    machine
        .charge_slot(slot, FinalizationCell::BYTES)
        .map_err(EvalFailure::Runtime)?;
    let HeapEntry::FinalizationRegistry { cells, .. } = &mut machine.heap[slot] else {
        unreachable!("FinalizationRegistry brand was checked")
    };
    cells.push(FinalizationCell {
        target,
        held_value,
        unregister_token,
    });
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn finalization_registry_unregister<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let slot = finalization_registry_slot(machine, this)?;
    let token = args.first().copied().unwrap_or(Value::UNDEFINED);
    require_weakly_holdable(
        machine,
        token,
        "FinalizationRegistry unregister token must be an object or symbol",
    )?;

    let removed = {
        let HeapEntry::FinalizationRegistry { cells, .. } = &mut machine.heap[slot] else {
            unreachable!("FinalizationRegistry brand was checked")
        };
        let before = cells.len();
        cells.retain(|cell| cell.unregister_token != Some(token));
        before - cells.len()
    };
    if removed != 0 {
        machine.refund_slot(slot, removed.saturating_mul(FinalizationCell::BYTES));
    }
    Ok(BuiltinOutcome::Value(if removed != 0 {
        Value::TRUE
    } else {
        Value::FALSE
    }))
}

fn weak_ref_slot<H: Host>(machine: &Machine<'_, H>, value: Value) -> Result<usize, EvalFailure> {
    let Some(slot) = machine.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
        return Err(type_error("WeakRef method called on incompatible receiver"));
    };
    if matches!(machine.heap[slot], HeapEntry::WeakRef { .. }) {
        Ok(slot)
    } else {
        Err(type_error("WeakRef method called on incompatible receiver"))
    }
}

fn finalization_registry_slot<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<usize, EvalFailure> {
    let Some(slot) = machine.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
        return Err(type_error(
            "FinalizationRegistry method called on incompatible receiver",
        ));
    };
    if matches!(machine.heap[slot], HeapEntry::FinalizationRegistry { .. }) {
        Ok(slot)
    } else {
        Err(type_error(
            "FinalizationRegistry method called on incompatible receiver",
        ))
    }
}

fn require_weakly_holdable<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
    operation: &'static str,
) -> Result<(), EvalFailure> {
    if machine.is_object(value) {
        return Ok(());
    }
    let Some(slot) = machine.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
        return Err(type_error(operation));
    };
    let can_be_held_weakly = matches!(&machine.heap[slot], HeapEntry::Symbol { .. })
        && !machine
            .intrinsics
            .symbol_registry
            .values()
            .any(|registered| *registered == value);
    if can_be_held_weakly {
        Ok(())
    } else {
        Err(type_error(operation))
    }
}

fn constructor_prototype<H: Host>(
    machine: &mut Machine<'_, H>,
    default: Value,
) -> Result<Value, EvalFailure> {
    let new_target = machine.current_new_target;
    if new_target == Value::UNDEFINED {
        return Ok(default);
    }
    let candidate = machine.get_named_property(new_target, "prototype")?;
    Ok(if machine.is_object(candidate) {
        candidate
    } else {
        default
    })
}

fn ordinary(heap: &mut Vec<HeapEntry>, prototype: Option<Value>) -> Value {
    super::super::push(
        heap,
        HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype,
            extensible: true,
            boxed_primitive: None,
        },
    )
}

/// Marks every strong edge owned by a weak-reference heap entry. Targets are
/// intentionally absent: the collector asks `process_weak_targets_after_marking`
/// about them only after the ordinary mark and ephemeron fixed point completes.
pub(crate) fn trace_strong_edges(entry: &HeapEntry, mut mark: impl FnMut(Value)) {
    match entry {
        HeapEntry::FinalizationRegistry {
            cleanup_callback,
            cells,
            pending_holdings,
            ..
        } => {
            mark(*cleanup_callback);
            for cell in cells {
                mark(cell.held_value);
                if let Some(token) = cell.unregister_token {
                    mark(token);
                }
            }
            for held_value in pending_holdings {
                mark(*held_value);
            }
        }
        HeapEntry::WeakRef { .. } => {}
        _ => unreachable!("weak tracing is only called for weak-reference entries"),
    }
}

impl<'a, H: Host> Machine<'a, H> {
    fn keep_alive_for_job(&mut self, target: Value) -> Result<(), EvalFailure> {
        if self.kept_alive.contains(&target) {
            return Ok(());
        }
        self.charge_machine(size_of::<Value>())
            .map_err(EvalFailure::Runtime)?;
        if self.kept_alive.try_reserve(1).is_err() {
            self.refund_machine(size_of::<Value>());
            return Err(EvalFailure::Runtime(
                RuntimeErrorKind::HeapByteLimitExceeded {
                    limit: self.limits.max_heap_bytes,
                },
            ));
        }
        self.kept_alive.push(target);
        Ok(())
    }

    /// Clears dead weak handles and extracts holdings after the collector's
    /// ephemeron fixed point. This queues candidates, not jobs: the host chooses
    /// when (or whether) to call `schedule_finalization_cleanup_jobs`.
    pub(crate) fn process_weak_targets_after_marking(&mut self, marks: &[bool], holders: &[usize]) {
        for &index in holders {
            let mut released = 0usize;
            let mut queue_registry = false;
            match &mut self.heap[index] {
                HeapEntry::WeakRef { target, .. } => {
                    if target.is_some_and(|value| !is_marked(marks, value)) {
                        *target = None;
                    }
                }
                HeapEntry::FinalizationRegistry {
                    cells,
                    pending_holdings,
                    cleanup_scheduled,
                    ..
                } => {
                    let mut cursor = 0;
                    while cursor < cells.len() {
                        if is_marked(marks, cells[cursor].target) {
                            cursor += 1;
                            continue;
                        }
                        let cell = cells.remove(cursor);
                        pending_holdings.push_back(cell.held_value);
                        released = released.saturating_add(
                            FinalizationCell::BYTES.saturating_sub(size_of::<Value>()),
                        );
                    }
                    if !pending_holdings.is_empty() && !*cleanup_scheduled {
                        *cleanup_scheduled = true;
                        queue_registry = true;
                    }
                }
                _ => {}
            }
            if released != 0 {
                self.refund_slot(index, released);
            }
            if queue_registry {
                self.finalization_cleanup_queue
                    .push_back(value_for_heap_index(index));
            }
        }
    }

    /// Explicit host scheduling point. GC itself makes no timing guarantee.
    /// Capacity failure leaves every candidate queued for a later checkpoint.
    pub(crate) fn schedule_finalization_cleanup_jobs(&mut self) -> Result<usize, RuntimeErrorKind> {
        let count = self.finalization_cleanup_queue.len();
        self.ensure_microtask_capacity(count)?;
        while let Some(registry) = self.finalization_cleanup_queue.pop_front() {
            self.microtasks.push_back(QueuedMicrotask::uncharged(
                MicrotaskJob::FinalizationCleanup {
                    registry,
                    context: self.context_global,
                },
            ));
        }
        Ok(count)
    }

    pub(crate) fn execute_finalization_cleanup_job(
        &mut self,
        registry: Value,
    ) -> Result<Option<CallbackException>, RuntimeErrorKind> {
        let slot = self
            .runtime_slot(registry)?
            .ok_or(RuntimeErrorKind::InvalidValue { value: registry })?;
        let callback = {
            let HeapEntry::FinalizationRegistry {
                cleanup_callback,
                cleanup_scheduled,
                ..
            } = &mut self.heap[slot]
            else {
                return Err(RuntimeErrorKind::InvalidValue { value: registry });
            };
            *cleanup_scheduled = false;
            *cleanup_callback
        };

        loop {
            let (held_value, has_more) = {
                let HeapEntry::FinalizationRegistry {
                    pending_holdings, ..
                } = &mut self.heap[slot]
                else {
                    return Err(RuntimeErrorKind::InvalidValue { value: registry });
                };
                let held_value = pending_holdings.pop_front();
                (held_value, !pending_holdings.is_empty())
            };
            let Some(held_value) = held_value else {
                return Ok(None);
            };
            self.refund_slot(slot, size_of::<Value>());

            match self.call_value(callback, Value::UNDEFINED, &[held_value]) {
                Ok(_) => {}
                Err(EvalFailure::Runtime(kind)) => {
                    if has_more {
                        self.queue_finalization_cleanup_candidate(registry);
                    }
                    return Err(kind);
                }
                Err(failure) => {
                    if has_more {
                        self.queue_finalization_cleanup_candidate(registry);
                    }
                    let (value, origin) =
                        self.promise_rejection_value(failure)
                            .map_err(|failure| match failure {
                                EvalFailure::Runtime(kind) => kind,
                                _ => RuntimeErrorKind::InvalidValue { value: callback },
                            })?;
                    return Ok(Some(CallbackException { value, origin }));
                }
            }
        }
    }

    fn queue_finalization_cleanup_candidate(&mut self, registry: Value) {
        let Ok(Some(slot)) = self.runtime_slot(registry) else {
            return;
        };
        let HeapEntry::FinalizationRegistry {
            cleanup_scheduled, ..
        } = &mut self.heap[slot]
        else {
            return;
        };
        if !*cleanup_scheduled {
            *cleanup_scheduled = true;
            self.finalization_cleanup_queue.push_back(registry);
        }
    }
}

fn is_marked(marks: &[bool], value: Value) -> bool {
    let Some(Decoded::HeapRef(id)) = value.decode() else {
        return false;
    };
    id.segment() == RUNTIME_HEAP_SEGMENT
        && marks.get(id.slot() as usize - 1).copied().unwrap_or(false)
}

fn value_for_heap_index(index: usize) -> Value {
    let slot = u32::try_from(index + 1).expect("heap limits keep slots within u32");
    Value::heap_ref(
        SlotId::from_parts(RUNTIME_HEAP_SEGMENT, slot)
            .expect("runtime segment and heap slot are nonzero"),
    )
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program};
    use super::*;
    use crate::{
        CollectionEntry, CollectionIndex, CollectionKind, Limits, MicrotaskDrain, ThrowOrigin,
    };

    fn object(machine: &mut Machine<'_, TestHost>) -> Value {
        machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .unwrap()
    }

    fn global(machine: &Machine<'_, TestHost>, name: &str) -> Value {
        machine.intrinsics.global(name).expect("builtin exists")
    }

    fn method(machine: &mut Machine<'_, TestHost>, receiver: Value, name: &str) -> Value {
        machine.get_named_property(receiver, name).unwrap()
    }

    fn record_holding(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.intrinsics.globals.insert(
            EcmaString::encode("cleanupHolding"),
            args.first().copied().unwrap_or(Value::UNDEFINED),
        );
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    fn throwing_cleanup(
        _machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "cleanup failed",
        }))
    }

    fn callback(machine: &mut Machine<'_, TestHost>, handler: BuiltinHandler<TestHost>) -> Value {
        install_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            &mut machine.intrinsics.builtins,
            crate::intrinsics::BuiltinDef {
                name: "cleanup",
                length: 1,
                handler,
            },
        )
    }

    #[test]
    fn installs_exact_constructor_and_prototype_contracts() {
        let module = blank_program("<weakref-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        for (constructor_name, method_name, method_length, tag) in [
            ("WeakRef", "deref", 0, "WeakRef"),
            (
                "FinalizationRegistry",
                "register",
                2,
                "FinalizationRegistry",
            ),
            (
                "FinalizationRegistry",
                "unregister",
                1,
                "FinalizationRegistry",
            ),
        ] {
            let constructor = global(&machine, constructor_name);
            let prototype = machine
                .get_named_property(constructor, "prototype")
                .unwrap();
            assert_eq!(
                machine
                    .get_named_property(prototype, "constructor")
                    .unwrap(),
                constructor
            );
            let method = method(&mut machine, prototype, method_name);
            let method_name_value = machine.get_named_property(method, "name").unwrap();
            assert!(
                machine
                    .to_string(method_name_value)
                    .unwrap()
                    .eq_ascii(method_name)
            );
            assert_eq!(
                machine.get_named_property(method, "length").unwrap(),
                Value::int32(method_length)
            );
            let tag_key = machine
                .property_key_from_value(machine.intrinsics.builtins.symbol_to_string_tag())
                .unwrap();
            let tag_value = machine.get_property_key(prototype, &tag_key).unwrap();
            assert!(machine.to_string(tag_value).unwrap().eq_ascii(tag));
        }
        let weak_ref_constructor = global(&machine, "WeakRef");
        let target = object(&mut machine);
        assert!(matches!(
            machine.call_value(weak_ref_constructor, Value::UNDEFINED, &[target]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn finalization_registry_rejects_non_callable_cleanup_callback() {
        let module = blank_program("<weakref-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = global(&machine, "FinalizationRegistry");
        assert!(matches!(
            machine.construct_value(constructor, &[Value::int32(0)]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn weak_ref_liveness_clearing_and_same_job_keep_alive() {
        let module = blank_program("<weakref-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let target = object(&mut machine);
        let target_slot = machine.runtime_slot(target).unwrap().unwrap();
        let constructor = global(&machine, "WeakRef");
        let weak_ref = machine.construct_value(constructor, &[target]).unwrap();
        machine
            .intrinsics
            .globals
            .insert(EcmaString::encode("weak"), weak_ref);

        machine.collect_garbage();
        let deref = method(&mut machine, weak_ref, "deref");
        assert_eq!(machine.call_value(deref, weak_ref, &[]).unwrap(), target);
        assert!(!matches!(machine.heap[target_slot], HeapEntry::Vacant));

        machine.clear_kept_alive_for_job();
        machine.collect_garbage();
        assert!(matches!(machine.heap[target_slot], HeapEntry::Vacant));
        assert_eq!(
            machine.call_value(deref, weak_ref, &[]).unwrap(),
            Value::UNDEFINED
        );
    }

    #[test]
    fn weak_map_value_keeps_weak_ref_target_alive() {
        let module = blank_program("<weakref-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let key = object(&mut machine);
        let target = object(&mut machine);
        let constructor = global(&machine, "WeakRef");
        let weak_ref = machine.construct_value(constructor, &[target]).unwrap();
        let weak_map = machine
            .allocate(HeapEntry::Collection {
                kind: CollectionKind::WeakMap,
                entries: vec![CollectionEntry {
                    key,
                    value: target,
                    live: true,
                    order: 0,
                }],
                index: CollectionIndex::default(),
                size: 1,
                next_order: 1,
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
            })
            .unwrap();
        for (name, value) in [("key", key), ("weak", weak_ref), ("weakMap", weak_map)] {
            machine
                .intrinsics
                .globals
                .insert(EcmaString::encode(name), value);
        }
        machine.clear_kept_alive_for_job();
        machine.collect_garbage();
        let deref = method(&mut machine, weak_ref, "deref");
        assert_eq!(machine.call_value(deref, weak_ref, &[]).unwrap(), target);
    }

    #[test]
    fn registry_does_not_retain_target_but_delivers_held_value() {
        let module = blank_program("<weakref-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let cleanup = callback(&mut machine, record_holding);
        let constructor = global(&machine, "FinalizationRegistry");
        let registry = machine.construct_value(constructor, &[cleanup]).unwrap();
        machine
            .intrinsics
            .globals
            .insert(EcmaString::encode("registry"), registry);
        let target = object(&mut machine);
        let target_slot = machine.runtime_slot(target).unwrap().unwrap();
        let held = object(&mut machine);
        let held_slot = machine.runtime_slot(held).unwrap().unwrap();
        let register = method(&mut machine, registry, "register");
        machine
            .call_value(register, registry, &[target, held])
            .unwrap();

        machine.collect_garbage();
        assert!(matches!(machine.heap[target_slot], HeapEntry::Vacant));
        assert!(!matches!(machine.heap[held_slot], HeapEntry::Vacant));
        assert_eq!(machine.schedule_finalization_cleanup_jobs().unwrap(), 1);
        assert_eq!(
            machine.drain_microtasks().unwrap(),
            MicrotaskDrain {
                executed: 1,
                uncaught: Vec::new()
            }
        );
        assert_eq!(
            machine
                .intrinsics
                .globals
                .get(&EcmaString::encode("cleanupHolding")),
            Some(&held)
        );
    }

    #[test]
    fn drain_microtasks_schedules_cleanup_without_explicit_host_call() {
        let module = blank_program("<weakref-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let cleanup = callback(&mut machine, record_holding);
        let constructor = global(&machine, "FinalizationRegistry");
        let registry = machine.construct_value(constructor, &[cleanup]).unwrap();
        machine
            .intrinsics
            .globals
            .insert(EcmaString::encode("registry"), registry);
        let register = method(&mut machine, registry, "register");
        let target = object(&mut machine);
        machine
            .call_value(register, registry, &[target, Value::int32(7)])
            .unwrap();
        machine.collect_garbage();
        assert_eq!(
            machine.drain_microtasks().unwrap(),
            MicrotaskDrain {
                executed: 1,
                uncaught: Vec::new(),
            }
        );
        assert_eq!(
            machine
                .intrinsics
                .globals
                .get(&EcmaString::encode("cleanupHolding")),
            Some(&Value::int32(7))
        );
    }

    #[test]
    fn unregister_removes_every_cell_for_token() {
        let module = blank_program("<weakref-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let cleanup = callback(&mut machine, record_holding);
        let constructor = global(&machine, "FinalizationRegistry");
        let registry = machine.construct_value(constructor, &[cleanup]).unwrap();
        machine
            .intrinsics
            .globals
            .insert(EcmaString::encode("registry"), registry);
        let token = object(&mut machine);
        let register = method(&mut machine, registry, "register");
        for held in [Value::int32(1), Value::int32(2)] {
            let target = object(&mut machine);
            machine
                .call_value(register, registry, &[target, held, token])
                .unwrap();
        }
        let unregister = method(&mut machine, registry, "unregister");
        assert_eq!(
            machine.call_value(unregister, registry, &[token]).unwrap(),
            Value::TRUE
        );
        assert_eq!(
            machine.call_value(unregister, registry, &[token]).unwrap(),
            Value::FALSE
        );
        machine.collect_garbage();
        assert_eq!(machine.schedule_finalization_cleanup_jobs().unwrap(), 0);
        assert!(matches!(
            machine.call_value(unregister, registry, &[Value::int32(1)]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn rejects_same_target_and_holding_before_mutation() {
        let module = blank_program("<weakref-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let cleanup = callback(&mut machine, record_holding);
        let constructor = global(&machine, "FinalizationRegistry");
        let registry = machine.construct_value(constructor, &[cleanup]).unwrap();
        let target = object(&mut machine);
        let register = method(&mut machine, registry, "register");
        assert!(matches!(
            machine.call_value(register, registry, &[target, target]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        let slot = machine.runtime_slot(registry).unwrap().unwrap();
        let HeapEntry::FinalizationRegistry { cells, .. } = &machine.heap[slot] else {
            panic!("registry entry")
        };
        assert!(cells.is_empty());
    }

    #[test]
    fn callback_throw_is_reported_and_later_holdings_remain_schedulable() {
        let module = blank_program("<weakref-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let cleanup = callback(&mut machine, throwing_cleanup);
        let constructor = global(&machine, "FinalizationRegistry");
        let registry = machine.construct_value(constructor, &[cleanup]).unwrap();
        machine
            .intrinsics
            .globals
            .insert(EcmaString::encode("registry"), registry);
        let register = method(&mut machine, registry, "register");
        for held in [Value::int32(1), Value::int32(2)] {
            let target = object(&mut machine);
            machine
                .call_value(register, registry, &[target, held])
                .unwrap();
        }
        machine.collect_garbage();
        assert_eq!(machine.schedule_finalization_cleanup_jobs().unwrap(), 1);
        let first = machine.drain_microtasks().unwrap();
        assert_eq!(first.executed, 1);
        assert_eq!(first.uncaught.len(), 1);
        assert_eq!(machine.schedule_finalization_cleanup_jobs().unwrap(), 1);
        let second = machine.drain_microtasks().unwrap();
        assert_eq!(second.executed, 1);
        assert_eq!(second.uncaught.len(), 1);
        assert_eq!(machine.schedule_finalization_cleanup_jobs().unwrap(), 0);
    }
    #[test]
    fn queued_cleanup_registry_survives_gc_until_microtask_finishes() {
        let module = blank_program("<weakref-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let cleanup = callback(&mut machine, record_holding);
        let constructor = global(&machine, "FinalizationRegistry");
        let registry = machine.construct_value(constructor, &[cleanup]).unwrap();
        let registry_slot = machine.runtime_slot(registry).unwrap().unwrap();
        machine
            .intrinsics
            .globals
            .insert(EcmaString::encode("registry"), registry);
        let register = method(&mut machine, registry, "register");
        let target = object(&mut machine);
        machine
            .call_value(register, registry, &[target, Value::int32(31)])
            .unwrap();

        machine.collect_garbage();
        machine
            .intrinsics
            .globals
            .remove(&EcmaString::encode("registry"));
        machine.collect_garbage();
        assert!(!matches!(machine.heap[registry_slot], HeapEntry::Vacant));

        assert_eq!(machine.schedule_finalization_cleanup_jobs().unwrap(), 1);
        machine.collect_garbage();
        assert!(!matches!(machine.heap[registry_slot], HeapEntry::Vacant));
        assert_eq!(
            machine.drain_microtasks().unwrap(),
            MicrotaskDrain {
                executed: 1,
                uncaught: Vec::new(),
            }
        );

        machine.collect_garbage();
        assert!(matches!(machine.heap[registry_slot], HeapEntry::Vacant));
    }
}
