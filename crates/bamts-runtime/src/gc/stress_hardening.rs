#![cfg(test)]

use bamts_bytecode::{
    Constant, ConstantId, EcmaString, Function, FunctionFlags, FunctionId, Instruction, Module,
    ModuleId, Program, ProgramModule, Verified,
};
use bamts_native::Value;

use crate::{
    ArrayElementKind, CollectionEntry, CollectionIndex, CollectionKind, HeapEntry, Host, Limits,
    Machine, Property, PropertyKey, PropertyMap, RuntimeErrorKind,
};

#[derive(Default)]
struct TestHost;

impl Host for TestHost {}

struct GcStress<'machine, 'program, H: Host> {
    machine: &'machine mut Machine<'program, H>,
}

impl<'machine, 'program, H: Host> GcStress<'machine, 'program, H> {
    fn new(machine: &'machine mut Machine<'program, H>) -> Self {
        Self { machine }
    }

    fn object(&mut self) -> Value {
        self.machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(self.machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .expect("stress object allocation succeeds")
    }

    fn construct(&mut self, name: &str, arguments: &[Value]) -> Value {
        let constructor = self
            .machine
            .intrinsics
            .global(name)
            .unwrap_or_else(|| panic!("{name} constructor is installed"));
        self.machine
            .construct_value(constructor, arguments)
            .unwrap_or_else(|failure| panic!("constructing {name} succeeds: {failure:?}"))
    }

    fn call_method(&mut self, receiver: Value, name: &str, arguments: &[Value]) -> Value {
        let method = self
            .machine
            .get_named_property(receiver, name)
            .unwrap_or_else(|failure| panic!("reading {name} succeeds: {failure:?}"));
        self.machine
            .call_value(method, receiver, arguments)
            .unwrap_or_else(|failure| panic!("calling {name} succeeds: {failure:?}"))
    }

    fn root(&mut self, name: &str, value: Value) {
        self.machine
            .intrinsics
            .globals
            .insert(EcmaString::encode(name), value);
    }

    fn unroot(&mut self, name: &str) {
        self.machine
            .intrinsics
            .globals
            .remove(&EcmaString::encode(name));
    }

    fn slot(&self, value: Value) -> usize {
        self.machine
            .runtime_slot(value)
            .expect("stress value is a valid runtime reference")
            .expect("stress value has a runtime slot")
    }

    fn assert_live(&self, value: Value) {
        assert!(
            self.machine
                .runtime_slot(value)
                .is_ok_and(|slot| slot.is_some()),
            "expected {value:?} to remain live"
        );
    }

    fn assert_dead(&self, value: Value) {
        assert!(
            matches!(
                self.machine.runtime_slot(value),
                Err(RuntimeErrorKind::InvalidRuntimeHeapReference { .. })
            ),
            "expected {value:?} to be reclaimed"
        );
    }

    fn collect(&mut self) {
        self.machine.collect_garbage();
        self.assert_ledger();
    }

    fn assert_ledger(&self) {
        assert_eq!(self.machine.slot_bytes.len(), self.machine.heap.len());
        assert_eq!(
            self.machine.heap_bytes,
            self.machine.machine_bytes + self.machine.slot_bytes.iter().sum::<usize>()
        );
    }
}

fn blank_program() -> Program<Verified> {
    let code = Module::new(
        vec![Constant::String(EcmaString::encode("<gc-stress>"))],
        vec![Function::new(
            None,
            0,
            0,
            1,
            FunctionFlags::default(),
            vec![Instruction::Halt],
            Vec::new(),
        )],
        FunctionId::new(0),
    )
    .verify()
    .expect("stress module verifies");
    Program::link(
        vec![ProgramModule {
            name: ConstantId::new(0),
            code,
            edges: Vec::new(),
            bindings: Vec::new(),
            exports: Vec::new(),
        }],
        ModuleId::new(0),
    )
    .expect("stress program links")
}

#[test]
fn ephemeron_chain_reaches_a_fixed_point_across_weak_maps() {
    let program = blank_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let mut stress = GcStress::new(&mut machine);

    let first = stress.construct("WeakMap", &[]);
    let second = stress.construct("WeakMap", &[]);
    let first_key = stress.object();
    let second_key = stress.object();
    let terminal = stress.object();
    stress.call_method(first, "set", &[first_key, second_key]);
    stress.call_method(second, "set", &[second_key, terminal]);

    // BTreeMap root order plus the collector's LIFO mark stack visits `second`
    // before `first`, so retaining `terminal` requires another ephemeron round.
    stress.root("first", first);
    stress.root("second", second);
    stress.root("firstKey", first_key);
    stress.collect();

    stress.assert_live(second_key);
    stress.assert_live(terminal);
    assert_eq!(stress.call_method(second, "get", &[second_key]), terminal);
}

#[test]
fn tracing_follows_composed_production_heap_edges() {
    let program = blank_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let mut stress = GcStress::new(&mut machine);

    let map_key = stress.object();
    let map_value = stress.object();
    let map = stress.construct("Map", &[]);
    stress.call_method(map, "set", &[map_key, map_value]);

    let array_property = stress.object();
    let mut array_properties = PropertyMap::default();
    let edge_key = PropertyKey::Named(stress.machine.intern_str("edge"));
    array_properties.insert(
        &mut stress.machine.shapes,
        edge_key,
        Property::Data {
            value: array_property,
            writable: true,
            enumerable: true,
            configurable: true,
        },
    );
    let array = stress
        .machine
        .allocate(HeapEntry::Array {
            kind: ArrayElementKind::for_elements(&[map]),
            elements: vec![map],
            properties: array_properties,
            prototype: Some(stress.machine.intrinsics.array_prototype),
            extensible: true,
            length_writable: true,
        })
        .expect("stress array allocation succeeds");

    let getter_edge = stress.object();
    let setter_edge = stress.object();
    let prototype_edge = stress.object();
    let mut root_properties = PropertyMap::default();
    let data_key = PropertyKey::Named(stress.machine.intern_str("data"));
    root_properties.insert(
        &mut stress.machine.shapes,
        data_key,
        Property::Data {
            value: array,
            writable: true,
            enumerable: true,
            configurable: true,
        },
    );
    let accessor_key = PropertyKey::Named(stress.machine.intern_str("accessor"));
    root_properties.insert(
        &mut stress.machine.shapes,
        accessor_key,
        Property::Accessor {
            getter: Some(getter_edge),
            setter: Some(setter_edge),
            enumerable: true,
            configurable: true,
        },
    );
    let root = stress
        .machine
        .allocate(HeapEntry::Object {
            properties: root_properties,
            prototype: Some(prototype_edge),
            extensible: true,
            boxed_primitive: None,
        })
        .expect("stress root allocation succeeds");
    stress.root("root", root);
    stress.collect();

    for value in [
        array,
        array_property,
        map,
        map_key,
        map_value,
        getter_edge,
        setter_edge,
        prototype_edge,
    ] {
        stress.assert_live(value);
    }
}

#[test]
fn finalization_cleanup_failure_reschedules_remaining_holdings() {
    let program = blank_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let mut stress = GcStress::new(&mut machine);

    // Calling the WeakRef constructor without `new` deterministically throws,
    // making it a host-independent cleanup callback failure.
    let throwing_cleanup = stress
        .machine
        .intrinsics
        .global("WeakRef")
        .expect("WeakRef is installed");
    let registry = stress.construct("FinalizationRegistry", &[throwing_cleanup]);
    stress.root("registry", registry);
    let register = stress
        .machine
        .get_named_property(registry, "register")
        .expect("register is readable");
    for held in [Value::int32(11), Value::int32(22)] {
        let target = stress.object();
        stress
            .machine
            .call_value(register, registry, &[target, held])
            .expect("registration succeeds");
    }

    stress.collect();
    assert_eq!(
        stress.machine.schedule_finalization_cleanup_jobs().unwrap(),
        1
    );
    let first = stress.machine.drain_microtasks().unwrap();
    assert_eq!(first.executed, 1);
    assert_eq!(first.uncaught.len(), 1);

    assert_eq!(
        stress.machine.schedule_finalization_cleanup_jobs().unwrap(),
        1
    );
    let second = stress.machine.drain_microtasks().unwrap();
    assert_eq!(second.executed, 1);
    assert_eq!(second.uncaught.len(), 1);
    assert_eq!(
        stress.machine.schedule_finalization_cleanup_jobs().unwrap(),
        0
    );
}

#[test]
fn weak_ref_target_is_kept_alive_for_exactly_one_job() {
    let program = blank_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let mut stress = GcStress::new(&mut machine);

    let target = stress.object();
    let weak_ref = stress.construct("WeakRef", &[target]);
    // Construction itself keeps the target alive for its current job.
    stress.machine.clear_kept_alive_for_job();
    stress.root("target", target);
    stress.root("weak", weak_ref);
    stress.collect();
    stress.unroot("target");

    let bytes_before_deref = stress.machine.machine_bytes;
    assert_eq!(stress.call_method(weak_ref, "deref", &[]), target);
    assert_eq!(
        stress.machine.machine_bytes,
        bytes_before_deref + std::mem::size_of::<Value>()
    );
    stress.collect();
    stress.assert_live(target);

    stress.machine.clear_kept_alive_for_job();
    assert_eq!(stress.machine.machine_bytes, bytes_before_deref);
    stress.collect();
    stress.assert_dead(target);
    assert_eq!(stress.call_method(weak_ref, "deref", &[]), Value::UNDEFINED);
}

#[test]
fn collections_follow_survivors_without_revisiting_vacant_slots() {
    let program = blank_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let mut stress = GcStress::new(&mut machine);

    let early = stress.object();
    stress.root("early", early);
    let early_garbage = stress.object();
    let early_garbage_slot = stress.machine.runtime_slot(early_garbage).unwrap();
    stress.collect();
    stress.assert_live(early);
    stress.assert_dead(early_garbage);
    let vacant_after_first = stress.machine.vacant_count;

    // A slot from before the last sweep stays tracked, and a later one is
    // picked up, whichever way each one goes.
    let late = stress.object();
    assert_eq!(
        stress.machine.runtime_slot(late).unwrap(),
        early_garbage_slot,
        "a vacated slot is reused before the heap grows"
    );
    stress.root("late", late);
    let late_garbage = stress.object();
    stress.collect();
    stress.assert_live(early);
    stress.assert_live(late);
    stress.assert_dead(late_garbage);
    assert_eq!(stress.machine.vacant_count, vacant_after_first);

    stress.unroot("early");
    stress.collect();
    stress.assert_dead(early);
    stress.assert_live(late);
    assert_eq!(stress.machine.vacant_count, vacant_after_first + 1);

    // Nothing is reclaimed twice once it has gone.
    stress.collect();
    assert_eq!(stress.machine.vacant_count, vacant_after_first + 1);
}

#[test]
fn allocation_pressure_requests_collection_and_a_small_live_set_gets_a_nursery() {
    let program = blank_program();
    let mut host = TestHost;
    let limits = Limits {
        max_heap_bytes: usize::MAX,
        ..Limits::default()
    };
    let mut machine = Machine::new(&program, &mut host, limits);
    let mut stress = GcStress::new(&mut machine);
    let survivor = stress.object();
    stress.root("survivor", survivor);

    let entry = HeapEntry::Object {
        properties: PropertyMap::default(),
        prototype: Some(stress.machine.intrinsics.object_prototype),
        extensible: true,
        boxed_primitive: None,
    };
    let allocation_bytes = entry.initial_bytes(&stress.machine.shapes, &stress.machine.atoms);
    let byte_boundary = stress.machine.heap_bytes + allocation_bytes;
    stress
        .machine
        .set_gc_watermarks_for_test(byte_boundary, usize::MAX);
    assert!(!stress.machine.gc_pending());

    let dead = stress
        .machine
        .allocate(entry)
        .expect("boundary allocation succeeds");
    assert!(stress.machine.gc_pending());
    stress.machine.collect_if_pending();
    stress.assert_ledger();
    stress.assert_dead(dead);
    assert!(!stress.machine.gc_pending());

    for _ in 0..64 {
        stress.object();
    }
    assert!(
        !stress.machine.gc_pending(),
        "a collection that left one live slot must not run again after a handful of allocations"
    );
}

#[test]
fn weak_collection_purge_rebuilds_index_size_and_refunds_exactly() {
    let program = blank_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let mut stress = GcStress::new(&mut machine);

    let weak_map = stress.construct("WeakMap", &[]);
    stress.root("weakMap", weak_map);
    let key = stress.object();
    let value = stress.object();
    let key_slot = stress.slot(key);
    let value_slot = stress.slot(value);
    let weak_map_slot = stress.slot(weak_map);
    let weak_map_base = stress.machine.slot_bytes[weak_map_slot];
    let entry_charge = CollectionEntry::BYTES + CollectionIndex::ENTRY_BYTES;
    stress.call_method(weak_map, "set", &[key, value]);

    let HeapEntry::Collection { entries, size, .. } = &stress.machine.heap[weak_map_slot] else {
        panic!("WeakMap has a collection entry");
    };
    let (size, entry_count) = (*size, entries.len());
    assert_eq!((size, entry_count), (1, 1));
    assert_eq!(
        crate::collection_lookup(stress.machine, weak_map_slot, key),
        Some(0)
    );
    assert_eq!(
        stress.machine.slot_bytes[weak_map_slot],
        weak_map_base + entry_charge
    );
    let before = stress.machine.heap_bytes;
    let reclaimed_slots =
        stress.machine.slot_bytes[key_slot] + stress.machine.slot_bytes[value_slot];

    stress.collect();

    let HeapEntry::Collection {
        entries,
        index,
        size,
        kind: CollectionKind::WeakMap,
        ..
    } = &stress.machine.heap[weak_map_slot]
    else {
        panic!("rooted WeakMap survives collection");
    };
    assert!(entries.is_empty());
    assert_eq!(*size, 0);
    assert!(index.buckets.is_empty());
    assert_eq!(stress.machine.slot_bytes[weak_map_slot], weak_map_base);
    assert_eq!(
        stress.machine.heap_bytes,
        before - reclaimed_slots - entry_charge
    );
    stress.assert_dead(key);
    stress.assert_dead(value);
}

struct XorShift64(u64);

impl XorShift64 {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn below(&mut self, bound: usize) -> usize {
        (self.next() % bound as u64) as usize
    }
}

#[test]
fn reused_slots_keep_prior_values_and_contents() {
    let program = blank_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let mut stress = GcStress::new(&mut machine);

    let mut rng = XorShift64(0x9E37_79B9_7F4A_7C15);
    let mut held: Vec<(String, Value, u64)> = Vec::new();
    let mut next_stamp = 0u64;

    for step in 0..10_000usize {
        match rng.below(10) {
            0..=5 => {
                let value = stress.object();
                let stamp = next_stamp;
                next_stamp += 1;
                stress
                    .machine
                    .set_data_property(value, "stamp", crate::number_value(stamp as f64))
                    .expect("stamping generation succeeds");
                if rng.below(3) == 0 {
                    let name = format!("held{step}");
                    stress.root(&name, value);
                    held.push((name, value, stamp));
                }
            }
            6..=7 => {
                stress.collect();
                for (name, value, expected) in &held {
                    let stamp = stress
                        .machine
                        .get_named_property(*value, "stamp")
                        .expect("reading stamp succeeds");
                    assert_eq!(
                        stamp,
                        crate::number_value(*expected as f64),
                        "held value {name} changed contents"
                    );
                    stress.assert_live(*value);
                }
            }
            _ => {
                if !held.is_empty() {
                    let position = rng.below(held.len());
                    let (name, _, _) = held.swap_remove(position);
                    stress.unroot(&name);
                }
            }
        }
    }
    stress.collect();
    for (name, value, expected) in &held {
        let stamp = stress
            .machine
            .get_named_property(*value, "stamp")
            .expect("reading stamp succeeds");
        assert_eq!(
            stamp,
            crate::number_value(*expected as f64),
            "held value {name} changed contents"
        );
        stress.assert_live(*value);
    }
}

#[test]
fn churn_keeps_peak_heap_slots_bounded() {
    let program = blank_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let mut stress = GcStress::new(&mut machine);

    let mut peak = stress.machine.heap.len();
    let mut survivors: Vec<Value> = Vec::new();
    for i in 0..100_000usize {
        let value = stress.object();
        if i % 1000 == 0 {
            survivors.push(value);
            stress.root(&format!("survivor{i}"), value);
        }
        if i % 512 == 0 {
            stress.collect();
            peak = peak.max(stress.machine.heap.len());
        }
    }
    stress.collect();
    peak = peak.max(stress.machine.heap.len());
    assert!(
        peak < 5_000,
        "peak heap slots {peak} reached the churn bound"
    );
    for value in &survivors {
        stress.assert_live(*value);
    }
}
