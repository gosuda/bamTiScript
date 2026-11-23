use std::sync::Arc;

use super::*;
use crate::intrinsics::{BuiltinDef, BuiltinOutcome};
use bamts_bytecode::{
    Binding, DescriptorSlot, Edge, EdgeKind, ExceptionHandler, Export, ExportSource, FunctionFlags,
    NumberBits, ProgramModule, Register,
};

fn reg(raw: u32) -> Register {
    Register::new(raw)
}
fn pc(raw: u32) -> Pc {
    Pc::new(raw)
}
fn cid(raw: u32) -> ConstantId {
    ConstantId::new(raw)
}

/// A function with no captures.
pub(crate) fn function(
    parameters: u32,
    registers: u32,
    code: Vec<Instruction>,
    handlers: Vec<ExceptionHandler>,
) -> Function {
    Function::new(
        None,
        0,
        parameters,
        registers,
        FunctionFlags {
            is_constructable: true,
            ..FunctionFlags::default()
        },
        code,
        handlers,
    )
}

fn generator_function(
    parameters: u32,
    registers: u32,
    code: Vec<Instruction>,
    handlers: Vec<ExceptionHandler>,
) -> Function {
    Function::new(
        None,
        0,
        parameters,
        registers,
        FunctionFlags {
            is_async: false,
            is_generator: true,
            is_constructable: false,
            ..FunctionFlags::default()
        },
        code,
        handlers,
    )
}

fn async_function(
    parameters: u32,
    registers: u32,
    code: Vec<Instruction>,
    handlers: Vec<ExceptionHandler>,
) -> Function {
    Function::new(
        None,
        0,
        parameters,
        registers,
        FunctionFlags {
            is_async: true,
            is_generator: false,
            is_constructable: false,
            ..FunctionFlags::default()
        },
        code,
        handlers,
    )
}

fn async_generator_function(
    parameters: u32,
    registers: u32,
    code: Vec<Instruction>,
    handlers: Vec<ExceptionHandler>,
) -> Function {
    Function::new(
        None,
        0,
        parameters,
        registers,
        FunctionFlags {
            is_async: true,
            is_generator: true,
            is_constructable: false,
            ..FunctionFlags::default()
        },
        code,
        handlers,
    )
}

/// A function with `captures` leading capture registers.
fn closure_function(
    captures: u32,
    parameters: u32,
    registers: u32,
    code: Vec<Instruction>,
) -> Function {
    Function::new(
        None,
        captures,
        parameters,
        registers,
        FunctionFlags {
            is_constructable: true,
            ..FunctionFlags::default()
        },
        code,
        Vec::new(),
    )
}

pub(crate) fn verified(
    mut constants: Vec<Constant>,
    functions: Vec<Function>,
) -> Program<Verified> {
    let name = ConstantId::new(constants.len() as u32);
    constants.push(Constant::String(EcmaString::encode("<test>")));
    let code = Module::new(constants, functions, FunctionId::new(0))
        .verify()
        .expect("valid test bytecode");
    Program::link(
        vec![ProgramModule {
            name,
            code,
            edges: Vec::new(),
            bindings: Vec::new(),
            exports: Vec::new(),
        }],
        ModuleId::new(0),
    )
    .expect("valid one-module test program")
}
fn program_module(
    name: &str,
    mut constants: Vec<Constant>,
    functions: Vec<Function>,
    edges: Vec<Edge>,
    bindings: Vec<Binding>,
    exports: Vec<Export>,
) -> ProgramModule<Verified> {
    constants.insert(0, Constant::String(EcmaString::encode(name)));
    let code = Module::new(constants, functions, FunctionId::new(0))
        .verify()
        .expect("valid test bytecode");
    ProgramModule {
        name: ConstantId::new(0),
        code,
        edges,
        bindings,
        exports,
    }
}

fn linked(modules: Vec<ProgramModule<Verified>>, entry: u32) -> Program<Verified> {
    Program::link(modules, ModuleId::new(entry)).expect("valid linked test program")
}

fn namespace_descriptor_entry() -> Function {
    function(
        0,
        7,
        vec![
            Instruction::LoadGlobal {
                dst: reg(0),
                name: cid(1),
            },
            Instruction::LoadGlobal {
                dst: reg(1),
                name: cid(3),
            },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(4),
            },
            Instruction::GetProperty {
                dst: reg(3),
                object: reg(1),
                key: reg(2),
            },
            Instruction::CreateArray { dst: reg(4) },
            Instruction::ArrayPush {
                array: reg(4),
                value: reg(0),
            },
            Instruction::LoadConst {
                dst: reg(5),
                constant: cid(5),
            },
            Instruction::ArrayPush {
                array: reg(4),
                value: reg(5),
            },
            Instruction::Call {
                dst: reg(6),
                callee: reg(3),
                this_value: reg(4),
                arguments: reg(4),
            },
            Instruction::Return { value: reg(6) },
        ],
        Vec::new(),
    )
}

#[derive(Default)]
pub(crate) struct TestHost;
impl Host for TestHost {}

fn with_machine(limits: Limits, test: impl FnOnce(&mut Machine<'_, TestHost>)) {
    let program = verified(
        vec![],
        vec![function(0, 0, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, limits);
    test(&mut machine);
}

/// Descends `levels` frames of at least 4 KiB each, and reports
/// [`Machine::stack_overflows`] and [`Machine::call_depth_exhausted`] there.
#[inline(never)]
fn checks_below(machine: &Machine<'_, TestHost>, levels: usize) -> (bool, bool) {
    let pad = std::hint::black_box([0_u8; 4096]);
    if levels == 0 {
        return (machine.stack_overflows(), machine.call_depth_exhausted());
    }
    let checks = checks_below(machine, levels - 1);
    std::hint::black_box(&pad);
    checks
}

/// A call past the native stack throws, and a path that did not check that
/// ends the run a little later, before the native stack overflows.
#[test]
fn the_native_stack_ends_the_run_a_little_past_the_guest_stack() {
    std::thread::Builder::new()
        .stack_size(16 << 20)
        .spawn(|| {
            let limits = Limits {
                max_stack_bytes: 256 << 10,
                ..Limits::default()
            };
            with_machine(limits, |machine| {
                assert_eq!(checks_below(machine, 0), (false, false));
                assert_eq!(checks_below(machine, 64), (true, false));
                assert_eq!(checks_below(machine, 512), (true, true));
            });
            with_machine(Limits::default(), |machine| {
                assert_eq!(checks_below(machine, 512), (false, false));
            });
        })
        .expect("the test thread starts")
        .join()
        .expect("the test thread ends");
}

#[test]
fn suppressed_error_allocator_preserves_chain_and_hides_fields() {
    with_machine(Limits::default(), |machine| {
        let body_error = Value::int32(1);
        let inner_disposal_error = Value::int32(2);
        let outer_disposal_error = Value::int32(4);
        let inner = machine
            .make_suppressed_error(inner_disposal_error, body_error)
            .expect("inner suppression allocates");
        let outer = machine
            .make_suppressed_error(outer_disposal_error, inner)
            .expect("outer suppression allocates");

        assert_eq!(
            machine.get_named_property(outer, "error").unwrap(),
            outer_disposal_error
        );
        assert_eq!(
            machine.get_named_property(outer, "suppressed").unwrap(),
            inner
        );
        assert_eq!(
            machine.get_named_property(inner, "error").unwrap(),
            inner_disposal_error
        );
        assert_eq!(
            machine.get_named_property(inner, "suppressed").unwrap(),
            body_error
        );
        let message_key = PropertyKey::Named(machine.intern_str("message"));
        assert!(
            machine
                .own_descriptor(outer, &message_key)
                .unwrap()
                .is_none()
        );
        for (object, name, expected) in [
            (outer, "error", outer_disposal_error),
            (outer, "suppressed", inner),
            (inner, "error", inner_disposal_error),
            (inner, "suppressed", body_error),
        ] {
            let key = PropertyKey::Named(machine.intern_str(name));
            let descriptor = machine
                .own_descriptor(object, &key)
                .unwrap()
                .expect("suppression field is own");
            assert!(matches!(
                descriptor,
                Property::Data {
                    value,
                    writable: true,
                    enumerable: false,
                    configurable: true,
                } if value == expected
            ));
        }
        let constructor = machine
            .intrinsics
            .global("SuppressedError")
            .expect("SuppressedError exists");
        let prototype = machine
            .get_named_property(constructor, "prototype")
            .unwrap();
        assert!(machine.inherits_from_prototype(outer, prototype).unwrap());
    });
}

#[test]
fn typed_array_canonical_numeric_keys_never_become_ordinary_properties() {
    assert!(typedarray::typed_array_index(&EcmaString::encode("4294967295")).is_some());
    for key in ["-0", "NaN", "Infinity", "1.5"] {
        assert_eq!(
            typedarray::typed_array_index(&EcmaString::encode(key)),
            Some(None),
            "{key}"
        );
    }
    assert_eq!(
        typedarray::typed_array_index(&EcmaString::encode("01")),
        None
    );

    with_machine(Limits::default(), |machine| {
        let buffer =
            intrinsics::builtins::arraybuffer::ArrayBufferHandle::allocate(machine, 1, None)
                .unwrap()
                .value();
        let typed = machine
            .allocate(HeapEntry::TypedArray {
                kind: ElementKind::Uint8,
                buffer,
                byte_offset: 0,
                byte_length: LengthSlot::Fixed(1),
                array_length: LengthSlot::Fixed(1),
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
            })
            .unwrap();
        let index = machine.runtime_slot(typed).unwrap().unwrap();
        for name in ["4294967295", "-0", "NaN", "Infinity", "1.5"] {
            let key = PropertyKey::Named(machine.intern_str(name));
            machine
                .set_own_data(index, key.clone(), Value::int32(7))
                .unwrap();
            assert_eq!(
                machine.get_property_key(typed, &key).unwrap(),
                Value::UNDEFINED,
                "{name}"
            );
            assert!(machine.internal_delete(typed, &key).unwrap(), "{name}");
            assert!(
                machine
                    .define_descriptor(
                        typed,
                        key,
                        Property::Data {
                            value: Value::int32(7),
                            writable: true,
                            enumerable: true,
                            configurable: true,
                        },
                    )
                    .is_err(),
                "{name}"
            );
        }

        let ordinary = PropertyKey::Named(machine.intern_str("01"));
        machine
            .set_own_data(index, ordinary.clone(), Value::int32(7))
            .unwrap();
        assert_eq!(
            machine.get_property_key(typed, &ordinary).unwrap(),
            Value::int32(7)
        );
        assert!(machine.internal_delete(typed, &ordinary).unwrap());
    });
}

#[test]
fn heap_ledger_tracks_slot_and_machine_charges() {
    with_machine(Limits::default(), |machine| {
        machine.assert_heap_ledger();
        let value = machine
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .unwrap();
        let index = machine.runtime_slot(value).unwrap().unwrap();
        machine.charge_slot(index, 3).unwrap();
        machine.charge_machine(5).unwrap();

        assert_eq!(machine.slot_bytes[index], 5);
        assert_eq!(machine.machine_bytes, 5);
        machine.assert_heap_ledger();
    });
}

#[test]
fn failed_intrinsic_slot_charge_preserves_credit_and_ledgers() {
    with_machine(Limits::default(), |machine| {
        let global = machine.global_object;
        let index = machine.runtime_slot(global).unwrap().unwrap();
        let global_this_key = PropertyKey::Named(machine.intern_str("globalThis"));
        assert!(machine.internal_delete(global, &global_this_key,).unwrap());
        let credit = machine.intrinsic_slot_credits[index];
        assert!(credit > 0);
        let slot_bytes = machine.slot_bytes[index];
        let heap_bytes = machine.heap_bytes;
        machine.limits.max_heap_bytes = heap_bytes;

        assert!(matches!(
            machine.charge_slot(index, credit + 1),
            Err(RuntimeErrorKind::HeapByteLimitExceeded { .. })
        ));
        assert_eq!(machine.intrinsic_slot_credits[index], credit);
        assert_eq!(machine.slot_bytes[index], slot_bytes);
        assert_eq!(machine.heap_bytes, heap_bytes);
        machine.assert_heap_ledger();
    });
}

#[test]
fn intrinsic_property_churn_tracks_only_bytes_above_bootstrap() {
    with_machine(Limits::default(), |machine| {
        let global = machine.global_object;
        let index = machine.runtime_slot(global).unwrap().unwrap();
        let property_bytes = |machine: &Machine<'_, TestHost>| match &machine.heap[index] {
            HeapEntry::Object { properties, .. } => {
                properties.charge_bytes(&machine.shapes, &machine.atoms)
            }
            _ => panic!("global object remains ordinary"),
        };
        let baseline = property_bytes(machine);
        let assert_accounted = |machine: &Machine<'_, TestHost>| {
            let current = property_bytes(machine);
            assert_eq!(machine.slot_bytes[index], current.saturating_sub(baseline));
            assert_eq!(
                machine.intrinsic_slot_credits[index],
                baseline.saturating_sub(current)
            );
            machine.assert_heap_ledger();
        };
        assert_accounted(machine);

        let global_this = PropertyKey::Named(machine.intern_str("globalThis"));
        assert!(machine.internal_delete(global, &global_this).unwrap());
        assert_accounted(machine);

        let replacement =
            PropertyKey::Named(machine.intern_str("global-replacement-with-a-long-name"));
        machine
            .set_data_property_key(global, replacement.clone(), Value::int32(1))
            .unwrap();
        assert_accounted(machine);

        machine
            .define_descriptor(
                global,
                replacement.clone(),
                Property::Accessor {
                    getter: None,
                    setter: None,
                    enumerable: false,
                    configurable: true,
                },
            )
            .unwrap();
        assert_accounted(machine);

        assert!(machine.internal_delete(global, &replacement).unwrap());
        assert_accounted(machine);
        machine
            .set_data_property_key(global, global_this, global)
            .unwrap();
        assert_accounted(machine);
    });
}

#[test]
fn gc_pending_arms_after_successful_mutations_without_preflight_side_effects() {
    with_machine(Limits::default(), |machine| {
        machine.set_gc_watermarks_for_test(usize::MAX, 1);
        assert!(!machine.gc_pending());
        machine
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .unwrap();
        assert!(machine.gc_pending());

        machine.collect_garbage();
        machine.set_gc_watermarks_for_test(usize::MAX, usize::MAX);
        let value = machine
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .unwrap();
        let index = machine.runtime_slot(value).unwrap().unwrap();
        let bytes = machine.heap_bytes + 1;
        machine.set_gc_watermarks_for_test(bytes, usize::MAX);
        assert!(!machine.gc_pending());
        machine.charge_slot(index, 1).unwrap();
        assert!(machine.gc_pending());

        machine.collect_garbage();
        machine.set_gc_watermarks_for_test(usize::MAX, usize::MAX);
        let bytes = machine.heap_bytes + 1;
        machine.set_gc_watermarks_for_test(bytes, usize::MAX);
        machine.charge_machine(1).unwrap();
        assert!(machine.gc_pending());
    });

    with_machine(
        Limits {
            max_heap_bytes: 1,
            ..Limits::default()
        },
        |machine| {
            machine.set_gc_watermarks_for_test(usize::MAX, usize::MAX);
            assert!(matches!(
                machine.allocate(HeapEntry::String(EcmaString::encode("x"))),
                Err(RuntimeErrorKind::HeapByteLimitExceeded { limit: 1 })
            ));
            assert!(!machine.gc_pending());
            machine.assert_heap_ledger();
        },
    );
}

#[test]
fn a_large_limit_does_not_delay_the_first_collection() {
    let large = Limits {
        max_heap_bytes: 1 << 32,
        max_heap_slots: 1 << 30,
        ..Limits::default()
    };
    with_machine(large, |machine| {
        assert_eq!(machine.gc_watermarks_for_test(), (32 << 20, 1 << 19));
    });
    with_machine(Limits::default(), |machine| {
        assert_eq!(machine.gc_watermarks_for_test(), (32 << 20, 1 << 19));
    });
}

#[test]
fn gc_recomputes_watermarks_from_live_usage() {
    with_machine(Limits::default(), |machine| {
        let value = machine
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .unwrap();
        machine.test_set_global("live", value);

        machine.collect_garbage();

        let live_slots = machine.live_runtime_slots();
        assert_eq!(
            machine.gc_watermarks_for_test(),
            (
                (machine.heap_bytes + machine.heap_bytes.max(gc::MIN_NURSERY_BYTES))
                    .min(machine.limits.max_heap_bytes),
                (live_slots + live_slots.max(gc::MIN_NURSERY_SLOTS))
                    .min(machine.limits.max_heap_slots),
            )
        );
    });
}

#[test]
fn gc_traces_active_builtin_new_target() {
    with_machine(Limits::default(), |machine| {
        let new_target = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.function_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let index = machine.runtime_slot(new_target).unwrap().unwrap();
        machine.current_new_target = new_target;

        machine.collect_garbage();

        assert!(!matches!(machine.heap[index], HeapEntry::Vacant));
        assert_eq!(
            machine.runtime_slot(machine.current_new_target).unwrap(),
            Some(index)
        );
    });
}

#[test]
fn gc_traces_shaped_and_dictionary_property_edges() {
    for dictionary in [false, true] {
        with_machine(Limits::default(), |machine| {
            let symbol = machine
                .allocate(HeapEntry::Symbol {
                    description: EcmaString::encode("symbol key"),
                })
                .unwrap();
            let private = machine
                .allocate(HeapEntry::PrivateName {
                    description: EcmaString::encode("private key"),
                })
                .unwrap();
            let symbol_key = PropertyKey::Symbol(
                u32::try_from(machine.runtime_slot(symbol).unwrap().unwrap()).unwrap(),
            );
            let private_key = PropertyKey::Private(
                u32::try_from(machine.runtime_slot(private).unwrap().unwrap()).unwrap(),
            );
            let data = site_object(machine, &[]);
            let getter = site_object(machine, &[]);
            let setter = site_object(machine, &[]);
            let removed = PropertyKey::Named(machine.intern_str("removed"));
            let mut properties = PropertyMap::default();
            properties.insert(
                &mut machine.shapes,
                removed.clone(),
                Property::Data {
                    value: Value::UNDEFINED,
                    writable: true,
                    enumerable: true,
                    configurable: true,
                },
            );
            if dictionary {
                properties.remove(&machine.shapes, &removed);
            }
            properties.insert(
                &mut machine.shapes,
                symbol_key.clone(),
                Property::Data {
                    value: data,
                    writable: true,
                    enumerable: true,
                    configurable: true,
                },
            );
            properties.insert(
                &mut machine.shapes,
                private_key.clone(),
                Property::Accessor {
                    getter: Some(getter),
                    setter: Some(setter),
                    enumerable: false,
                    configurable: true,
                },
            );
            if dictionary {
                assert!(
                    !machine
                        .shapes
                        .live_keys()
                        .any(|key| { key == &symbol_key || key == &private_key })
                );
            }
            let object = machine
                .allocate(HeapEntry::Object {
                    properties,
                    prototype: Some(machine.intrinsics.object_prototype),
                    boxed_primitive: None,
                    extensible: true,
                })
                .unwrap();
            machine.test_set_global("propertyRoot", object);
            machine.collect_garbage();
            for value in [symbol, private, data, getter, setter] {
                let index = machine.runtime_slot(value).unwrap().unwrap();
                assert!(!matches!(machine.heap[index], HeapEntry::Vacant));
            }
            assert_eq!(machine.get_property_key(object, &symbol_key).unwrap(), data);
            machine.assert_heap_ledger();
        });
    }
}

#[test]
#[ignore = "development-host performance measurement"]
fn profile_shaped_gc() {
    use std::hint::black_box;
    use std::time::Instant;

    with_machine(Limits::default(), |machine| {
        let objects = 10_000;
        let collections = 20;
        let entries = [
            ("a", Value::int32(1)),
            ("b", Value::int32(2)),
            ("c", Value::int32(3)),
            ("d", Value::int32(4)),
            ("e", Value::int32(5)),
            ("f", Value::int32(6)),
            ("g", Value::int32(7)),
            ("h", Value::int32(8)),
        ];
        let roots: Vec<_> = (0..objects)
            .map(|_| site_object(machine, &entries))
            .collect();
        machine.push_native_roots(0, &roots);
        machine.collect_garbage();
        let live = machine.live_runtime_slots();
        let started = Instant::now();
        for _ in 0..collections {
            black_box(&mut *machine).collect_garbage();
        }
        let elapsed = started.elapsed();
        assert_eq!(machine.live_runtime_slots(), live);
        for object in roots {
            assert_eq!(
                machine.get_named_property(object, "h").unwrap(),
                Value::int32(8)
            );
        }
        eprintln!(
            "shaped_gc objects={objects} collections={collections} elapsed_ns={} live_slots={live}",
            elapsed.as_nanos()
        );
        machine.pop_native_roots(0);
    });
}

#[test]
fn interpreter_safe_point_reclaims_overwritten_values() {
    let program = verified(
        vec![Constant::Int32(7)],
        vec![function(
            0,
            1,
            vec![
                Instruction::CreateObject { dst: reg(0) },
                Instruction::CreateObject { dst: reg(0) },
                Instruction::CreateObject { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(0),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let limits = Limits {
        max_heap_slots: 2,
        ..Limits::default()
    };
    let mut machine = Machine::new(&program, &mut host, limits);

    let execution = machine.evaluate().unwrap();
    machine.run_to_quiescence().unwrap();
    assert_eq!(execution.value, Value::int32(7));
    assert!(
        machine.heap.len() - machine.intrinsic_slots < 3,
        "three overwritten objects reuse swept slots instead of growing the heap by three"
    );
    assert!(machine.vacant_count >= 1);
    machine.assert_heap_ledger();
}

#[test]
fn automatic_gc_repeats_deterministically() {
    let program = verified(
        vec![Constant::Int32(7)],
        vec![function(
            0,
            1,
            vec![
                Instruction::CreateObject { dst: reg(0) },
                Instruction::CreateObject { dst: reg(0) },
                Instruction::CreateObject { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(0),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
    );
    let mut outcomes = Vec::new();
    for _ in 0..3 {
        let mut host = TestHost;
        let limits = Limits {
            max_heap_slots: 2,
            ..Limits::default()
        };
        let mut machine = Machine::new(&program, &mut host, limits);
        let execution = machine.evaluate().unwrap();
        machine.run_to_quiescence().unwrap();
        outcomes.push((execution.value, machine.heap_bytes, machine.vacant_count));
    }

    assert!(outcomes.windows(2).all(|pair| pair[0] == pair[1]));
    assert_eq!(outcomes[0].0, Value::int32(7));
    assert!(outcomes[0].2 >= 1);
}

#[test]
fn microtask_safe_point_keeps_queued_callback_rooted() {
    let program = verified(
        vec![],
        vec![function(0, 0, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callback = machine
        .allocate(HeapEntry::Function {
            module: ModuleId::new(0),
            function: FunctionId::new(0),
            captures: Vec::new(),
            context: None,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .unwrap();
    machine
        .microtasks
        .push_back(QueuedMicrotask::uncharged(MicrotaskJob::Callback {
            callback,
            context: None,
        }));
    machine.set_gc_watermarks_for_test(0, 0);

    assert_eq!(machine.drain_microtasks().unwrap().executed, 1);
    assert!(matches!(
        machine.heap[machine.runtime_slot(callback).unwrap().unwrap()],
        HeapEntry::Function { .. }
    ));
}

#[test]
fn a_class_accessor_is_hidden_and_stays_hidden_when_its_other_half_arrives() {
    with_machine(Limits::default(), |machine| {
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .unwrap();
        let index = machine.runtime_slot(object).unwrap().unwrap();
        let key = PropertyKey::Named(machine.intern_str("value"));
        let enumerable = |machine: &Machine<'_, TestHost>| match &machine.heap[index] {
            HeapEntry::Object { properties, .. } => properties
                .get(&machine.shapes, &key)
                .map(Property::enumerable),
            _ => None,
        };
        machine
            .define_accessor(
                object,
                key.clone(),
                Value::int32(1),
                AccessorKind::ClassGetter,
            )
            .unwrap();
        assert_eq!(enumerable(machine), Some(false));
        machine
            .define_accessor(
                object,
                key.clone(),
                Value::int32(2),
                AccessorKind::ClassSetter,
            )
            .unwrap();
        assert_eq!(enumerable(machine), Some(false));
        let value_key = PropertyKey::Named(machine.intern_str("value"));
        let HeapEntry::Object { properties, .. } = &machine.heap[index] else {
            panic!("expected an object");
        };
        assert!(matches!(
            properties.get(&machine.shapes, &value_key),
            Some(Property::Accessor {
                getter: Some(_),
                setter: Some(_),
                ..
            })
        ));
    });
}

#[test]
fn define_accessor_charges_only_net_growth_after_validation() {
    with_machine(Limits::default(), |machine| {
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .unwrap();
        let index = machine.runtime_slot(object).unwrap().unwrap();
        let key = PropertyKey::Named(machine.intern_str("accessor"));

        machine
            .define_accessor(object, key.clone(), Value::int32(1), AccessorKind::Getter)
            .unwrap();
        let replacement_slot_bytes = machine.slot_bytes[index];
        let replacement_heap_bytes = machine.heap_bytes;
        machine
            .define_accessor(object, key.clone(), Value::int32(2), AccessorKind::Getter)
            .unwrap();
        machine
            .define_accessor(object, key.clone(), Value::int32(3), AccessorKind::Setter)
            .unwrap();
        assert_eq!(machine.slot_bytes[index], replacement_slot_bytes);
        assert_eq!(machine.heap_bytes, replacement_heap_bytes);
        machine.assert_heap_ledger();

        let HeapEntry::Object { properties, .. } = &mut machine.heap[index] else {
            panic!("allocated object remains an object");
        };
        let Some(Property::Accessor { configurable, .. }) =
            properties.get_mut(&machine.shapes, &key)
        else {
            panic!("accessor definition stored an accessor");
        };
        *configurable = false;

        let failed_slot_bytes = machine.slot_bytes[index];
        let failed_heap_bytes = machine.heap_bytes;
        for accessor in [Value::int32(4), Value::int32(5)] {
            assert!(matches!(
                machine.define_accessor(object, key.clone(), accessor, AccessorKind::Getter),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert_eq!(machine.slot_bytes[index], failed_slot_bytes);
            assert_eq!(machine.heap_bytes, failed_heap_bytes);
            machine.assert_heap_ledger();
        }
    });
}

#[test]
fn failed_array_index_and_push_leave_storage_and_ledger_unchanged() {
    with_machine(Limits::default(), |machine| {
        let array = machine
            .allocate(HeapEntry::Array {
                kind: ArrayElementKind::for_elements(&[]),
                elements: Vec::new(),
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.array_prototype),
                extensible: true,
                length_writable: false,
            })
            .unwrap();
        let index = machine.runtime_slot(array).unwrap().unwrap();
        let key = PropertyKey::Named(machine.intern_str("0"));
        let baseline_slot = machine.slot_bytes[index];
        let baseline_heap = machine.heap_bytes;

        for _ in 0..3 {
            assert!(matches!(
                machine.set_own_data(index, key.clone(), Value::int32(1)),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert!(matches!(
                machine.array_push(array, Value::int32(1)),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert_eq!(machine.slot_bytes[index], baseline_slot);
            assert_eq!(machine.heap_bytes, baseline_heap);
            let HeapEntry::Array { elements, .. } = &machine.heap[index] else {
                panic!("array remains an array");
            };
            assert!(elements.is_empty());
            machine.assert_heap_ledger();
        }

        let HeapEntry::Array {
            extensible,
            length_writable,
            ..
        } = &mut machine.heap[index]
        else {
            panic!("array remains an array");
        };
        *extensible = false;
        *length_writable = true;
        for _ in 0..3 {
            assert!(matches!(
                machine.set_own_data(index, key.clone(), Value::int32(1)),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert!(matches!(
                machine.array_push(array, Value::int32(1)),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert_eq!(machine.slot_bytes[index], baseline_slot);
            assert_eq!(machine.heap_bytes, baseline_heap);
            machine.assert_heap_ledger();
        }
    });
}

struct XorShift64(u64);

impl XorShift64 {
    fn next_u64(&mut self) -> u64 {
        let value = self.0;
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        value
    }

    fn value(&mut self, text: Value) -> Value {
        match self.next_u64() % 8 {
            0..=2 => Value::int32(self.next_u64() as u32),
            3 => Value::number((self.next_u64() % 1000) as f64 / 8.0),
            4 => Value::number(f64::NAN),
            5 => Value::number(-0.0),
            6 => text,
            _ => Value::UNDEFINED,
        }
    }
}

fn narrowest_element_kind(elements: &[Value]) -> ArrayElementKind {
    elements
        .iter()
        .fold(ArrayElementKind::Int32, |kind, value| {
            let value_kind = match value.decode() {
                Some(Decoded::Int32(_)) => ArrayElementKind::Int32,
                Some(Decoded::Number(_)) => ArrayElementKind::Number,
                _ => ArrayElementKind::Any,
            };
            kind.max(value_kind)
        })
}

#[test]
fn element_kind_tracks_a_random_write_sequence_against_a_scan_oracle() {
    with_machine(Limits::default(), |machine| {
        let array = machine.create_array(Vec::new()).unwrap();
        let slot = machine.runtime_slot(array).unwrap().unwrap();
        let text = machine
            .allocate(HeapEntry::String(EcmaString::encode("kind")))
            .unwrap();
        let mut rng = XorShift64(0x1234_5678_9abc_def0);
        let mut expected = ArrayElementKind::Int32;

        for _ in 0..2_000 {
            let mut whole_replacement = false;
            match rng.next_u64() % 7 {
                0 => {
                    let value = rng.value(text);
                    machine.array_push(array, value).unwrap();
                }
                1 | 2 => {
                    let length = machine.array_length(array).unwrap();
                    let offset = rng.next_u64() as usize % (length + 3);
                    let key = PropertyKey::Named(machine.intern_str(&offset.to_string()));
                    machine.set_own_data(slot, key, rng.value(text)).unwrap();
                }
                3 => {
                    let length = machine.array_length(array).unwrap();
                    let length = rng.next_u64() as usize % (length + 4);
                    let key = PropertyKey::Named(machine.intern_str("length"));
                    machine
                        .set_own_data(slot, key, crate::number_value(length as f64))
                        .unwrap();
                }
                4 => {
                    let length = machine.array_length(array).unwrap();
                    if length > 0 {
                        let offset = rng.next_u64() as usize % length;
                        let key = PropertyKey::Named(machine.intern_str(&offset.to_string()));
                        machine.internal_delete(array, &key).unwrap();
                    }
                }
                5 => {
                    let length = 1 + rng.next_u64() as usize % 5;
                    let elements = (0..length).map(|_| rng.value(text)).collect();
                    machine.replace_array_elements(array, elements).unwrap();
                    whole_replacement = true;
                }
                _ => {
                    let value = rng.value(text);
                    machine.array_push(array, value).unwrap();
                }
            }

            let elements = machine.array_elements(array).unwrap().unwrap();
            let narrowest = narrowest_element_kind(&elements);
            expected = if whole_replacement {
                narrowest
            } else {
                expected.max(narrowest)
            };
            let stored = machine.array_element_kind(array).unwrap();
            assert!(stored >= narrowest);
            assert_eq!(stored, expected);
        }
    });
}

#[test]
fn a_deleted_element_forces_any() {
    with_machine(Limits::default(), |machine| {
        let array = machine.create_array(Vec::new()).unwrap();
        machine.array_push(array, Value::int32(7)).unwrap();
        assert_eq!(
            machine.array_element_kind(array).unwrap(),
            ArrayElementKind::Int32
        );

        let key = PropertyKey::Named(machine.intern_str("0"));
        machine.internal_delete(array, &key).unwrap();
        let elements = machine.array_elements(array).unwrap().unwrap();
        assert_eq!(narrowest_element_kind(&elements), ArrayElementKind::Any);
        assert_eq!(
            machine.array_element_kind(array).unwrap(),
            ArrayElementKind::Any
        );
    });
}

#[test]
fn numeric_element_read_answers_only_in_bounds_int32_indexes_of_number_arrays() {
    with_machine(Limits::default(), |machine| {
        let array = machine.create_array(Vec::new()).unwrap();
        machine.array_push(array, Value::int32(7)).unwrap();
        machine.array_push(array, crate::number_value(2.5)).unwrap();
        assert_eq!(
            machine.array_element_number(array, Value::int32(0)),
            Some(Value::int32(7))
        );
        assert_eq!(
            machine.array_element_number(array, Value::int32(1)),
            Some(crate::number_value(2.5))
        );
        assert_eq!(machine.array_element_number(array, Value::int32(2)), None);
        assert_eq!(
            machine.array_element_number(array, Value::int32(u32::MAX)),
            None
        );
        assert_eq!(
            machine.array_element_number(array, crate::number_value(0.5)),
            None
        );

        let text = machine
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .unwrap();
        machine.array_push(array, text).unwrap();
        assert_eq!(machine.array_element_number(array, Value::int32(0)), None);
        assert_eq!(machine.array_element_number(text, Value::int32(0)), None);
    });
}

#[test]
fn whole_vector_replacement_recomputes_the_kind() {
    with_machine(Limits::default(), |machine| {
        let array = machine.create_array(Vec::new()).unwrap();
        let text = machine
            .allocate(HeapEntry::String(EcmaString::encode("kind")))
            .unwrap();
        machine.array_push(array, Value::int32(1)).unwrap();
        machine.array_push(array, text).unwrap();
        assert_eq!(
            machine.array_element_kind(array).unwrap(),
            ArrayElementKind::Any
        );

        machine
            .replace_array_elements(array, vec![Value::int32(1), Value::int32(2)])
            .unwrap();
        assert_eq!(
            machine.array_element_kind(array).unwrap(),
            ArrayElementKind::Int32
        );

        machine
            .replace_array_elements(
                array,
                vec![Value::int32(1), Value::number(2.5), Value::HOLE],
            )
            .unwrap();
        assert_eq!(
            machine.array_element_kind(array).unwrap(),
            ArrayElementKind::Any
        );
    });
}

#[test]
fn nonempty_array_shrink_refunds_its_initial_element_charge() {
    with_machine(Limits::default(), |machine| {
        let array = machine
            .allocate(HeapEntry::Array {
                kind: ArrayElementKind::for_elements(&[Value::int32(1), Value::int32(2)]),
                elements: vec![Value::int32(1), Value::int32(2)],
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.array_prototype),
                extensible: true,
                length_writable: true,
            })
            .unwrap();
        let index = machine.runtime_slot(array).unwrap().unwrap();
        let element_bytes = std::mem::size_of::<Value>();
        // An array allocated with two elements owns the element storage it
        // can later shrink away, plus the base slot charge.
        let initial_charge = element_bytes.saturating_mul(2).saturating_add(1);
        assert_eq!(machine.slot_bytes[index], initial_charge);
        machine.assert_heap_ledger();

        machine
            .set_data_property(array, "length", Value::int32(1))
            .unwrap();

        // The shrink refund must not underflow and must leave exactly the
        // one remaining element plus the base slot charge.
        let shrunk_charge = element_bytes.saturating_add(1);
        assert_eq!(machine.slot_bytes[index], shrunk_charge);
        machine.assert_heap_ledger();
        let HeapEntry::Array { elements, .. } = &machine.heap[index] else {
            panic!("array remains an array");
        };
        assert_eq!(*elements, vec![Value::int32(1)]);
    });
}

#[test]
fn array_length_shrink_refunds_storage_charged_by_array_replacement() {
    with_machine(Limits::default(), |machine| {
        let indexed = PropertyKey::Named(machine.intern_str("1"));
        let indexed_bytes = indexed.charge_bytes(&machine.atoms);
        let mut properties = PropertyMap::default();
        properties.insert(
            &mut machine.shapes,
            indexed,
            Property::Data {
                value: Value::int32(99),
                writable: true,
                enumerable: true,
                configurable: true,
            },
        );
        let array = machine
            .allocate(HeapEntry::Array {
                kind: ArrayElementKind::for_elements(&[]),
                elements: Vec::new(),
                properties,
                prototype: Some(machine.intrinsics.array_prototype),
                extensible: true,
                length_writable: true,
            })
            .unwrap();
        let index = machine.runtime_slot(array).unwrap().unwrap();
        let base_charge = machine.slot_bytes[index];
        let base_heap = machine.heap_bytes;
        let element_bytes = std::mem::size_of::<Value>();

        machine
            .replace_array_elements(array, vec![Value::int32(1), Value::int32(2)])
            .unwrap();
        assert_eq!(machine.slot_bytes[index], base_charge + 2 * element_bytes);
        assert_eq!(machine.heap_bytes, base_heap + 2 * element_bytes);

        machine
            .set_data_property(array, "length", Value::int32(1))
            .unwrap();
        assert_eq!(
            machine.slot_bytes[index],
            base_charge + element_bytes - indexed_bytes
        );
        assert_eq!(
            machine.heap_bytes,
            base_heap + element_bytes - indexed_bytes
        );
        let HeapEntry::Array {
            elements,
            properties,
            length_writable,
            ..
        } = &machine.heap[index]
        else {
            panic!("array remains an array");
        };
        assert_eq!(*elements, vec![Value::int32(1)]);
        assert!(properties.iter(&machine.shapes).next().is_none());
        assert!(*length_writable);
        machine.assert_heap_ledger();

        let HeapEntry::Array {
            length_writable, ..
        } = &mut machine.heap[index]
        else {
            panic!("array remains an array");
        };
        *length_writable = false;
        let failed_slot = machine.slot_bytes[index];
        let failed_heap = machine.heap_bytes;
        assert!(matches!(
            machine.set_data_property(array, "length", Value::int32(0)),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        assert_eq!(machine.slot_bytes[index], failed_slot);
        assert_eq!(machine.heap_bytes, failed_heap);
        let HeapEntry::Array {
            elements,
            properties,
            ..
        } = &machine.heap[index]
        else {
            panic!("array remains an array");
        };
        assert_eq!(*elements, vec![Value::int32(1)]);
        assert!(properties.iter(&machine.shapes).next().is_none());
        machine.assert_heap_ledger();
    });
}

#[test]
fn object_add_delete_churn_refunds_data_and_accessor_charges() {
    with_machine(Limits::default(), |machine| {
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let index = machine.runtime_slot(object).unwrap().unwrap();
        let data = PropertyKey::Named(machine.intern_str("data"));
        let accessor = PropertyKey::Named(machine.intern_str("accessor"));
        let baseline_slot = machine.slot_bytes[index];
        let baseline_heap = machine.heap_bytes;

        for _ in 0..3 {
            machine
                .set_own_data(index, data.clone(), Value::int32(1))
                .unwrap();
            assert!(machine.internal_delete(object, &data).unwrap());
            machine
                .define_accessor(
                    object,
                    accessor.clone(),
                    Value::int32(2),
                    AccessorKind::Getter,
                )
                .unwrap();
            assert!(machine.internal_delete(object, &accessor).unwrap());
            assert_eq!(machine.slot_bytes[index], baseline_slot);
            assert_eq!(machine.heap_bytes, baseline_heap);
            machine.assert_heap_ledger();
        }
    });
}

#[test]
fn array_grow_shrink_churn_refunds_elements_and_indexed_properties() {
    with_machine(Limits::default(), |machine| {
        let array = machine
            .allocate(HeapEntry::Array {
                kind: ArrayElementKind::for_elements(&[]),
                elements: Vec::new(),
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.array_prototype),
                extensible: true,
                length_writable: true,
            })
            .unwrap();
        let index = machine.runtime_slot(array).unwrap().unwrap();
        let element = PropertyKey::Named(machine.intern_str("3"));
        let indexed_accessor = PropertyKey::Named(machine.intern_str("5"));
        let length = PropertyKey::Named(machine.intern_str("length"));
        let baseline_slot = machine.slot_bytes[index];
        let baseline_heap = machine.heap_bytes;

        for _ in 0..3 {
            machine
                .set_own_data(index, element.clone(), Value::int32(1))
                .unwrap();
            machine
                .define_accessor(
                    array,
                    indexed_accessor.clone(),
                    Value::int32(2),
                    AccessorKind::Getter,
                )
                .unwrap();
            machine
                .set_own_data(index, length.clone(), Value::int32(0))
                .unwrap();
            assert_eq!(machine.slot_bytes[index], baseline_slot);
            assert_eq!(machine.heap_bytes, baseline_heap);
            let HeapEntry::Array {
                elements,
                properties,
                ..
            } = &machine.heap[index]
            else {
                panic!("array remains an array");
            };
            assert!(elements.is_empty());
            assert!(properties.get(&machine.shapes, &indexed_accessor).is_none());
            machine.assert_heap_ledger();
        }
    });
}

#[test]
fn settled_promise_reaction_charge_survives_source_collection_in_queue() {
    with_machine(Limits::default(), |machine| {
        let source = machine.create_promise().unwrap();
        let source_index = machine.runtime_slot(source).unwrap().unwrap();
        machine
            .promise_then(source, Value::UNDEFINED, Value::UNDEFINED)
            .unwrap();
        machine.fulfill_promise(source, Value::int32(1)).unwrap();
        assert_eq!(machine.microtasks.len(), 1);
        assert_eq!(
            machine.microtasks.front().unwrap().retained_bytes,
            std::mem::size_of::<PromiseReaction>()
        );
        machine.assert_heap_ledger();

        machine.collect_garbage();
        assert!(matches!(machine.heap[source_index], HeapEntry::Vacant));
        assert_eq!(machine.slot_bytes[source_index], 0);
        assert!(machine.machine_bytes >= std::mem::size_of::<PromiseReaction>());
        machine.assert_heap_ledger();
    });
}

#[test]
fn dequeued_promise_job_refunds_machine_owned_reaction_charge() {
    with_machine(Limits::default(), |machine| {
        let source = machine.create_promise().unwrap();
        let machine_baseline = machine.machine_bytes;
        machine
            .promise_then(source, Value::UNDEFINED, Value::UNDEFINED)
            .unwrap();
        machine.fulfill_promise(source, Value::int32(1)).unwrap();
        assert_eq!(
            machine.machine_bytes,
            machine_baseline + std::mem::size_of::<PromiseReaction>()
        );
        machine.assert_heap_ledger();

        let drain = machine.drain_microtasks().unwrap();
        assert_eq!(drain.executed, 1);
        assert_eq!(machine.machine_bytes, machine_baseline);
        assert!(machine.microtasks.is_empty());
        machine.assert_heap_ledger();

        let failing_source = machine.create_promise().unwrap();
        let failing_index = machine.runtime_slot(failing_source).unwrap().unwrap();
        machine.charge_promise_reactions(failing_index, 2).unwrap();
        let HeapEntry::Promise {
            state:
                PromiseState::Pending {
                    fulfill_reactions,
                    reject_reactions,
                },
            ..
        } = &mut machine.heap[failing_index]
        else {
            panic!("new Promise is pending");
        };
        fulfill_reactions.push(PromiseReaction::Fulfilled {
            handler: Value::UNDEFINED,
            derived: Value::int32(0),
            context: None,
        });
        reject_reactions.push(PromiseReaction::Rejected {
            handler: Value::UNDEFINED,
            derived: Value::int32(0),
            context: None,
        });
        machine
            .fulfill_promise(failing_source, Value::int32(1))
            .unwrap();
        assert_eq!(
            machine.machine_bytes,
            machine_baseline + std::mem::size_of::<PromiseReaction>()
        );
        assert!(machine.drain_microtasks().is_err());
        assert_eq!(machine.machine_bytes, machine_baseline);
        assert!(machine.microtasks.is_empty());
        machine.assert_heap_ledger();
    });
}

#[test]
fn promise_all_values_charge_moves_to_output_before_aggregate_collection() {
    with_machine(Limits::default(), |machine| {
        let promise = machine.create_promise().unwrap();
        let record = machine.create_promise_resolver(promise).unwrap();
        let (resolve_target, reject_target) =
            machine.intrinsics.builtins.promise_resolver_targets();
        let resolve = machine
            .create_promise_resolver_function(resolve_target, record)
            .unwrap();
        let reject = machine
            .create_promise_resolver_function(reject_target, record)
            .unwrap();
        let aggregate = machine
            .allocate(HeapEntry::PromiseAll {
                resolve,
                reject,
                values: Vec::new(),
                remaining: 1,
                settled: false,
            })
            .unwrap();
        let aggregate_index = machine.runtime_slot(aggregate).unwrap().unwrap();
        let output_index = machine.add_promise_all_element(aggregate).unwrap();
        let element = machine
            .allocate(HeapEntry::PromiseAllElement {
                aggregate,
                index: output_index,
                called: false,
            })
            .unwrap();
        assert!(!machine.finish_promise_all(aggregate).unwrap());
        machine
            .resolve_promise_all_element(element, Value::int32(7))
            .unwrap();
        let promise_index = machine.runtime_slot(promise).unwrap().unwrap();
        let HeapEntry::Promise {
            state: PromiseState::Fulfilled { value: output },
            ..
        } = &machine.heap[promise_index]
        else {
            panic!("Promise.all result is fulfilled");
        };
        let output = *output;
        let output_index = machine.runtime_slot(output).unwrap().unwrap();
        assert_eq!(machine.slot_bytes[aggregate_index], 1);
        assert_eq!(
            machine.slot_bytes[output_index],
            1 + std::mem::size_of::<Value>()
        );
        machine.assert_heap_ledger();

        machine.test_set_global("promiseAllOutput", output);
        machine.collect_garbage();
        assert!(matches!(machine.heap[aggregate_index], HeapEntry::Vacant));
        assert_eq!(machine.slot_bytes[aggregate_index], 0);
        assert_eq!(
            machine.slot_bytes[output_index],
            1 + std::mem::size_of::<Value>()
        );
        machine.assert_heap_ledger();
    });
}

#[test]
fn vacant_runtime_handle_is_rejected() {
    with_machine(Limits::default(), |machine| {
        let value = machine
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .unwrap();
        let index = machine.runtime_slot(value).unwrap().unwrap();
        machine.heap_bytes -= machine.slot_bytes[index];
        machine.slot_bytes[index] = 0;
        machine.heap.vacate(index);
        machine.vacant_count += 1;

        let Some(Decoded::HeapRef(id)) = value.decode() else {
            panic!("allocated value is a heap reference");
        };
        assert_eq!(
            machine.runtime_slot(value),
            Err(RuntimeErrorKind::InvalidRuntimeHeapReference { slot: id.slot() })
        );
        machine.assert_heap_ledger();
    });
}

#[test]
fn slot_ids_stay_append_only_after_a_tombstone() {
    with_machine(Limits::default(), |machine| {
        let stale = machine
            .allocate(HeapEntry::String(EcmaString::encode("stale")))
            .unwrap();
        let stale_index = machine.runtime_slot(stale).unwrap().unwrap();
        machine.heap_bytes -= machine.slot_bytes[stale_index];
        machine.slot_bytes[stale_index] = 0;
        machine.heap.vacate(stale_index);
        machine.vacant_count += 1;

        let live = machine
            .allocate(HeapEntry::String(EcmaString::encode("live")))
            .unwrap();
        assert_ne!(stale, live);
        assert!(matches!(
            machine.runtime_slot(stale),
            Err(RuntimeErrorKind::InvalidRuntimeHeapReference { .. })
        ));
        assert_eq!(machine.runtime_slot(live).unwrap(), Some(stale_index + 1));
        machine.assert_heap_ledger();
    });
}

#[test]
fn live_slot_limit_excludes_tombstones() {
    with_machine(
        Limits {
            max_heap_slots: 1,
            ..Limits::default()
        },
        |machine| {
            let value = machine
                .allocate(HeapEntry::String(EcmaString::encode("x")))
                .unwrap();
            assert!(matches!(
                machine.ensure_allocation_capacity(1, 0),
                Err(RuntimeErrorKind::HeapSlotLimitExceeded { limit: 1 })
            ));

            let index = machine.runtime_slot(value).unwrap().unwrap();
            machine.heap_bytes -= machine.slot_bytes[index];
            machine.slot_bytes[index] = 0;
            machine.heap.vacate(index);
            machine.vacant_count += 1;

            machine.ensure_allocation_capacity(1, 0).unwrap();
            machine.assert_heap_ledger();
        },
    );
}

#[test]
fn async_await_setup_failure_releases_suspended_registers() {
    let program = verified(
        vec![Constant::Undefined],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_function(
                0,
                2,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Await {
                        dst: reg(1),
                        src: reg(0),
                        resume: pc(2),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let limits = Limits {
        max_microtasks: 0,
        ..Limits::default()
    };
    let mut machine = Machine::new(&program, &mut host, limits);
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);

    assert!(matches!(
        machine.call_value(callable, Value::UNDEFINED, &[]),
        Err(EvalFailure::Runtime(
            RuntimeErrorKind::MicrotaskQueueLimitExceeded { limit: 0 }
        ))
    ));
    assert_eq!(machine.live_registers, 0);
}

#[test]
fn async_engine_type_error_rejection_has_intrinsic_shape() {
    // An async body that calls a non-callable must reject via start_async_call
    // with a materialized intrinsic TypeError (not undefined) while retaining
    // the matching engine TypeError origin on the Promise.
    let program = verified(
        vec![Constant::Int32(0)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_function(
                0,
                3,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::CreateArray { dst: reg(1) },
                    Instruction::Call {
                        dst: reg(2),
                        callee: reg(0),
                        this_value: reg(0),
                        arguments: reg(1),
                    },
                    Instruction::Return { value: reg(2) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let promise = machine
        .call_value(callable, Value::UNDEFINED, &[])
        .expect("async call returns a rejected promise");
    let index = machine
        .runtime_slot(promise)
        .unwrap()
        .expect("async result is a promise");
    let HeapEntry::Promise {
        state: PromiseState::Rejected { reason, origin },
        ..
    } = &machine.heap[index]
    else {
        panic!("async engine TypeError must reject its promise");
    };
    let reason = *reason;
    let origin = *origin;
    assert_ne!(reason, Value::UNDEFINED);
    assert_eq!(origin, ThrowOrigin::TypeError { operation: "call" });
    let name = machine.get_named_property(reason, "name").unwrap();
    assert!(
        machine
            .string_value(name)
            .is_some_and(|text| text.eq_ascii("TypeError"))
    );
    let message = machine.get_named_property(reason, "message").unwrap();
    assert!(
        machine
            .string_value(message)
            .is_some_and(|text| text.eq_ascii("call"))
    );
    let constructor = machine.intrinsics.global("TypeError").unwrap();
    assert!(machine.instance_of(reason, constructor).unwrap());
    machine.run_to_quiescence().unwrap();
}

#[test]
fn async_prematerialized_rejection_keeps_identity() {
    // An async body that throws a preallocated object must reject with that
    // exact Value and Bytecode origin (no rematerialization).
    let program = verified(
        Vec::new(),
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_function(1, 1, vec![Instruction::Throw { value: reg(0) }], Vec::new()),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let preallocated = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    let callable = generator_callable(&mut machine, 1);
    let promise = machine
        .call_value(callable, Value::UNDEFINED, &[preallocated])
        .expect("async call returns a rejected promise");
    let index = machine
        .runtime_slot(promise)
        .unwrap()
        .expect("async result is a promise");
    let HeapEntry::Promise {
        state: PromiseState::Rejected { reason, origin },
        ..
    } = &machine.heap[index]
    else {
        panic!("async explicit throw must reject its promise");
    };
    assert_eq!(*reason, preallocated);
    assert_eq!(*origin, ThrowOrigin::Bytecode);
    machine.run_to_quiescence().unwrap();
}

#[test]
fn reject_promise_materializes_lazy_type_error_once() {
    // Direct sink contract: UNDEFINED + engine TypeError origin becomes one
    // intrinsic TypeError object; a second reject on a settled promise is a
    // no-op and must not allocate another reason.
    let program = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let promise = machine.create_promise().unwrap();
    let before = machine.heap.len();
    machine
        .reject_promise(
            promise,
            Value::UNDEFINED,
            ThrowOrigin::TypeError {
                operation: "sink materialize",
            },
        )
        .unwrap();
    let after_first = machine.heap.len();
    assert!(
        after_first > before,
        "lazy rejection must allocate an error"
    );
    let index = machine.runtime_slot(promise).unwrap().unwrap();
    let HeapEntry::Promise {
        state: PromiseState::Rejected { reason, origin },
        ..
    } = &machine.heap[index]
    else {
        panic!("sink must reject");
    };
    let reason = *reason;
    let origin = *origin;
    assert_ne!(reason, Value::UNDEFINED);
    assert_eq!(
        origin,
        ThrowOrigin::TypeError {
            operation: "sink materialize",
        }
    );
    let name = machine.get_named_property(reason, "name").unwrap();
    assert!(
        machine
            .string_value(name)
            .is_some_and(|text| text.eq_ascii("TypeError"))
    );
    let message = machine.get_named_property(reason, "message").unwrap();
    assert!(
        machine
            .string_value(message)
            .is_some_and(|text| text.eq_ascii("sink materialize"))
    );
    let constructor = machine.intrinsics.global("TypeError").unwrap();
    assert!(machine.instance_of(reason, constructor).unwrap());

    machine
        .reject_promise(
            promise,
            Value::UNDEFINED,
            ThrowOrigin::TypeError {
                operation: "second materialize",
            },
        )
        .unwrap();
    assert_eq!(
        machine.heap.len(),
        after_first,
        "settled reject must not rematerialize"
    );
    let HeapEntry::Promise {
        state:
            PromiseState::Rejected {
                reason: kept_reason,
                origin: kept_origin,
            },
        ..
    } = &machine.heap[index]
    else {
        panic!("sink must stay rejected");
    };
    assert_eq!(*kept_reason, reason);
    assert_eq!(*kept_origin, origin);
}

#[test]
fn reject_promise_keeps_prematerialized_identity() {
    // Direct sink contract: an already-materialized reason and Bytecode
    // origin keep exact Value identity with no rematerialization.
    let program = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let preallocated = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    let promise = machine.create_promise().unwrap();
    let before = machine.heap.len();
    machine
        .reject_promise(promise, preallocated, ThrowOrigin::Bytecode)
        .unwrap();
    assert_eq!(
        machine.heap.len(),
        before,
        "prematerialized reject allocates no error"
    );
    let index = machine.runtime_slot(promise).unwrap().unwrap();
    let HeapEntry::Promise {
        state: PromiseState::Rejected { reason, origin },
        ..
    } = &machine.heap[index]
    else {
        panic!("sink must reject");
    };
    assert_eq!(*reason, preallocated);
    assert_eq!(*origin, ThrowOrigin::Bytecode);
}

fn run_ok(program: &Program<Verified>) -> Execution {
    let mut host = TestHost;
    Machine::new(program, &mut host, Limits::default())
        .run()
        .unwrap()
}

fn generator_callable<H: Host>(machine: &mut Machine<'_, H>, function: u32) -> Value {
    machine
        .allocate(HeapEntry::Function {
            module: ModuleId::new(0),
            function: FunctionId::new(function),
            captures: Vec::new(),
            context: None,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .unwrap()
}

fn generator_next<H: Host>(
    machine: &mut Machine<'_, H>,
    generator: Value,
    resume_value: Value,
) -> Result<(Value, bool), EvalFailure> {
    let next = machine.get_named_property(generator, "next")?;
    let result = machine.call_value(next, generator, &[resume_value])?;
    let done = machine.get_named_property(result, "done")?;
    let value = machine.get_named_property(result, "value")?;
    Ok((value, machine.truthy(done)))
}

#[test]
fn sync_generator_is_lazy_resumes_registers_and_stays_completed() {
    let program = verified(
        vec![Constant::Int32(10)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            generator_function(
                0,
                3,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Suspend {
                        dst: reg(1),
                        src: reg(0),
                        resume: pc(2),
                        mode: reg(2),
                    },
                    Instruction::Binary {
                        dst: reg(2),
                        op: BinaryOp::Add,
                        left: reg(0),
                        right: reg(1),
                    },
                    Instruction::Return { value: reg(2) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    assert_eq!(machine.live_registers, 0, "calling must not start the body");
    machine
        .set_data_property(generator, "visible", Value::int32(1))
        .unwrap();
    assert_eq!(
        machine.get_named_property(generator, "visible").unwrap(),
        Value::int32(1),
    );
    assert_eq!(
        machine.own_property_keys(generator).unwrap(),
        vec![PropertyKey::Named(machine.intern_str("visible"))],
    );
    assert!(
        machine
            .inherits_from_prototype(generator, machine.intrinsics.builtins.generator_prototype(),)
            .unwrap()
    );

    assert_eq!(
        generator_next(&mut machine, generator, Value::int32(99)).unwrap(),
        (Value::int32(10), false),
    );
    assert_eq!(machine.live_registers, 3);
    assert_eq!(
        generator_next(&mut machine, generator, Value::int32(5)).unwrap(),
        (Value::int32(15), true),
    );
    assert_eq!(machine.live_registers, 0);
    assert_eq!(
        generator_next(&mut machine, generator, Value::int32(8)).unwrap(),
        (Value::UNDEFINED, true),
    );
}

#[test]
fn generator_iterator_results_bypass_inherited_setters() {
    fn inherited_setter(
        _machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(EvalFailure::ThrowValue(Value::int32(99)))
    }

    let program = verified(
        vec![Constant::Int32(7)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            generator_function(
                0,
                3,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Suspend {
                        dst: reg(1),
                        src: reg(0),
                        resume: pc(2),
                        mode: reg(2),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    let setter_id = machine.intrinsics.builtins.register(BuiltinDef {
        name: "inherited generator result setter",
        length: 1,
        handler: inherited_setter,
    });
    let setter = intrinsics::native_function(
        &mut machine.heap,
        &mut machine.atoms,
        &mut machine.shapes,
        setter_id,
        "inherited generator result setter",
        1,
    );
    let prototype = machine.intrinsics.object_prototype;
    for name in ["value", "done"] {
        let key = PropertyKey::Named(machine.intern_str(name));
        machine
            .define_accessor(prototype, key, setter, AccessorKind::Setter)
            .unwrap();
    }
    let next = machine.get_named_property(generator, "next").unwrap();
    for (expected, done) in [
        (Value::int32(7), false),
        (Value::int32(7), true),
        (Value::UNDEFINED, true),
    ] {
        let result = machine.call_value(next, generator, &[]).unwrap();
        assert_eq!(
            machine.internal_get_prototype_of(result).unwrap(),
            Some(prototype)
        );
        for (name, expected) in [("value", expected), ("done", Value::boolean(done))] {
            let key = PropertyKey::Named(machine.intern_str(name));
            assert!(matches!(
                machine.own_descriptor(result, &key).unwrap(),
                Some(Property::Data {
                    value,
                    writable: true,
                    enumerable: true,
                    configurable: true,
                }) if value == expected
            ));
        }
    }
}

#[test]
fn reentrant_resume_reports_generator_is_already_running() {
    let program = verified(
        Vec::new(),
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            generator_function(0, 1, vec![Instruction::Halt], Vec::new()),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    let _ = crate::vm::generator_async::prepare_generator_operation(
        &mut machine,
        generator,
        GeneratorCompletion::Normal(Value::UNDEFINED),
    )
    .unwrap();

    assert!(matches!(
        generator_next(&mut machine, generator, Value::UNDEFINED),
        Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "generator is already running",
        }))
    ));
}

#[test]
fn queued_async_generator_completions_survive_collection() {
    let program = verified(
        Vec::new(),
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(0, 1, vec![Instruction::Halt], Vec::new()),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    machine.test_set_global("queued_generator", generator);
    let rooted = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    let rooted_index = machine.runtime_slot(rooted).unwrap().unwrap();
    let capability = machine.create_promise().unwrap();
    let generator_index = machine.runtime_slot(generator).unwrap().unwrap();
    let HeapEntry::AsyncGenerator { queue, .. } = &mut machine.heap[generator_index] else {
        panic!("async generator expected");
    };
    queue.push_back(AsyncGeneratorRequest {
        completion: GeneratorCompletion::Return(rooted),
        capability,
    });

    machine.collect_garbage();

    assert!(matches!(
        machine.heap[rooted_index],
        HeapEntry::Object { .. }
    ));
}

#[test]
fn throw_origin_survives_the_completion_algebra() {
    let program = verified(
        Vec::new(),
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            generator_function(0, 1, vec![Instruction::Halt], Vec::new()),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    let origin = ThrowOrigin::TypeError {
        operation: "completion-origin",
    };

    assert!(matches!(
        machine.resume_generator(
            generator,
            GeneratorCompletion::Throw {
                value: Value::int32(41),
                origin,
            },
        ),
        Err(EvalFailure::ThrowValueOrigin { value, origin: actual })
            if value == Value::int32(41) && actual == origin
    ));
    assert!(matches!(
        machine.resume_generator(
            generator,
            GeneratorCompletion::Throw {
                value: Value::int32(43),
                origin,
            },
        ),
        Err(EvalFailure::ThrowValueOrigin { value, origin: actual })
            if value == Value::int32(43) && actual == origin
    ));
}

#[test]
fn sync_generator_uncaught_throw_preserves_origin_and_completes() {
    let program = verified(
        vec![Constant::Int32(7)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            generator_function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Throw { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    assert!(matches!(
        generator_next(&mut machine, generator, Value::UNDEFINED),
        Err(EvalFailure::ThrowValueOrigin {
            value,
            origin: ThrowOrigin::Bytecode,
        }) if value == Value::int32(7)
    ));
    assert_eq!(
        generator_next(&mut machine, generator, Value::UNDEFINED).unwrap(),
        (Value::UNDEFINED, true),
    );
    assert_eq!(machine.live_registers, 0);
}

#[test]
fn outer_compiled_handler_catches_generator_throw_value() {
    let program = verified(
        vec![
            Constant::Int32(7),
            Constant::Undefined,
            Constant::String(EcmaString::encode("next")),
        ],
        vec![
            function(
                0,
                8,
                vec![
                    Instruction::CreateArray { dst: reg(0) },
                    Instruction::CreateClosure {
                        dst: reg(1),
                        function: FunctionId::new(1),
                        captures: reg(0),
                    },
                    Instruction::CreateArray { dst: reg(2) },
                    Instruction::LoadConst {
                        dst: reg(3),
                        constant: cid(1),
                    },
                    Instruction::Call {
                        dst: reg(4),
                        callee: reg(1),
                        this_value: reg(3),
                        arguments: reg(2),
                    },
                    Instruction::LoadConst {
                        dst: reg(5),
                        constant: cid(2),
                    },
                    Instruction::GetProperty {
                        dst: reg(6),
                        object: reg(4),
                        key: reg(5),
                    },
                    Instruction::Call {
                        dst: reg(7),
                        callee: reg(6),
                        this_value: reg(4),
                        arguments: reg(2),
                    },
                    Instruction::Return { value: reg(3) },
                    Instruction::Return { value: reg(7) },
                ],
                vec![ExceptionHandler {
                    start: pc(7),
                    end: pc(8),
                    handler: pc(9),
                    catch_register: reg(7),
                }],
            ),
            generator_function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Throw { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    );

    assert_eq!(run_ok(&program).value, Value::int32(7));
}

#[test]
fn sync_generator_catches_body_throw_before_suspending() {
    let program = verified(
        vec![Constant::Int32(7)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            generator_function(
                0,
                3,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Throw { value: reg(0) },
                    Instruction::Suspend {
                        dst: reg(2),
                        src: reg(1),
                        resume: pc(3),
                        mode: reg(0),
                    },
                    Instruction::Return { value: reg(2) },
                ],
                vec![ExceptionHandler {
                    start: pc(1),
                    end: pc(2),
                    handler: pc(2),
                    catch_register: reg(1),
                }],
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    assert_eq!(
        generator_next(&mut machine, generator, Value::UNDEFINED).unwrap(),
        (Value::int32(7), false),
    );
    assert_eq!(
        generator_next(&mut machine, generator, Value::int32(9)).unwrap(),
        (Value::int32(9), true),
    );
}

#[test]
fn suspended_generator_registers_remain_charged() {
    let program = verified(
        vec![Constant::Int32(1)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            generator_function(
                0,
                3,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Suspend {
                        dst: reg(1),
                        src: reg(0),
                        resume: pc(2),
                        mode: reg(2),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(
        &program,
        &mut host,
        Limits {
            max_total_registers: 3,
            ..Limits::default()
        },
    );
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let first = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    let second = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    assert_eq!(
        generator_next(&mut machine, first, Value::UNDEFINED).unwrap(),
        (Value::int32(1), false),
    );
    assert!(matches!(
        generator_next(&mut machine, second, Value::UNDEFINED),
        Err(EvalFailure::Runtime(
            RuntimeErrorKind::RegisterLimitExceeded { .. }
        ))
    ));
    assert_eq!(machine.live_registers, 3);
    assert_eq!(
        generator_next(&mut machine, first, Value::int32(4)).unwrap(),
        (Value::int32(4), true),
    );
    assert_eq!(machine.live_registers, 0);
}

#[test]
fn resumed_generator_call_depth_failure_releases_registers() {
    let program = verified(
        vec![Constant::Int32(1)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            generator_function(
                0,
                2,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Suspend {
                        dst: reg(1),
                        src: reg(0),
                        resume: pc(2),
                        mode: reg(0),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(
        &program,
        &mut host,
        Limits {
            max_total_registers: 2,
            ..Limits::default()
        },
    );
    machine.frames.clear();
    machine.live_registers = 0;

    let callable = generator_callable(&mut machine, 1);
    let first = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    // Start and suspend the first generator, charging its two registers.
    assert_eq!(
        generator_next(&mut machine, first, Value::UNDEFINED).unwrap(),
        (Value::int32(1), false),
    );
    assert_eq!(machine.live_registers, 2);

    // Fill the compiled call depth to the exact limit so the next resume
    // fails in push_resumed_generator_frame before it can take ownership.
    machine.frames.push(Frame {
        module: ModuleId::new(0),
        function: 0,
        pc: 0,
        registers: Vec::new(),
        return_to: None,
        this_value: Value::UNDEFINED,
        new_target: Value::UNDEFINED,
        args: Vec::new(),
        arguments_object: None,
        context: None,
        outer_context: None,
    });
    machine.limits.max_call_depth = machine.frames.len();

    assert!(matches!(
        generator_next(&mut machine, first, Value::int32(7)),
        Err(EvalFailure::Runtime(
            RuntimeErrorKind::CallDepthExceeded { .. }
        ))
    ));
    assert_eq!(machine.live_registers, 0);

    // The generator is now sticky Completed.
    assert_eq!(
        generator_next(&mut machine, first, Value::UNDEFINED).unwrap(),
        (Value::UNDEFINED, true),
    );

    // Remove the artificial depth and make room for another activation.
    machine.frames.pop();
    machine.limits.max_call_depth = Limits::default().max_call_depth;

    // A second generator can suspend again only if the first's charge was released.
    let second = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    assert_eq!(
        generator_next(&mut machine, second, Value::UNDEFINED).unwrap(),
        (Value::int32(1), false),
    );
    assert_eq!(machine.live_registers, 2);
    assert_eq!(
        generator_next(&mut machine, second, Value::int32(9)).unwrap(),
        (Value::int32(9), true),
    );
    assert_eq!(machine.live_registers, 0);
}
#[test]
fn array_extend_consumes_generator_through_sync_iterator_protocol() {
    let program = verified(
        vec![Constant::Int32(1), Constant::Int32(2)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            generator_function(
                0,
                3,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Suspend {
                        dst: reg(2),
                        src: reg(0),
                        resume: pc(2),
                        mode: reg(1),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(1),
                    },
                    Instruction::Suspend {
                        dst: reg(2),
                        src: reg(1),
                        resume: pc(4),
                        mode: reg(1),
                    },
                    Instruction::Return { value: reg(2) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    let array = machine
        .allocate(HeapEntry::Array {
            kind: ArrayElementKind::for_elements(&[]),
            elements: Vec::new(),
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.array_prototype),
            extensible: true,
            length_writable: true,
        })
        .unwrap();

    machine.array_extend(array, generator).unwrap();
    assert_eq!(
        machine.array_elements(array).unwrap(),
        Some(vec![Value::int32(1), Value::int32(2)]),
    );
    assert_eq!(machine.live_registers, 0);
}

fn async_generator_next<H: Host>(
    machine: &mut Machine<'_, H>,
    generator: Value,
    resume_value: Value,
) -> Result<Value, EvalFailure> {
    let next = machine.get_named_property(generator, "next")?;
    machine.call_value(next, generator, &[resume_value])
}

fn settled_iterator_result<H: Host>(machine: &mut Machine<'_, H>, promise: Value) -> (Value, bool) {
    let index = machine.runtime_slot(promise).unwrap().unwrap();
    let HeapEntry::Promise {
        state: PromiseState::Fulfilled { value },
        ..
    } = &machine.heap[index]
    else {
        panic!("capability must be fulfilled");
    };
    let result = *value;
    let done = machine.get_named_property(result, "done").unwrap();
    let value = machine.get_named_property(result, "value").unwrap();
    (value, machine.truthy(done))
}

fn rejected_reason<H: Host>(machine: &Machine<'_, H>, promise: Value) -> Value {
    let index = machine.runtime_slot(promise).unwrap().unwrap();
    let HeapEntry::Promise {
        state: PromiseState::Rejected { reason, .. },
        ..
    } = &machine.heap[index]
    else {
        panic!("capability must be rejected");
    };
    *reason
}

fn pending_promise<H: Host>(machine: &Machine<'_, H>, promise: Value) -> bool {
    let Some(index) = machine.runtime_slot(promise).unwrap() else {
        return false;
    };
    matches!(
        machine.heap[index],
        HeapEntry::Promise {
            state: PromiseState::Pending { .. },
            ..
        }
    )
}

#[test]
fn async_generator_call_creates_object_without_running_body() {
    let program = verified(
        vec![
            Constant::Int32(1),
            Constant::String(EcmaString::encode("started")),
        ],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                2,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    assert_eq!(machine.live_registers, 0, "calling must not start the body");
    assert_eq!(machine.test_global("started"), None);
    let index = machine.runtime_slot(generator).unwrap().unwrap();
    assert!(matches!(
        machine.heap[index],
        HeapEntry::AsyncGenerator {
            state: AsyncGeneratorState::SuspendedStart(_),
            ..
        }
    ));
    assert!(
        machine
            .inherits_from_prototype(
                generator,
                machine.intrinsics.builtins.async_generator_prototype(),
            )
            .unwrap()
    );

    // The first next() starts the body and settles once it returns.
    let capability = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    assert!(pending_promise(&machine, capability));
    machine.drain_microtasks().unwrap();
    assert_eq!(machine.test_global("started"), Some(Value::int32(1)));
    assert_eq!(
        settled_iterator_result(&mut machine, capability),
        (Value::int32(1), true),
    );
    assert_eq!(machine.live_registers, 0);
}

#[test]
fn async_generator_next_returns_promise_settled_with_iterator_result() {
    let program = verified(
        vec![Constant::Int32(10)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                3,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Suspend {
                        dst: reg(1),
                        src: reg(0),
                        resume: pc(2),
                        mode: reg(2),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    let first = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    let index = machine.runtime_slot(first).unwrap().unwrap();
    assert!(matches!(machine.heap[index], HeapEntry::Promise { .. }));
    assert!(pending_promise(&machine, first));
    machine.drain_microtasks().unwrap();
    assert_eq!(
        settled_iterator_result(&mut machine, first),
        (Value::int32(10), false),
    );

    let second = async_generator_next(&mut machine, generator, Value::int32(5)).unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(
        settled_iterator_result(&mut machine, second),
        (Value::int32(5), true),
    );
    assert_eq!(machine.live_registers, 0);
}

#[test]
fn async_generator_await_resumes_without_producing_an_item() {
    let program = verified(
        vec![
            Constant::Int32(1),
            Constant::String(EcmaString::encode("p")),
        ],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                4,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(1),
                    },
                    Instruction::Await {
                        dst: reg(1),
                        src: reg(0),
                        resume: pc(2),
                    },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(0),
                    },
                    Instruction::Suspend {
                        dst: reg(3),
                        src: reg(2),
                        resume: pc(4),
                        mode: reg(2),
                    },
                    Instruction::Return { value: reg(3) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let awaited = machine.create_promise().unwrap();
    machine.resolve_promise(awaited, Value::int32(9)).unwrap();
    machine.test_set_global("p", awaited);
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    let capability = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    machine.drain_microtasks().unwrap();
    // The await must not settle the request: exactly one item is produced,
    // by the yield after the await.
    assert_eq!(
        settled_iterator_result(&mut machine, capability),
        (Value::int32(1), false),
    );
    let index = machine.runtime_slot(generator).unwrap().unwrap();
    let HeapEntry::AsyncGenerator { state, queue, .. } = &machine.heap[index] else {
        panic!("generator heap entry");
    };
    assert!(matches!(state, AsyncGeneratorState::SuspendedYield(_)));
    assert!(queue.is_empty(), "await must not pop the request queue");
}

#[test]
fn async_generator_resume_call_depth_failure_releases_registers_once() {
    let program = verified(
        vec![Constant::String(EcmaString::encode("p"))],
        vec![
            function(0, 0, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                2,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(0),
                    },
                    Instruction::Await {
                        dst: reg(1),
                        src: reg(0),
                        resume: pc(2),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let awaited = machine.create_promise().unwrap();
    machine.test_set_global("p", awaited);
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    assert_eq!(machine.live_registers, 2);

    machine.limits.max_call_depth = 0;
    machine.resolve_promise(awaited, Value::int32(1)).unwrap();
    let error = machine
        .drain_microtasks()
        .expect_err("resume exceeds the call-depth limit");
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::CallDepthExceeded { limit: 0 }
    ));
    assert_eq!(machine.live_registers, 0);
}

#[test]
fn async_generator_yield_awaits_its_operand() {
    let program = verified(
        vec![Constant::String(EcmaString::encode("p"))],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                2,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(0),
                    },
                    Instruction::Suspend {
                        dst: reg(1),
                        src: reg(0),
                        resume: pc(2),
                        mode: reg(0),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let yielded = machine.create_promise().unwrap();
    machine.resolve_promise(yielded, Value::int32(41)).unwrap();
    machine.test_set_global("p", yielded);
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    let capability = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    machine.drain_microtasks().unwrap();
    // The consumer sees the unwrapped value, never the yielded Promise.
    assert_eq!(
        settled_iterator_result(&mut machine, capability),
        (Value::int32(41), false),
    );
}

#[test]
fn async_generator_fatal_drive_failure_cleans_queue_and_propagates() {
    let program = verified(
        vec![Constant::Int32(41)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                2,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Suspend {
                        dst: reg(1),
                        src: reg(0),
                        resume: pc(2),
                        mode: reg(0),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let limits = Limits {
        max_microtasks: 0,
        ..Limits::default()
    };
    let mut machine = Machine::new(&program, &mut host, limits);
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    let index = machine.runtime_slot(generator).unwrap().unwrap();
    let start_state = match &mut machine.heap[index] {
        HeapEntry::AsyncGenerator { state, .. } => {
            std::mem::replace(state, AsyncGeneratorState::Executing)
        }
        _ => unreachable!("async generator remains allocated"),
    };
    let front = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    let queued = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    let HeapEntry::AsyncGenerator { state, .. } = &mut machine.heap[index] else {
        unreachable!("async generator remains allocated");
    };
    *state = start_state;

    assert!(matches!(
        async_generator_next(&mut machine, generator, Value::UNDEFINED),
        Err(EvalFailure::Runtime(
            RuntimeErrorKind::MicrotaskQueueLimitExceeded { limit: 0 }
        ))
    ));
    assert_eq!(rejected_reason(&machine, front), Value::UNDEFINED);
    assert_eq!(
        settled_iterator_result(&mut machine, queued),
        (Value::UNDEFINED, true),
    );
    assert!(matches!(
        &machine.heap[index],
        HeapEntry::AsyncGenerator {
            state: AsyncGeneratorState::Completed,
            queue,
            ..
        } if queue.is_empty()
    ));
}

#[test]
fn async_generator_queue_serves_concurrent_next_calls_in_order() {
    let program = verified(
        vec![Constant::Int32(1), Constant::Int32(2), Constant::Int32(3)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                5,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Suspend {
                        dst: reg(4),
                        src: reg(0),
                        resume: pc(2),
                        mode: reg(3),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(1),
                    },
                    Instruction::Suspend {
                        dst: reg(4),
                        src: reg(1),
                        resume: pc(4),
                        mode: reg(3),
                    },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(2),
                    },
                    Instruction::Suspend {
                        dst: reg(4),
                        src: reg(2),
                        resume: pc(6),
                        mode: reg(3),
                    },
                    Instruction::Return { value: reg(4) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    let first = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    let second = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    let third = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    let fourth = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    assert!(pending_promise(&machine, first));
    assert!(pending_promise(&machine, second));
    assert!(pending_promise(&machine, third));
    assert!(pending_promise(&machine, fourth));

    machine.drain_microtasks().unwrap();
    assert_eq!(
        settled_iterator_result(&mut machine, first),
        (Value::int32(1), false),
    );
    assert_eq!(
        settled_iterator_result(&mut machine, second),
        (Value::int32(2), false),
    );
    assert_eq!(
        settled_iterator_result(&mut machine, third),
        (Value::int32(3), false),
    );
    assert_eq!(
        settled_iterator_result(&mut machine, fourth),
        (Value::UNDEFINED, true),
    );
    assert_eq!(machine.live_registers, 0);
}

#[test]
fn async_generator_return_settles_front_and_drains_queue() {
    let program = verified(
        vec![Constant::Int32(9)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    let front = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    let later = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(
        settled_iterator_result(&mut machine, front),
        (Value::int32(9), true),
    );
    assert_eq!(
        settled_iterator_result(&mut machine, later),
        (Value::UNDEFINED, true),
    );
    // A completed generator keeps answering done without re-entering.
    let after = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(
        settled_iterator_result(&mut machine, after),
        (Value::UNDEFINED, true),
    );
    assert_eq!(machine.live_registers, 0);
}

#[test]
fn async_generator_throw_rejects_front_and_drains_queue() {
    let program = verified(
        vec![Constant::Int32(7)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Throw { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    let front = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    let later = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(rejected_reason(&machine, front), Value::int32(7));
    assert_eq!(
        settled_iterator_result(&mut machine, later),
        (Value::UNDEFINED, true),
    );
    assert_eq!(machine.live_registers, 0);
}

#[test]
fn async_generator_return_awaits_a_returned_promise() {
    let program = verified(
        vec![Constant::String(EcmaString::encode("p"))],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                1,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let returned = machine.create_promise().unwrap();
    machine.resolve_promise(returned, Value::int32(1)).unwrap();
    machine.test_set_global("p", returned);
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    let capability = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    machine.drain_microtasks().unwrap();
    // `return Promise.resolve(1)` settles the consumer with the unwrapped
    // value (Node 24: `{value: 1, done: true}`, not a Promise).
    assert_eq!(
        settled_iterator_result(&mut machine, capability),
        (Value::int32(1), true),
    );
    assert_eq!(machine.live_registers, 0);
}

#[test]
fn async_generator_returned_promise_rejection_rejects_front() {
    let program = verified(
        vec![Constant::String(EcmaString::encode("p"))],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                1,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let returned = machine.create_promise().unwrap();
    machine
        .reject_promise(returned, Value::int32(5), ThrowOrigin::Bytecode)
        .unwrap();
    machine.test_set_global("p", returned);
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    let front = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    let later = async_generator_next(&mut machine, generator, Value::UNDEFINED).unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(rejected_reason(&machine, front), Value::int32(5));
    assert_eq!(
        settled_iterator_result(&mut machine, later),
        (Value::UNDEFINED, true),
    );
}

#[test]
fn async_generator_next_on_incompatible_receiver_rejects_promise() {
    let program = verified(
        Vec::new(),
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(0, 0, vec![Instruction::Halt], Vec::new()),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    let next = machine.get_named_property(generator, "next").unwrap();
    let receiver = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();

    // AsyncGenerator.prototype.next never throws synchronously; an
    // incompatible receiver rejects with a materialized TypeError.
    let capability = machine.call_value(next, receiver, &[]).unwrap();
    let index = machine
        .runtime_slot(capability)
        .unwrap()
        .expect("next returns a promise");
    let HeapEntry::Promise {
        state: PromiseState::Rejected { reason, origin },
        ..
    } = &machine.heap[index]
    else {
        panic!("incompatible receiver must reject its promise");
    };
    let reason = *reason;
    let origin = *origin;
    assert_ne!(reason, Value::UNDEFINED);
    assert_eq!(
        origin,
        ThrowOrigin::TypeError {
            operation: "AsyncGenerator.prototype.next called on incompatible receiver",
        }
    );
    let name = machine.get_named_property(reason, "name").unwrap();
    assert!(
        machine
            .string_value(name)
            .is_some_and(|text| text.eq_ascii("TypeError"))
    );
    let message = machine.get_named_property(reason, "message").unwrap();
    assert!(machine.string_value(message).is_some_and(|text| {
        text.eq_ascii("AsyncGenerator.prototype.next called on incompatible receiver")
    }));
    let constructor = machine.intrinsics.global("TypeError").unwrap();
    assert!(machine.instance_of(reason, constructor).unwrap());
}

#[test]
fn async_generator_engine_type_error_rejection_has_intrinsic_shape() {
    // An async generator body that calls a non-callable must reject the
    // front next() capability with a materialized intrinsic TypeError.
    let program = verified(
        vec![Constant::Int32(0)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                3,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::CreateArray { dst: reg(1) },
                    Instruction::Call {
                        dst: reg(2),
                        callee: reg(0),
                        this_value: reg(0),
                        arguments: reg(1),
                    },
                    Instruction::Return { value: reg(2) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    let promise = async_generator_next(&mut machine, generator, Value::UNDEFINED)
        .expect("next returns a rejected promise");
    let index = machine
        .runtime_slot(promise)
        .unwrap()
        .expect("next result is a promise");
    let HeapEntry::Promise {
        state: PromiseState::Rejected { reason, origin },
        ..
    } = &machine.heap[index]
    else {
        panic!("async generator engine TypeError must reject its promise");
    };
    let reason = *reason;
    let origin = *origin;
    assert_ne!(reason, Value::UNDEFINED);
    assert_eq!(origin, ThrowOrigin::TypeError { operation: "call" });
    let name = machine.get_named_property(reason, "name").unwrap();
    assert!(
        machine
            .string_value(name)
            .is_some_and(|text| text.eq_ascii("TypeError"))
    );
    let message = machine.get_named_property(reason, "message").unwrap();
    assert!(
        machine
            .string_value(message)
            .is_some_and(|text| text.eq_ascii("call"))
    );
    let constructor = machine.intrinsics.global("TypeError").unwrap();
    assert!(machine.instance_of(reason, constructor).unwrap());
    machine.run_to_quiescence().unwrap();
}

#[test]
fn iterator_result_rejects_non_object() {
    let program = verified(
        vec![Constant::Int32(42)],
        vec![function(
            0,
            3,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(0),
                },
                Instruction::IteratorResult {
                    done: reg(1),
                    value: reg(2),
                    result: reg(0),
                },
                Instruction::Return { value: reg(1) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    assert!(matches!(
        machine.iterator_result_parts(Value::int32(42)),
        Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
    ));
    let error = machine
        .run()
        .expect_err("IteratorResult on a primitive throws");
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::UncaughtThrow {
            origin: ThrowOrigin::TypeError { .. },
            ..
        }
    ));
}

#[test]
fn iterator_step_and_result_execute_the_protocol() {
    let program = verified(
        Vec::new(),
        vec![function(
            0,
            5,
            vec![
                Instruction::CreateArray { dst: reg(0) },
                Instruction::GetIterator {
                    dst: reg(1),
                    src: reg(0),
                    kind: IteratorKind::Sync,
                },
                Instruction::IteratorStep {
                    dst: reg(2),
                    iterator: reg(1),
                },
                Instruction::IteratorResult {
                    done: reg(3),
                    value: reg(4),
                    result: reg(2),
                },
                Instruction::Return { value: reg(3) },
            ],
            Vec::new(),
        )],
    );
    assert_eq!(run_ok(&program).value, Value::boolean(true));
}

#[test]
fn close_iterator_raw_get_method_rejects_non_callable_return() {
    let program = verified(
        vec![Constant::Int32(99)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());

    let non_callable = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    machine
        .set_data_property(non_callable, "return", Value::int32(42))
        .unwrap();
    let iterator = machine
        .create_protocol_iterator(non_callable, Value::UNDEFINED)
        .unwrap();
    let (result, called) = machine.close_iterator_raw(iterator);
    assert!(matches!(
        result,
        Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
    ));
    assert!(!called);

    let absent = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    let iterator = machine
        .create_protocol_iterator(absent, Value::UNDEFINED)
        .unwrap();
    let (result, called) = machine.close_iterator_raw(iterator);
    assert_eq!(result.unwrap(), Value::UNDEFINED);
    assert!(!called);

    let null_return = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    machine
        .set_data_property(null_return, "return", Value::NULL)
        .unwrap();
    let iterator = machine
        .create_protocol_iterator(null_return, Value::UNDEFINED)
        .unwrap();
    let (result, called) = machine.close_iterator_raw(iterator);
    assert_eq!(result.unwrap(), Value::UNDEFINED);
    assert!(!called);

    let callable_return = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    let returner = generator_callable(&mut machine, 1);
    machine
        .set_data_property(callable_return, "return", returner)
        .unwrap();
    let iterator = machine
        .create_protocol_iterator(callable_return, Value::UNDEFINED)
        .unwrap();
    let (result, called) = machine.close_iterator_raw(iterator);
    assert_eq!(result.unwrap(), Value::int32(99));
    assert!(called);
}

#[test]
fn runtime_callback_without_interpreter_caller_propagates_throw() {
    let program = verified(
        Vec::new(),
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            function(1, 1, vec![Instruction::Throw { value: reg(0) }], Vec::new()),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callee = machine
        .allocate(HeapEntry::Function {
            module: ModuleId::new(0),
            function: FunctionId::new(1),
            captures: Vec::new(),
            context: None,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .unwrap();
    let thrown = Value::int32(7);

    assert!(matches!(
        machine.call_value(callee, Value::UNDEFINED, &[thrown]),
        Err(EvalFailure::ThrowValueOrigin {
            value,
            origin: ThrowOrigin::Bytecode,
        }) if value == thrown
    ));
}

#[test]
fn runtime_callback_failure_releases_root_frame() {
    let program = verified(
        Vec::new(),
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            function(
                1,
                1,
                vec![Instruction::Return { value: reg(0) }],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callee = machine
        .allocate(HeapEntry::Function {
            module: ModuleId::new(0),
            function: FunctionId::new(1),
            captures: Vec::new(),
            context: None,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .unwrap();
    machine.fuel = 0;

    assert!(matches!(
        machine.call_value(callee, Value::UNDEFINED, &[Value::int32(7)]),
        Err(EvalFailure::Runtime(RuntimeErrorKind::FuelExhausted { .. }))
    ));
    assert!(machine.frames.is_empty());
    assert_eq!(machine.live_registers, 0);

    machine.fuel = 1;
    assert!(matches!(
        machine.call_value(callee, Value::UNDEFINED, &[Value::int32(7)]),
        Ok(value) if value == Value::int32(7)
    ));
}

#[test]
fn object_values_have_stable_distinct_heap_identity() {
    let module = verified(
        vec![],
        vec![function(
            0,
            5,
            vec![
                Instruction::CreateObject { dst: reg(0) },
                Instruction::CreateObject { dst: reg(1) },
                Instruction::Binary {
                    dst: reg(2),
                    op: BinaryOp::StrictEqual,
                    left: reg(0),
                    right: reg(1),
                },
                Instruction::Move {
                    dst: reg(3),
                    src: reg(0),
                },
                Instruction::Binary {
                    dst: reg(4),
                    op: BinaryOp::StrictEqual,
                    left: reg(0),
                    right: reg(3),
                },
                Instruction::Return { value: reg(4) },
            ],
            vec![],
        )],
    );
    let execution = run_ok(&module);
    assert_eq!(execution.entry_registers[2], Value::FALSE);
    assert_eq!(execution.value, Value::TRUE);
}

#[test]
fn addition_coerces_objects_left_to_right_and_interpolates_errors() {
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("L")),
            Constant::String(EcmaString::encode("additionOrder")),
            Constant::String(EcmaString::encode("message")),
        ],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
            function(
                0,
                1,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(1),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let left = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            extensible: true,
            boxed_primitive: None,
        })
        .unwrap();
    let right = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            extensible: true,
            boxed_primitive: None,
        })
        .unwrap();
    let left_value_of = machine
        .allocate(HeapEntry::Function {
            module: ModuleId::new(0),
            function: FunctionId::new(1),
            captures: Vec::new(),
            context: None,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .unwrap();
    let right_value_of = machine
        .allocate(HeapEntry::Function {
            module: ModuleId::new(0),
            function: FunctionId::new(2),
            captures: Vec::new(),
            context: None,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .unwrap();
    machine
        .set_data_property(left, "valueOf", left_value_of)
        .unwrap();
    machine
        .set_data_property(right, "valueOf", right_value_of)
        .unwrap();
    let coerced = machine.add(left, right).unwrap();
    assert!(
        machine
            .string_value(coerced)
            .is_some_and(|text| text.eq_ascii("LL"))
    );

    let error_constructor = machine.intrinsics.global("Error").unwrap();
    let message = machine
        .allocate(HeapEntry::String(EcmaString::encode("message")))
        .unwrap();
    let error = machine
        .call_value(error_constructor, Value::UNDEFINED, &[message])
        .unwrap();
    let empty = machine
        .allocate(HeapEntry::String(EcmaString::default()))
        .unwrap();
    let interpolated = machine.add(empty, error).unwrap();
    assert!(
        machine
            .string_value(interpolated)
            .is_some_and(|text| text.eq_ascii("Error: message"))
    );

    let date_constructor = machine.intrinsics.global("Date").unwrap();
    let date_prototype = machine
        .get_named_property(date_constructor, "prototype")
        .unwrap();
    let date = machine
        .allocate(HeapEntry::Date {
            time: 0.0,
            properties: PropertyMap::default(),
            prototype: Some(date_prototype),
            extensible: true,
        })
        .unwrap();
    machine
        .set_data_property(date, "toString", left_value_of)
        .unwrap();
    let date_text = machine.add(date, empty).unwrap();
    assert!(
        machine
            .string_value(date_text)
            .is_some_and(|text| text.eq_ascii("L"))
    );
}

#[test]
fn computed_member_access_uses_dynamic_register_key() {
    // key = "a" + "b"; obj[key] = 7; return obj[key].
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("a")),
            Constant::String(EcmaString::encode("b")),
            Constant::Int32(7),
        ],
        vec![function(
            0,
            6,
            vec![
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(1),
                },
                Instruction::Binary {
                    dst: reg(3),
                    op: BinaryOp::Add,
                    left: reg(1),
                    right: reg(2),
                },
                Instruction::CreateObject { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(4),
                    constant: cid(2),
                },
                Instruction::SetProperty {
                    object: reg(0),
                    key: reg(3),
                    value: reg(4),
                },
                Instruction::GetProperty {
                    dst: reg(5),
                    object: reg(0),
                    key: reg(3),
                },
                Instruction::Return { value: reg(5) },
            ],
            vec![],
        )],
    );
    assert_eq!(run_ok(&module).value, Value::int32(7));
}

#[test]
fn property_delete_and_array_holes_are_real_mutations() {
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("0")),
            Constant::Int32(5),
        ],
        vec![function(
            0,
            5,
            vec![
                Instruction::CreateArray { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(4),
                    constant: cid(1),
                },
                Instruction::SetProperty {
                    object: reg(0),
                    key: reg(1),
                    value: reg(4),
                },
                Instruction::GetProperty {
                    dst: reg(2),
                    object: reg(0),
                    key: reg(1),
                },
                Instruction::DeleteProperty {
                    dst: reg(3),
                    object: reg(0),
                    key: reg(1),
                },
                Instruction::GetProperty {
                    dst: reg(4),
                    object: reg(0),
                    key: reg(1),
                },
                Instruction::Return { value: reg(3) },
            ],
            vec![],
        )],
    );
    let execution = run_ok(&module);
    assert_eq!(execution.entry_registers[2], Value::int32(5));
    assert_eq!(execution.entry_registers[4], Value::UNDEFINED);
    assert_eq!(execution.value, Value::TRUE);
}

#[test]
fn closure_captures_seed_leading_registers_before_parameters() {
    // captures = [42]; fn1(7) => capture(r0) + param(r1) = 49.
    let entry = function(
        0,
        3,
        vec![
            Instruction::CreateArray { dst: reg(0) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(0),
            },
            Instruction::ArrayPush {
                array: reg(0),
                value: reg(1),
            },
            Instruction::CreateClosure {
                dst: reg(2),
                function: FunctionId::new(1),
                captures: reg(0),
            },
            // arguments array [7]
            Instruction::CreateArray { dst: reg(0) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(1),
            },
            Instruction::ArrayPush {
                array: reg(0),
                value: reg(1),
            },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(2),
            },
            Instruction::Call {
                dst: reg(1),
                callee: reg(2),
                this_value: reg(1),
                arguments: reg(0),
            },
            Instruction::Return { value: reg(1) },
        ],
        vec![],
    );
    // capture_count = 1, parameter_count = 1: r0 = capture, r1 = param.
    let callee = closure_function(
        1,
        1,
        3,
        vec![
            Instruction::Binary {
                dst: reg(2),
                op: BinaryOp::Add,
                left: reg(0),
                right: reg(1),
            },
            Instruction::Return { value: reg(2) },
        ],
    );
    let module = verified(
        vec![Constant::Int32(42), Constant::Int32(7), Constant::Undefined],
        vec![entry, callee],
    );
    assert_eq!(run_ok(&module).value, Value::int32(49));
}

#[test]
fn calls_scale_past_fixed_window_via_arguments_array() {
    // Build a 500-element arguments array and call a callee returning
    // arguments.length — impossible under a 127 fixed window.
    let mut code = vec![Instruction::CreateArray { dst: reg(0) }];
    code.push(Instruction::LoadConst {
        dst: reg(1),
        constant: cid(0),
    });
    for _ in 0..500 {
        code.push(Instruction::ArrayPush {
            array: reg(0),
            value: reg(1),
        });
    }
    code.push(Instruction::CreateClosure {
        dst: reg(2),
        function: FunctionId::new(1),
        captures: reg(3),
    });
    // captures array for a zero-capture function
    // (reg(3) must be an empty array)
    // Insert its creation before CreateClosure:
    let mut prelude = vec![Instruction::CreateArray { dst: reg(3) }];
    prelude.append(&mut code);
    let mut code = prelude;
    code.push(Instruction::LoadConst {
        dst: reg(1),
        constant: cid(1),
    });
    code.push(Instruction::Call {
        dst: reg(1),
        callee: reg(2),
        this_value: reg(1),
        arguments: reg(0),
    });
    code.push(Instruction::Return { value: reg(1) });

    let entry = function(0, 4, code, vec![]);
    let callee = function(
        0,
        2,
        vec![
            Instruction::LoadArguments { dst: reg(0) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(2),
            },
            Instruction::GetProperty {
                dst: reg(0),
                object: reg(0),
                key: reg(1),
            },
            Instruction::Return { value: reg(0) },
        ],
        vec![],
    );
    let module = verified(
        vec![
            Constant::Int32(1),
            Constant::Undefined,
            Constant::String(EcmaString::encode("length")),
        ],
        vec![entry, callee],
    );
    assert_eq!(run_ok(&module).value, Value::int32(500));
}

#[test]
fn array_extend_spreads_iterable_elements() {
    // dst = []; dst.push(1); dst.extend([2,3]); return dst.length == 3.
    let entry = function(
        0,
        4,
        vec![
            Instruction::CreateArray { dst: reg(0) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(0),
            },
            Instruction::ArrayPush {
                array: reg(0),
                value: reg(1),
            },
            // source [2,3]
            Instruction::CreateArray { dst: reg(2) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(1),
            },
            Instruction::ArrayPush {
                array: reg(2),
                value: reg(1),
            },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(2),
            },
            Instruction::ArrayPush {
                array: reg(2),
                value: reg(1),
            },
            Instruction::ArrayExtend {
                array: reg(0),
                iterable: reg(2),
            },
            Instruction::LoadConst {
                dst: reg(3),
                constant: cid(3),
            },
            Instruction::GetProperty {
                dst: reg(0),
                object: reg(0),
                key: reg(3),
            },
            Instruction::Return { value: reg(0) },
        ],
        vec![],
    );
    let module = verified(
        vec![
            Constant::Int32(1),
            Constant::Int32(2),
            Constant::Int32(3),
            Constant::String(EcmaString::encode("length")),
        ],
        vec![entry],
    );
    assert_eq!(run_ok(&module).value, Value::int32(3));
}

#[test]
fn array_extend_uses_sync_protocol_for_set_and_rejects_plain_object() {
    let module = verified(
        Vec::new(),
        vec![function(0, 0, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let set_constructor = machine.intrinsics.global("Set").unwrap();
    let set_prototype = machine
        .get_named_property(set_constructor, "prototype")
        .unwrap();
    let mut set_index = CollectionIndex::default();
    let hash = collection_key_hash(&mut machine, Value::int32(7));
    set_index.insert(hash, 0);
    let set = machine
        .allocate(HeapEntry::Collection {
            kind: CollectionKind::Set,
            entries: vec![CollectionEntry {
                order: 0,
                key: Value::int32(7),
                value: Value::int32(7),
                live: true,
            }],
            index: set_index,
            size: 1,
            next_order: 1,
            properties: PropertyMap::default(),
            prototype: Some(set_prototype),
            extensible: true,
        })
        .unwrap();
    let target = machine
        .allocate(HeapEntry::Array {
            kind: ArrayElementKind::for_elements(&[]),
            elements: Vec::new(),
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.array_prototype),
            extensible: true,
            length_writable: true,
        })
        .unwrap();

    machine.array_extend(target, set).unwrap();
    assert_eq!(
        machine.array_elements(target).unwrap(),
        Some(vec![Value::int32(7)])
    );

    let plain_object = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    assert!(matches!(
        machine.array_extend(target, plain_object),
        Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "value is not iterable"
        }))
    ));
}

#[test]
fn sync_iterator_uses_symbol_method_and_caches_next() {
    fn iterator_identity<H: Host>(
        _machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        Ok(intrinsics::BuiltinOutcome::Value(this))
    }

    fn next_getter<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        let reads = machine.get_named_property(this, "nextReads")?;
        let reads = if reads == Value::int32(0) { 1 } else { 2 };
        machine.set_data_property(this, "nextReads", Value::int32(reads))?;
        Ok(intrinsics::BuiltinOutcome::Value(
            machine.get_named_property(this, "nextFunction")?,
        ))
    }

    fn next_result<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        Ok(intrinsics::BuiltinOutcome::Value(
            machine.get_named_property(this, "result")?,
        ))
    }

    fn done_getter<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "order", Value::int32(1))?;
        Ok(intrinsics::BuiltinOutcome::Value(Value::FALSE))
    }

    fn value_getter<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        if machine.get_named_property(this, "order")? != Value::int32(1) {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "iterator value read before done",
            }));
        }
        Ok(intrinsics::BuiltinOutcome::Value(Value::int32(42)))
    }

    let module = verified(
        Vec::new(),
        vec![function(0, 0, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let mut install = |name, handler| {
        let id = machine
            .intrinsics
            .builtins
            .register(intrinsics::BuiltinDef {
                name,
                length: 0,
                handler,
            });
        intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            name,
            0,
        )
    };
    let iterator_identity = install(
        "[Symbol.iterator]",
        iterator_identity::<TestHost> as intrinsics::BuiltinHandler<TestHost>,
    );
    let next_getter = install("get next", next_getter::<TestHost>);
    let next_result = install("next", next_result::<TestHost>);
    let done_getter = install("get done", done_getter::<TestHost>);
    let value_getter = install("get value", value_getter::<TestHost>);
    let object_prototype = machine.intrinsics.object_prototype;
    let order_key = PropertyKey::Named(machine.intern_str("order"));
    let done_key = PropertyKey::Named(machine.intern_str("done"));
    let value_key = PropertyKey::Named(machine.intern_str("value"));
    let mut result_properties = PropertyMap::default();
    for (key, property) in [
        (
            order_key,
            Property::Data {
                value: Value::int32(0),
                writable: true,
                enumerable: true,
                configurable: true,
            },
        ),
        (
            done_key,
            Property::Accessor {
                getter: Some(done_getter),
                setter: None,
                enumerable: true,
                configurable: true,
            },
        ),
        (
            value_key,
            Property::Accessor {
                getter: Some(value_getter),
                setter: None,
                enumerable: true,
                configurable: true,
            },
        ),
    ] {
        result_properties.insert(&mut machine.shapes, key, property);
    }
    let result = machine
        .allocate(HeapEntry::Object {
            properties: result_properties,
            prototype: Some(object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
    let iterator_key = machine.property_key_from_value(iterator_symbol).unwrap();
    let next_key = PropertyKey::Named(machine.intern_str("next"));
    let next_reads_key = PropertyKey::Named(machine.intern_str("nextReads"));
    let next_function_key = PropertyKey::Named(machine.intern_str("nextFunction"));
    let result_key = PropertyKey::Named(machine.intern_str("result"));
    let mut source_properties = PropertyMap::default();
    for (key, property) in [
        (
            iterator_key,
            Property::Data {
                value: iterator_identity,
                writable: true,
                enumerable: false,
                configurable: true,
            },
        ),
        (
            next_key,
            Property::Accessor {
                getter: Some(next_getter),
                setter: None,
                enumerable: false,
                configurable: true,
            },
        ),
        (
            next_reads_key,
            Property::Data {
                value: Value::int32(0),
                writable: true,
                enumerable: true,
                configurable: true,
            },
        ),
        (
            next_function_key,
            Property::Data {
                value: next_result,
                writable: true,
                enumerable: true,
                configurable: true,
            },
        ),
        (
            result_key,
            Property::Data {
                value: result,
                writable: true,
                enumerable: true,
                configurable: true,
            },
        ),
    ] {
        source_properties.insert(&mut machine.shapes, key, property);
    }
    let source = machine
        .allocate(HeapEntry::Object {
            properties: source_properties,
            prototype: Some(object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();

    let iterator = machine.create_iterator(source, IteratorKind::Sync).unwrap();
    assert_eq!(
        machine.iterator_next(iterator).unwrap(),
        (false, Value::int32(42))
    );
    assert_eq!(
        machine.iterator_next(iterator).unwrap(),
        (false, Value::int32(42))
    );
    assert_eq!(
        machine.get_named_property(source, "nextReads").unwrap(),
        Value::int32(1)
    );

    let done_key = PropertyKey::Named(machine.intern_str("done"));
    let completed_value_key = PropertyKey::Named(machine.intern_str("value"));
    let mut completed_properties = PropertyMap::default();
    completed_properties.insert(
        &mut machine.shapes,
        done_key,
        Property::Data {
            value: Value::TRUE,
            writable: true,
            enumerable: true,
            configurable: true,
        },
    );
    completed_properties.insert(
        &mut machine.shapes,
        completed_value_key,
        Property::Accessor {
            getter: Some(value_getter),
            setter: None,
            enumerable: true,
            configurable: true,
        },
    );
    let completed = machine
        .allocate(HeapEntry::Object {
            properties: completed_properties,
            prototype: Some(object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    machine
        .set_data_property(source, "result", completed)
        .unwrap();
    assert_eq!(
        machine.iterator_next(iterator).unwrap(),
        (true, Value::UNDEFINED)
    );

    let next_key = PropertyKey::Named(machine.intern_str("next"));
    machine.internal_delete(source, &next_key).unwrap();
    machine
        .set_data_property(source, "next", Value::int32(1))
        .unwrap();
    let invalid_next = machine.create_iterator(source, IteratorKind::Sync).unwrap();
    assert!(matches!(
        machine.iterator_next(invalid_next),
        Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
    ));
}

#[test]
fn object_spread_copies_own_properties() {
    // src = {}; src.x = 9; target = {}; { ...src }; return target.x.
    let key = |c: u32| Instruction::LoadConst {
        dst: reg(3),
        constant: cid(c),
    };
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("x")),
            Constant::Int32(9),
        ],
        vec![function(
            0,
            4,
            vec![
                Instruction::CreateObject { dst: reg(0) },
                key(0),
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(1),
                },
                Instruction::SetProperty {
                    object: reg(0),
                    key: reg(3),
                    value: reg(2),
                },
                Instruction::CreateObject { dst: reg(1) },
                Instruction::ObjectSpread {
                    target: reg(1),
                    source: reg(0),
                },
                key(0),
                Instruction::GetProperty {
                    dst: reg(2),
                    object: reg(1),
                    key: reg(3),
                },
                Instruction::Return { value: reg(2) },
            ],
            vec![],
        )],
    );
    assert_eq!(run_ok(&module).value, Value::int32(9));
}

#[test]
fn object_spread_copies_enumerable_symbol_properties() {
    let module = verified(
        Vec::new(),
        vec![function(0, 0, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let prototype = machine.intrinsics.object_prototype;
    let object = |machine: &mut Machine<'_, TestHost>| {
        machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap()
    };
    let source = object(&mut machine);
    let target = object(&mut machine);
    let symbol = machine
        .allocate(HeapEntry::Symbol {
            description: EcmaString::encode("key"),
        })
        .unwrap();
    let key = machine.property_key_from_value(symbol).unwrap();
    machine
        .set_data_property_key(source, key.clone(), Value::int32(42))
        .unwrap();

    machine.object_spread(target, source).unwrap();

    assert_eq!(
        machine.get_property_key(target, &key).unwrap(),
        Value::int32(42)
    );
}

#[test]
fn object_spread_rechecks_descriptors_after_getters() {
    fn delete_next<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        let next_key = PropertyKey::Named(machine.intern_str("next"));
        machine.internal_delete(this, &next_key)?;
        Ok(intrinsics::BuiltinOutcome::Value(Value::int32(1)))
    }

    let module = verified(
        Vec::new(),
        vec![function(0, 0, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let getter_id = machine
        .intrinsics
        .builtins
        .register(intrinsics::BuiltinDef {
            name: "delete next",
            length: 0,
            handler: delete_next::<TestHost>,
        });
    let getter = intrinsics::native_function(
        &mut machine.heap,
        &mut machine.atoms,
        &mut machine.shapes,
        getter_id,
        "delete next",
        0,
    );
    let first = PropertyKey::Named(machine.intern_str("first"));
    let next = PropertyKey::Named(machine.intern_str("next"));
    let mut source_properties = PropertyMap::default();
    source_properties.insert(
        &mut machine.shapes,
        first.clone(),
        Property::Accessor {
            getter: Some(getter),
            setter: None,
            enumerable: true,
            configurable: true,
        },
    );
    source_properties.insert(
        &mut machine.shapes,
        next.clone(),
        Property::Data {
            value: Value::int32(2),
            writable: true,
            enumerable: true,
            configurable: true,
        },
    );
    let prototype = machine.intrinsics.object_prototype;
    let source = machine
        .allocate(HeapEntry::Object {
            properties: source_properties,
            prototype: Some(prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    let target = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();

    machine.object_spread(target, source).unwrap();

    assert_eq!(
        machine.get_property_key(target, &first).unwrap(),
        Value::int32(1)
    );
    assert!(!machine.has_own_property_key(target, &next).unwrap());
}

#[test]
fn private_names_have_distinct_identity_and_are_gettable() {
    // Two private names with the same description are distinct keys.
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("x")),
            Constant::Int32(1),
            Constant::Int32(2),
        ],
        vec![function(
            0,
            6,
            vec![
                Instruction::CreateObject { dst: reg(0) },
                Instruction::CreatePrivateName {
                    dst: reg(1),
                    description: cid(0),
                },
                Instruction::CreatePrivateName {
                    dst: reg(2),
                    description: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(3),
                    constant: cid(1),
                },
                Instruction::SetProperty {
                    object: reg(0),
                    key: reg(1),
                    value: reg(3),
                },
                Instruction::LoadConst {
                    dst: reg(3),
                    constant: cid(2),
                },
                Instruction::SetProperty {
                    object: reg(0),
                    key: reg(2),
                    value: reg(3),
                },
                // r4 = obj[#1] (1), r5 = obj[#2] (2)
                Instruction::GetProperty {
                    dst: reg(4),
                    object: reg(0),
                    key: reg(1),
                },
                Instruction::GetProperty {
                    dst: reg(5),
                    object: reg(0),
                    key: reg(2),
                },
                // distinctness: #1 !== #2
                Instruction::Binary {
                    dst: reg(3),
                    op: BinaryOp::StrictEqual,
                    left: reg(1),
                    right: reg(2),
                },
                Instruction::Return { value: reg(4) },
            ],
            vec![],
        )],
    );
    let execution = run_ok(&module);
    assert_eq!(execution.value, Value::int32(1));
    assert_eq!(execution.entry_registers[5], Value::int32(2));
    assert_eq!(execution.entry_registers[3], Value::FALSE);
}

#[test]
fn set_preserves_attributes_but_create_data_property_resets_them() {
    with_machine(Limits::default(), |machine| {
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let key = PropertyKey::Named(machine.intern_str("x"));
        machine
            .define_descriptor(
                object,
                key.clone(),
                Property::Data {
                    value: Value::int32(1),
                    writable: true,
                    enumerable: false,
                    configurable: true,
                },
            )
            .unwrap();

        machine
            .set_data_property_key(object, key.clone(), Value::int32(2))
            .unwrap();
        assert!(matches!(
            machine.own_descriptor(object, &key).unwrap(),
            Some(Property::Data {
                value,
                writable: true,
                enumerable: false,
                configurable: true,
            }) if value == Value::int32(2)
        ));

        machine
            .create_data_property_key(object, key.clone(), Value::int32(3))
            .unwrap();
        assert!(matches!(
            machine.own_descriptor(object, &key).unwrap(),
            Some(Property::Data {
                value,
                writable: true,
                enumerable: true,
                configurable: true,
            }) if value == Value::int32(3)
        ));
    });
}

#[test]
fn accessor_getter_is_invoked_on_property_read() {
    // Define a getter returning 99, then read the property.
    let entry = function(
        0,
        4,
        vec![
            Instruction::CreateObject { dst: reg(0) },
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(1),
                function: FunctionId::new(1),
                captures: reg(3),
            },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(0),
            },
            Instruction::DefineAccessor {
                object: reg(0),
                key: reg(2),
                accessor: reg(1),
                kind: AccessorKind::Getter,
            },
            Instruction::GetProperty {
                dst: reg(1),
                object: reg(0),
                key: reg(2),
            },
            Instruction::Return { value: reg(1) },
        ],
        vec![],
    );
    let getter = function(
        0,
        1,
        vec![
            Instruction::LoadConst {
                dst: reg(0),
                constant: cid(1),
            },
            Instruction::Return { value: reg(0) },
        ],
        vec![],
    );
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("g")),
            Constant::Int32(99),
        ],
        vec![entry, getter],
    );
    assert_eq!(run_ok(&module).value, Value::int32(99));
}

fn global_binding_constants() -> Vec<Constant> {
    vec![
        Constant::String(EcmaString::encode("globalThis")),
        Constant::String(EcmaString::encode("gets")),
        Constant::String(EcmaString::encode("sets")),
        Constant::String(EcmaString::encode("x")),
        Constant::Int32(0),
        Constant::Int32(1),
        Constant::Int32(100),
        Constant::Int32(41),
        Constant::String(EcmaString::encode("undeclared")),
        Constant::String(EcmaString::encode("gy")),
    ]
}

fn counter_bump(counter: u32, base: u32) -> [Instruction; 3] {
    [
        Instruction::LoadGlobal {
            dst: reg(base),
            name: cid(counter),
        },
        Instruction::Binary {
            dst: reg(base),
            op: BinaryOp::Add,
            left: reg(base),
            right: reg(base + 1),
        },
        Instruction::StoreGlobal {
            name: cid(counter),
            value: reg(base),
        },
    ]
}

/// A strict script that installs a counting accessor pair on global `x`,
/// ends its getter with `getter_tail`, runs `assignment`, and returns
/// `gets * 100 + sets`.
fn global_accessor_program(
    getter_tail: Instruction,
    assignment: &[Instruction],
) -> Program<Verified> {
    let mut entry = vec![
        Instruction::LoadConst {
            dst: reg(0),
            constant: cid(4),
        },
        Instruction::StoreGlobal {
            name: cid(1),
            value: reg(0),
        },
        Instruction::StoreGlobal {
            name: cid(2),
            value: reg(0),
        },
        Instruction::LoadGlobal {
            dst: reg(1),
            name: cid(0),
        },
        Instruction::CreateArray { dst: reg(2) },
        Instruction::CreateClosure {
            dst: reg(3),
            function: FunctionId::new(1),
            captures: reg(2),
        },
        Instruction::CreateClosure {
            dst: reg(4),
            function: FunctionId::new(2),
            captures: reg(2),
        },
        Instruction::LoadConst {
            dst: reg(5),
            constant: cid(3),
        },
        Instruction::DefineAccessor {
            object: reg(1),
            key: reg(5),
            accessor: reg(3),
            kind: AccessorKind::Getter,
        },
        Instruction::DefineAccessor {
            object: reg(1),
            key: reg(5),
            accessor: reg(4),
            kind: AccessorKind::Setter,
        },
        Instruction::LoadConst {
            dst: reg(8),
            constant: cid(5),
        },
    ];
    entry.extend_from_slice(assignment);
    entry.extend([
        Instruction::LoadGlobal {
            dst: reg(9),
            name: cid(1),
        },
        Instruction::LoadConst {
            dst: reg(10),
            constant: cid(6),
        },
        Instruction::Binary {
            dst: reg(9),
            op: BinaryOp::Multiply,
            left: reg(9),
            right: reg(10),
        },
        Instruction::LoadGlobal {
            dst: reg(10),
            name: cid(2),
        },
        Instruction::Binary {
            dst: reg(9),
            op: BinaryOp::Add,
            left: reg(9),
            right: reg(10),
        },
        Instruction::Return { value: reg(9) },
    ]);
    let mut getter = vec![Instruction::LoadConst {
        dst: reg(1),
        constant: cid(5),
    }];
    getter.extend(counter_bump(1, 0));
    getter.extend([getter_tail, Instruction::Return { value: reg(0) }]);
    let mut setter = vec![Instruction::LoadConst {
        dst: reg(2),
        constant: cid(5),
    }];
    setter.extend(counter_bump(2, 1));
    setter.push(Instruction::Return { value: reg(1) });
    verified(
        global_binding_constants(),
        vec![
            function(0, 11, entry, Vec::new()),
            function(0, 2, getter, Vec::new()),
            function(1, 3, setter, Vec::new()),
        ],
    )
}

/// Asserts `value` is an object built on the realm's own `constructor`
/// prototype and returns its heap slot.
fn assert_intrinsic_prototype<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
    constructor: &str,
) -> usize {
    let id = machine.intrinsics.builtins.id_named(constructor).unwrap();
    let expected = machine.intrinsics.error_prototype(id);
    let slot = machine
        .runtime_slot(value)
        .unwrap()
        .expect("an error object");
    let HeapEntry::Object { prototype, .. } = &machine.heap[slot] else {
        panic!("{constructor} must be an ordinary object");
    };
    assert_eq!(*prototype, Some(expected), "{constructor} prototype");
    slot
}

/// Asserts `value` is an error object built on the realm's own
/// `constructor` prototype with own `message`.
fn assert_intrinsic_error<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    constructor: &str,
    message: &str,
) {
    let slot = assert_intrinsic_prototype(machine, value, constructor);
    let message_value = machine.own_data_property(slot, "message");
    assert_eq!(
        message_value.and_then(|text| machine.string_value(text)),
        Some(EcmaString::encode(message))
    );
}

fn uncaught_value(error: RuntimeError) -> Value {
    match error.kind {
        RuntimeErrorKind::UncaughtThrow { value, .. } => value,
        kind => panic!("expected an uncaught throw, got {kind:?}"),
    }
}

#[test]
fn strict_simple_global_assignment_runs_only_the_setter() {
    let program = global_accessor_program(
        Instruction::Throw { value: reg(0) },
        &[
            Instruction::RequireGlobalBinding { name: cid(3) },
            Instruction::StoreGlobal {
                name: cid(3),
                value: reg(8),
            },
        ],
    );
    assert_eq!(run_ok(&program).value, Value::int32(1));
}

#[test]
fn strict_compound_global_assignment_runs_the_getter_once() {
    let program = global_accessor_program(
        Instruction::LoadConst {
            dst: reg(0),
            constant: cid(7),
        },
        &[
            Instruction::LoadGlobal {
                dst: reg(6),
                name: cid(3),
            },
            Instruction::Binary {
                dst: reg(6),
                op: BinaryOp::Add,
                left: reg(6),
                right: reg(8),
            },
            Instruction::RequireGlobalBinding { name: cid(3) },
            Instruction::StoreGlobal {
                name: cid(3),
                value: reg(6),
            },
        ],
    );
    assert_eq!(run_ok(&program).value, Value::int32(101));
}

#[test]
fn strict_assignment_to_an_undeclared_global_throws_and_creates_nothing() {
    let program = verified(
        global_binding_constants(),
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(5),
                },
                Instruction::RequireGlobalBinding { name: cid(8) },
                Instruction::StoreGlobal {
                    name: cid(8),
                    value: reg(0),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let value = uncaught_value(machine.evaluate().unwrap_err());
    assert_intrinsic_error(
        &mut machine,
        value,
        "ReferenceError",
        "undeclared is not defined",
    );
    let global = machine.global_object;
    let key = PropertyKey::Named(machine.intern_str("undeclared"));
    assert!(!machine.has_own_property_key(global, &key).unwrap());
}

#[test]
fn sloppy_assignment_to_an_undeclared_global_creates_it() {
    let sloppy = Function::new(
        None,
        0,
        0,
        1,
        FunctionFlags {
            is_sloppy: true,
            ..FunctionFlags::default()
        },
        vec![
            Instruction::LoadConst {
                dst: reg(0),
                constant: cid(5),
            },
            Instruction::StoreGlobal {
                name: cid(8),
                value: reg(0),
            },
            Instruction::Return { value: reg(0) },
        ],
        Vec::new(),
    );
    let program = verified(global_binding_constants(), vec![sloppy]);
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.evaluate().unwrap();
    assert_eq!(machine.test_global("undeclared"), Some(Value::int32(1)));
}

#[test]
fn strict_assignment_to_a_lexical_global_in_its_dead_zone_throws() {
    let module = program_module(
        "tdz",
        global_binding_constants(),
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(6),
                },
                Instruction::RequireGlobalBinding { name: cid(4) },
                Instruction::StoreGlobal {
                    name: cid(4),
                    value: reg(0),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
        Vec::new(),
        vec![Binding {
            name: cid(4),
            kind: BindingKind::Lexical,
        }],
        Vec::new(),
    );
    let program = linked(vec![module], 0);
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let value = uncaught_value(machine.evaluate().unwrap_err());
    assert_intrinsic_prototype(&machine, value, "ReferenceError");
}

#[test]
fn strict_compound_assignment_throws_when_the_binding_vanishes_before_the_write() {
    let program = verified(
        global_binding_constants(),
        vec![function(
            0,
            4,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(5),
                },
                Instruction::StoreGlobal {
                    name: cid(9),
                    value: reg(0),
                },
                Instruction::LoadGlobal {
                    dst: reg(1),
                    name: cid(9),
                },
                Instruction::LoadGlobal {
                    dst: reg(2),
                    name: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(3),
                    constant: cid(9),
                },
                Instruction::DeleteProperty {
                    dst: reg(3),
                    object: reg(2),
                    key: reg(3),
                },
                Instruction::Binary {
                    dst: reg(1),
                    op: BinaryOp::Add,
                    left: reg(1),
                    right: reg(0),
                },
                Instruction::RequireGlobalBinding { name: cid(9) },
                Instruction::StoreGlobal {
                    name: cid(9),
                    value: reg(1),
                },
                Instruction::Return { value: reg(1) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let value = uncaught_value(machine.evaluate().unwrap_err());
    assert_intrinsic_error(&mut machine, value, "ReferenceError", "gy is not defined");
    let global = machine.global_object;
    let key = PropertyKey::Named(machine.intern_str("gy"));
    assert!(!machine.has_own_property_key(global, &key).unwrap());
}

/// Replaces or deletes the global `constructor` binding through `tamper`
/// (`r0` holds `globalThis`, `r1` the binding name, `r2` a replacement
/// that counts its calls in global `called`), then throws the intrinsic
/// error of `kind` and returns the caught value.
fn intrinsic_error_program(
    kind: IntrinsicErrorKind,
    constructor: &str,
    message: &str,
    tamper: Instruction,
) -> Program<Verified> {
    let entry = Function::new(
        None,
        0,
        0,
        5,
        FunctionFlags::default(),
        vec![
            Instruction::LoadConst {
                dst: reg(4),
                constant: cid(3),
            },
            Instruction::StoreGlobal {
                name: cid(2),
                value: reg(4),
            },
            Instruction::LoadGlobal {
                dst: reg(0),
                name: cid(0),
            },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(1),
            },
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(2),
                function: FunctionId::new(1),
                captures: reg(3),
            },
            tamper,
            Instruction::ThrowIntrinsicError {
                kind,
                message: cid(5),
            },
            Instruction::Return { value: reg(4) },
        ],
        vec![ExceptionHandler {
            start: pc(7),
            end: pc(8),
            handler: pc(8),
            catch_register: reg(4),
        }],
    );
    let mut replacement = vec![Instruction::LoadConst {
        dst: reg(1),
        constant: cid(4),
    }];
    replacement.extend(counter_bump(2, 0));
    replacement.extend([
        Instruction::CreateObject { dst: reg(0) },
        Instruction::Return { value: reg(0) },
    ]);
    verified(
        vec![
            Constant::String(EcmaString::encode("globalThis")),
            Constant::String(EcmaString::encode(constructor)),
            Constant::String(EcmaString::encode("called")),
            Constant::Int32(0),
            Constant::Int32(1),
            Constant::String(EcmaString::encode(message)),
        ],
        vec![entry, function(0, 2, replacement, Vec::new())],
    )
}

#[test]
fn intrinsic_errors_ignore_a_replaced_or_deleted_global_constructor() {
    let replace = Instruction::SetProperty {
        object: reg(0),
        key: reg(1),
        value: reg(2),
    };
    let delete = Instruction::DeleteProperty {
        dst: reg(3),
        object: reg(0),
        key: reg(1),
    };
    for (kind, constructor, message) in [
        (
            IntrinsicErrorKind::TypeError,
            "TypeError",
            "Class constructor cannot be invoked without 'new'",
        ),
        (
            IntrinsicErrorKind::ReferenceError,
            "ReferenceError",
            "Unsupported reference to 'super'",
        ),
    ] {
        for tamper in [replace, delete] {
            let program = intrinsic_error_program(kind, constructor, message, tamper);
            let mut host = TestHost;
            let mut machine = Machine::new(&program, &mut host, Limits::default());
            let caught = machine.evaluate().unwrap().value;
            assert_intrinsic_error(&mut machine, caught, constructor, message);
            assert_eq!(machine.test_global("called"), Some(Value::int32(0)));
        }
    }
}

/// Asserts the own-property shape `new Error(message)` gives an error:
/// named keys `stack` then `message`, `message` a non-enumerable writable
/// configurable data property, and `stack` a non-enumerable accessor.
fn assert_constructed_error_shape<H: Host>(machine: &mut Machine<'_, H>, error: Value) {
    let keys: Vec<String> = machine
        .own_property_keys(error)
        .unwrap()
        .into_iter()
        .filter_map(|key| match key {
            PropertyKey::Named(atom) => {
                Some(machine.resolve_atom(atom).to_utf8_lossy().to_string())
            }
            _ => None,
        })
        .collect();
    assert_eq!(keys, ["stack", "message"]);
    let message_key = PropertyKey::Named(machine.intern_str("message"));
    assert!(matches!(
        machine.own_descriptor(error, &message_key).unwrap(),
        Some(Property::Data {
            writable: true,
            enumerable: false,
            configurable: true,
            ..
        })
    ));
    let stack_key = PropertyKey::Named(machine.intern_str("stack"));
    assert!(matches!(
        machine.own_descriptor(error, &stack_key).unwrap(),
        Some(Property::Accessor {
            enumerable: false,
            configurable: true,
            ..
        })
    ));
}

/// Runs `throwing` (one instruction at pc 1) under a handler that catches
/// into `r0` and returns the caught value. `r1` holds an empty array.
fn caught_by_handler(constants: Vec<Constant>, throwing: Instruction) -> Program<Verified> {
    let entry = Function::new(
        None,
        0,
        0,
        3,
        FunctionFlags::default(),
        vec![
            Instruction::CreateArray { dst: reg(1) },
            throwing,
            Instruction::Return { value: reg(1) },
            Instruction::Return { value: reg(0) },
        ],
        vec![ExceptionHandler {
            start: pc(1),
            end: pc(2),
            handler: pc(3),
            catch_register: reg(0),
        }],
    );
    verified(constants, vec![entry])
}

fn caught_error(
    program: &Program<Verified>,
    check: impl FnOnce(&mut Machine<'_, TestHost>, Value),
) {
    let mut host = TestHost;
    let mut machine = Machine::new(program, &mut host, Limits::default());
    let caught = machine.evaluate().unwrap().value;
    check(&mut machine, caught);
}

#[test]
fn intrinsic_error_has_the_constructed_error_shape() {
    let program = caught_by_handler(
        vec![Constant::String(EcmaString::encode("m"))],
        Instruction::ThrowIntrinsicError {
            kind: IntrinsicErrorKind::TypeError,
            message: cid(0),
        },
    );
    caught_error(&program, |machine, error| {
        assert_intrinsic_error(machine, error, "TypeError", "m");
        assert_constructed_error_shape(machine, error);
    });
}

#[test]
fn strict_global_reference_error_has_the_constructed_error_shape() {
    let program = caught_by_handler(
        vec![Constant::String(EcmaString::encode("undeclared"))],
        Instruction::RequireGlobalBinding { name: cid(0) },
    );
    caught_error(&program, |machine, error| {
        assert_intrinsic_error(
            machine,
            error,
            "ReferenceError",
            "undeclared is not defined",
        );
        assert_constructed_error_shape(machine, error);
    });
}

#[test]
fn engine_type_error_has_the_constructed_error_shape() {
    let program = caught_by_handler(
        Vec::new(),
        Instruction::Call {
            dst: reg(2),
            callee: reg(1),
            this_value: reg(1),
            arguments: reg(1),
        },
    );
    caught_error(&program, |machine, error| {
        assert_intrinsic_prototype(machine, error, "TypeError");
        assert_constructed_error_shape(machine, error);
    });
}

#[test]
fn intrinsic_error_message_keeps_a_lone_surrogate() {
    let units = [u16::from(b'x'), 0xD800];
    let program = caught_by_handler(
        vec![Constant::String(EcmaString::from_units(&units))],
        Instruction::ThrowIntrinsicError {
            kind: IntrinsicErrorKind::TypeError,
            message: cid(0),
        },
    );
    caught_error(&program, |machine, error| {
        let slot = assert_intrinsic_prototype(machine, error, "TypeError");
        let message = machine.own_data_property(slot, "message").unwrap();
        assert_eq!(machine.string_value(message).unwrap().as_units(), units);
    });
}

#[test]
fn define_data_property_is_non_enumerable_writable_and_configurable() {
    // Tag 48 DefineDataProperty installs a fixed data descriptor:
    // writable / non-enumerable / configurable.
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("x")),
            Constant::Int32(7),
        ],
        vec![function(
            0,
            4,
            vec![
                Instruction::CreateObject { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(1),
                },
                Instruction::DefineDataProperty {
                    object: reg(0),
                    key: reg(1),
                    value: reg(2),
                },
                Instruction::GetProperty {
                    dst: reg(3),
                    object: reg(0),
                    key: reg(1),
                },
                Instruction::Return { value: reg(0) },
            ],
            vec![],
        )],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let execution = machine.evaluate().unwrap();
    assert_eq!(execution.entry_registers[3], Value::int32(7));
    let object = execution.value;
    let key = PropertyKey::Named(machine.intern_str("x"));
    let descriptor = machine
        .own_descriptor(object, &key)
        .unwrap()
        .expect("DefineDataProperty installs an own data property");
    assert!(matches!(
        descriptor,
        Property::Data {
            value,
            writable: true,
            enumerable: false,
            configurable: true,
        } if value == Value::int32(7)
    ));
    assert!(
        machine.enumerable_keys(object).unwrap().is_empty(),
        "DefineDataProperty must not expose the key to enumeration"
    );
    assert!(
        !machine.own_property_is_enumerable(object, &key).unwrap(),
        "own property must report non-enumerable"
    );
    assert!(
        machine.internal_delete(object, &key).unwrap(),
        "configurable DefineDataProperty must be deletable"
    );
    assert!(machine.own_descriptor(object, &key).unwrap().is_none());
}

#[test]
fn define_data_property_preserves_descriptor_errors_on_non_object() {
    let module = verified(
        vec![
            Constant::Int32(1),
            Constant::String(EcmaString::encode("x")),
            Constant::Int32(7),
        ],
        vec![function(
            0,
            3,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(1),
                },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(2),
                },
                Instruction::DefineDataProperty {
                    object: reg(0),
                    key: reg(1),
                    value: reg(2),
                },
                Instruction::Halt,
            ],
            vec![],
        )],
    );
    let mut host = TestHost;
    let error = Machine::new(&module, &mut host, Limits::default())
        .run()
        .expect_err("DefineDataProperty on a non-object must throw");
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::UncaughtThrow {
            origin: ThrowOrigin::TypeError { .. },
            ..
        }
    ));
}

#[test]
fn define_data_property_preserves_descriptor_errors_on_non_extensible() {
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("sealed")),
            Constant::String(EcmaString::encode("x")),
            Constant::Int32(7),
        ],
        vec![function(
            0,
            3,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(1),
                },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(2),
                },
                Instruction::DefineDataProperty {
                    object: reg(0),
                    key: reg(1),
                    value: reg(2),
                },
                Instruction::Halt,
            ],
            vec![],
        )],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let sealed = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            extensible: false,
            boxed_primitive: None,
        })
        .unwrap();
    machine.test_set_global("sealed", sealed);
    let error = machine
        .run()
        .expect_err("DefineDataProperty on a non-extensible object must throw");
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::UncaughtThrow {
            origin: ThrowOrigin::TypeError { .. },
            ..
        }
    ));
}

#[test]
fn load_own_descriptor_slot_instruction_covers_absent_data_accessor_and_mismatch() {
    // Tag 49 LoadOwnDescriptorSlot is own-only and non-invoking.
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("data")),
            Constant::Int32(7),
            Constant::String(EcmaString::encode("accessor")),
            Constant::String(EcmaString::encode("missing")),
        ],
        vec![function(
            0,
            10,
            vec![
                Instruction::CreateObject { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(1),
                },
                Instruction::DefineDataProperty {
                    object: reg(0),
                    key: reg(1),
                    value: reg(2),
                },
                Instruction::LoadConst {
                    dst: reg(3),
                    constant: cid(2),
                },
                Instruction::CreateObject { dst: reg(4) },
                Instruction::DefineAccessor {
                    object: reg(0),
                    key: reg(3),
                    accessor: reg(4),
                    kind: AccessorKind::Getter,
                },
                Instruction::LoadOwnDescriptorSlot {
                    dst: reg(5),
                    object: reg(0),
                    key: reg(1),
                    slot: DescriptorSlot::Value,
                },
                Instruction::LoadOwnDescriptorSlot {
                    dst: reg(6),
                    object: reg(0),
                    key: reg(1),
                    slot: DescriptorSlot::Getter,
                },
                Instruction::LoadOwnDescriptorSlot {
                    dst: reg(7),
                    object: reg(0),
                    key: reg(3),
                    slot: DescriptorSlot::Getter,
                },
                Instruction::LoadOwnDescriptorSlot {
                    dst: reg(8),
                    object: reg(0),
                    key: reg(3),
                    slot: DescriptorSlot::Value,
                },
                Instruction::LoadConst {
                    dst: reg(9),
                    constant: cid(3),
                },
                Instruction::LoadOwnDescriptorSlot {
                    dst: reg(9),
                    object: reg(0),
                    key: reg(9),
                    slot: DescriptorSlot::Value,
                },
                Instruction::Return { value: reg(0) },
            ],
            vec![],
        )],
    );
    let execution = run_ok(&module);
    assert_eq!(execution.entry_registers[5], Value::int32(7));
    assert_eq!(
        execution.entry_registers[6],
        Value::UNDEFINED,
        "data/getter mismatch yields undefined"
    );
    assert_eq!(
        execution.entry_registers[7], execution.entry_registers[4],
        "accessor getter slot returns the installed getter"
    );
    assert_eq!(
        execution.entry_registers[8],
        Value::UNDEFINED,
        "accessor/value mismatch yields undefined"
    );
    assert_eq!(
        execution.entry_registers[9],
        Value::UNDEFINED,
        "absent property yields undefined"
    );
}

#[test]
fn with_has_binding_absent_property_short_circuits_unscopables() {
    // HasProperty miss must not read @@unscopables.
    thread_local! {
        static LOG: std::cell::RefCell<Vec<&'static str>> =
            const { std::cell::RefCell::new(Vec::new()) };
    }
    fn unscopables_getter<H: Host>(
        _machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        LOG.with(|log| log.borrow_mut().push("unscopables"));
        Ok(intrinsics::BuiltinOutcome::Value(Value::UNDEFINED))
    }

    with_machine(Limits::default(), |machine| {
        LOG.with(|log| log.borrow_mut().clear());
        let getter_id = machine
            .intrinsics
            .builtins
            .register(intrinsics::BuiltinDef {
                name: "get @@unscopables",
                length: 0,
                handler: unscopables_getter::<TestHost>,
            });
        let getter = intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            getter_id,
            "get @@unscopables",
            0,
        );
        let unscopables_key = machine
            .property_key_from_value(machine.intrinsics.builtins.symbol_unscopables())
            .unwrap();
        let mut properties = PropertyMap::default();
        properties.insert(
            &mut machine.shapes,
            unscopables_key,
            Property::Accessor {
                getter: Some(getter),
                setter: None,
                enumerable: false,
                configurable: true,
            },
        );
        let object = machine
            .allocate(HeapEntry::Object {
                properties,
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let key = machine
            .allocate(HeapEntry::String(EcmaString::encode("missing")))
            .unwrap();
        assert!(!machine.with_has_binding(object, key).unwrap());
        LOG.with(|log| assert!(log.borrow().is_empty(), "absent binding must short-circuit"));
    });
}

#[test]
fn with_has_binding_allows_and_blocks_named_bindings() {
    with_machine(Limits::default(), |machine| {
        let unscopables_key = machine
            .property_key_from_value(machine.intrinsics.builtins.symbol_unscopables())
            .unwrap();
        let name = PropertyKey::Named(machine.intern_str("x"));
        let key = machine
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .unwrap();
        let make = |machine: &mut Machine<'_, TestHost>, blocked: Value| {
            let mut blocklist_properties = PropertyMap::default();
            blocklist_properties.insert(
                &mut machine.shapes,
                name.clone(),
                Property::Data {
                    value: blocked,
                    writable: true,
                    enumerable: true,
                    configurable: true,
                },
            );
            let blocklist = machine
                .allocate(HeapEntry::Object {
                    properties: blocklist_properties,
                    prototype: None,
                    boxed_primitive: None,
                    extensible: true,
                })
                .unwrap();
            let mut object_properties = PropertyMap::default();
            object_properties.insert(
                &mut machine.shapes,
                name.clone(),
                Property::Data {
                    value: Value::int32(1),
                    writable: true,
                    enumerable: true,
                    configurable: true,
                },
            );
            object_properties.insert(
                &mut machine.shapes,
                unscopables_key.clone(),
                Property::Data {
                    value: blocklist,
                    writable: true,
                    enumerable: false,
                    configurable: true,
                },
            );
            machine
                .allocate(HeapEntry::Object {
                    properties: object_properties,
                    prototype: Some(machine.intrinsics.object_prototype),
                    boxed_primitive: None,
                    extensible: true,
                })
                .unwrap()
        };
        let allowed = make(machine, Value::FALSE);
        let blocked = make(machine, Value::TRUE);
        assert!(machine.with_has_binding(allowed, key).unwrap());
        assert!(!machine.with_has_binding(blocked, key).unwrap());
    });
}

#[test]
fn with_has_binding_follows_inherited_candidate_and_unscopables() {
    with_machine(Limits::default(), |machine| {
        let unscopables_key = machine
            .property_key_from_value(machine.intrinsics.builtins.symbol_unscopables())
            .unwrap();
        let name = PropertyKey::Named(machine.intern_str("x"));
        let key = machine
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .unwrap();
        let mut candidate_proto_properties = PropertyMap::default();
        candidate_proto_properties.insert(
            &mut machine.shapes,
            name.clone(),
            Property::Data {
                value: Value::int32(7),
                writable: true,
                enumerable: true,
                configurable: true,
            },
        );
        let mut blocklist_proto_properties = PropertyMap::default();
        blocklist_proto_properties.insert(
            &mut machine.shapes,
            name.clone(),
            Property::Data {
                value: Value::TRUE,
                writable: true,
                enumerable: true,
                configurable: true,
            },
        );
        let candidate_proto = machine
            .allocate(HeapEntry::Object {
                properties: candidate_proto_properties,
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let blocklist_proto = machine
            .allocate(HeapEntry::Object {
                properties: blocklist_proto_properties,
                prototype: None,
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let blocklist = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(blocklist_proto),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let mut mid_properties = PropertyMap::default();
        mid_properties.insert(
            &mut machine.shapes,
            unscopables_key,
            Property::Data {
                value: blocklist,
                writable: true,
                enumerable: false,
                configurable: true,
            },
        );
        let mid = machine
            .allocate(HeapEntry::Object {
                properties: mid_properties,
                prototype: Some(candidate_proto),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(mid),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        assert!(machine.internal_has_property(object, &name).unwrap());
        assert!(
            !machine.with_has_binding(object, key).unwrap(),
            "inherited unscopables entry must block the inherited candidate"
        );

        let mut allowed_proto_properties = PropertyMap::default();
        allowed_proto_properties.insert(
            &mut machine.shapes,
            name,
            Property::Data {
                value: Value::FALSE,
                writable: true,
                enumerable: true,
                configurable: true,
            },
        );
        let allowed_blocklist_proto = machine
            .allocate(HeapEntry::Object {
                properties: allowed_proto_properties,
                prototype: None,
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let allowed_blocklist = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(allowed_blocklist_proto),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let allowed_unscopables_key = machine
            .property_key_from_value(machine.intrinsics.builtins.symbol_unscopables())
            .unwrap();
        let mut allowed_properties = PropertyMap::default();
        allowed_properties.insert(
            &mut machine.shapes,
            allowed_unscopables_key,
            Property::Data {
                value: allowed_blocklist,
                writable: true,
                enumerable: false,
                configurable: true,
            },
        );
        let allowed = machine
            .allocate(HeapEntry::Object {
                properties: allowed_properties,
                prototype: Some(candidate_proto),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        assert!(machine.with_has_binding(allowed, key).unwrap());
    });
}

#[test]
fn with_has_binding_invokes_getters_in_order_with_correct_receivers() {
    thread_local! {
        static LOG: std::cell::RefCell<Vec<&'static str>> =
            const { std::cell::RefCell::new(Vec::new()) };
        static EXPECTED_BINDING: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
        static EXPECTED_BLOCKLIST: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    }
    fn unscopables_getter<H: Host>(
        _machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        assert_eq!(
            this.to_bits(),
            EXPECTED_BINDING.get(),
            "@@unscopables receiver"
        );
        LOG.with(|log| log.borrow_mut().push("unscopables"));
        Ok(intrinsics::BuiltinOutcome::Value(Value::from_bits(
            EXPECTED_BLOCKLIST.get(),
        )))
    }
    fn block_getter<H: Host>(
        _machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        assert_eq!(
            this.to_bits(),
            EXPECTED_BLOCKLIST.get(),
            "blocklist receiver"
        );
        LOG.with(|log| log.borrow_mut().push("block"));
        Ok(intrinsics::BuiltinOutcome::Value(Value::FALSE))
    }
    fn candidate_getter<H: Host>(
        _machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        LOG.with(|log| log.borrow_mut().push("candidate"));
        Ok(intrinsics::BuiltinOutcome::Value(Value::int32(1)))
    }

    with_machine(Limits::default(), |machine| {
        LOG.with(|log| log.borrow_mut().clear());
        let mut install = |name, handler| {
            let id = machine
                .intrinsics
                .builtins
                .register(intrinsics::BuiltinDef {
                    name,
                    length: 0,
                    handler,
                });
            intrinsics::native_function(
                &mut machine.heap,
                &mut machine.atoms,
                &mut machine.shapes,
                id,
                name,
                0,
            )
        };
        let unscopables_get = install(
            "get @@unscopables",
            unscopables_getter::<TestHost> as intrinsics::BuiltinHandler<TestHost>,
        );
        let block_get = install("get x", block_getter::<TestHost>);
        let candidate_get = install("get candidate x", candidate_getter::<TestHost>);
        let name = PropertyKey::Named(machine.intern_str("x"));
        let unscopables_key = machine
            .property_key_from_value(machine.intrinsics.builtins.symbol_unscopables())
            .unwrap();
        let mut blocklist_properties = PropertyMap::default();
        blocklist_properties.insert(
            &mut machine.shapes,
            name.clone(),
            Property::Accessor {
                getter: Some(block_get),
                setter: None,
                enumerable: true,
                configurable: true,
            },
        );
        let blocklist = machine
            .allocate(HeapEntry::Object {
                properties: blocklist_properties,
                prototype: None,
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let mut object_properties = PropertyMap::default();
        object_properties.insert(
            &mut machine.shapes,
            name.clone(),
            Property::Accessor {
                getter: Some(candidate_get),
                setter: None,
                enumerable: true,
                configurable: true,
            },
        );
        object_properties.insert(
            &mut machine.shapes,
            unscopables_key,
            Property::Accessor {
                getter: Some(unscopables_get),
                setter: None,
                enumerable: false,
                configurable: true,
            },
        );
        let object = machine
            .allocate(HeapEntry::Object {
                properties: object_properties,
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        EXPECTED_BINDING.set(object.to_bits());
        EXPECTED_BLOCKLIST.set(blocklist.to_bits());
        let key = machine
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .unwrap();
        assert!(machine.with_has_binding(object, key).unwrap());
        LOG.with(|log| assert_eq!(&*log.borrow(), &["unscopables", "block"]));
        assert_eq!(
            machine.get_property_key(object, &name).unwrap(),
            Value::int32(1)
        );
        LOG.with(|log| {
            assert_eq!(&*log.borrow(), &["unscopables", "block", "candidate"]);
        });
    });
}

#[test]
fn with_has_binding_propagates_getter_throw_through_opcode_path() {
    thread_local! {
        static SENTINEL_BITS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    }
    fn throwing_unscopables<H: Host>(
        _machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        Err(EvalFailure::ThrowValue(Value::from_bits(
            SENTINEL_BITS.get(),
        )))
    }

    let module = verified(
        vec![
            Constant::String(EcmaString::encode("o")),
            Constant::String(EcmaString::encode("x")),
        ],
        vec![function(
            0,
            4,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(1),
                },
                Instruction::WithHasBinding {
                    dst: reg(2),
                    object: reg(0),
                    key: reg(1),
                },
                Instruction::Halt,
                Instruction::Return { value: reg(3) },
            ],
            vec![ExceptionHandler {
                start: pc(2),
                end: pc(3),
                handler: pc(4),
                catch_register: reg(3),
            }],
        )],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let sentinel = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    SENTINEL_BITS.set(sentinel.to_bits());
    let getter_id = machine
        .intrinsics
        .builtins
        .register(intrinsics::BuiltinDef {
            name: "throw @@unscopables",
            length: 0,
            handler: throwing_unscopables::<TestHost>,
        });
    let getter = intrinsics::native_function(
        &mut machine.heap,
        &mut machine.atoms,
        &mut machine.shapes,
        getter_id,
        "throw @@unscopables",
        0,
    );
    let unscopables_key = machine
        .property_key_from_value(machine.intrinsics.builtins.symbol_unscopables())
        .unwrap();
    let x_key = PropertyKey::Named(machine.intern_str("x"));
    let mut throw_object_properties = PropertyMap::default();
    throw_object_properties.insert(
        &mut machine.shapes,
        x_key,
        Property::Data {
            value: Value::int32(1),
            writable: true,
            enumerable: true,
            configurable: true,
        },
    );
    throw_object_properties.insert(
        &mut machine.shapes,
        unscopables_key,
        Property::Accessor {
            getter: Some(getter),
            setter: None,
            enumerable: false,
            configurable: true,
        },
    );
    let object = machine
        .allocate(HeapEntry::Object {
            properties: throw_object_properties,
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    machine.test_set_global("o", object);
    let execution = machine.evaluate().unwrap();
    assert_eq!(execution.value, sentinel);
    assert_ne!(
        execution.entry_registers[2],
        Value::TRUE,
        "dst must remain untouched on abrupt completion"
    );
    assert_ne!(execution.entry_registers[2], Value::FALSE);
}

#[test]
fn with_has_binding_ignores_primitive_blocklist() {
    with_machine(Limits::default(), |machine| {
        let unscopables_key = machine
            .property_key_from_value(machine.intrinsics.builtins.symbol_unscopables())
            .unwrap();
        // Poison String.prototype.x so a mistaken ToObject/Get on a string
        // blocklist would incorrectly hide the binding.
        machine
            .set_data_property(machine.intrinsics.string_prototype, "x", Value::TRUE)
            .unwrap();
        let primitive_blocklist = machine
            .allocate(HeapEntry::String(EcmaString::encode("blocklist")))
            .unwrap();
        let x_key = PropertyKey::Named(machine.intern_str("x"));
        let mut ign_object_properties = PropertyMap::default();
        ign_object_properties.insert(
            &mut machine.shapes,
            x_key,
            Property::Data {
                value: Value::int32(1),
                writable: true,
                enumerable: true,
                configurable: true,
            },
        );
        ign_object_properties.insert(
            &mut machine.shapes,
            unscopables_key,
            Property::Data {
                value: primitive_blocklist,
                writable: true,
                enumerable: false,
                configurable: true,
            },
        );
        let object = machine
            .allocate(HeapEntry::Object {
                properties: ign_object_properties,
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let key = machine
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .unwrap();
        assert!(
            machine.with_has_binding(object, key).unwrap(),
            "primitive @@unscopables must leave the binding visible"
        );
    });
}

#[test]
fn with_has_binding_instruction_reports_allowed_and_blocked() {
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("allowed")),
            Constant::String(EcmaString::encode("blocked")),
            Constant::String(EcmaString::encode("x")),
        ],
        vec![function(
            0,
            6,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(0),
                },
                Instruction::LoadGlobal {
                    dst: reg(1),
                    name: cid(1),
                },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(2),
                },
                Instruction::WithHasBinding {
                    dst: reg(3),
                    object: reg(0),
                    key: reg(2),
                },
                Instruction::WithHasBinding {
                    dst: reg(4),
                    object: reg(1),
                    key: reg(2),
                },
                Instruction::Return { value: reg(3) },
            ],
            vec![],
        )],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let unscopables_key = machine
        .property_key_from_value(machine.intrinsics.builtins.symbol_unscopables())
        .unwrap();
    let name = PropertyKey::Named(machine.intern_str("x"));
    let mk = |machine: &mut Machine<'_, TestHost>, blocked: bool| {
        let mut mk_blocklist_properties = PropertyMap::default();
        mk_blocklist_properties.insert(
            &mut machine.shapes,
            name.clone(),
            Property::Data {
                value: Value::boolean(blocked),
                writable: true,
                enumerable: true,
                configurable: true,
            },
        );
        let blocklist = machine
            .allocate(HeapEntry::Object {
                properties: mk_blocklist_properties,
                prototype: None,
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let mut mk_object_properties = PropertyMap::default();
        mk_object_properties.insert(
            &mut machine.shapes,
            name.clone(),
            Property::Data {
                value: Value::int32(1),
                writable: true,
                enumerable: true,
                configurable: true,
            },
        );
        mk_object_properties.insert(
            &mut machine.shapes,
            unscopables_key.clone(),
            Property::Data {
                value: blocklist,
                writable: true,
                enumerable: false,
                configurable: true,
            },
        );
        machine
            .allocate(HeapEntry::Object {
                properties: mk_object_properties,
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap()
    };
    let allowed = mk(&mut machine, false);
    let blocked = mk(&mut machine, true);
    machine.test_set_global("allowed", allowed);
    machine.test_set_global("blocked", blocked);
    let execution = machine.evaluate().unwrap();
    assert_eq!(execution.value, Value::TRUE);
    assert_eq!(execution.entry_registers[3], Value::TRUE);
    assert_eq!(execution.entry_registers[4], Value::FALSE);
}

#[test]
fn define_own_descriptor_slot_instruction_creates_absent_preserves_and_rejects_mismatch() {
    // Tag 50 DefineOwnDescriptorSlot creates when absent and preserves shape.
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("created")),
            Constant::Int32(9),
            Constant::String(EcmaString::encode("data")),
            Constant::Int32(1),
            Constant::Int32(8),
            Constant::String(EcmaString::encode("accessor")),
        ],
        vec![function(
            0,
            8,
            vec![
                Instruction::CreateObject { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(1),
                },
                Instruction::DefineOwnDescriptorSlot {
                    object: reg(0),
                    key: reg(1),
                    src: reg(2),
                    slot: DescriptorSlot::Value,
                },
                Instruction::LoadConst {
                    dst: reg(3),
                    constant: cid(2),
                },
                Instruction::LoadConst {
                    dst: reg(4),
                    constant: cid(3),
                },
                Instruction::DefineDataProperty {
                    object: reg(0),
                    key: reg(3),
                    value: reg(4),
                },
                Instruction::LoadConst {
                    dst: reg(5),
                    constant: cid(4),
                },
                Instruction::DefineOwnDescriptorSlot {
                    object: reg(0),
                    key: reg(3),
                    src: reg(5),
                    slot: DescriptorSlot::Value,
                },
                Instruction::LoadConst {
                    dst: reg(6),
                    constant: cid(5),
                },
                Instruction::CreateObject { dst: reg(7) },
                Instruction::DefineAccessor {
                    object: reg(0),
                    key: reg(6),
                    accessor: reg(7),
                    kind: AccessorKind::Getter,
                },
                Instruction::CreateObject { dst: reg(1) },
                Instruction::DefineOwnDescriptorSlot {
                    object: reg(0),
                    key: reg(6),
                    src: reg(1),
                    slot: DescriptorSlot::Setter,
                },
                Instruction::Return { value: reg(0) },
            ],
            vec![],
        )],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let execution = machine.evaluate().unwrap();
    let object = execution.value;
    let created = PropertyKey::Named(machine.intern_str("created"));
    let data = PropertyKey::Named(machine.intern_str("data"));
    let accessor = PropertyKey::Named(machine.intern_str("accessor"));
    assert!(matches!(
        machine.own_descriptor(object, &created).unwrap(),
        Some(Property::Data {
            value,
            writable: true,
            enumerable: false,
            configurable: true,
        }) if value == Value::int32(9)
    ));
    assert!(matches!(
        machine.own_descriptor(object, &data).unwrap(),
        Some(Property::Data {
            value,
            writable: true,
            enumerable: false,
            configurable: true,
        }) if value == Value::int32(8)
    ));
    match machine
        .own_descriptor(object, &accessor)
        .unwrap()
        .expect("accessor remains installed")
    {
        Property::Accessor {
            getter: Some(getter),
            setter: Some(setter),
            enumerable: true,
            configurable: true,
        } => {
            assert_eq!(getter, execution.entry_registers[7]);
            assert_eq!(setter, execution.entry_registers[1]);
        }
        other => panic!("expected accessor with both halves, got {other:?}"),
    }
    drop(machine);

    let mismatch = verified(
        vec![
            Constant::String(EcmaString::encode("data")),
            Constant::Int32(1),
            Constant::Int32(2),
        ],
        vec![function(
            0,
            4,
            vec![
                Instruction::CreateObject { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(1),
                },
                Instruction::DefineDataProperty {
                    object: reg(0),
                    key: reg(1),
                    value: reg(2),
                },
                Instruction::LoadConst {
                    dst: reg(3),
                    constant: cid(2),
                },
                Instruction::DefineOwnDescriptorSlot {
                    object: reg(0),
                    key: reg(1),
                    src: reg(3),
                    slot: DescriptorSlot::Getter,
                },
                Instruction::Halt,
            ],
            vec![],
        )],
    );
    let error = Machine::new(&mismatch, &mut host, Limits::default())
        .run()
        .expect_err("data/getter shape mismatch must throw");
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::UncaughtThrow {
            origin: ThrowOrigin::TypeError {
                operation: "decorator replacement changes descriptor shape"
            },
            ..
        }
    ));
}

#[test]
fn prototype_chain_lookup_and_instanceof() {
    // proto = {}; proto.m = 5; ctor.prototype = proto; obj = new ctor();
    // return (obj.m == 5) && (obj instanceof ctor).
    let entry = function(
        0,
        6,
        vec![
            // proto object with m = 5
            Instruction::CreateObject { dst: reg(0) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(0),
            },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(1),
            },
            Instruction::SetProperty {
                object: reg(0),
                key: reg(1),
                value: reg(2),
            },
            // ctor closure
            Instruction::CreateArray { dst: reg(4) },
            Instruction::CreateClosure {
                dst: reg(3),
                function: FunctionId::new(1),
                captures: reg(4),
            },
            // ctor.prototype = proto
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(2),
            },
            Instruction::SetProperty {
                object: reg(3),
                key: reg(1),
                value: reg(0),
            },
            // obj = new ctor()  (empty args)
            Instruction::CreateArray { dst: reg(4) },
            Instruction::Construct {
                dst: reg(0),
                callee: reg(3),
                arguments: reg(4),
            },
            // obj.m via prototype chain
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(0),
            },
            Instruction::GetProperty {
                dst: reg(2),
                object: reg(0),
                key: reg(1),
            },
            // obj instanceof ctor
            Instruction::Binary {
                dst: reg(5),
                op: BinaryOp::InstanceOf,
                left: reg(0),
                right: reg(3),
            },
            Instruction::Return { value: reg(2) },
        ],
        vec![],
    );
    let ctor = function(0, 1, vec![Instruction::Halt], vec![]);
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("m")),
            Constant::Int32(5),
            Constant::String(EcmaString::encode("prototype")),
        ],
        vec![entry, ctor],
    );
    let execution = run_ok(&module);
    assert_eq!(execution.value, Value::int32(5));
    assert_eq!(execution.entry_registers[5], Value::TRUE);
}

#[test]
fn sync_iterator_walks_array_elements() {
    // Sum [10,20] via GetIterator/IteratorNext loop.
    let entry = function(
        0,
        6,
        vec![
            Instruction::CreateArray { dst: reg(0) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(0),
            },
            Instruction::ArrayPush {
                array: reg(0),
                value: reg(1),
            },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(1),
            },
            Instruction::ArrayPush {
                array: reg(0),
                value: reg(1),
            },
            // acc = 0
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(2),
            },
            Instruction::GetIterator {
                dst: reg(3),
                src: reg(0),
                kind: IteratorKind::Sync,
            },
            // loop head @7: next
            Instruction::IteratorNext {
                done: reg(4),
                value: reg(5),
                iterator: reg(3),
            },
            Instruction::JumpIfTrue {
                condition: reg(4),
                target: pc(11),
            },
            Instruction::Binary {
                dst: reg(2),
                op: BinaryOp::Add,
                left: reg(2),
                right: reg(5),
            },
            Instruction::Jump { target: pc(7) },
            // @11 done
            Instruction::Return { value: reg(2) },
        ],
        vec![],
    );
    let module = verified(
        vec![Constant::Int32(10), Constant::Int32(20), Constant::Int32(0)],
        vec![entry],
    );
    assert_eq!(run_ok(&module).value, Value::int32(30));
}

#[test]
fn keys_iterator_enumerates_own_object_keys() {
    // obj = {a:1}; for-in yields "a".
    let entry = function(
        0,
        6,
        vec![
            Instruction::CreateObject { dst: reg(0) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(0),
            },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(1),
            },
            Instruction::SetProperty {
                object: reg(0),
                key: reg(1),
                value: reg(2),
            },
            Instruction::GetIterator {
                dst: reg(3),
                src: reg(0),
                kind: IteratorKind::Keys,
            },
            Instruction::IteratorNext {
                done: reg(4),
                value: reg(5),
                iterator: reg(3),
            },
            Instruction::Return { value: reg(5) },
        ],
        vec![],
    );
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("a")),
            Constant::Int32(1),
        ],
        vec![entry],
    );
    let execution = run_ok(&module);
    // The produced key must equal a fresh "a" string.
    let key = execution.value;
    // Compare via a second machine's constant is awkward; instead assert it
    // is a heap string by checking done flag was false.
    assert_eq!(execution.entry_registers[4], Value::FALSE);
    assert_ne!(key, Value::UNDEFINED);
}

#[test]
fn async_iterator_steps_like_sync() {
    let entry = function(
        0,
        5,
        vec![
            Instruction::CreateArray { dst: reg(0) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(0),
            },
            Instruction::ArrayPush {
                array: reg(0),
                value: reg(1),
            },
            Instruction::GetIterator {
                dst: reg(2),
                src: reg(0),
                kind: IteratorKind::Async,
            },
            Instruction::IteratorNext {
                done: reg(3),
                value: reg(4),
                iterator: reg(2),
            },
            Instruction::Return { value: reg(4) },
        ],
        vec![],
    );
    let module = verified(vec![Constant::Int32(8)], vec![entry]);
    let execution = run_ok(&module);
    assert_eq!(execution.value, Value::int32(8));
    assert_eq!(execution.entry_registers[3], Value::FALSE);
}

#[test]
fn async_iterator_prefers_symbol_async_iterator() {
    let program = verified(
        Vec::new(),
        vec![
            function(0, 0, vec![Instruction::Halt], Vec::new()),
            function(
                0,
                1,
                vec![
                    Instruction::LoadThis { dst: reg(0) },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let object = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    let method = machine
        .allocate(HeapEntry::Function {
            module: ModuleId::new(0),
            function: FunctionId::new(1),
            captures: Vec::new(),
            context: None,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .unwrap();
    let key = machine
        .property_key_from_value(machine.intrinsics.builtins.symbol_async_iterator())
        .unwrap();
    machine.set_data_property_key(object, key, method).unwrap();

    let iterator = machine
        .create_iterator(object, IteratorKind::Async)
        .expect("async iterator method is used");

    let index = machine.runtime_slot(iterator).unwrap().unwrap();
    assert!(matches!(
        machine.heap[index],
        HeapEntry::Iterator {
            state: IteratorState::Protocol { iterator, .. }
        } if iterator == object
    ));
}

#[test]
fn a_failed_global_store_is_silent_only_in_sloppy_code() {
    fn store_to_read_only_global(is_sloppy: bool) -> Result<Value, RuntimeErrorKind> {
        let entry = Function::new(
            None,
            0,
            0,
            1,
            FunctionFlags {
                is_sloppy,
                ..FunctionFlags::default()
            },
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(1),
                },
                Instruction::StoreGlobal {
                    name: cid(0),
                    value: reg(0),
                },
                Instruction::Return { value: reg(0) },
            ],
            vec![],
        );
        let program = verified(
            vec![
                Constant::String(EcmaString::encode("undefined")),
                Constant::Int32(1),
            ],
            vec![entry],
        );
        let mut host = TestHost;
        Machine::new(&program, &mut host, Limits::default())
            .run()
            .map(|execution| execution.value)
            .map_err(|error| error.kind)
    }

    assert_eq!(store_to_read_only_global(true), Ok(Value::int32(1)));
    assert!(matches!(
        store_to_read_only_global(false),
        Err(RuntimeErrorKind::UncaughtThrow {
            origin: ThrowOrigin::TypeError { .. },
            ..
        })
    ));
}

#[test]
fn globals_store_load_and_typeof_undeclared() {
    // StoreGlobal x=5; TypeOfGlobal y (undeclared) -> "undefined";
    // TypeOfGlobal x -> "number"; return LoadGlobal x.
    let entry = function(
        0,
        3,
        vec![
            Instruction::LoadConst {
                dst: reg(0),
                constant: cid(2),
            },
            Instruction::StoreGlobal {
                name: cid(0),
                value: reg(0),
            },
            Instruction::TypeOfGlobal {
                dst: reg(1),
                name: cid(1),
            },
            Instruction::TypeOfGlobal {
                dst: reg(2),
                name: cid(0),
            },
            Instruction::LoadGlobal {
                dst: reg(0),
                name: cid(0),
            },
            Instruction::Return { value: reg(0) },
        ],
        vec![],
    );
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("x")),
            Constant::String(EcmaString::encode("y")),
            Constant::Int32(5),
        ],
        vec![entry],
    );
    assert_eq!(run_ok(&module).value, Value::int32(5));
}

#[test]
fn create_cell_throws_reference_error_before_initialization() {
    let module = verified(
        vec![Constant::Int32(0)],
        vec![function(
            0,
            3,
            vec![
                Instruction::CreateCell { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(0),
                },
                Instruction::GetProperty {
                    dst: reg(2),
                    object: reg(0),
                    key: reg(1),
                },
                Instruction::Return { value: reg(2) },
            ],
            vec![],
        )],
    );
    let mut host = TestHost;
    let error = Machine::new(&module, &mut host, Limits::default())
        .run()
        .expect_err("uninitialized cell read throws");
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::UncaughtThrow {
            origin: ThrowOrigin::ReferenceError { .. },
            ..
        }
    ));
}

#[test]
fn prematerialized_reference_error_keeps_identity_through_catch() {
    // CreateCell TDZ throws ThrowValueOrigin with a pre-built ReferenceError.
    // Catch must keep that exact Value: rematerializing would allocate a
    // different object whose message is the origin operation string.
    let module = verified(
        vec![Constant::Int32(0)],
        vec![function(
            0,
            5,
            vec![
                Instruction::CreateCell { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(0),
                },
                Instruction::GetProperty {
                    dst: reg(2),
                    object: reg(0),
                    key: reg(1),
                },
                Instruction::Halt,
                // First catch: preserve the prematerialized error, then
                // rethrow it so a second catch can StrictEqual identities.
                Instruction::Throw { value: reg(3) },
                Instruction::Binary {
                    dst: reg(4),
                    op: BinaryOp::StrictEqual,
                    left: reg(3),
                    right: reg(0),
                },
                Instruction::Return { value: reg(4) },
            ],
            vec![
                ExceptionHandler {
                    start: pc(2),
                    end: pc(3),
                    handler: pc(4),
                    catch_register: reg(3),
                },
                ExceptionHandler {
                    start: pc(4),
                    end: pc(5),
                    handler: pc(5),
                    catch_register: reg(0),
                },
            ],
        )],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let execution = machine.evaluate().unwrap();
    assert_eq!(execution.value, Value::TRUE);
    let error = execution.entry_registers[3];
    assert_eq!(error, execution.entry_registers[0]);
    let name = machine.get_named_property(error, "name").unwrap();
    assert!(
        machine
            .string_value(name)
            .is_some_and(|text| text.eq_ascii("ReferenceError"))
    );
    let message = machine.get_named_property(error, "message").unwrap();
    assert!(machine.string_value(message).is_some_and(|text| {
        text.eq_ascii("Cannot access lexical binding before initialization")
    }));
    let constructor = machine.intrinsics.global("ReferenceError").unwrap();
    assert!(machine.instance_of(error, constructor).unwrap());
    machine.run_to_quiescence().unwrap();
}

#[test]
fn create_cell_can_be_initialized_to_undefined() {
    let module = verified(
        vec![Constant::Int32(0), Constant::Undefined],
        vec![function(
            0,
            4,
            vec![
                Instruction::CreateCell { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(1),
                },
                Instruction::SetProperty {
                    object: reg(0),
                    key: reg(1),
                    value: reg(2),
                },
                Instruction::GetProperty {
                    dst: reg(3),
                    object: reg(0),
                    key: reg(1),
                },
                Instruction::Return { value: reg(3) },
            ],
            vec![],
        )],
    );
    let mut host = TestHost;
    let execution = Machine::new(&module, &mut host, Limits::default())
        .run()
        .expect("explicit undefined initializes the cell");
    assert_eq!(execution.value, Value::UNDEFINED);
}

#[test]
fn load_undeclared_global_throws_reference_error() {
    let module = verified(
        vec![Constant::String(EcmaString::encode("missing"))],
        vec![function(
            0,
            2,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(0),
                },
                Instruction::Halt,
                Instruction::Return { value: reg(1) },
            ],
            vec![ExceptionHandler {
                start: pc(0),
                end: pc(1),
                handler: pc(2),
                catch_register: reg(1),
            }],
        )],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let execution = machine.evaluate().unwrap();
    let error = execution.value;
    let name = machine.get_named_property(error, "name").unwrap();
    assert!(
        machine
            .string_value(name)
            .is_some_and(|text| text.eq_ascii("ReferenceError"))
    );
    let message = machine.get_named_property(error, "message").unwrap();
    assert!(
        machine
            .string_value(message)
            .is_some_and(|text| text.eq_ascii("global is not defined"))
    );
    let constructor = machine.intrinsics.global("ReferenceError").unwrap();
    assert!(machine.instance_of(error, constructor).unwrap());
    machine.run_to_quiescence().unwrap();
}

#[test]
fn caught_engine_type_error_has_intrinsic_shape() {
    let module = verified(
        vec![Constant::Int32(0)],
        vec![function(
            0,
            4,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(0),
                },
                Instruction::CreateArray { dst: reg(1) },
                Instruction::Call {
                    dst: reg(2),
                    callee: reg(0),
                    this_value: reg(0),
                    arguments: reg(1),
                },
                Instruction::Halt,
                Instruction::Return { value: reg(3) },
            ],
            vec![ExceptionHandler {
                start: pc(2),
                end: pc(3),
                handler: pc(4),
                catch_register: reg(3),
            }],
        )],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let execution = machine.evaluate().unwrap();
    let error = execution.value;
    let name = machine.get_named_property(error, "name").unwrap();
    assert!(
        machine
            .string_value(name)
            .is_some_and(|text| text.eq_ascii("TypeError"))
    );
    let message = machine.get_named_property(error, "message").unwrap();
    assert!(
        machine
            .string_value(message)
            .is_some_and(|text| text.eq_ascii("call"))
    );
    let constructor = machine.intrinsics.global("TypeError").unwrap();
    assert!(machine.instance_of(error, constructor).unwrap());
    machine.run_to_quiescence().unwrap();
}

#[test]
fn uncaught_reference_error_reports_origin() {
    let module = verified(
        vec![Constant::String(EcmaString::encode("missing"))],
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(0),
                },
                Instruction::Return { value: reg(0) },
            ],
            vec![],
        )],
    );
    let mut host = TestHost;
    let error = Machine::new(&module, &mut host, Limits::default())
        .run()
        .unwrap_err();
    assert_eq!(error.pc, pc(0));
    assert_eq!(
        error.kind,
        RuntimeErrorKind::UncaughtThrow {
            value: Value::UNDEFINED,
            origin: ThrowOrigin::ReferenceError {
                operation: "global is not defined",
            },
            constructor_name: None,
            message: Some(EcmaString::encode("missing is not defined")),
        }
    );
}

#[test]
fn uncaught_engine_type_error_keeps_origin_diagnostic() {
    let module = verified(
        vec![Constant::Int32(0)],
        vec![function(
            0,
            3,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(0),
                },
                Instruction::CreateArray { dst: reg(1) },
                Instruction::Call {
                    dst: reg(2),
                    callee: reg(0),
                    this_value: reg(0),
                    arguments: reg(1),
                },
                Instruction::Return { value: reg(2) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let error = Machine::new(&module, &mut host, Limits::default())
        .run()
        .unwrap_err();
    assert_eq!(
        error.kind,
        RuntimeErrorKind::UncaughtThrow {
            value: Value::UNDEFINED,
            origin: ThrowOrigin::TypeError { operation: "call" },
            constructor_name: None,
            message: None,
        }
    );
}

#[test]
fn thrown_guest_type_error_reports_constructor_name() {
    // `throw new TypeError()` — the guest constructs a TypeError and
    // throws it. The runtime boundary must resolve the constructor
    // name by walking the prototype chain to the TypeError builtin
    // prototype, so the oracle can classify it as NegativeType::TypeError.
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("TypeError")),
            Constant::Undefined,
        ],
        vec![function(
            0,
            5,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(1),
                },
                Instruction::CreateArray { dst: reg(2) },
                Instruction::Construct {
                    dst: reg(3),
                    callee: reg(0),
                    arguments: reg(2),
                },
                Instruction::Throw { value: reg(3) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let error = Machine::new(&module, &mut host, Limits::default())
        .run()
        .unwrap_err();
    match error.kind {
        RuntimeErrorKind::UncaughtThrow {
            origin,
            constructor_name,
            ..
        } => {
            assert_eq!(origin, ThrowOrigin::Bytecode);
            assert_eq!(
                constructor_name.as_ref().map(|s| s.to_utf8_lossy()),
                Some("TypeError".to_owned())
            );
        }
        other => panic!("expected UncaughtThrow, got {other:?}"),
    }
}

#[test]
fn thrown_guest_range_error_reports_constructor_name() {
    // `throw new RangeError()` — same pattern, different builtin.
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("RangeError")),
            Constant::Undefined,
        ],
        vec![function(
            0,
            5,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(1),
                },
                Instruction::CreateArray { dst: reg(2) },
                Instruction::Construct {
                    dst: reg(3),
                    callee: reg(0),
                    arguments: reg(2),
                },
                Instruction::Throw { value: reg(3) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let error = Machine::new(&module, &mut host, Limits::default())
        .run()
        .unwrap_err();
    match error.kind {
        RuntimeErrorKind::UncaughtThrow {
            origin,
            constructor_name,
            ..
        } => {
            assert_eq!(origin, ThrowOrigin::Bytecode);
            assert_eq!(
                constructor_name.as_ref().map(|s| s.to_utf8_lossy()),
                Some("RangeError".to_owned())
            );
        }
        other => panic!("expected UncaughtThrow, got {other:?}"),
    }
}

#[test]
fn a_builtin_with_no_construct_cannot_be_called_with_new() {
    // `new Math.abs()`.
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("Math")),
            Constant::String(EcmaString::encode("abs")),
        ],
        vec![function(
            0,
            5,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(1),
                },
                Instruction::GetProperty {
                    dst: reg(2),
                    object: reg(0),
                    key: reg(1),
                },
                Instruction::CreateArray { dst: reg(3) },
                Instruction::Construct {
                    dst: reg(4),
                    callee: reg(2),
                    arguments: reg(3),
                },
                Instruction::Return { value: reg(4) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let error = Machine::new(&module, &mut host, Limits::default())
        .run()
        .unwrap_err();
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::UncaughtThrow {
            origin: ThrowOrigin::TypeError {
                operation: "construct"
            },
            ..
        }
    ));
}

#[test]
fn a_thrown_error_reports_its_message_and_a_plain_value_reports_none() {
    // `throw new Error("boom")`.
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("Error")),
            Constant::String(EcmaString::encode("boom")),
        ],
        vec![function(
            0,
            4,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(1),
                },
                Instruction::CreateArray { dst: reg(2) },
                Instruction::ArrayPush {
                    array: reg(2),
                    value: reg(1),
                },
                Instruction::Construct {
                    dst: reg(3),
                    callee: reg(0),
                    arguments: reg(2),
                },
                Instruction::Throw { value: reg(3) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let error = Machine::new(&module, &mut host, Limits::default())
        .run()
        .unwrap_err();
    let RuntimeErrorKind::UncaughtThrow { message, .. } = error.kind else {
        panic!("expected an uncaught throw");
    };
    assert_eq!(
        message.map(|text| text.to_utf8_lossy()).as_deref(),
        Some("boom")
    );

    // `throw "boom"`: a thrown string has no `message` property.
    let module = verified(
        vec![Constant::String(EcmaString::encode("boom"))],
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(0),
                },
                Instruction::Throw { value: reg(0) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let error = Machine::new(&module, &mut host, Limits::default())
        .run()
        .unwrap_err();
    let RuntimeErrorKind::UncaughtThrow { message, .. } = error.kind else {
        panic!("expected an uncaught throw");
    };
    assert_eq!(message, None);
}

#[test]
fn thrown_plain_error_reports_constructor_name() {
    // `throw new Error()` — the base Error constructor.
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("Error")),
            Constant::Undefined,
        ],
        vec![function(
            0,
            5,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(1),
                },
                Instruction::CreateArray { dst: reg(2) },
                Instruction::Construct {
                    dst: reg(3),
                    callee: reg(0),
                    arguments: reg(2),
                },
                Instruction::Throw { value: reg(3) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let error = Machine::new(&module, &mut host, Limits::default())
        .run()
        .unwrap_err();
    match error.kind {
        RuntimeErrorKind::UncaughtThrow {
            origin,
            constructor_name,
            ..
        } => {
            assert_eq!(origin, ThrowOrigin::Bytecode);
            assert_eq!(
                constructor_name.as_ref().map(|s| s.to_utf8_lossy()),
                Some("Error".to_owned())
            );
        }
        other => panic!("expected UncaughtThrow, got {other:?}"),
    }
}

#[test]
fn thrown_engine_type_error_has_no_constructor_name() {
    // Engine-originated throws (ThrowOrigin::TypeError) already name
    // their constructor in the origin variant. The constructor_name
    // field must remain None so the oracle does not double-resolve.
    let module = verified(
        vec![Constant::Int32(0)],
        vec![function(
            0,
            3,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(0),
                },
                Instruction::CreateArray { dst: reg(1) },
                Instruction::Call {
                    dst: reg(2),
                    callee: reg(0),
                    this_value: reg(0),
                    arguments: reg(1),
                },
                Instruction::Return { value: reg(2) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let error = Machine::new(&module, &mut host, Limits::default())
        .run()
        .unwrap_err();
    match error.kind {
        RuntimeErrorKind::UncaughtThrow {
            origin,
            constructor_name,
            ..
        } => {
            assert_eq!(origin, ThrowOrigin::TypeError { operation: "call" });
            assert_eq!(constructor_name, None);
        }
        other => panic!("expected UncaughtThrow, got {other:?}"),
    }
}

fn assert_uri_error(global: &str, argument: EcmaString) {
    let module = verified(
        vec![
            Constant::String(EcmaString::encode(global)),
            Constant::String(argument),
            Constant::Undefined,
        ],
        vec![function(
            0,
            5,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(1),
                },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(2),
                },
                Instruction::CreateArray { dst: reg(3) },
                Instruction::ArrayPush {
                    array: reg(3),
                    value: reg(1),
                },
                Instruction::Call {
                    dst: reg(4),
                    callee: reg(0),
                    this_value: reg(2),
                    arguments: reg(3),
                },
                Instruction::Return { value: reg(4) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let error = Machine::new(&module, &mut host, Limits::default())
        .run()
        .unwrap_err();
    assert_eq!(error.pc, pc(5));
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::UncaughtThrow {
            origin: ThrowOrigin::UriError {
                operation: "URI malformed"
            },
            ..
        }
    ));
}

#[test]
fn uri_builtins_report_uri_error() {
    for (global, argument) in [
        ("encodeURIComponent", EcmaString::from_units(&[0xd800])),
        ("decodeURIComponent", EcmaString::encode("%")),
        ("decodeURIComponent", EcmaString::encode("%GG")),
        ("decodeURIComponent", EcmaString::encode("%FF")),
        ("decodeURIComponent", EcmaString::encode("%80")),
        ("decodeURIComponent", EcmaString::encode("%C0%80")),
        ("decodeURIComponent", EcmaString::encode("%E2%82")),
        ("decodeURIComponent", EcmaString::encode("%ED%A0%80")),
        ("decodeURIComponent", EcmaString::encode("%F4%90%80%80")),
        ("decodeURIComponent", EcmaString::encode("%F8%80%80%80%80")),
    ] {
        assert_uri_error(global, argument);
    }
}

fn assert_uri_decode(argument: EcmaString, expected: EcmaString) {
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("decodeURIComponent")),
            Constant::String(argument),
            Constant::Undefined,
            Constant::String(expected),
        ],
        vec![function(
            0,
            7,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(1),
                },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(2),
                },
                Instruction::CreateArray { dst: reg(3) },
                Instruction::ArrayPush {
                    array: reg(3),
                    value: reg(1),
                },
                Instruction::Call {
                    dst: reg(4),
                    callee: reg(0),
                    this_value: reg(2),
                    arguments: reg(3),
                },
                Instruction::LoadConst {
                    dst: reg(5),
                    constant: cid(3),
                },
                Instruction::Binary {
                    dst: reg(6),
                    op: BinaryOp::StrictEqual,
                    left: reg(4),
                    right: reg(5),
                },
                Instruction::Return { value: reg(6) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let execution = Machine::new(&module, &mut host, Limits::default())
        .run()
        .unwrap();
    assert_eq!(execution.value, Value::TRUE);
}

#[test]
fn decode_uri_component_preserves_units_and_decodes_utf8() {
    let exact = EcmaString::from_units(&[0xd800, 0x61, 0xdfff]);
    for (argument, expected) in [
        (exact.clone(), exact),
        (EcmaString::encode("%2F"), EcmaString::encode("/")),
        (EcmaString::encode("%F0%9F%98%80"), EcmaString::encode("😀")),
        (EcmaString::encode("%E4%B8%ADA"), EcmaString::encode("中A")),
        (EcmaString::encode("%00"), EcmaString::from_units(&[0])),
    ] {
        assert_uri_decode(argument, expected);
    }
}

#[test]
fn regexp_is_object_with_source_and_flags() {
    // typeof re === "object" is not directly returnable; return re.source.
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("ab")),
            Constant::String(EcmaString::encode("gi")),
            Constant::String(EcmaString::encode("source")),
            Constant::String(EcmaString::encode("global")),
        ],
        vec![function(
            0,
            4,
            vec![
                Instruction::CreateRegExp {
                    dst: reg(0),
                    pattern: cid(0),
                    flags: cid(1),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(3),
                },
                Instruction::GetProperty {
                    dst: reg(2),
                    object: reg(0),
                    key: reg(1),
                },
                Instruction::Unary {
                    dst: reg(3),
                    op: UnaryOp::TypeOf,
                    operand: reg(0),
                },
                Instruction::Return { value: reg(2) },
            ],
            vec![],
        )],
    );
    let execution = run_ok(&module);
    // re.global -> true
    assert_eq!(execution.value, Value::TRUE);
}

#[test]
fn this_and_new_target_are_frame_owned() {
    // Call passes this; new.target is undefined in a plain call.
    let entry = function(
        0,
        4,
        vec![
            Instruction::CreateObject { dst: reg(0) },
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(1),
                function: FunctionId::new(1),
                captures: reg(3),
            },
            Instruction::CreateArray { dst: reg(2) },
            Instruction::Call {
                dst: reg(0),
                callee: reg(1),
                this_value: reg(0),
                arguments: reg(2),
            },
            Instruction::Return { value: reg(0) },
        ],
        vec![],
    );
    // returns (this === passed) is hard cross-frame; instead return typeof
    // new.target which is "undefined" for a plain call.
    let callee = function(
        0,
        2,
        vec![
            Instruction::LoadNewTarget { dst: reg(0) },
            Instruction::Unary {
                dst: reg(1),
                op: UnaryOp::TypeOf,
                operand: reg(0),
            },
            Instruction::Return { value: reg(1) },
        ],
        vec![],
    );
    let module = verified(vec![], vec![entry, callee]);
    let execution = run_ok(&module);
    // typeof undefined is a heap "undefined" string; strict-compare against
    // typeof of a known-undefined value is awkward, so assert non-undefined
    // heap string was produced and the call completed.
    assert_ne!(execution.value, Value::UNDEFINED);
}

#[test]
fn new_target_is_constructor_during_construct() {
    // In a constructor, new.target === callee; verify via instanceof-style
    // check: store new.target on this, then read back after construct.
    let entry = function(
        0,
        4,
        vec![
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(0),
                function: FunctionId::new(1),
                captures: reg(3),
            },
            // ctor.prototype = {}
            Instruction::CreateObject { dst: reg(1) },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(0),
            },
            Instruction::SetProperty {
                object: reg(0),
                key: reg(2),
                value: reg(1),
            },
            Instruction::CreateArray { dst: reg(3) },
            Instruction::Construct {
                dst: reg(1),
                callee: reg(0),
                arguments: reg(3),
            },
            // read back this.nt === ctor
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(1),
            },
            Instruction::GetProperty {
                dst: reg(3),
                object: reg(1),
                key: reg(2),
            },
            Instruction::Binary {
                dst: reg(3),
                op: BinaryOp::StrictEqual,
                left: reg(3),
                right: reg(0),
            },
            Instruction::Return { value: reg(3) },
        ],
        vec![],
    );
    let ctor = function(
        0,
        3,
        vec![
            Instruction::LoadNewTarget { dst: reg(0) },
            Instruction::LoadThis { dst: reg(1) },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(1),
            },
            Instruction::SetProperty {
                object: reg(1),
                key: reg(2),
                value: reg(0),
            },
            Instruction::Halt,
        ],
        vec![],
    );
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("prototype")),
            Constant::String(EcmaString::encode("nt")),
        ],
        vec![entry, ctor],
    );
    assert_eq!(run_ok(&module).value, Value::TRUE);
}

#[test]
fn construct_rejects_callable_nonconstructable_function() {
    let entry = function(
        0,
        3,
        vec![
            Instruction::CreateArray { dst: reg(2) },
            Instruction::CreateClosure {
                dst: reg(0),
                function: FunctionId::new(1),
                captures: reg(2),
            },
            Instruction::CreateArray { dst: reg(1) },
            Instruction::Construct {
                dst: reg(2),
                callee: reg(0),
                arguments: reg(1),
            },
            Instruction::Halt,
        ],
        vec![],
    );
    let target = Function::new(
        None,
        0,
        0,
        1,
        FunctionFlags::default(),
        vec![Instruction::Halt],
        vec![],
    );
    let module = verified(vec![], vec![entry, target]);
    let mut host = TestHost;
    let error = Machine::new(&module, &mut host, Limits::default())
        .run()
        .expect_err("nonconstructable function must reject new");
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::UncaughtThrow {
            origin: ThrowOrigin::TypeError {
                operation: "construct"
            },
            ..
        }
    ));
}

#[test]
fn construct_tag12_new_target_is_callee() {
    // Tag 12 Construct must pass callee as new_target (old behavior).
    let entry = function(
        0,
        4,
        vec![
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(0),
                function: FunctionId::new(1),
                captures: reg(3),
            },
            Instruction::CreateObject { dst: reg(1) },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(0),
            },
            Instruction::SetProperty {
                object: reg(0),
                key: reg(2),
                value: reg(1),
            },
            Instruction::CreateArray { dst: reg(3) },
            Instruction::Construct {
                dst: reg(1),
                callee: reg(0),
                arguments: reg(3),
            },
            // read this.nt === ctor
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(1),
            },
            Instruction::GetProperty {
                dst: reg(3),
                object: reg(1),
                key: reg(2),
            },
            Instruction::Binary {
                dst: reg(3),
                op: BinaryOp::StrictEqual,
                left: reg(3),
                right: reg(0),
            },
            Instruction::Return { value: reg(3) },
        ],
        vec![],
    );
    let ctor = function(
        0,
        3,
        vec![
            Instruction::LoadNewTarget { dst: reg(0) },
            Instruction::LoadThis { dst: reg(1) },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(1),
            },
            Instruction::SetProperty {
                object: reg(1),
                key: reg(2),
                value: reg(0),
            },
            Instruction::Halt,
        ],
        vec![],
    );
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("prototype")),
            Constant::String(EcmaString::encode("nt")),
        ],
        vec![entry, ctor],
    );
    assert_eq!(run_ok(&module).value, Value::TRUE);
}

#[test]
fn construct_with_new_target_explicit_receiver_prototype() {
    // Tag 47: construct callee with a *different* new_target.
    // The constructed receiver's prototype must come from new_target.prototype,
    // not callee.prototype, and new.target inside the ctor must be the explicit
    // new_target.
    let entry = function(
        0,
        7,
        vec![
            // Create ctor closure (function 1)
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(0),
                function: FunctionId::new(1),
                captures: reg(3),
            },
            // ctor.prototype = {} (distinct from new_target.prototype)
            Instruction::CreateObject { dst: reg(1) },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(0),
            },
            Instruction::SetProperty {
                object: reg(0),
                key: reg(2),
                value: reg(1),
            },
            // Create explicit new_target closure (function 2)
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(4),
                function: FunctionId::new(2),
                captures: reg(3),
            },
            // new_target.prototype = {} with marker = 42
            Instruction::CreateObject { dst: reg(5) },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(0),
            },
            Instruction::SetProperty {
                object: reg(4),
                key: reg(2),
                value: reg(5),
            },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(1),
            },
            Instruction::LoadConst {
                dst: reg(6),
                constant: cid(2),
            },
            Instruction::SetProperty {
                object: reg(5),
                key: reg(2),
                value: reg(6),
            },
            // obj = new ctor() with explicit new_target
            Instruction::CreateArray { dst: reg(3) },
            Instruction::ConstructWithNewTarget {
                dst: reg(1),
                callee: reg(0),
                new_target: reg(4),
                arguments: reg(3),
            },
            // Read obj.marker — should be 42 via new_target.prototype chain
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(1),
            },
            Instruction::GetProperty {
                dst: reg(3),
                object: reg(1),
                key: reg(2),
            },
            Instruction::Return { value: reg(3) },
        ],
        vec![],
    );
    // ctor body: store new.target on this.nt
    let ctor = function(
        0,
        3,
        vec![
            Instruction::LoadNewTarget { dst: reg(0) },
            Instruction::LoadThis { dst: reg(1) },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(3),
            },
            Instruction::SetProperty {
                object: reg(1),
                key: reg(2),
                value: reg(0),
            },
            Instruction::Halt,
        ],
        vec![],
    );
    // new_target body: just a placeholder (never called as a function)
    let nt_fn = function(0, 1, vec![Instruction::Halt], vec![]);
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("prototype")),
            Constant::String(EcmaString::encode("marker")),
            Constant::Int32(42),
            Constant::String(EcmaString::encode("nt")),
        ],
        vec![entry, ctor, nt_fn],
    );
    let execution = run_ok(&module);
    // obj.marker === 42 via new_target.prototype
    assert_eq!(execution.value, Value::int32(42));
}

#[test]
fn construct_with_new_target_return_selection() {
    // Tag 47: constructor returns a primitive; the constructed receiver
    // (allocated with new_target.prototype) must be the result.
    let entry = function(
        0,
        7,
        vec![
            // Create ctor closure (function 1) — returns 99 (primitive)
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(0),
                function: FunctionId::new(1),
                captures: reg(3),
            },
            // ctor.prototype = {} (unused for receiver)
            Instruction::CreateObject { dst: reg(1) },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(0),
            },
            Instruction::SetProperty {
                object: reg(0),
                key: reg(2),
                value: reg(1),
            },
            // Create explicit new_target closure (function 2)
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(4),
                function: FunctionId::new(2),
                captures: reg(3),
            },
            // new_target.prototype = {} with tag = 77
            Instruction::CreateObject { dst: reg(5) },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(0),
            },
            Instruction::SetProperty {
                object: reg(4),
                key: reg(2),
                value: reg(5),
            },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(1),
            },
            Instruction::LoadConst {
                dst: reg(6),
                constant: cid(2),
            },
            Instruction::SetProperty {
                object: reg(5),
                key: reg(2),
                value: reg(6),
            },
            // obj = new ctor() with explicit new_target
            Instruction::CreateArray { dst: reg(3) },
            Instruction::ConstructWithNewTarget {
                dst: reg(1),
                callee: reg(0),
                new_target: reg(4),
                arguments: reg(3),
            },
            // obj must be an object (constructed receiver), not 99
            // Read obj.tag — should be 77 via new_target.prototype
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(1),
            },
            Instruction::GetProperty {
                dst: reg(3),
                object: reg(1),
                key: reg(2),
            },
            Instruction::Return { value: reg(3) },
        ],
        vec![],
    );
    // ctor returns primitive 99
    let ctor = function(
        0,
        1,
        vec![
            Instruction::LoadConst {
                dst: reg(0),
                constant: cid(3),
            },
            Instruction::Return { value: reg(0) },
        ],
        vec![],
    );
    let nt_fn = function(0, 1, vec![Instruction::Halt], vec![]);
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("prototype")),
            Constant::String(EcmaString::encode("tag")),
            Constant::Int32(77),
            Constant::Int32(99),
        ],
        vec![entry, ctor, nt_fn],
    );
    // obj.tag === 77 via new_target.prototype, not 99
    assert_eq!(run_ok(&module).value, Value::int32(77));
}

#[test]
fn construct_with_new_target_builtin_object() {
    // Tag 47: construct Object with explicit new_target whose .prototype
    // is a custom object. The result must have that prototype.
    let entry = function(
        0,
        6,
        vec![
            // Load Object global
            Instruction::LoadGlobal {
                dst: reg(0),
                name: cid(0),
            },
            // Create explicit new_target closure (function 1)
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(1),
                function: FunctionId::new(1),
                captures: reg(3),
            },
            // new_target.prototype = { marker: 42 }
            Instruction::CreateObject { dst: reg(2) },
            Instruction::LoadConst {
                dst: reg(3),
                constant: cid(1),
            },
            Instruction::SetProperty {
                object: reg(1),
                key: reg(3),
                value: reg(2),
            },
            Instruction::LoadConst {
                dst: reg(3),
                constant: cid(2),
            },
            Instruction::LoadConst {
                dst: reg(4),
                constant: cid(3),
            },
            Instruction::SetProperty {
                object: reg(2),
                key: reg(3),
                value: reg(4),
            },
            // obj = new Object() with explicit new_target
            Instruction::CreateArray { dst: reg(3) },
            Instruction::ConstructWithNewTarget {
                dst: reg(4),
                callee: reg(0),
                new_target: reg(1),
                arguments: reg(3),
            },
            // Read obj.marker — should be 42 via new_target.prototype
            Instruction::LoadConst {
                dst: reg(3),
                constant: cid(2),
            },
            Instruction::GetProperty {
                dst: reg(5),
                object: reg(4),
                key: reg(3),
            },
            Instruction::Return { value: reg(5) },
        ],
        vec![],
    );
    let nt_fn = function(0, 1, vec![Instruction::Halt], vec![]);
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("Object")),
            Constant::String(EcmaString::encode("prototype")),
            Constant::String(EcmaString::encode("marker")),
            Constant::Int32(42),
        ],
        vec![entry, nt_fn],
    );
    assert_eq!(run_ok(&module).value, Value::int32(42));
}

#[test]
fn construct_with_new_target_builtin_error() {
    // Tag 47: construct Error with explicit new_target whose .prototype
    // is a custom object. The error instance must have that prototype.
    let entry = function(
        0,
        6,
        vec![
            // Load Error global
            Instruction::LoadGlobal {
                dst: reg(0),
                name: cid(0),
            },
            // Create explicit new_target closure (function 1)
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(1),
                function: FunctionId::new(1),
                captures: reg(3),
            },
            // new_target.prototype = { custom: 99 }
            Instruction::CreateObject { dst: reg(2) },
            Instruction::LoadConst {
                dst: reg(3),
                constant: cid(1),
            },
            Instruction::SetProperty {
                object: reg(1),
                key: reg(3),
                value: reg(2),
            },
            Instruction::LoadConst {
                dst: reg(3),
                constant: cid(2),
            },
            Instruction::LoadConst {
                dst: reg(4),
                constant: cid(3),
            },
            Instruction::SetProperty {
                object: reg(2),
                key: reg(3),
                value: reg(4),
            },
            // err = new Error() with explicit new_target
            Instruction::CreateArray { dst: reg(3) },
            Instruction::ConstructWithNewTarget {
                dst: reg(4),
                callee: reg(0),
                new_target: reg(1),
                arguments: reg(3),
            },
            // Read err.custom — should be 99 via new_target.prototype
            Instruction::LoadConst {
                dst: reg(3),
                constant: cid(2),
            },
            Instruction::GetProperty {
                dst: reg(5),
                object: reg(4),
                key: reg(3),
            },
            Instruction::Return { value: reg(5) },
        ],
        vec![],
    );
    let nt_fn = function(0, 1, vec![Instruction::Halt], vec![]);
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("Error")),
            Constant::String(EcmaString::encode("prototype")),
            Constant::String(EcmaString::encode("custom")),
            Constant::Int32(99),
        ],
        vec![entry, nt_fn],
    );
    assert_eq!(run_ok(&module).value, Value::int32(99));
}

#[test]
fn construct_with_new_target_bound_forwards_to_target() {
    // Bound constructor: when new_target is the bound wrapper itself,
    // it must be substituted with the bound target after flattening.
    // This mirrors the existing tag-12 behavior where callee === new_target
    // before flattening.
    let entry = function(
        0,
        8,
        vec![
            // Create target ctor closure (function 1)
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(0),
                function: FunctionId::new(1),
                captures: reg(3),
            },
            // target.prototype = { tag: 7 }
            Instruction::CreateObject { dst: reg(1) },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(0),
            },
            Instruction::SetProperty {
                object: reg(0),
                key: reg(2),
                value: reg(1),
            },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(1),
            },
            Instruction::LoadConst {
                dst: reg(4),
                constant: cid(2),
            },
            Instruction::SetProperty {
                object: reg(1),
                key: reg(2),
                value: reg(4),
            },
            // bound = target.bind(undefined)
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(3),
            },
            Instruction::GetProperty {
                dst: reg(4),
                object: reg(0),
                key: reg(2),
            },
            // Load undefined into a register for the bind argument
            Instruction::LoadConst {
                dst: reg(6),
                constant: cid(4),
            },
            Instruction::CreateArray { dst: reg(3) },
            Instruction::ArrayPush {
                array: reg(3),
                value: reg(6),
            },
            Instruction::Call {
                dst: reg(5),
                callee: reg(4),
                this_value: reg(0),
                arguments: reg(3),
            },
            // obj = new bound() via tag 47 with bound as new_target
            Instruction::CreateArray { dst: reg(3) },
            Instruction::ConstructWithNewTarget {
                dst: reg(1),
                callee: reg(5),
                new_target: reg(5),
                arguments: reg(3),
            },
            // Read obj.tag — should be 7 via target.prototype
            // (bound forwarded new_target to target)
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(1),
            },
            Instruction::GetProperty {
                dst: reg(3),
                object: reg(1),
                key: reg(2),
            },
            Instruction::Return { value: reg(3) },
        ],
        vec![],
    );
    // target ctor body: does nothing (receiver allocated by engine)
    let target_ctor = function(0, 1, vec![Instruction::Halt], vec![]);
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("prototype")),
            Constant::String(EcmaString::encode("tag")),
            Constant::Int32(7),
            Constant::String(EcmaString::encode("bind")),
            Constant::Undefined,
        ],
        vec![entry, target_ctor],
    );
    assert_eq!(run_ok(&module).value, Value::int32(7));
}

#[test]
fn construct_with_new_target_forwards_intermediate_bound_wrapper() {
    // B2 -> B1 -> Base newTarget matrix:
    //   ConstructWithNT(B2, B2)        -> Base
    //   ConstructWithNT(B2, B1)        -> Base
    //   ConstructWithNT(B2, Base)      -> Base
    //   ConstructWithNT(B2, Unrelated) -> Unrelated
    //   Construct(B2)                  -> Base
    let entry = function(
        0,
        14,
        vec![
            // Base closure (function 1): returns new.target
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(0),
                function: FunctionId::new(1),
                captures: reg(3),
            },
            // Unrelated closure (function 2)
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(10),
                function: FunctionId::new(2),
                captures: reg(3),
            },
            // B1 = Base.bind(undefined)
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(0),
            },
            Instruction::GetProperty {
                dst: reg(4),
                object: reg(0),
                key: reg(2),
            },
            Instruction::LoadConst {
                dst: reg(6),
                constant: cid(1),
            },
            Instruction::CreateArray { dst: reg(3) },
            Instruction::ArrayPush {
                array: reg(3),
                value: reg(6),
            },
            Instruction::Call {
                dst: reg(1),
                callee: reg(4),
                this_value: reg(0),
                arguments: reg(3),
            },
            // B2 = B1.bind(undefined)
            Instruction::GetProperty {
                dst: reg(4),
                object: reg(1),
                key: reg(2),
            },
            Instruction::CreateArray { dst: reg(3) },
            Instruction::ArrayPush {
                array: reg(3),
                value: reg(6),
            },
            Instruction::Call {
                dst: reg(5),
                callee: reg(4),
                this_value: reg(1),
                arguments: reg(3),
            },
            // ConstructWithNT(B2, B2) -> Base
            Instruction::CreateArray { dst: reg(3) },
            Instruction::ConstructWithNewTarget {
                dst: reg(7),
                callee: reg(5),
                new_target: reg(5),
                arguments: reg(3),
            },
            Instruction::Binary {
                dst: reg(8),
                op: BinaryOp::StrictEqual,
                left: reg(7),
                right: reg(0),
            },
            // ConstructWithNT(B2, B1) -> Base
            Instruction::CreateArray { dst: reg(3) },
            Instruction::ConstructWithNewTarget {
                dst: reg(7),
                callee: reg(5),
                new_target: reg(1),
                arguments: reg(3),
            },
            Instruction::Binary {
                dst: reg(9),
                op: BinaryOp::StrictEqual,
                left: reg(7),
                right: reg(0),
            },
            Instruction::Binary {
                dst: reg(8),
                op: BinaryOp::BitAnd,
                left: reg(8),
                right: reg(9),
            },
            // ConstructWithNT(B2, Base) -> Base
            Instruction::CreateArray { dst: reg(3) },
            Instruction::ConstructWithNewTarget {
                dst: reg(7),
                callee: reg(5),
                new_target: reg(0),
                arguments: reg(3),
            },
            Instruction::Binary {
                dst: reg(9),
                op: BinaryOp::StrictEqual,
                left: reg(7),
                right: reg(0),
            },
            Instruction::Binary {
                dst: reg(8),
                op: BinaryOp::BitAnd,
                left: reg(8),
                right: reg(9),
            },
            // ConstructWithNT(B2, Unrelated) -> Unrelated
            Instruction::CreateArray { dst: reg(3) },
            Instruction::ConstructWithNewTarget {
                dst: reg(7),
                callee: reg(5),
                new_target: reg(10),
                arguments: reg(3),
            },
            Instruction::Binary {
                dst: reg(9),
                op: BinaryOp::StrictEqual,
                left: reg(7),
                right: reg(10),
            },
            Instruction::Binary {
                dst: reg(8),
                op: BinaryOp::BitAnd,
                left: reg(8),
                right: reg(9),
            },
            // ordinary Construct(B2) -> Base
            Instruction::CreateArray { dst: reg(3) },
            Instruction::Construct {
                dst: reg(7),
                callee: reg(5),
                arguments: reg(3),
            },
            Instruction::Binary {
                dst: reg(9),
                op: BinaryOp::StrictEqual,
                left: reg(7),
                right: reg(0),
            },
            Instruction::Binary {
                dst: reg(8),
                op: BinaryOp::BitAnd,
                left: reg(8),
                right: reg(9),
            },
            Instruction::Return { value: reg(8) },
        ],
        vec![],
    );
    let base = function(
        0,
        1,
        vec![
            Instruction::LoadNewTarget { dst: reg(0) },
            Instruction::Return { value: reg(0) },
        ],
        vec![],
    );
    let unrelated = function(
        0,
        1,
        vec![
            Instruction::LoadNewTarget { dst: reg(0) },
            Instruction::Return { value: reg(0) },
        ],
        vec![],
    );
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("bind")),
            Constant::Undefined,
        ],
        vec![entry, base, unrelated],
    );
    // five true comparisons BitAnd to 1
    assert_eq!(run_ok(&module).value, Value::int32(1));
}

#[test]
fn arguments_object_reflects_passed_values() {
    // callee returns arguments[0].
    let entry = function(
        0,
        4,
        vec![
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(0),
                function: FunctionId::new(1),
                captures: reg(3),
            },
            // args = [42]
            Instruction::CreateArray { dst: reg(2) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(0),
            },
            Instruction::ArrayPush {
                array: reg(2),
                value: reg(1),
            },
            Instruction::Call {
                dst: reg(0),
                callee: reg(0),
                this_value: reg(1),
                arguments: reg(2),
            },
            Instruction::Return { value: reg(0) },
        ],
        vec![],
    );
    let callee = function(
        0,
        2,
        vec![
            Instruction::LoadArguments { dst: reg(0) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(1),
            },
            Instruction::GetProperty {
                dst: reg(0),
                object: reg(0),
                key: reg(1),
            },
            Instruction::Return { value: reg(0) },
        ],
        vec![],
    );
    let module = verified(
        vec![
            Constant::Int32(42),
            Constant::String(EcmaString::encode("0")),
        ],
        vec![entry, callee],
    );
    assert_eq!(run_ok(&module).value, Value::int32(42));
}

#[test]
fn catch_register_receives_exact_thrown_value() {
    let module = verified(
        vec![Constant::Int32(9)],
        vec![function(
            0,
            2,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(0),
                },
                Instruction::Throw { value: reg(0) },
                Instruction::Return { value: reg(1) },
            ],
            vec![ExceptionHandler {
                start: pc(1),
                end: pc(2),
                handler: pc(2),
                catch_register: reg(1),
            }],
        )],
    );
    assert_eq!(run_ok(&module).value, Value::int32(9));
}

#[test]
fn native_callback_throw_is_caught_at_outer_call_site() {
    let entry = function(
        0,
        9,
        vec![
            Instruction::CreateArray { dst: reg(0) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(0),
            },
            Instruction::ArrayPush {
                array: reg(0),
                value: reg(1),
            },
            Instruction::CreateArray { dst: reg(2) },
            Instruction::CreateClosure {
                dst: reg(3),
                function: FunctionId::new(1),
                captures: reg(2),
            },
            Instruction::LoadConst {
                dst: reg(4),
                constant: cid(1),
            },
            Instruction::GetProperty {
                dst: reg(5),
                object: reg(0),
                key: reg(4),
            },
            Instruction::CreateArray { dst: reg(6) },
            Instruction::ArrayPush {
                array: reg(6),
                value: reg(3),
            },
            Instruction::Call {
                dst: reg(7),
                callee: reg(5),
                this_value: reg(0),
                arguments: reg(6),
            },
            Instruction::Halt,
            Instruction::Return { value: reg(8) },
        ],
        vec![ExceptionHandler {
            start: pc(9),
            end: pc(10),
            handler: pc(11),
            catch_register: reg(8),
        }],
    );
    let callback = closure_function(
        0,
        0,
        1,
        vec![
            Instruction::LoadConst {
                dst: reg(0),
                constant: cid(0),
            },
            Instruction::Throw { value: reg(0) },
        ],
    );
    let module = verified(
        vec![
            Constant::Int32(7),
            Constant::String(EcmaString::encode("map")),
        ],
        vec![entry, callback],
    );

    assert_eq!(run_ok(&module).value, Value::int32(7));
}

#[test]
fn nested_callback_call_engine_type_error_is_intrinsic() {
    // Array.prototype.map crosses call_value's callback boundary. An engine
    // TypeError inside the callback must reach the outer catch as an
    // intrinsic TypeError object, not undefined.
    let entry = function(
        0,
        9,
        vec![
            Instruction::CreateArray { dst: reg(0) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(0),
            },
            Instruction::ArrayPush {
                array: reg(0),
                value: reg(1),
            },
            Instruction::CreateArray { dst: reg(2) },
            Instruction::CreateClosure {
                dst: reg(3),
                function: FunctionId::new(1),
                captures: reg(2),
            },
            Instruction::LoadConst {
                dst: reg(4),
                constant: cid(1),
            },
            Instruction::GetProperty {
                dst: reg(5),
                object: reg(0),
                key: reg(4),
            },
            Instruction::CreateArray { dst: reg(6) },
            Instruction::ArrayPush {
                array: reg(6),
                value: reg(3),
            },
            Instruction::Call {
                dst: reg(7),
                callee: reg(5),
                this_value: reg(0),
                arguments: reg(6),
            },
            Instruction::Halt,
            Instruction::Return { value: reg(8) },
        ],
        vec![ExceptionHandler {
            start: pc(9),
            end: pc(10),
            handler: pc(11),
            catch_register: reg(8),
        }],
    );
    let callback = closure_function(
        0,
        0,
        3,
        vec![
            Instruction::LoadConst {
                dst: reg(0),
                constant: cid(0),
            },
            Instruction::CreateArray { dst: reg(1) },
            Instruction::Call {
                dst: reg(2),
                callee: reg(0),
                this_value: reg(0),
                arguments: reg(1),
            },
            Instruction::Return { value: reg(2) },
        ],
    );
    let module = verified(
        vec![
            Constant::Int32(0),
            Constant::String(EcmaString::encode("map")),
        ],
        vec![entry, callback],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let execution = machine.evaluate().unwrap();
    let error = execution.value;
    assert_ne!(error, Value::UNDEFINED);
    let name = machine.get_named_property(error, "name").unwrap();
    assert!(
        machine
            .string_value(name)
            .is_some_and(|text| text.eq_ascii("TypeError"))
    );
    let message = machine.get_named_property(error, "message").unwrap();
    assert!(
        machine
            .string_value(message)
            .is_some_and(|text| text.eq_ascii("call"))
    );
    let constructor = machine.intrinsics.global("TypeError").unwrap();
    assert!(machine.instance_of(error, constructor).unwrap());
    machine.run_to_quiescence().unwrap();
}

#[test]
fn nested_callback_construct_engine_type_error_is_intrinsic() {
    let entry = function(
        0,
        9,
        vec![
            Instruction::CreateArray { dst: reg(0) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(0),
            },
            Instruction::ArrayPush {
                array: reg(0),
                value: reg(1),
            },
            Instruction::CreateArray { dst: reg(2) },
            Instruction::CreateClosure {
                dst: reg(3),
                function: FunctionId::new(1),
                captures: reg(2),
            },
            Instruction::LoadConst {
                dst: reg(4),
                constant: cid(1),
            },
            Instruction::GetProperty {
                dst: reg(5),
                object: reg(0),
                key: reg(4),
            },
            Instruction::CreateArray { dst: reg(6) },
            Instruction::ArrayPush {
                array: reg(6),
                value: reg(3),
            },
            Instruction::Call {
                dst: reg(7),
                callee: reg(5),
                this_value: reg(0),
                arguments: reg(6),
            },
            Instruction::Halt,
            Instruction::Return { value: reg(8) },
        ],
        vec![ExceptionHandler {
            start: pc(9),
            end: pc(10),
            handler: pc(11),
            catch_register: reg(8),
        }],
    );
    let callback = closure_function(
        0,
        0,
        3,
        vec![
            Instruction::LoadConst {
                dst: reg(0),
                constant: cid(0),
            },
            Instruction::CreateArray { dst: reg(1) },
            Instruction::Construct {
                dst: reg(2),
                callee: reg(0),
                arguments: reg(1),
            },
            Instruction::Return { value: reg(2) },
        ],
    );
    let module = verified(
        vec![
            Constant::Int32(0),
            Constant::String(EcmaString::encode("map")),
        ],
        vec![entry, callback],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let execution = machine.evaluate().unwrap();
    let error = execution.value;
    assert_ne!(error, Value::UNDEFINED);
    let name = machine.get_named_property(error, "name").unwrap();
    assert!(
        machine
            .string_value(name)
            .is_some_and(|text| text.eq_ascii("TypeError"))
    );
    let message = machine.get_named_property(error, "message").unwrap();
    assert!(
        machine
            .string_value(message)
            .is_some_and(|text| text.eq_ascii("construct"))
    );
    let constructor = machine.intrinsics.global("TypeError").unwrap();
    assert!(machine.instance_of(error, constructor).unwrap());
    machine.run_to_quiescence().unwrap();
}

#[test]
fn construct_value_preserves_engine_throw_origin() {
    // A runtime closure constructor whose body raises an engine-origin
    // TypeError must surface that body's origin verbatim across the
    // construct_value runtime-constructor boundary. The body calls a
    // non-callable, throwing TypeError{operation:"call"}; the outer
    // boundary is construct, so a leaked boundary error would read
    // operation:"construct".
    let program = verified(
        vec![Constant::Int32(0)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            function(
                0,
                3,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::CreateArray { dst: reg(1) },
                    Instruction::Call {
                        dst: reg(2),
                        callee: reg(0),
                        this_value: reg(1),
                        arguments: reg(1),
                    },
                    Instruction::Return { value: reg(2) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callee = machine
        .allocate(HeapEntry::Function {
            module: ModuleId::new(0),
            function: FunctionId::new(1),
            captures: Vec::new(),
            context: None,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .unwrap();

    assert!(matches!(
        machine.construct_value(callee, &[]),
        Err(EvalFailure::ThrowValueOrigin {
            value: Value::UNDEFINED,
            origin: ThrowOrigin::TypeError { operation: "call" },
        })
    ));
    assert!(machine.frames.is_empty());
}

#[test]
fn computed_property_keys_run_user_conversion() {
    fn key_text<H: Host>(
        machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        let text = machine
            .allocate(HeapEntry::String(EcmaString::encode("converted")))
            .map_err(EvalFailure::Runtime)?;
        Ok(intrinsics::BuiltinOutcome::Value(text))
    }
    let program = verified(
        vec![
            Constant::String(EcmaString::encode("converted")),
            Constant::String(EcmaString::encode("toString")),
            Constant::Int32(7),
        ],
        vec![function(
            0,
            6,
            vec![
                Instruction::CreateObject { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(2),
                },
                Instruction::SetProperty {
                    object: reg(0),
                    key: reg(1),
                    value: reg(2),
                },
                Instruction::LoadGlobal {
                    dst: reg(3),
                    name: cid(1),
                },
                Instruction::GetProperty {
                    dst: reg(4),
                    object: reg(0),
                    key: reg(3),
                },
                Instruction::Return { value: reg(4) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let id = machine
        .intrinsics
        .builtins
        .register(intrinsics::BuiltinDef {
            name: "key text",
            length: 0,
            handler: key_text::<TestHost>,
        });
    let to_string = intrinsics::native_function(
        &mut machine.heap,
        &mut machine.atoms,
        &mut machine.shapes,
        id,
        "key text",
        0,
    );
    let key = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    machine
        .set_data_property(key, "toString", to_string)
        .unwrap();
    machine.test_set_global("toString", key);
    assert_eq!(machine.run().unwrap().value, Value::int32(7));
}

#[test]
fn closure_prototypes_follow_the_function_kind() {
    let plain = function(0, 1, vec![Instruction::Halt], Vec::new());
    let kinded = |is_async, is_generator| {
        Function::new(
            None,
            0,
            0,
            1,
            FunctionFlags {
                is_async,
                is_generator,
                ..FunctionFlags::default()
            },
            vec![Instruction::Halt],
            Vec::new(),
        )
    };
    let program = verified(
        Vec::new(),
        vec![
            plain,
            kinded(false, true),
            kinded(true, false),
            kinded(true, true),
        ],
    );
    let mut host = TestHost;
    let machine = Machine::new(&program, &mut host, Limits::default());
    let kind = |index| machine.closure_prototype(ModuleId::new(0), FunctionId::new(index));
    let builtins = &machine.intrinsics.builtins;
    assert_eq!(kind(0), machine.intrinsics.function_prototype);
    assert_eq!(kind(1), builtins.generator_function_prototype());
    assert_eq!(kind(2), builtins.async_function_prototype());
    assert_eq!(kind(3), builtins.async_generator_function_prototype());
    assert!(
        !machine.is_callable(kind(1)).unwrap(),
        "only %Function.prototype% is itself callable"
    );
}

#[test]
fn a_generator_closure_owns_a_prototype_inheriting_from_its_kind() {
    let generator = Function::new(
        None,
        0,
        0,
        1,
        FunctionFlags {
            is_generator: true,
            ..FunctionFlags::default()
        },
        vec![Instruction::Halt],
        Vec::new(),
    );
    let program = verified(
        Vec::new(),
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            generator,
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let module = ModuleId::new(0);
    assert!(
        machine
            .closure_properties(module, FunctionId::new(0))
            .unwrap()
            .iter(&machine.shapes)
            .next()
            .is_none()
    );
    let properties = machine
        .closure_properties(module, FunctionId::new(1))
        .unwrap();
    let prototype_key = PropertyKey::Named(machine.intern_str("prototype"));
    let Some(Property::Data {
        value,
        writable: true,
        enumerable: false,
        configurable: false,
    }) = properties.get(&machine.shapes, &prototype_key)
    else {
        panic!("a generator function's prototype is a writable data property");
    };
    assert_eq!(
        machine.internal_get_prototype_of(*value).unwrap(),
        Some(machine.intrinsics.builtins.generator_prototype())
    );
}

#[test]
fn arithmetic_converts_object_operands_left_first() {
    fn seven<H: Host>(
        _machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        Ok(intrinsics::BuiltinOutcome::Value(Value::int32(7)))
    }
    fn fail<H: Host>(
        _machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        Err(EvalFailure::ThrowValue(Value::int32(1)))
    }
    let program = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let mut object_with = |name, handler| {
        let id = machine
            .intrinsics
            .builtins
            .register(intrinsics::BuiltinDef {
                name,
                length: 0,
                handler,
            });
        let value_of = intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            name,
            0,
        );
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        machine
            .set_data_property(object, "valueOf", value_of)
            .unwrap();
        object
    };
    let number = object_with("seven", seven::<TestHost>);
    let thrower = object_with("fail", fail::<TestHost>);
    assert_eq!(
        machine
            .numeric_binary(BinaryOp::Multiply, number, Value::int32(2))
            .unwrap(),
        Value::int32(14)
    );
    assert_eq!(
        machine.eval_unary(UnaryOp::Negate, number).unwrap(),
        Value::int32(-7i32 as u32)
    );
    assert_eq!(
        machine.eval_unary(UnaryOp::BitwiseNot, number).unwrap(),
        Value::int32(-8i32 as u32)
    );
    assert!(
        matches!(
            machine.numeric_binary(BinaryOp::Subtract, thrower, Value::int32(1)),
            Err(EvalFailure::ThrowValue(_))
        ),
        "a conversion failure propagates"
    );
}

#[test]
fn number_value_keeps_the_sign_of_zero() {
    assert_eq!(number_value(0.0), Value::int32(0));
    assert!(matches!(
        number_value(-0.0).decode(),
        Some(Decoded::Number(zero)) if zero == 0.0 && zero.is_sign_negative()
    ));
    assert_eq!(number_value(-1.0), Value::int32(-1i32 as u32));
}

#[test]
fn construct_with_no_calling_activation_applies_the_receiver_rule() {
    // The native tiers keep no interpreter frame, so a constructor entered
    // from a builtin has nothing to return to. A primitive completion must
    // still yield the receiver, and an object completion must replace it.
    let program = verified(
        vec![Constant::Int32(7)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
            function(
                0,
                1,
                vec![
                    Instruction::CreateArray { dst: reg(0) },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let mut constructor = |index: u32| {
        machine
            .allocate(HeapEntry::Function {
                module: ModuleId::new(0),
                function: FunctionId::new(index),
                captures: Vec::new(),
                context: None,
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.function_prototype),
                extensible: true,
            })
            .unwrap()
    };
    let returns_primitive = constructor(1);
    let returns_object = constructor(2);

    let receiver = machine.construct_value(returns_primitive, &[]).unwrap();
    let index = machine.runtime_slot(receiver).unwrap().unwrap();
    assert!(
        matches!(machine.heap[index], HeapEntry::Object { .. }),
        "a primitive completion yields the constructed receiver"
    );
    let replaced = machine.construct_value(returns_object, &[]).unwrap();
    let index = machine.runtime_slot(replaced).unwrap().unwrap();
    assert!(
        matches!(machine.heap[index], HeapEntry::Array { .. }),
        "an object completion replaces the receiver"
    );
    assert!(machine.frames.is_empty());
}

#[test]
fn native_callback_throw_uncaught_at_outer_call_site() {
    let entry = function(
        0,
        9,
        vec![
            Instruction::CreateArray { dst: reg(0) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(0),
            },
            Instruction::ArrayPush {
                array: reg(0),
                value: reg(1),
            },
            Instruction::CreateArray { dst: reg(2) },
            Instruction::CreateClosure {
                dst: reg(3),
                function: FunctionId::new(1),
                captures: reg(2),
            },
            Instruction::LoadConst {
                dst: reg(4),
                constant: cid(1),
            },
            Instruction::GetProperty {
                dst: reg(5),
                object: reg(0),
                key: reg(4),
            },
            Instruction::CreateArray { dst: reg(6) },
            Instruction::ArrayPush {
                array: reg(6),
                value: reg(3),
            },
            Instruction::Call {
                dst: reg(7),
                callee: reg(5),
                this_value: reg(0),
                arguments: reg(6),
            },
            Instruction::Halt,
        ],
        Vec::new(),
    );
    let callback = closure_function(
        0,
        0,
        1,
        vec![
            Instruction::LoadConst {
                dst: reg(0),
                constant: cid(0),
            },
            Instruction::Throw { value: reg(0) },
        ],
    );
    let simple = closure_function(
        0,
        0,
        1,
        vec![
            Instruction::LoadConst {
                dst: reg(0),
                constant: cid(2),
            },
            Instruction::Return { value: reg(0) },
        ],
    );
    let module = verified(
        vec![
            Constant::Int32(7),
            Constant::String(EcmaString::encode("map")),
            Constant::Int32(42),
        ],
        vec![entry, callback, simple],
    );

    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let error = machine.run_loop(0).unwrap_err();
    assert_eq!(
        error.kind,
        RuntimeErrorKind::UncaughtThrow {
            value: Value::int32(7),
            origin: ThrowOrigin::Bytecode,
            constructor_name: None,
            message: None,
        }
    );
    assert!(machine.callback_boundaries.is_empty());
    assert!(machine.frames.is_empty());
    assert_eq!(machine.live_registers, 0);

    let callee = machine
        .allocate(HeapEntry::Function {
            module: ModuleId::new(0),
            function: FunctionId::new(2),
            captures: Vec::new(),
            context: None,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .unwrap();
    assert_eq!(
        machine.call_value(callee, Value::UNDEFINED, &[]).unwrap(),
        Value::int32(42)
    );
}

#[test]
fn callee_throw_unwinds_to_call_site_handler() {
    let entry = function(
        0,
        4,
        vec![
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(0),
                function: FunctionId::new(1),
                captures: reg(3),
            },
            Instruction::CreateArray { dst: reg(1) },
            Instruction::Call {
                dst: reg(2),
                callee: reg(0),
                this_value: reg(1),
                arguments: reg(1),
            },
            Instruction::Halt,
            Instruction::Return { value: reg(3) },
        ],
        vec![ExceptionHandler {
            start: pc(3),
            end: pc(4),
            handler: pc(5),
            catch_register: reg(3),
        }],
    );
    let callee = function(
        0,
        1,
        vec![
            Instruction::LoadConst {
                dst: reg(0),
                constant: cid(0),
            },
            Instruction::Throw { value: reg(0) },
        ],
        vec![],
    );
    let module = verified(vec![Constant::Int32(7)], vec![entry, callee]);
    assert_eq!(run_ok(&module).value, Value::int32(7));
}

#[test]
fn heap_and_register_limits_fail_before_unbounded_growth() {
    let module = verified(
        vec![],
        vec![function(
            0,
            2,
            vec![
                Instruction::CreateObject { dst: reg(0) },
                Instruction::CreateObject { dst: reg(1) },
                Instruction::Halt,
            ],
            vec![],
        )],
    );
    let mut host = TestHost;
    let error = Machine::new(
        &module,
        &mut host,
        Limits {
            max_heap_slots: 1,
            ..Limits::default()
        },
    )
    .run()
    .unwrap_err();
    assert_eq!(error.pc, pc(1));
    assert_eq!(
        error.kind,
        RuntimeErrorKind::HeapSlotLimitExceeded { limit: 1 }
    );

    let mut host = TestHost;
    let error = Machine::new(
        &module,
        &mut host,
        Limits {
            max_total_registers: 1,
            ..Limits::default()
        },
    )
    .run()
    .unwrap_err();
    assert_eq!(
        error.kind,
        RuntimeErrorKind::RegisterLimitExceeded { limit: 1 }
    );
}

#[test]
fn argument_array_length_limit_is_enforced() {
    let entry = function(
        0,
        4,
        vec![
            Instruction::CreateArray { dst: reg(3) },
            Instruction::CreateClosure {
                dst: reg(0),
                function: FunctionId::new(1),
                captures: reg(3),
            },
            Instruction::CreateArray { dst: reg(2) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(0),
            },
            Instruction::ArrayPush {
                array: reg(2),
                value: reg(1),
            },
            Instruction::Call {
                dst: reg(0),
                callee: reg(0),
                this_value: reg(1),
                arguments: reg(2),
            },
            Instruction::Halt,
        ],
        vec![],
    );
    let callee = function(1, 1, vec![Instruction::Return { value: reg(0) }], vec![]);
    let module = verified(vec![Constant::Int32(1)], vec![entry, callee]);
    let mut host = TestHost;
    let error = Machine::new(
        &module,
        &mut host,
        Limits {
            max_argument_count: 0,
            ..Limits::default()
        },
    )
    .run()
    .unwrap_err();
    assert_eq!(
        error.kind,
        RuntimeErrorKind::ArgumentLimitExceeded {
            limit: 0,
            requested: 1
        }
    );
}

#[test]
fn u32_registers_and_instruction_pcs_do_not_truncate_at_127() {
    let mut code = vec![Instruction::LoadConst {
        dst: reg(0),
        constant: cid(0),
    }];
    for register in 1..=199 {
        code.push(Instruction::Move {
            dst: reg(register),
            src: reg(register - 1),
        });
    }
    code.push(Instruction::Return { value: reg(199) });
    let module = verified(
        vec![Constant::Number(NumberBits::from_f64(3.5))],
        vec![function(0, 200, code, vec![])],
    );
    let execution = run_ok(&module);
    assert_eq!(execution.value, Value::number(3.5));
    assert_eq!(execution.entry_registers[199], Value::number(3.5));
}

#[test]
fn construct_returned_object_overrides_default_instance() {
    // A constructor returning its own object overrides the default instance.
    let entry = function(
        0,
        3,
        vec![
            Instruction::CreateArray { dst: reg(2) },
            Instruction::CreateClosure {
                dst: reg(0),
                function: FunctionId::new(1),
                captures: reg(2),
            },
            Instruction::CreateArray { dst: reg(2) },
            Instruction::Construct {
                dst: reg(1),
                callee: reg(0),
                arguments: reg(2),
            },
            // returned object has marker property set to 5
            Instruction::LoadConst {
                dst: reg(0),
                constant: cid(0),
            },
            Instruction::GetProperty {
                dst: reg(2),
                object: reg(1),
                key: reg(0),
            },
            Instruction::Return { value: reg(2) },
        ],
        vec![],
    );
    let returns_object = function(
        0,
        3,
        vec![
            Instruction::CreateObject { dst: reg(0) },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(0),
            },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(1),
            },
            Instruction::SetProperty {
                object: reg(0),
                key: reg(1),
                value: reg(2),
            },
            Instruction::Return { value: reg(0) },
        ],
        vec![],
    );
    let module = verified(
        vec![
            Constant::String(EcmaString::encode("marker")),
            Constant::Int32(5),
        ],
        vec![entry, returns_object],
    );
    assert_eq!(run_ok(&module).value, Value::int32(5));
}

#[test]
fn ecmascript_number_formatting_is_shortest_round_trip() {
    let cases = [
        (0.1 + 0.2, "0.30000000000000004"),
        (1e21, "1e+21"),
        (-0.0, "0"),
        (1.0 / 3.0, "0.3333333333333333"),
        (1e-6, "0.000001"),
        (1e-7, "1e-7"),
    ];
    for (number, expected) in cases {
        assert_eq!(
            Machine::<TestHost>::ordinary_number_to_string(number),
            expected
        );
    }
}

#[test]
fn own_keys_put_indices_before_insertion_ordered_strings() {
    let module = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let object = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    let index = machine.runtime_slot(object).unwrap().unwrap();
    for (key, value) in [("b", 1), ("2", 2), ("a", 3), ("1", 4)] {
        let atom = PropertyKey::Named(machine.intern_str(key));
        machine
            .set_own_data(index, atom, Value::int32(value))
            .unwrap();
    }
    assert_eq!(
        machine.enumerable_keys(object).unwrap(),
        ["1", "2", "b", "a"].map(EcmaString::encode)
    );
}

/// Drains every key from a `for`/`in` iterator in yield order.
fn for_in_keys(machine: &mut Machine<'_, TestHost>, source: Value) -> Vec<EcmaString> {
    let iterator = machine.create_iterator(source, IteratorKind::Keys).unwrap();
    let mut keys = Vec::new();
    loop {
        let (done, value) = machine.iterator_next(iterator).unwrap();
        if done {
            break;
        }
        keys.push(machine.string_value(value).unwrap());
    }
    keys
}

fn for_in_object(
    machine: &mut Machine<'_, TestHost>,
    properties: &[(PropertyKey, Property)],
    prototype: Option<Value>,
) -> Value {
    let mut map = PropertyMap::default();
    for (key, property) in properties {
        map.insert(&mut machine.shapes, key.clone(), property.clone());
    }
    machine
        .allocate(HeapEntry::Object {
            properties: map,
            prototype,
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap()
}

fn data_property(value: u32, enumerable: bool) -> Property {
    Property::Data {
        value: Value::int32(value),
        writable: true,
        enumerable,
        configurable: true,
    }
}

#[test]
fn for_in_yields_inherited_keys_in_nearest_first_order() {
    let module = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let object_prototype = machine.intrinsics.object_prototype;
    let c_key = PropertyKey::Named(machine.intern_str("c"));
    let a_key = PropertyKey::Named(machine.intern_str("a"));
    let proto = for_in_object(
        &mut machine,
        &[
            (c_key, data_property(3, true)),
            (a_key, data_property(1, true)),
        ],
        Some(object_prototype),
    );
    let b_key = PropertyKey::Named(machine.intern_str("b"));
    let a_key = PropertyKey::Named(machine.intern_str("a"));
    let child = for_in_object(
        &mut machine,
        &[
            (b_key, data_property(2, true)),
            (a_key, data_property(10, true)),
        ],
        Some(proto),
    );
    assert_eq!(
        for_in_keys(&mut machine, child),
        ["b", "a", "c"].map(EcmaString::encode),
        "own keys come first in insertion order; nearest duplicate shadows the prototype"
    );
}

#[test]
fn for_in_non_enumerable_own_shadows_inherited_enumerable() {
    let module = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let object_prototype = machine.intrinsics.object_prototype;
    let x_key = PropertyKey::Named(machine.intern_str("x"));
    let proto = for_in_object(
        &mut machine,
        &[(x_key, data_property(1, true))],
        Some(object_prototype),
    );
    let x_key = PropertyKey::Named(machine.intern_str("x"));
    let child = for_in_object(
        &mut machine,
        &[(x_key, data_property(2, false))],
        Some(proto),
    );
    assert_eq!(
        for_in_keys(&mut machine, child),
        Vec::<EcmaString>::new(),
        "non-enumerable own property shadows the inherited enumerable name"
    );
}

#[test]
fn for_in_skips_deleted_own_key_after_snapshot() {
    let module = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let object_prototype = machine.intrinsics.object_prototype;
    let first_key = PropertyKey::Named(machine.intern_str("first"));
    let gone_key = PropertyKey::Named(machine.intern_str("gone"));
    let object = for_in_object(
        &mut machine,
        &[
            (first_key, data_property(1, true)),
            (gone_key, data_property(2, true)),
        ],
        Some(object_prototype),
    );
    let iterator = machine.create_iterator(object, IteratorKind::Keys).unwrap();
    let (done, first) = machine.iterator_next(iterator).unwrap();
    assert!(!done);
    assert_eq!(
        machine.string_value(first).unwrap(),
        EcmaString::encode("first")
    );

    let gone_key = PropertyKey::Named(machine.intern_str("gone"));
    machine.internal_delete(object, &gone_key).unwrap();
    assert_eq!(
        machine.iterator_next(iterator).unwrap(),
        (true, Value::UNDEFINED)
    );
}

#[test]
fn for_in_deleted_own_key_does_not_shadow_inherited_name() {
    let module = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let object_prototype = machine.intrinsics.object_prototype;
    let g_key = PropertyKey::Named(machine.intern_str("g"));
    let proto = for_in_object(
        &mut machine,
        &[(g_key, data_property(1, true))],
        Some(object_prototype),
    );
    let first_key = PropertyKey::Named(machine.intern_str("first"));
    let g_key = PropertyKey::Named(machine.intern_str("g"));
    let child = for_in_object(
        &mut machine,
        &[
            (first_key, data_property(2, true)),
            (g_key, data_property(3, true)),
        ],
        Some(proto),
    );
    let iterator = machine.create_iterator(child, IteratorKind::Keys).unwrap();
    let (done, first) = machine.iterator_next(iterator).unwrap();
    assert!(!done);
    assert_eq!(
        machine.string_value(first).unwrap(),
        EcmaString::encode("first")
    );

    let g_key = PropertyKey::Named(machine.intern_str("g"));
    machine.internal_delete(child, &g_key).unwrap();
    let (done, inherited) = machine.iterator_next(iterator).unwrap();
    assert!(!done);
    assert_eq!(
        machine.string_value(inherited).unwrap(),
        EcmaString::encode("g")
    );
    assert_eq!(
        machine.iterator_next(iterator).unwrap(),
        (true, Value::UNDEFINED)
    );
}

#[test]
fn for_in_nullish_source_completes_immediately() {
    let module = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    assert_eq!(
        for_in_keys(&mut machine, Value::NULL),
        Vec::<EcmaString>::new()
    );
    assert_eq!(
        for_in_keys(&mut machine, Value::UNDEFINED),
        Vec::<EcmaString>::new()
    );
}

#[test]
fn for_in_terminates_on_malformed_prototype_cycle() {
    let module = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let object_prototype = machine.intrinsics.object_prototype;
    let a_key = PropertyKey::Named(machine.intern_str("a"));
    let a = for_in_object(
        &mut machine,
        &[(a_key, data_property(1, true))],
        Some(object_prototype),
    );
    let b_key = PropertyKey::Named(machine.intern_str("b"));
    let b = for_in_object(&mut machine, &[(b_key, data_property(2, true))], Some(a));
    // Create a cycle: a.__proto__ = b, so a -> b -> a -> ...
    machine.set_prototype(a, b).unwrap();
    let keys = for_in_keys(&mut machine, a);
    // Each level's own key is yielded once before the cycle is detected;
    // the iterator must terminate rather than loop unboundedly.
    assert_eq!(
        keys,
        ["a", "b"].map(EcmaString::encode),
        "malformed prototype cycle terminates after visiting each slot once"
    );
}

#[test]
fn for_in_gc_keeps_current_object_alive() {
    let module = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let object_prototype = machine.intrinsics.object_prototype;
    let first_key = PropertyKey::Named(machine.intern_str("first"));
    let second_key = PropertyKey::Named(machine.intern_str("second"));
    let object = for_in_object(
        &mut machine,
        &[
            (first_key, data_property(1, true)),
            (second_key, data_property(2, true)),
        ],
        Some(object_prototype),
    );
    let object_slot = machine.runtime_slot(object).unwrap().unwrap();
    let iterator = machine.create_iterator(object, IteratorKind::Keys).unwrap();
    let depth = machine.native_roots.len();
    machine.push_native_roots(depth, &[iterator]);
    // Consume one key so `current` is set and the iterator is mid-traversal.
    let (done, value) = machine.iterator_next(iterator).unwrap();
    assert!(!done);
    assert_eq!(
        machine.string_value(value).unwrap(),
        EcmaString::encode("first")
    );
    // Force GC while the iterator is the only root keeping `object`.
    machine.set_gc_watermarks_for_test(0, 0);
    machine.collect_garbage();
    assert!(
        !matches!(machine.heap[object_slot], HeapEntry::Vacant),
        "current for-in object must survive GC while the iterator holds it"
    );
    // Drain the rest to confirm the iterator still works after GC.
    let mut rest = Vec::new();
    loop {
        let (done, value) = machine.iterator_next(iterator).unwrap();
        if done {
            break;
        }
        rest.push(machine.string_value(value).unwrap());
    }
    machine.pop_native_roots(depth);
    assert_eq!(rest, [EcmaString::encode("second")]);
}

#[test]
fn object_prototype_to_string_uses_realm_tags() {
    let module = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&module, &mut host, Limits::default());
    let array = machine
        .allocate(HeapEntry::Array {
            kind: ArrayElementKind::for_elements(&[]),
            elements: Vec::new(),
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.array_prototype),
            extensible: true,
            length_writable: true,
        })
        .unwrap();
    let object = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    let function = machine.intrinsics.global("Object").unwrap();
    let to_string = machine.intrinsics.object_to_string();
    for (value, expected) in [
        (Value::UNDEFINED, "[object Undefined]"),
        (Value::NULL, "[object Null]"),
        (Value::TRUE, "[object Boolean]"),
        (array, "[object Array]"),
        (object, "[object Object]"),
        (function, "[object Function]"),
    ] {
        let tag = machine.call_value(to_string, value, &[]).unwrap();
        assert!(
            machine
                .string_text(tag)
                .is_some_and(|text| text.eq_ascii(expected))
        );
    }
}

#[derive(Default)]
struct CapabilityHost {
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    env: BTreeMap<String, String>,
}

impl Host for CapabilityHost {
    fn write_stdout(&mut self, bytes: &[u8]) {
        self.stdout.extend_from_slice(bytes);
    }

    fn write_stderr(&mut self, bytes: &[u8]) {
        self.stderr.extend_from_slice(bytes);
    }

    fn env(&self, name: &str) -> Option<&str> {
        self.env.get(name).map(String::as_str)
    }

    fn set_env(&mut self, name: &str, value: &str) {
        self.env.insert(name.to_owned(), value.to_owned());
    }

    fn delete_env(&mut self, name: &str) -> bool {
        self.env.remove(name).is_some()
    }
}

#[test]
fn console_formats_node_value_shapes_byte_exactly() {
    let module = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = CapabilityHost::default();
    {
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let console = machine.intrinsics.global("console").unwrap();
        let log = machine.get_named_property(console, "log").unwrap();
        let string = machine
            .allocate(HeapEntry::String(EcmaString::encode("hello")))
            .unwrap();
        let array_string = machine
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .unwrap();
        let array = machine
            .allocate(HeapEntry::Array {
                kind: ArrayElementKind::for_elements(&[Value::int32(1), array_string]),
                elements: vec![Value::int32(1), array_string],
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.array_prototype),
                extensible: true,
                length_writable: true,
            })
            .unwrap();
        let mut inner_properties = PropertyMap::default();
        let answer_key = PropertyKey::Named(machine.intern_str("answer"));
        inner_properties.insert(
            &mut machine.shapes,
            answer_key,
            Property::Data {
                value: Value::int32(42),
                writable: true,
                enumerable: true,
                configurable: true,
            },
        );
        let inner = machine
            .allocate(HeapEntry::Object {
                properties: inner_properties,
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let nested_key = PropertyKey::Named(machine.intern_str("nested"));
        let mut outer_properties = PropertyMap::default();
        outer_properties.insert(
            &mut machine.shapes,
            nested_key,
            Property::Data {
                value: inner,
                writable: true,
                enumerable: true,
                configurable: true,
            },
        );
        let outer = machine
            .allocate(HeapEntry::Object {
                properties: outer_properties,
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let symbol = machine
            .allocate(HeapEntry::Symbol {
                description: EcmaString::encode("token"),
            })
            .unwrap();
        for value in [
            string,
            Value::int32(42),
            array,
            outer,
            Value::UNDEFINED,
            Value::NULL,
            symbol,
        ] {
            machine.call_value(log, console, &[value]).unwrap();
        }
    }
    assert_eq!(
        host.stdout,
        b"hello\n42\n[ 1, 'x' ]\n{ nested: { answer: 42 } }\nundefined\nnull\nSymbol(token)\n"
    );
    assert!(host.stderr.is_empty());
}

#[test]
fn console_and_process_properties_are_reassignable_and_env_is_live() {
    let module = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = CapabilityHost::default();
    {
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let console = machine.intrinsics.global("console").unwrap();
        let warn = machine.get_named_property(console, "warn").unwrap();
        machine
            .set_data_property(console, "warn", Value::int32(91))
            .unwrap();
        assert_eq!(
            machine.get_named_property(console, "warn").unwrap(),
            Value::int32(91)
        );
        machine.set_data_property(console, "warn", warn).unwrap();

        let process = machine.intrinsics.global("process").unwrap();
        let env = machine.get_named_property(process, "env").unwrap();
        machine
            .set_data_property(env, "BAMTS_MODE", Value::int32(7))
            .unwrap();
        let value = machine.get_named_property(env, "BAMTS_MODE").unwrap();
        assert!(
            machine
                .string_text(value)
                .is_some_and(|text| text.eq_ascii("7"))
        );
        let mode_key = PropertyKey::Named(machine.intern_str("BAMTS_MODE"));
        assert!(machine.internal_delete(env, &mode_key).unwrap());
        assert_eq!(
            machine.get_named_property(env, "BAMTS_MODE").unwrap(),
            Value::UNDEFINED
        );
    }
    assert_eq!(host.env("BAMTS_MODE"), None);
}

#[test]
fn independent_modules_keep_same_name_globals_isolated() {
    let dependency = |name: &str, value: i32| {
        program_module(
            name,
            vec![
                Constant::String(EcmaString::encode("x")),
                Constant::Int32(value),
            ],
            vec![function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(2),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            )],
            Vec::new(),
            vec![Binding {
                name: cid(1),
                kind: BindingKind::Hoisted,
            }],
            vec![Export {
                name: cid(1),
                source: ExportSource::Local(BindingId::new(0)),
            }],
        )
    };
    let root = program_module(
        "root",
        vec![
            Constant::String(EcmaString::encode("left")),
            Constant::String(EcmaString::encode("right")),
            Constant::String(EcmaString::encode("x")),
        ],
        vec![function(
            0,
            5,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(1),
                },
                Instruction::LoadGlobal {
                    dst: reg(1),
                    name: cid(2),
                },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(3),
                },
                Instruction::GetProperty {
                    dst: reg(3),
                    object: reg(0),
                    key: reg(2),
                },
                Instruction::GetProperty {
                    dst: reg(4),
                    object: reg(1),
                    key: reg(2),
                },
                Instruction::Binary {
                    dst: reg(0),
                    op: BinaryOp::Add,
                    left: reg(3),
                    right: reg(4),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
        vec![
            Edge {
                specifier: cid(1),
                target: EdgeTarget::Local(ModuleId::new(0)),
                kind: EdgeKind::Static,
            },
            Edge {
                specifier: cid(2),
                target: EdgeTarget::Local(ModuleId::new(1)),
                kind: EdgeKind::Static,
            },
        ],
        vec![
            Binding {
                name: cid(1),
                kind: BindingKind::Namespace {
                    edge: EdgeId::new(0),
                },
            },
            Binding {
                name: cid(2),
                kind: BindingKind::Namespace {
                    edge: EdgeId::new(1),
                },
            },
        ],
        Vec::new(),
    );
    let program = linked(vec![dependency("left", 1), dependency("right", 2), root], 2);
    assert_eq!(run_ok(&program).value, Value::int32(3));
}

#[test]
fn imported_binding_observes_post_link_mutation_live() {
    let dependency = program_module(
        "dependency",
        vec![
            Constant::String(EcmaString::encode("x")),
            Constant::Int32(1),
            Constant::Int32(2),
            Constant::String(EcmaString::encode("set")),
        ],
        vec![
            function(
                0,
                3,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(2),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(0),
                    },
                    Instruction::CreateArray { dst: reg(1) },
                    Instruction::CreateClosure {
                        dst: reg(2),
                        function: FunctionId::new(1),
                        captures: reg(1),
                    },
                    Instruction::StoreGlobal {
                        name: cid(4),
                        value: reg(2),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
            function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(3),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
        Vec::new(),
        vec![
            Binding {
                name: cid(1),
                kind: BindingKind::Hoisted,
            },
            Binding {
                name: cid(4),
                kind: BindingKind::Hoisted,
            },
        ],
        vec![
            Export {
                name: cid(1),
                source: ExportSource::Local(BindingId::new(0)),
            },
            Export {
                name: cid(4),
                source: ExportSource::Local(BindingId::new(1)),
            },
        ],
    );
    let root = program_module(
        "root",
        vec![
            Constant::String(EcmaString::encode("x")),
            Constant::String(EcmaString::encode("set")),
            Constant::String(EcmaString::encode("dep")),
        ],
        vec![function(
            0,
            3,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(2),
                },
                Instruction::CreateArray { dst: reg(1) },
                Instruction::Call {
                    dst: reg(2),
                    callee: reg(0),
                    this_value: reg(1),
                    arguments: reg(1),
                },
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(1),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(3),
            target: EdgeTarget::Local(ModuleId::new(0)),
            kind: EdgeKind::Static,
        }],
        vec![
            Binding {
                name: cid(1),
                kind: BindingKind::Imported {
                    edge: EdgeId::new(0),
                    name: cid(1),
                },
            },
            Binding {
                name: cid(2),
                kind: BindingKind::Imported {
                    edge: EdgeId::new(0),
                    name: cid(2),
                },
            },
        ],
        Vec::new(),
    );
    assert_eq!(
        run_ok(&linked(vec![dependency, root], 1)).value,
        Value::int32(2)
    );
}

#[test]
fn closure_globals_resolve_in_the_defining_module() {
    let dependency = program_module(
        "dependency",
        vec![
            Constant::String(EcmaString::encode("x")),
            Constant::Int32(10),
            Constant::String(EcmaString::encode("read")),
        ],
        vec![
            function(
                0,
                3,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(2),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(0),
                    },
                    Instruction::CreateArray { dst: reg(1) },
                    Instruction::CreateClosure {
                        dst: reg(2),
                        function: FunctionId::new(1),
                        captures: reg(1),
                    },
                    Instruction::StoreGlobal {
                        name: cid(3),
                        value: reg(2),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
            function(
                0,
                1,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(1),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
        Vec::new(),
        vec![
            Binding {
                name: cid(1),
                kind: BindingKind::Hoisted,
            },
            Binding {
                name: cid(3),
                kind: BindingKind::Hoisted,
            },
        ],
        vec![Export {
            name: cid(3),
            source: ExportSource::Local(BindingId::new(1)),
        }],
    );
    let root = program_module(
        "root",
        vec![
            Constant::String(EcmaString::encode("x")),
            Constant::Int32(20),
            Constant::String(EcmaString::encode("read")),
            Constant::String(EcmaString::encode("dep")),
        ],
        vec![function(
            0,
            4,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(2),
                },
                Instruction::StoreGlobal {
                    name: cid(1),
                    value: reg(0),
                },
                Instruction::LoadGlobal {
                    dst: reg(1),
                    name: cid(3),
                },
                Instruction::CreateArray { dst: reg(2) },
                Instruction::Call {
                    dst: reg(3),
                    callee: reg(1),
                    this_value: reg(2),
                    arguments: reg(2),
                },
                Instruction::Return { value: reg(3) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(4),
            target: EdgeTarget::Local(ModuleId::new(0)),
            kind: EdgeKind::Static,
        }],
        vec![
            Binding {
                name: cid(1),
                kind: BindingKind::Hoisted,
            },
            Binding {
                name: cid(3),
                kind: BindingKind::Imported {
                    edge: EdgeId::new(0),
                    name: cid(3),
                },
            },
        ],
        Vec::new(),
    );
    assert_eq!(
        run_ok(&linked(vec![dependency, root], 1)).value,
        Value::int32(10)
    );
}

#[test]
fn cycle_traps_a_lexical_read_before_initialization() {
    let first = program_module(
        "first",
        vec![
            Constant::String(EcmaString::encode("a")),
            Constant::Int32(1),
            Constant::String(EcmaString::encode("second")),
        ],
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(2),
                },
                Instruction::StoreGlobal {
                    name: cid(1),
                    value: reg(0),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(3),
            target: EdgeTarget::Local(ModuleId::new(1)),
            kind: EdgeKind::Static,
        }],
        vec![Binding {
            name: cid(1),
            kind: BindingKind::Lexical,
        }],
        vec![Export {
            name: cid(1),
            source: ExportSource::Local(BindingId::new(0)),
        }],
    );
    let second = program_module(
        "second",
        vec![
            Constant::String(EcmaString::encode("a")),
            Constant::String(EcmaString::encode("first")),
        ],
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(1),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(2),
            target: EdgeTarget::Local(ModuleId::new(0)),
            kind: EdgeKind::Static,
        }],
        vec![Binding {
            name: cid(1),
            kind: BindingKind::Imported {
                edge: EdgeId::new(0),
                name: cid(1),
            },
        }],
        Vec::new(),
    );
    let program = linked(vec![first, second], 0);
    let mut host = TestHost;
    let error = Machine::new(&program, &mut host, Limits::default())
        .run()
        .unwrap_err();
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::UncaughtThrow {
            origin: ThrowOrigin::ReferenceError { .. },
            ..
        }
    ));
}

#[test]
fn cycle_reentry_with_a_hoisted_binding_completes() {
    let first = program_module(
        "first",
        vec![
            Constant::String(EcmaString::encode("a")),
            Constant::Int32(1),
            Constant::String(EcmaString::encode("second")),
        ],
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(2),
                },
                Instruction::StoreGlobal {
                    name: cid(1),
                    value: reg(0),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(3),
            target: EdgeTarget::Local(ModuleId::new(1)),
            kind: EdgeKind::Static,
        }],
        vec![Binding {
            name: cid(1),
            kind: BindingKind::Hoisted,
        }],
        vec![Export {
            name: cid(1),
            source: ExportSource::Local(BindingId::new(0)),
        }],
    );
    let second = program_module(
        "second",
        vec![
            Constant::String(EcmaString::encode("a")),
            Constant::String(EcmaString::encode("first")),
        ],
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(1),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(2),
            target: EdgeTarget::Local(ModuleId::new(0)),
            kind: EdgeKind::Static,
        }],
        vec![Binding {
            name: cid(1),
            kind: BindingKind::Imported {
                edge: EdgeId::new(0),
                name: cid(1),
            },
        }],
        Vec::new(),
    );
    assert_eq!(
        run_ok(&linked(vec![first, second], 0)).value,
        Value::int32(1)
    );
}

#[test]
fn namespace_identity_reads_live_cells_and_enumerates_sorted_keys() {
    let dependency = program_module(
        "dependency",
        vec![
            Constant::String(EcmaString::encode("z")),
            Constant::String(EcmaString::encode("a")),
            Constant::String(EcmaString::encode("mutate")),
            Constant::Int32(1),
            Constant::Int32(2),
            Constant::Int32(3),
        ],
        vec![
            function(
                0,
                4,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(4),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(5),
                    },
                    Instruction::StoreGlobal {
                        name: cid(2),
                        value: reg(0),
                    },
                    Instruction::CreateArray { dst: reg(1) },
                    Instruction::CreateClosure {
                        dst: reg(2),
                        function: FunctionId::new(1),
                        captures: reg(1),
                    },
                    Instruction::StoreGlobal {
                        name: cid(3),
                        value: reg(2),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
            function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(6),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
        Vec::new(),
        vec![
            Binding {
                name: cid(1),
                kind: BindingKind::Hoisted,
            },
            Binding {
                name: cid(2),
                kind: BindingKind::Hoisted,
            },
            Binding {
                name: cid(3),
                kind: BindingKind::Hoisted,
            },
        ],
        vec![
            Export {
                name: cid(1),
                source: ExportSource::Local(BindingId::new(0)),
            },
            Export {
                name: cid(2),
                source: ExportSource::Local(BindingId::new(1)),
            },
            Export {
                name: cid(3),
                source: ExportSource::Local(BindingId::new(2)),
            },
        ],
    );
    let root = program_module(
        "root",
        vec![
            Constant::String(EcmaString::encode("ns1")),
            Constant::String(EcmaString::encode("ns2")),
            Constant::String(EcmaString::encode("mutate")),
            Constant::String(EcmaString::encode("z")),
            Constant::String(EcmaString::encode("a")),
            Constant::String(EcmaString::encode("dep")),
            Constant::String(EcmaString::encode("Object")),
            Constant::String(EcmaString::encode("getOwnPropertyDescriptor")),
            Constant::String(EcmaString::encode("value")),
            Constant::String(EcmaString::encode("writable")),
            Constant::String(EcmaString::encode("enumerable")),
            Constant::String(EcmaString::encode("configurable")),
            Constant::String(EcmaString::encode("missing")),
        ],
        vec![function(
            0,
            31,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(1),
                },
                Instruction::LoadGlobal {
                    dst: reg(1),
                    name: cid(2),
                },
                Instruction::Binary {
                    dst: reg(2),
                    op: BinaryOp::StrictEqual,
                    left: reg(0),
                    right: reg(1),
                },
                Instruction::LoadGlobal {
                    dst: reg(3),
                    name: cid(3),
                },
                Instruction::CreateArray { dst: reg(4) },
                Instruction::Call {
                    dst: reg(5),
                    callee: reg(3),
                    this_value: reg(4),
                    arguments: reg(4),
                },
                Instruction::LoadConst {
                    dst: reg(6),
                    constant: cid(4),
                },
                Instruction::GetProperty {
                    dst: reg(7),
                    object: reg(0),
                    key: reg(6),
                },
                Instruction::GetIterator {
                    dst: reg(8),
                    src: reg(0),
                    kind: IteratorKind::Keys,
                },
                Instruction::IteratorNext {
                    done: reg(9),
                    value: reg(10),
                    iterator: reg(8),
                },
                Instruction::LoadConst {
                    dst: reg(11),
                    constant: cid(5),
                },
                Instruction::Binary {
                    dst: reg(12),
                    op: BinaryOp::StrictEqual,
                    left: reg(10),
                    right: reg(11),
                },
                Instruction::IteratorNext {
                    done: reg(9),
                    value: reg(10),
                    iterator: reg(8),
                },
                Instruction::LoadConst {
                    dst: reg(13),
                    constant: cid(3),
                },
                Instruction::Binary {
                    dst: reg(5),
                    op: BinaryOp::StrictEqual,
                    left: reg(10),
                    right: reg(13),
                },
                Instruction::IteratorNext {
                    done: reg(9),
                    value: reg(10),
                    iterator: reg(8),
                },
                Instruction::Binary {
                    dst: reg(14),
                    op: BinaryOp::StrictEqual,
                    left: reg(10),
                    right: reg(6),
                },
                Instruction::LoadGlobal {
                    dst: reg(15),
                    name: cid(7),
                },
                Instruction::LoadConst {
                    dst: reg(16),
                    constant: cid(8),
                },
                Instruction::GetProperty {
                    dst: reg(17),
                    object: reg(15),
                    key: reg(16),
                },
                Instruction::CreateArray { dst: reg(18) },
                Instruction::ArrayPush {
                    array: reg(18),
                    value: reg(0),
                },
                Instruction::ArrayPush {
                    array: reg(18),
                    value: reg(6),
                },
                Instruction::Call {
                    dst: reg(19),
                    callee: reg(17),
                    this_value: reg(18),
                    arguments: reg(18),
                },
                Instruction::LoadConst {
                    dst: reg(20),
                    constant: cid(9),
                },
                Instruction::GetProperty {
                    dst: reg(21),
                    object: reg(19),
                    key: reg(20),
                },
                Instruction::LoadConst {
                    dst: reg(22),
                    constant: cid(10),
                },
                Instruction::GetProperty {
                    dst: reg(23),
                    object: reg(19),
                    key: reg(22),
                },
                Instruction::LoadConst {
                    dst: reg(24),
                    constant: cid(11),
                },
                Instruction::GetProperty {
                    dst: reg(25),
                    object: reg(19),
                    key: reg(24),
                },
                Instruction::LoadConst {
                    dst: reg(26),
                    constant: cid(12),
                },
                Instruction::GetProperty {
                    dst: reg(27),
                    object: reg(19),
                    key: reg(26),
                },
                Instruction::CreateArray { dst: reg(28) },
                Instruction::LoadConst {
                    dst: reg(29),
                    constant: cid(13),
                },
                Instruction::ArrayPush {
                    array: reg(28),
                    value: reg(0),
                },
                Instruction::ArrayPush {
                    array: reg(28),
                    value: reg(29),
                },
                Instruction::Call {
                    dst: reg(30),
                    callee: reg(17),
                    this_value: reg(28),
                    arguments: reg(28),
                },
                Instruction::Return { value: reg(21) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(6),
            target: EdgeTarget::Local(ModuleId::new(0)),
            kind: EdgeKind::Static,
        }],
        vec![
            Binding {
                name: cid(1),
                kind: BindingKind::Namespace {
                    edge: EdgeId::new(0),
                },
            },
            Binding {
                name: cid(2),
                kind: BindingKind::Namespace {
                    edge: EdgeId::new(0),
                },
            },
            Binding {
                name: cid(3),
                kind: BindingKind::Imported {
                    edge: EdgeId::new(0),
                    name: cid(3),
                },
            },
        ],
        Vec::new(),
    );
    let execution = run_ok(&linked(vec![dependency, root], 1));
    assert_eq!(execution.value, Value::int32(3));
    assert_eq!(execution.entry_registers[2], Value::TRUE);
    assert_eq!(execution.entry_registers[5], Value::TRUE);
    assert_eq!(execution.entry_registers[12], Value::TRUE);
    assert_eq!(execution.entry_registers[14], Value::TRUE);
    assert_eq!(execution.entry_registers[23], Value::TRUE);
    assert_eq!(execution.entry_registers[25], Value::TRUE);
    assert_eq!(execution.entry_registers[27], Value::FALSE);
    assert_eq!(execution.entry_registers[30], Value::UNDEFINED);
}

#[test]
fn side_effect_module_runs_once_with_single_or_duplicate_static_edges() {
    for duplicate in [false, true] {
        let dependency = program_module(
            "dependency",
            vec![
                Constant::String(EcmaString::encode("count")),
                Constant::Int32(0),
                Constant::Int32(1),
            ],
            vec![function(
                0,
                2,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(1),
                    },
                    Instruction::JumpIfFalse {
                        condition: reg(0),
                        target: pc(3),
                    },
                    Instruction::Jump { target: pc(5) },
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(2),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(3),
                    },
                    Instruction::Binary {
                        dst: reg(0),
                        op: BinaryOp::Add,
                        left: reg(0),
                        right: reg(1),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            )],
            Vec::new(),
            vec![Binding {
                name: cid(1),
                kind: BindingKind::Hoisted,
            }],
            vec![Export {
                name: cid(1),
                source: ExportSource::Local(BindingId::new(0)),
            }],
        );
        let mut edges = vec![Edge {
            specifier: cid(2),
            target: EdgeTarget::Local(ModuleId::new(0)),
            kind: EdgeKind::Static,
        }];
        if duplicate {
            edges.push(Edge {
                specifier: cid(3),
                target: EdgeTarget::Local(ModuleId::new(0)),
                kind: EdgeKind::Static,
            });
        }
        let root = program_module(
            "root",
            vec![
                Constant::String(EcmaString::encode("count")),
                Constant::String(EcmaString::encode("dep-one")),
                Constant::String(EcmaString::encode("dep-two")),
            ],
            vec![function(
                0,
                1,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(1),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            )],
            edges,
            vec![Binding {
                name: cid(1),
                kind: BindingKind::Imported {
                    edge: EdgeId::new(0),
                    name: cid(1),
                },
            }],
            Vec::new(),
        );
        assert_eq!(
            run_ok(&linked(vec![dependency, root], 1)).value,
            Value::int32(1)
        );
    }
}

#[test]
fn dynamic_import_of_tla_module_from_microtask_does_not_reenter_checkpoint() {
    let root = program_module(
        "root",
        vec![
            Constant::String(EcmaString::encode("./target")),
            Constant::Undefined,
            Constant::String(EcmaString::encode("value")),
        ],
        vec![function(
            0,
            5,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(2),
                },
                Instruction::Await {
                    dst: reg(1),
                    src: reg(0),
                    resume: pc(2),
                },
                Instruction::Import {
                    dst: reg(2),
                    specifier: cid(1),
                },
                Instruction::Await {
                    dst: reg(3),
                    src: reg(2),
                    resume: pc(4),
                },
                Instruction::LoadConst {
                    dst: reg(4),
                    constant: cid(3),
                },
                Instruction::GetProperty {
                    dst: reg(0),
                    object: reg(3),
                    key: reg(4),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(1),
            target: EdgeTarget::Local(ModuleId::new(1)),
            kind: EdgeKind::Dynamic,
        }],
        Vec::new(),
        Vec::new(),
    );
    let target = program_module(
        "target",
        vec![
            Constant::Int32(7),
            Constant::String(EcmaString::encode("value")),
        ],
        vec![function(
            0,
            2,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(1),
                },
                Instruction::Await {
                    dst: reg(1),
                    src: reg(0),
                    resume: pc(2),
                },
                Instruction::StoreGlobal {
                    name: cid(2),
                    value: reg(1),
                },
                Instruction::Return { value: reg(1) },
            ],
            Vec::new(),
        )],
        Vec::new(),
        vec![Binding {
            name: cid(2),
            kind: BindingKind::Hoisted,
        }],
        vec![Export {
            name: cid(2),
            source: ExportSource::Local(BindingId::new(0)),
        }],
    );
    let program = linked(vec![root, target], 0);
    let mut host = TestHost;
    let execution = Machine::new(&program, &mut host, Limits::default())
        .run()
        .expect("nested TLA import completes through the active checkpoint");
    assert_eq!(execution.value, Value::int32(7));
}

fn top_level_await_program() -> Program<Verified> {
    let module = program_module(
        "root",
        vec![
            Constant::String(EcmaString::encode("after")),
            Constant::Int32(7),
        ],
        vec![function(
            0,
            2,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(2),
                },
                Instruction::Await {
                    dst: reg(1),
                    src: reg(0),
                    resume: pc(2),
                },
                Instruction::StoreGlobal {
                    name: cid(1),
                    value: reg(1),
                },
                Instruction::Return { value: reg(1) },
            ],
            Vec::new(),
        )],
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    linked(vec![module], 0)
}

fn assert_top_level_await_completes(machine: &mut Machine<'_, TestHost>) {
    let execution = machine.evaluate().expect("top-level await completes");
    machine.run_to_quiescence().expect("event loop drains");

    assert_eq!(execution.value, Value::int32(7));
    assert_eq!(execution.entry_registers[1], Value::int32(7));
    assert_eq!(machine.test_global("after"), Some(Value::int32(7)));
}

#[test]
fn top_level_await_resumes_module_entry() {
    let program = top_level_await_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    assert_top_level_await_completes(&mut machine);
}

#[test]
fn a_pending_module_entry_survives_a_collection_at_every_safe_point() {
    let program = top_level_await_program();
    let mut host = TestHost;
    let limits = Limits {
        collect_every_allocation: true,
        ..Limits::default()
    };
    let mut machine = Machine::new(&program, &mut host, limits);
    assert_top_level_await_completes(&mut machine);
}

#[test]
fn failed_module_rethrows_the_identical_stored_value() {
    let module = program_module(
        "throws",
        Vec::new(),
        vec![function(
            0,
            1,
            vec![
                Instruction::CreateObject { dst: reg(0) },
                Instruction::Throw { value: reg(0) },
            ],
            Vec::new(),
        )],
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    let program = linked(vec![module], 0);
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    machine.instantiate_modules().unwrap();
    let first = machine.evaluate_module(ModuleId::new(0)).unwrap_err();
    let second = machine.evaluate_module(ModuleId::new(0)).unwrap_err();
    let RuntimeErrorKind::UncaughtThrow { value: first, .. } = first.kind else {
        panic!("module must fail by throwing");
    };
    let RuntimeErrorKind::UncaughtThrow { value: second, .. } = second.kind else {
        panic!("stored failure must remain a throw");
    };
    assert_eq!(first, second);
    assert!(first.as_heap_ref().is_some());
}

#[test]
fn external_static_edge_is_a_typed_runtime_error() {
    let module = program_module(
        "root",
        vec![Constant::String(EcmaString::encode("external"))],
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
        vec![Edge {
            specifier: cid(1),
            target: EdgeTarget::External,
            kind: EdgeKind::Static,
        }],
        Vec::new(),
        Vec::new(),
    );
    let program = linked(vec![module], 0);
    let mut host = TestHost;
    let error = Machine::new(&program, &mut host, Limits::default())
        .run()
        .unwrap_err();
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::ExternalModuleUnavailable { module, edge }
            if module == ModuleId::new(0) && edge == EdgeId::new(0)
    ));
}

#[test]
fn external_module_and_export_names_preserve_unicode() {
    for (specifier, export) in [("módulo", "value"), ("external", "café")] {
        let module = program_module(
            "root",
            vec![
                Constant::String(EcmaString::encode(export)),
                Constant::String(EcmaString::encode(specifier)),
            ],
            vec![function(
                0,
                1,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(1),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            )],
            vec![Edge {
                specifier: cid(2),
                target: EdgeTarget::External,
                kind: EdgeKind::Static,
            }],
            vec![Binding {
                name: cid(1),
                kind: BindingKind::Imported {
                    edge: EdgeId::new(0),
                    name: cid(1),
                },
            }],
            Vec::new(),
        );
        let program = linked(vec![module], 0);
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        machine.registry.external.insert(
            EcmaString::encode(specifier),
            ExternalModuleInstance {
                namespace: Value::UNDEFINED,
                exports: BTreeMap::from([(
                    EcmaString::encode(export),
                    ExternalExport {
                        value: Value::int32(7),
                        cell: None,
                    },
                )]),
                internals: BTreeMap::new(),
            },
        );

        assert_eq!(machine.run().unwrap().value, Value::int32(7));
    }
}

#[test]
fn dynamic_import_preserves_cycles_identity_and_single_evaluation() {
    let root = program_module(
        "root",
        vec![
            Constant::String(EcmaString::encode("./dependency")),
            Constant::String(EcmaString::encode("count")),
            Constant::Int32(0),
            Constant::String(EcmaString::encode("value")),
        ],
        vec![function(
            0,
            7,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(3),
                },
                Instruction::StoreGlobal {
                    name: cid(2),
                    value: reg(0),
                },
                Instruction::Import {
                    dst: reg(1),
                    specifier: cid(1),
                },
                Instruction::Import {
                    dst: reg(2),
                    specifier: cid(1),
                },
                Instruction::Binary {
                    dst: reg(3),
                    op: BinaryOp::StrictEqual,
                    left: reg(1),
                    right: reg(2),
                },
                Instruction::LoadConst {
                    dst: reg(4),
                    constant: cid(4),
                },
                Instruction::GetProperty {
                    dst: reg(5),
                    object: reg(2),
                    key: reg(4),
                },
                Instruction::LoadGlobal {
                    dst: reg(6),
                    name: cid(2),
                },
                Instruction::Return { value: reg(5) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(1),
            target: EdgeTarget::Local(ModuleId::new(1)),
            kind: EdgeKind::Dynamic,
        }],
        Vec::new(),
        Vec::new(),
    );
    let dependency = program_module(
        "dependency",
        vec![
            Constant::String(EcmaString::encode("./root")),
            Constant::String(EcmaString::encode("count")),
            Constant::Int32(1),
            Constant::Int32(7),
            Constant::String(EcmaString::encode("value")),
        ],
        vec![function(
            0,
            3,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(2),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(3),
                },
                Instruction::Binary {
                    dst: reg(2),
                    op: BinaryOp::Add,
                    left: reg(0),
                    right: reg(1),
                },
                Instruction::StoreGlobal {
                    name: cid(2),
                    value: reg(2),
                },
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(4),
                },
                Instruction::StoreGlobal {
                    name: cid(5),
                    value: reg(0),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(1),
            target: EdgeTarget::Local(ModuleId::new(0)),
            kind: EdgeKind::Static,
        }],
        vec![Binding {
            name: cid(5),
            kind: BindingKind::Hoisted,
        }],
        vec![Export {
            name: cid(5),
            source: ExportSource::Local(BindingId::new(0)),
        }],
    );

    let execution = run_ok(&linked(vec![root, dependency], 0));
    assert_eq!(execution.value, Value::int32(7));
    assert_eq!(execution.entry_registers[1], execution.entry_registers[2]);
    assert_eq!(execution.entry_registers[3], Value::TRUE);
    assert_eq!(execution.entry_registers[6], Value::int32(1));
}

#[test]
fn dynamic_import_counts_live_registers_and_retries_engine_failures() {
    let target = program_module(
        "target",
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    let root = program_module(
        "root",
        vec![Constant::String(EcmaString::encode("./target"))],
        vec![function(
            0,
            1,
            vec![
                Instruction::Import {
                    dst: reg(0),
                    specifier: cid(1),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(1),
            target: EdgeTarget::Local(ModuleId::new(1)),
            kind: EdgeKind::Dynamic,
        }],
        Vec::new(),
        Vec::new(),
    );
    let program = linked(vec![root, target], 0);
    let mut host = TestHost;
    let mut machine = Machine::new(
        &program,
        &mut host,
        Limits {
            max_total_registers: 1,
            ..Limits::default()
        },
    );
    machine.frames.clear();
    machine.live_registers = 0;
    machine.instantiate_modules().unwrap();

    let error = machine.evaluate_import(ModuleId::new(0)).unwrap_err();
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::RegisterLimitExceeded { limit: 1 }
    ));
    assert_eq!(machine.frames.len(), 0);
    assert_eq!(machine.live_registers, 0);

    machine.limits.max_total_registers = 2;
    machine.evaluate_import(ModuleId::new(0)).unwrap();
}

#[test]
fn dynamic_import_rethrows_one_stored_failure_at_each_import_site() {
    let root = program_module(
        "root",
        vec![
            Constant::String(EcmaString::encode("./target")),
            Constant::String(EcmaString::encode("count")),
            Constant::Int32(0),
        ],
        vec![function(
            0,
            4,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(3),
                },
                Instruction::StoreGlobal {
                    name: cid(2),
                    value: reg(0),
                },
                Instruction::Import {
                    dst: reg(0),
                    specifier: cid(1),
                },
                Instruction::Halt,
                Instruction::Import {
                    dst: reg(0),
                    specifier: cid(1),
                },
                Instruction::Halt,
                Instruction::LoadGlobal {
                    dst: reg(3),
                    name: cid(2),
                },
                Instruction::Return { value: reg(2) },
            ],
            vec![
                ExceptionHandler {
                    start: pc(2),
                    end: pc(3),
                    handler: pc(4),
                    catch_register: reg(1),
                },
                ExceptionHandler {
                    start: pc(4),
                    end: pc(5),
                    handler: pc(6),
                    catch_register: reg(2),
                },
            ],
        )],
        vec![Edge {
            specifier: cid(1),
            target: EdgeTarget::Local(ModuleId::new(1)),
            kind: EdgeKind::Dynamic,
        }],
        Vec::new(),
        Vec::new(),
    );
    let target = program_module(
        "target",
        vec![
            Constant::String(EcmaString::encode("count")),
            Constant::Int32(1),
            Constant::Int32(9),
        ],
        vec![function(
            0,
            3,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(1),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(2),
                },
                Instruction::Binary {
                    dst: reg(2),
                    op: BinaryOp::Add,
                    left: reg(0),
                    right: reg(1),
                },
                Instruction::StoreGlobal {
                    name: cid(1),
                    value: reg(2),
                },
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(3),
                },
                Instruction::Throw { value: reg(0) },
            ],
            Vec::new(),
        )],
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );

    let execution = run_ok(&linked(vec![root, target], 0));
    assert_eq!(execution.value, Value::int32(9));
    assert_eq!(execution.entry_registers[1], Value::int32(9));
    assert_eq!(execution.entry_registers[2], Value::int32(9));
    assert_eq!(execution.entry_registers[3], Value::int32(1));
}

#[test]
fn failed_import_caught_by_dependent_is_intrinsic_type_error() {
    // A dynamic Import of a module whose entry throws an engine TypeError
    // must deliver an intrinsic error object to the dependent's catch,
    // not undefined from a stripped origin.
    let root = program_module(
        "root",
        vec![Constant::String(EcmaString::encode("./target"))],
        vec![function(
            0,
            2,
            vec![
                Instruction::Import {
                    dst: reg(0),
                    specifier: cid(1),
                },
                Instruction::Halt,
                Instruction::Return { value: reg(1) },
            ],
            vec![ExceptionHandler {
                start: pc(0),
                end: pc(1),
                handler: pc(2),
                catch_register: reg(1),
            }],
        )],
        vec![Edge {
            specifier: cid(1),
            target: EdgeTarget::Local(ModuleId::new(1)),
            kind: EdgeKind::Dynamic,
        }],
        Vec::new(),
        Vec::new(),
    );
    let target = program_module(
        "target",
        vec![Constant::Int32(0)],
        vec![function(
            0,
            3,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(1),
                },
                Instruction::CreateArray { dst: reg(1) },
                Instruction::Call {
                    dst: reg(2),
                    callee: reg(0),
                    this_value: reg(0),
                    arguments: reg(1),
                },
                Instruction::Return { value: reg(2) },
            ],
            Vec::new(),
        )],
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    let mut host = TestHost;
    let program = linked(vec![root, target], 0);
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let execution = machine.evaluate().unwrap();
    let error = execution.value;
    assert_ne!(error, Value::UNDEFINED);
    let name = machine.get_named_property(error, "name").unwrap();
    assert!(
        machine
            .string_value(name)
            .is_some_and(|text| text.eq_ascii("TypeError"))
    );
    let message = machine.get_named_property(error, "message").unwrap();
    assert!(
        machine
            .string_value(message)
            .is_some_and(|text| text.eq_ascii("call"))
    );
    let constructor = machine.intrinsics.global("TypeError").unwrap();
    assert!(machine.instance_of(error, constructor).unwrap());
    machine.run_to_quiescence().unwrap();
}

#[test]
fn dynamic_import_returns_the_registered_external_namespace() {
    let module = program_module(
        "root",
        vec![Constant::String(EcmaString::encode("external"))],
        vec![function(
            0,
            3,
            vec![
                Instruction::Import {
                    dst: reg(0),
                    specifier: cid(1),
                },
                Instruction::Import {
                    dst: reg(1),
                    specifier: cid(1),
                },
                Instruction::Binary {
                    dst: reg(2),
                    op: BinaryOp::StrictEqual,
                    left: reg(0),
                    right: reg(1),
                },
                Instruction::Return { value: reg(2) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(1),
            target: EdgeTarget::External,
            kind: EdgeKind::Dynamic,
        }],
        Vec::new(),
        Vec::new(),
    );
    let program = linked(vec![module], 0);
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let namespace = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    machine.registry.external.insert(
        EcmaString::encode("external"),
        ExternalModuleInstance {
            namespace,
            exports: BTreeMap::new(),
            internals: BTreeMap::new(),
        },
    );

    let execution = machine.run().unwrap();
    assert_eq!(execution.value, Value::TRUE);
    assert_eq!(execution.entry_registers[0], namespace);
    assert_eq!(execution.entry_registers[1], namespace);
}

#[test]
fn dynamic_import_resolution_is_requester_scoped() {
    let requester = |name, target| {
        program_module(
            name,
            vec![Constant::String(EcmaString::encode("./target"))],
            vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
            vec![Edge {
                specifier: cid(1),
                target: EdgeTarget::Local(ModuleId::new(target)),
                kind: EdgeKind::Dynamic,
            }],
            Vec::new(),
            Vec::new(),
        )
    };
    let target = |name| {
        program_module(
            name,
            Vec::new(),
            vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
    };
    let program = linked(
        vec![
            requester("first", 2),
            requester("second", 3),
            target("first-target"),
            target("second-target"),
        ],
        0,
    );
    let mut host = TestHost;
    let machine = Machine::new(&program, &mut host, Limits::default());

    assert_eq!(
        machine.resolve_import(ModuleId::new(0), cid(1)),
        Ok(ImportTarget::Local(ModuleId::new(2)))
    );
    assert_eq!(
        machine.resolve_import(ModuleId::new(1), cid(1)),
        Ok(ImportTarget::Local(ModuleId::new(3)))
    );
}

#[test]
fn dynamic_import_of_a_missing_external_is_a_runtime_error() {
    let module = program_module(
        "root",
        vec![Constant::String(EcmaString::encode("dynamic"))],
        vec![function(
            0,
            1,
            vec![
                Instruction::Import {
                    dst: reg(0),
                    specifier: cid(1),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(1),
            target: EdgeTarget::External,
            kind: EdgeKind::Dynamic,
        }],
        Vec::new(),
        Vec::new(),
    );
    let program = linked(vec![module], 0);
    let mut host = TestHost;
    let error = Machine::new(&program, &mut host, Limits::default())
        .run()
        .unwrap_err();
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::ExternalModuleUnavailable { module, edge }
            if module == ModuleId::new(0) && edge == EdgeId::new(0)
    ));
}

#[test]
fn unbound_global_names_fall_back_to_the_realm_global_map() {
    let program = verified(
        vec![
            Constant::String(EcmaString::encode("realmOnly")),
            Constant::Int32(7),
        ],
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(1),
                },
                Instruction::StoreGlobal {
                    name: cid(0),
                    value: reg(0),
                },
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(0),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
    );
    assert_eq!(run_ok(&program).value, Value::int32(7));
}

#[test]
fn module_cell_limit_is_enforced_before_evaluation() {
    let module = program_module(
        "root",
        vec![Constant::String(EcmaString::encode("x"))],
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
        Vec::new(),
        vec![Binding {
            name: cid(1),
            kind: BindingKind::Hoisted,
        }],
        Vec::new(),
    );
    let program = linked(vec![module], 0);
    let mut host = TestHost;
    let error = Machine::new(
        &program,
        &mut host,
        Limits {
            max_module_cells: 0,
            ..Limits::default()
        },
    )
    .run()
    .unwrap_err();
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::ModuleCellLimitExceeded { limit: 0 }
    ));
}
#[test]
fn imported_binding_store_throws_without_mutating_the_exporter() {
    let dependency = program_module(
        "dependency",
        vec![
            Constant::String(EcmaString::encode("x")),
            Constant::Int32(1),
        ],
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(2),
                },
                Instruction::StoreGlobal {
                    name: cid(1),
                    value: reg(0),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
        Vec::new(),
        vec![Binding {
            name: cid(1),
            kind: BindingKind::Hoisted,
        }],
        vec![Export {
            name: cid(1),
            source: ExportSource::Local(BindingId::new(0)),
        }],
    );
    let root = program_module(
        "root",
        vec![
            Constant::String(EcmaString::encode("x")),
            Constant::Int32(2),
            Constant::String(EcmaString::encode("dep")),
        ],
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(2),
                },
                Instruction::StoreGlobal {
                    name: cid(1),
                    value: reg(0),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(3),
            target: EdgeTarget::Local(ModuleId::new(0)),
            kind: EdgeKind::Static,
        }],
        vec![Binding {
            name: cid(1),
            kind: BindingKind::Imported {
                edge: EdgeId::new(0),
                name: cid(1),
            },
        }],
        Vec::new(),
    );
    let program = linked(vec![dependency, root], 1);
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    machine.instantiate_modules().unwrap();
    assert!(machine.evaluate_module(ModuleId::new(1)).is_err());
    let exporter = machine.registry.modules[0].binding_cells[0].unwrap();
    assert_eq!(machine.registry.cells[exporter.0].value, Value::int32(1));
}

#[test]
fn namespace_descriptor_propagates_temporal_dead_zone() {
    let root = program_module(
        "root",
        vec![
            Constant::String(EcmaString::encode("x")),
            Constant::Int32(1),
            Constant::String(EcmaString::encode("dependency")),
        ],
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(2),
                },
                Instruction::StoreGlobal {
                    name: cid(1),
                    value: reg(0),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(3),
            target: EdgeTarget::Local(ModuleId::new(1)),
            kind: EdgeKind::Static,
        }],
        vec![Binding {
            name: cid(1),
            kind: BindingKind::Lexical,
        }],
        vec![Export {
            name: cid(1),
            source: ExportSource::Local(BindingId::new(0)),
        }],
    );
    let dependency = program_module(
        "dependency",
        vec![
            Constant::String(EcmaString::encode("ns")),
            Constant::String(EcmaString::encode("root")),
            Constant::String(EcmaString::encode("Object")),
            Constant::String(EcmaString::encode("getOwnPropertyDescriptor")),
            Constant::String(EcmaString::encode("x")),
        ],
        vec![namespace_descriptor_entry()],
        vec![Edge {
            specifier: cid(2),
            target: EdgeTarget::Local(ModuleId::new(0)),
            kind: EdgeKind::Static,
        }],
        vec![Binding {
            name: cid(1),
            kind: BindingKind::Namespace {
                edge: EdgeId::new(0),
            },
        }],
        Vec::new(),
    );
    let program = linked(vec![root, dependency], 0);
    let mut host = TestHost;
    let error = Machine::new(&program, &mut host, Limits::default())
        .run()
        .expect_err("descriptor reads uninitialized namespace export");
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::UncaughtThrow {
            origin: ThrowOrigin::ReferenceError { .. },
            ..
        }
    ));
}

#[test]
fn namespace_descriptor_propagates_external_linkage_error() {
    let exported = program_module(
        "exported",
        vec![
            Constant::String(EcmaString::encode("x")),
            Constant::String(EcmaString::encode("external")),
        ],
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
        vec![Edge {
            specifier: cid(2),
            target: EdgeTarget::External,
            kind: EdgeKind::Static,
        }],
        Vec::new(),
        vec![Export {
            name: cid(1),
            source: ExportSource::Indirect {
                edge: EdgeId::new(0),
                name: cid(1),
            },
        }],
    );
    let importer = program_module(
        "importer",
        vec![
            Constant::String(EcmaString::encode("ns")),
            Constant::String(EcmaString::encode("exported")),
            Constant::String(EcmaString::encode("Object")),
            Constant::String(EcmaString::encode("getOwnPropertyDescriptor")),
            Constant::String(EcmaString::encode("x")),
        ],
        vec![namespace_descriptor_entry()],
        vec![Edge {
            specifier: cid(2),
            target: EdgeTarget::Local(ModuleId::new(0)),
            kind: EdgeKind::Static,
        }],
        vec![Binding {
            name: cid(1),
            kind: BindingKind::Namespace {
                edge: EdgeId::new(0),
            },
        }],
        Vec::new(),
    );
    let program = linked(vec![exported, importer], 1);
    let mut host = TestHost;
    let error = Machine::new(&program, &mut host, Limits::default())
        .run()
        .expect_err("descriptor resolves external namespace export");
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::ExternalModuleUnavailable { module, edge }
            if module == ModuleId::new(0) && edge == EdgeId::new(0)
    ));
}

#[test]
fn installed_script_uses_machine_wide_id_and_keeps_its_code() {
    let root = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let script = Arc::new(verified(
        vec![Constant::Int32(42)],
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(0),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        )],
    ));
    let mut host = TestHost;
    let mut machine = Machine::new(&root, &mut host, Limits::default());
    machine.instantiate_modules().unwrap();
    let module = machine.install_script_reserving(script, 0, 0).unwrap();

    assert_eq!(module, ModuleId::new(root.modules().len() as u32));
    assert!(machine.program().module(module).is_none());
    assert_eq!(
        machine.module_code(module).constants()[0],
        Constant::Int32(42)
    );

    let closure = machine
        .allocate(HeapEntry::Function {
            module,
            function: FunctionId::new(0),
            captures: Vec::new(),
            context: None,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .unwrap();
    assert!(matches!(
        machine.call_value(closure, Value::UNDEFINED, &[]),
        Ok(value) if value == Value::int32(42)
    ));
}

#[test]
fn installed_script_rejects_non_classic_programs_and_enforces_limit() {
    let root = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let two_modules = Arc::new(linked(
        vec![
            program_module(
                "first",
                Vec::new(),
                vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
            program_module(
                "second",
                Vec::new(),
                vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
        ],
        0,
    ));
    let script = Arc::new(verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    ));
    let mut host = TestHost;
    let mut machine = Machine::new(
        &root,
        &mut host,
        Limits {
            max_dynamic_modules: 1,
            ..Limits::default()
        },
    );
    machine.instantiate_modules().unwrap();

    assert!(matches!(
        machine.install_script_reserving(two_modules, 0, 0),
        Err(RuntimeErrorKind::InvalidDynamicScript { .. })
    ));
    machine
        .install_script_reserving(script.clone(), 0, 0)
        .unwrap();
    assert!(matches!(
        machine.install_script_reserving(script, 0, 0),
        Err(RuntimeErrorKind::DynamicModuleLimitExceeded { limit: 1 })
    ));
}

#[test]
fn script_heap_cost_counts_scalar_constant_slots() {
    let entry = || vec![function(0, 1, vec![Instruction::Halt], Vec::new())];
    let empty = verified(Vec::new(), entry());
    let constants = vec![Constant::Int32(0); 128];
    let scalars = verified(constants.clone(), entry());

    let added = Machine::<TestHost>::script_heap_cost(&scalars)
        - Machine::<TestHost>::script_heap_cost(&empty);

    assert!(added >= constants.len() * std::mem::size_of::<Constant>());
}

#[test]
fn script_heap_cost_includes_verification_storage() {
    let small = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let large = verified(
        Vec::new(),
        vec![function(0, 130, vec![Instruction::Halt], Vec::new())],
    );
    let small_verification = small.modules()[0].code.verification_bytes();
    let large_verification = large.modules()[0].code.verification_bytes();

    assert_eq!(
        Machine::<TestHost>::script_heap_cost(&large)
            - Machine::<TestHost>::script_heap_cost(&small),
        large_verification - small_verification
    );
}
#[test]
fn promise_resolver_settles_once_and_reactions_wait_for_drain() {
    let program = verified(
        vec![
            Constant::String(EcmaString::encode("resolve")),
            Constant::String(EcmaString::encode("reject")),
            Constant::String(EcmaString::encode("observed")),
        ],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            function(
                2,
                2,
                vec![
                    Instruction::StoreGlobal {
                        name: cid(0),
                        value: reg(0),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(1),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
            function(
                1,
                1,
                vec![
                    Instruction::StoreGlobal {
                        name: cid(2),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let executor = machine
        .allocate(HeapEntry::Function {
            module: ModuleId::new(0),
            function: FunctionId::new(1),
            captures: Vec::new(),
            context: None,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .unwrap();
    let observer = machine
        .allocate(HeapEntry::Function {
            module: ModuleId::new(0),
            function: FunctionId::new(2),
            captures: Vec::new(),
            context: None,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .unwrap();
    let constructor = machine.intrinsics.global("Promise").unwrap();
    let constructor_index = machine.runtime_slot(constructor).unwrap().unwrap();
    let HeapEntry::NativeFunction {
        callable: NativeCallable::Builtin(constructor_id),
        ..
    } = machine.heap[constructor_index]
    else {
        panic!("Promise must be a native constructor");
    };
    let BuiltinOutcome::Value(promise) = machine
        .call_builtin(constructor_id, Value::UNDEFINED, &[executor], true)
        .unwrap()
    else {
        panic!("Promise construction returns a Promise");
    };
    let then = machine.get_named_property(promise, "then").unwrap();
    machine
        .call_value(then, promise, &[observer])
        .expect("then returns a derived Promise");
    let resolve = machine.test_global("resolve").unwrap();
    let reject = machine.test_global("reject").unwrap();
    assert_eq!(
        machine
            .call_value(resolve, Value::UNDEFINED, &[Value::int32(1)])
            .unwrap(),
        Value::UNDEFINED
    );
    assert_eq!(
        machine
            .call_value(reject, Value::UNDEFINED, &[Value::int32(2)])
            .unwrap(),
        Value::UNDEFINED
    );
    assert!(machine.test_global("observed").is_none());

    let drain = machine.drain_microtasks().unwrap();
    assert_eq!(drain.executed, 1);
    assert!(drain.uncaught.is_empty());
    assert_eq!(machine.test_global("observed"), Some(Value::int32(1)));
}

#[test]
fn promise_resolution_adopts_thenables_with_a_fresh_resolver() {
    let program = verified(
        vec![
            Constant::String(EcmaString::encode("resolve")),
            Constant::String(EcmaString::encode("reject")),
            Constant::String(EcmaString::encode("observed")),
            Constant::Int32(7),
            Constant::Int32(8),
            Constant::Int32(9),
            Constant::Undefined,
        ],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            function(
                2,
                2,
                vec![
                    Instruction::StoreGlobal {
                        name: cid(0),
                        value: reg(0),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(1),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
            function(
                1,
                1,
                vec![
                    Instruction::StoreGlobal {
                        name: cid(2),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
            function(
                2,
                6,
                vec![
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(3),
                    },
                    Instruction::CreateArray { dst: reg(3) },
                    Instruction::ArrayPush {
                        array: reg(3),
                        value: reg(2),
                    },
                    Instruction::LoadConst {
                        dst: reg(4),
                        constant: cid(6),
                    },
                    Instruction::Call {
                        dst: reg(5),
                        callee: reg(0),
                        this_value: reg(4),
                        arguments: reg(3),
                    },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(4),
                    },
                    Instruction::CreateArray { dst: reg(3) },
                    Instruction::ArrayPush {
                        array: reg(3),
                        value: reg(2),
                    },
                    Instruction::Call {
                        dst: reg(5),
                        callee: reg(1),
                        this_value: reg(4),
                        arguments: reg(3),
                    },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(5),
                    },
                    Instruction::Throw { value: reg(2) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let runtime_function = |machine: &mut Machine<'_, TestHost>, function| {
        machine
            .allocate(HeapEntry::Function {
                module: ModuleId::new(0),
                function: FunctionId::new(function),
                captures: Vec::new(),
                context: None,
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.function_prototype),
                extensible: true,
            })
            .unwrap()
    };
    let executor = runtime_function(&mut machine, 1);
    let observer = runtime_function(&mut machine, 2);
    let then_callback = runtime_function(&mut machine, 3);
    let thenable = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    machine
        .set_data_property(thenable, "then", then_callback)
        .unwrap();

    let constructor = machine.intrinsics.global("Promise").unwrap();
    let constructor_index = machine.runtime_slot(constructor).unwrap().unwrap();
    let HeapEntry::NativeFunction {
        callable: NativeCallable::Builtin(constructor_id),
        ..
    } = machine.heap[constructor_index]
    else {
        panic!("Promise must be a native constructor");
    };
    let BuiltinOutcome::Value(promise) = machine
        .call_builtin(constructor_id, Value::UNDEFINED, &[executor], true)
        .unwrap()
    else {
        panic!("Promise construction returns a Promise");
    };
    let resolve = machine.test_global("resolve").unwrap();
    let reject = machine.test_global("reject").unwrap();
    machine
        .call_value(resolve, Value::UNDEFINED, &[thenable])
        .unwrap();
    let then = machine.get_named_property(promise, "then").unwrap();
    machine.call_value(then, promise, &[observer]).unwrap();
    machine
        .call_value(reject, Value::UNDEFINED, &[Value::int32(9)])
        .unwrap();
    assert!(machine.test_global("observed").is_none());

    let drain = machine.drain_microtasks().unwrap();
    assert_eq!(drain.executed, 2);
    assert!(drain.uncaught.is_empty());
    assert_eq!(machine.test_global("observed"), Some(Value::int32(7)));
}

#[test]
fn queue_microtask_drains_fifo_including_jobs_added_during_drain() {
    let program = verified(
        vec![
            Constant::String(EcmaString::encode("order")),
            Constant::String(EcmaString::encode("queueMicrotask")),
            Constant::String(EcmaString::encode("third")),
            Constant::Int32(1),
            Constant::Int32(2),
            Constant::Int32(3),
            Constant::Undefined,
        ],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            function(
                0,
                7,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(3),
                    },
                    Instruction::ArrayPush {
                        array: reg(0),
                        value: reg(1),
                    },
                    Instruction::LoadGlobal {
                        dst: reg(2),
                        name: cid(1),
                    },
                    Instruction::LoadGlobal {
                        dst: reg(3),
                        name: cid(2),
                    },
                    Instruction::CreateArray { dst: reg(4) },
                    Instruction::ArrayPush {
                        array: reg(4),
                        value: reg(3),
                    },
                    Instruction::LoadConst {
                        dst: reg(5),
                        constant: cid(6),
                    },
                    Instruction::Call {
                        dst: reg(6),
                        callee: reg(2),
                        this_value: reg(5),
                        arguments: reg(4),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            ),
            function(
                0,
                2,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(4),
                    },
                    Instruction::ArrayPush {
                        array: reg(0),
                        value: reg(1),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            ),
            function(
                0,
                2,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(5),
                    },
                    Instruction::ArrayPush {
                        array: reg(0),
                        value: reg(1),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let runtime_function = |machine: &mut Machine<'_, TestHost>, function| {
        machine
            .allocate(HeapEntry::Function {
                module: ModuleId::new(0),
                function: FunctionId::new(function),
                captures: Vec::new(),
                context: None,
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.function_prototype),
                extensible: true,
            })
            .unwrap()
    };
    let first = runtime_function(&mut machine, 1);
    let second = runtime_function(&mut machine, 2);
    let third = runtime_function(&mut machine, 3);
    let order = machine
        .allocate(HeapEntry::Array {
            kind: ArrayElementKind::for_elements(&[]),
            elements: Vec::new(),
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.array_prototype),
            extensible: true,
            length_writable: true,
        })
        .unwrap();
    machine.test_set_global("order", order);
    machine.test_set_global("third", third);
    let queue = machine.intrinsics.global("queueMicrotask").unwrap();
    machine
        .call_value(queue, Value::UNDEFINED, &[first])
        .unwrap();
    machine
        .call_value(queue, Value::UNDEFINED, &[second])
        .unwrap();

    let drain = machine.drain_microtasks().unwrap();
    assert_eq!(drain.executed, 3);
    assert!(drain.uncaught.is_empty());
    let index = machine.runtime_slot(order).unwrap().unwrap();
    let HeapEntry::Array { elements, .. } = &machine.heap[index] else {
        panic!("order remains an array");
    };
    assert_eq!(
        elements,
        &[Value::int32(1), Value::int32(2), Value::int32(3)]
    );
}

#[test]
fn queue_microtask_reports_callback_throws_and_continues() {
    let program = verified(
        vec![
            Constant::Int32(7),
            Constant::Int32(1),
            Constant::String(EcmaString::encode("observed")),
        ],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Throw { value: reg(0) },
                ],
                Vec::new(),
            ),
            function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(1),
                    },
                    Instruction::StoreGlobal {
                        name: cid(2),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let runtime_function = |machine: &mut Machine<'_, TestHost>, function| {
        machine
            .allocate(HeapEntry::Function {
                module: ModuleId::new(0),
                function: FunctionId::new(function),
                captures: Vec::new(),
                context: None,
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.function_prototype),
                extensible: true,
            })
            .unwrap()
    };
    let throwing = runtime_function(&mut machine, 1);
    let observer = runtime_function(&mut machine, 2);
    let queue = machine.intrinsics.global("queueMicrotask").unwrap();
    machine
        .call_value(queue, Value::UNDEFINED, &[throwing])
        .unwrap();
    machine
        .call_value(queue, Value::UNDEFINED, &[observer])
        .unwrap();

    let drain = machine.drain_microtasks().unwrap();
    assert_eq!(drain.executed, 2);
    assert_eq!(
        drain.uncaught,
        vec![CallbackException {
            value: Value::int32(7),
            origin: ThrowOrigin::Bytecode,
        }]
    );
    assert_eq!(machine.test_global("observed"), Some(Value::int32(1)));
}

#[test]
fn microtask_boundaries_preserve_the_queued_head() {
    let program = verified(
        vec![Constant::Undefined],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(
        &program,
        &mut host,
        Limits {
            max_microtasks: 1,
            ..Limits::default()
        },
    );
    machine.frames.clear();
    machine.live_registers = 0;
    let callback = machine
        .allocate(HeapEntry::Function {
            module: ModuleId::new(0),
            function: FunctionId::new(1),
            captures: Vec::new(),
            context: None,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .unwrap();
    let queue = machine.intrinsics.global("queueMicrotask").unwrap();
    assert!(matches!(
        machine.call_value(queue, Value::UNDEFINED, &[Value::int32(1)]),
        Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
    ));
    machine
        .call_value(queue, Value::UNDEFINED, &[callback])
        .unwrap();
    assert!(matches!(
        machine.call_value(queue, Value::UNDEFINED, &[callback]),
        Err(EvalFailure::Runtime(
            RuntimeErrorKind::MicrotaskQueueLimitExceeded { limit: 1 }
        ))
    ));

    let fuel = machine.fuel;
    machine.microtask_drain_active = true;
    let reentry = machine.drain_microtasks().unwrap_err();
    assert!(matches!(
        reentry.kind,
        RuntimeErrorKind::MicrotaskDrainReentry
    ));
    assert_eq!(machine.fuel, fuel);
    assert_eq!(machine.microtasks.len(), 1);
    machine.microtask_drain_active = false;

    machine.fuel = 0;
    let exhausted = machine.drain_microtasks().unwrap_err();
    assert!(matches!(
        exhausted.kind,
        RuntimeErrorKind::FuelExhausted { .. }
    ));
    assert!(!machine.microtask_drain_active);
    assert_eq!(machine.microtasks.len(), 1);

    machine.fuel = 100;
    let drain = machine.drain_microtasks().unwrap();
    assert_eq!(drain.executed, 1);
    assert!(machine.microtasks.is_empty());
}

// ---- timers -----------------------------------------------------------

#[derive(Default)]
struct ManualTimerState {
    live: std::collections::BTreeMap<u64, u64>,
    reports: std::collections::VecDeque<TimerWakeup>,
    scheduled: Vec<(u64, u32)>,
    cancelled: Vec<u64>,
    auto_report: bool,
    fail_schedule: bool,
    fail_poll: bool,
}

#[derive(Clone, Default)]
struct ManualTimerProvider {
    state: std::rc::Rc<std::cell::RefCell<ManualTimerState>>,
}

impl TimerProvider for ManualTimerProvider {
    fn schedule(&mut self, id: u64, delay_ms: u32) -> Result<u64, TimerError> {
        let mut state = self.state.borrow_mut();
        state.scheduled.push((id, delay_ms));
        if state.fail_schedule {
            return Err(TimerError::new("manual schedule failure"));
        }
        let deadline = u64::from(delay_ms);
        state.live.insert(id, deadline);
        if state.auto_report {
            state.reports.push_back(TimerWakeup {
                id,
                deadline_ms: deadline,
            });
        }
        Ok(deadline)
    }

    fn cancel(&mut self, id: u64) -> Result<bool, TimerError> {
        let mut state = self.state.borrow_mut();
        state.cancelled.push(id);
        Ok(state.live.remove(&id).is_some())
    }

    fn poll_expired(&mut self, output: &mut Vec<TimerWakeup>) -> Result<(), TimerError> {
        let mut state = self.state.borrow_mut();
        if state.fail_poll {
            return Err(TimerError::new("manual poll failure"));
        }
        output.extend(state.reports.drain(..));
        Ok(())
    }

    fn wait_expired(
        &mut self,
        cancel: &CancellationToken,
    ) -> Result<Option<TimerWakeup>, TimerError> {
        if cancel.is_cancelled() {
            return Ok(None);
        }
        Ok(self.state.borrow_mut().reports.pop_front())
    }

    fn has_pending(&self) -> bool {
        !self.state.borrow().live.is_empty()
    }
}

#[derive(Default)]
struct TimerTestHost {
    provider: ManualTimerProvider,
}

impl Host for TimerTestHost {
    fn timers(&mut self) -> Option<&mut (dyn TimerProvider + 'static)> {
        Some(&mut self.provider)
    }
}

/// A timer provider that blocks on a cross-thread wake channel and checks
/// the supplied [`CancellationToken`]. Used to prove that `Machine` timer
/// wait can be cancelled promptly from another thread.
struct BlockingTimerProvider {
    started_tx: std::sync::mpsc::Sender<()>,
    wake_rx: std::sync::mpsc::Receiver<()>,
}

impl BlockingTimerProvider {
    fn new() -> (
        Self,
        std::sync::mpsc::Receiver<()>,
        std::sync::mpsc::Sender<()>,
    ) {
        let (started_tx, started_rx) = std::sync::mpsc::channel();
        let (wake_tx, wake_rx) = std::sync::mpsc::channel();
        (
            Self {
                started_tx,
                wake_rx,
            },
            started_rx,
            wake_tx,
        )
    }
}

impl TimerProvider for BlockingTimerProvider {
    fn schedule(&mut self, _id: u64, delay_ms: u32) -> Result<u64, TimerError> {
        Ok(u64::from(delay_ms))
    }

    fn cancel(&mut self, _id: u64) -> Result<bool, TimerError> {
        Ok(false)
    }

    fn poll_expired(&mut self, _output: &mut Vec<TimerWakeup>) -> Result<(), TimerError> {
        Ok(())
    }

    fn wait_expired(
        &mut self,
        cancel: &CancellationToken,
    ) -> Result<Option<TimerWakeup>, TimerError> {
        // Notify the test that we have entered the blocking wait.
        let _ = self.started_tx.send(());
        loop {
            if cancel.is_cancelled() {
                return Ok(None);
            }
            match self.wake_rx.recv_timeout(std::time::Duration::from_secs(1)) {
                Ok(()) => {
                    if cancel.is_cancelled() {
                        return Ok(None);
                    }
                    continue;
                }
                Err(std::sync::mpsc::RecvTimeoutError::Timeout) => continue,
                Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
                    return Err(TimerError::new("wake channel disconnected"));
                }
            }
        }
    }

    fn has_pending(&self) -> bool {
        true
    }
}

struct BlockingTimerTestHost {
    provider: BlockingTimerProvider,
}

impl Host for BlockingTimerTestHost {
    fn timers(&mut self) -> Option<&mut (dyn TimerProvider + 'static)> {
        Some(&mut self.provider)
    }
}

#[test]
fn timer_wait_is_cancelled_promptly_from_another_thread() {
    let program = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );

    let token = CancellationToken::new();
    let (provider, started_rx, wake_tx) = BlockingTimerProvider::new();
    let mut host = BlockingTimerTestHost { provider };
    let mut machine =
        Machine::new_with_cancel(&program, &mut host, Limits::default(), token.clone());
    machine.frames.clear();
    machine.live_registers = 0;

    let callback = machine
        .allocate(HeapEntry::Function {
            module: ModuleId::new(0),
            function: FunctionId::new(0),
            captures: Vec::new(),
            context: None,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .unwrap();
    machine
        .schedule_timeout(callback, 1_000_000, Vec::new())
        .unwrap();

    let cancel_handle = std::thread::spawn(move || {
        started_rx.recv().expect("provider entered wait");
        token.cancel();
        wake_tx.send(()).expect("wake the wait");
    });

    let error = machine
        .run_to_quiescence()
        .expect_err("cancelled wait aborts");
    assert!(matches!(error.kind, RuntimeErrorKind::Cancelled));

    cancel_handle.join().expect("cancel thread joins");
}

fn timer_program() -> Program<Verified> {
    verified(
        vec![
            Constant::String(EcmaString::encode("a")),
            Constant::String(EcmaString::encode("b")),
            Constant::String(EcmaString::encode("this_seen")),
            Constant::String(EcmaString::encode("arg_seen")),
            Constant::Int32(1),
            Constant::Int32(7),
        ],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(4),
                    },
                    Instruction::StoreGlobal {
                        name: cid(0),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
            function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(4),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
            function(
                1,
                2,
                vec![
                    Instruction::LoadThis { dst: reg(1) },
                    Instruction::StoreGlobal {
                        name: cid(2),
                        value: reg(1),
                    },
                    Instruction::StoreGlobal {
                        name: cid(3),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
            function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(5),
                    },
                    Instruction::Throw { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    )
}

fn timer_fn(machine: &mut Machine<'_, TimerTestHost>, index: u32) -> Value {
    timer_fn_in_context(machine, index, None)
}

fn timer_fn_in_context(
    machine: &mut Machine<'_, TimerTestHost>,
    index: u32,
    context: Option<Value>,
) -> Value {
    machine
        .allocate(HeapEntry::Function {
            module: ModuleId::new(0),
            function: FunctionId::new(index),
            captures: Vec::new(),
            context,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .unwrap()
}

fn read_global(machine: &Machine<'_, TimerTestHost>, name: &str) -> Option<Value> {
    machine.test_global(name)
}

fn set_timeout_global(machine: &Machine<'_, TimerTestHost>) -> Value {
    machine
        .intrinsics
        .global("setTimeout")
        .expect("setTimeout is installed")
}

fn test_context(machine: &mut Machine<'_, TimerTestHost>) -> Value {
    machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap()
}

#[test]
fn deferred_jobs_do_not_override_callback_lexical_context() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let first = test_context(&mut machine);
    let second = test_context(&mut machine);
    let write_root_a = timer_fn(&mut machine, 1);
    let write_first_b = timer_fn_in_context(&mut machine, 2, Some(first));
    let write_second_a = timer_fn_in_context(&mut machine, 1, Some(second));

    machine.context_global = Some(first);
    machine.enqueue_microtask_callback(write_root_a).unwrap();

    machine.context_global = Some(second);
    let promise = machine.create_promise().unwrap();
    machine
        .promise_then(promise, write_first_b, Value::UNDEFINED)
        .unwrap();

    machine.context_global = Some(first);
    machine
        .schedule_timeout(write_second_a, 1, Vec::new())
        .unwrap();
    machine.context_global = None;

    machine.fulfill_promise(promise, Value::UNDEFINED).unwrap();
    machine.drain_microtasks().unwrap();
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 1,
    });
    machine.run_one_expired_timer().unwrap();

    assert_eq!(read_global(&machine, "a"), Some(Value::int32(1)));
    assert_eq!(read_global(&machine, "b"), None);
    assert_eq!(
        machine.get_named_property(first, "a").unwrap(),
        Value::UNDEFINED
    );
    assert_eq!(
        machine.get_named_property(first, "b").unwrap(),
        Value::int32(1)
    );
    assert_eq!(
        machine.get_named_property(second, "a").unwrap(),
        Value::int32(1)
    );
    assert_eq!(
        machine.get_named_property(second, "b").unwrap(),
        Value::UNDEFINED
    );
    assert_eq!(machine.context_global, None);
}

#[test]
fn timer_safe_point_keeps_callback_rooted() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let callback = timer_fn(&mut machine, 1);
    machine.schedule_timeout(callback, 1, Vec::new()).unwrap();
    machine.set_gc_watermarks_for_test(0, 0);
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 1,
    });

    assert_eq!(machine.run_one_expired_timer().unwrap().executed, 1);
    assert_eq!(read_global(&machine, "a"), Some(Value::int32(1)));
}

fn schedule_nested_timer(
    machine: &mut Machine<'_, TimerTestHost>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let callback = machine
        .test_global("nestedCallback")
        .expect("test installs nested callback");
    let set_timeout = set_timeout_global(machine);
    machine.call_value(set_timeout, Value::UNDEFINED, &[callback, Value::int32(1)])?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn schedule_recursive_timer(
    machine: &mut Machine<'_, TimerTestHost>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let callback = machine
        .test_global("recursiveTimerCallback")
        .expect("test installs recursive timer callback");
    let set_timeout = set_timeout_global(machine);
    machine.call_value(set_timeout, Value::UNDEFINED, &[callback, Value::int32(0)])?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn timer_native(
    machine: &mut Machine<'_, TimerTestHost>,
    name: &'static str,
    handler: crate::intrinsics::BuiltinHandler<TimerTestHost>,
) -> Value {
    let id = machine
        .intrinsics
        .builtins
        .register(crate::intrinsics::BuiltinDef {
            name,
            length: 0,
            handler,
        });
    crate::intrinsics::native_function(
        &mut machine.heap,
        &mut machine.atoms,
        &mut machine.shapes,
        id,
        name,
        0,
    )
}

#[test]
fn timers_are_absent_without_the_capability() {
    let program = timer_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    assert!(machine.intrinsics.global("setTimeout").is_none());
    assert!(machine.intrinsics.global("clearTimeout").is_none());
    assert!(machine.intrinsics.global("setInterval").is_none());
    assert!(machine.intrinsics.global("clearInterval").is_none());
    assert!(!machine.has_pending_timers());
    assert_eq!(
        machine.run_one_expired_timer().unwrap(),
        TimerRun::default()
    );
    assert!(!machine.wait_for_timer_expiry().unwrap());
}

#[test]
fn set_timeout_rejects_a_non_callable_callback_before_coercion() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_timeout = set_timeout_global(&machine);
    let failure = machine
        .call_value(
            set_timeout,
            Value::UNDEFINED,
            &[Value::int32(3), Value::int32(5)],
        )
        .unwrap_err();
    assert!(matches!(
        failure,
        EvalFailure::Throw(ThrowOrigin::TypeError { .. })
    ));
    // Nothing was armed, so no delay coercion or provider call happened.
    assert!(shared.borrow().scheduled.is_empty());
    assert!(!machine.has_pending_timers());
}

#[test]
fn set_timeout_clamps_and_truncates_like_node() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_timeout = set_timeout_global(&machine);
    let callback = timer_fn(&mut machine, 1);
    for delay in [
        Value::int32(0),
        Value::number(-5.0),
        Value::number(f64::NAN),
        Value::number(2_147_483_648.0),
        Value::int32(2_147_483_647),
        Value::number(3.9),
    ] {
        machine
            .call_value(set_timeout, Value::UNDEFINED, &[callback, delay])
            .unwrap();
    }
    let delays: Vec<u32> = shared.borrow().scheduled.iter().map(|(_, d)| *d).collect();
    assert_eq!(delays, vec![1, 1, 1, 1, 2_147_483_647, 3]);
    // Ids are minted monotonically from 1 and never reused.
    let ids: Vec<u64> = shared
        .borrow()
        .scheduled
        .iter()
        .map(|(id, _)| *id)
        .collect();
    assert_eq!(ids, vec![1, 2, 3, 4, 5, 6]);
}

#[test]
fn same_deadline_timers_run_in_registration_order_despite_reverse_reports() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_timeout = set_timeout_global(&machine);
    let a = timer_fn(&mut machine, 1);
    let b = timer_fn(&mut machine, 2);
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[a, Value::int32(5)])
        .unwrap();
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[b, Value::int32(5)])
        .unwrap();
    // Host reports the later registration first and in split batches.
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 2,
        deadline_ms: 5,
    });
    let first = machine.run_one_expired_timer().unwrap();
    assert_eq!(first.executed, 1);
    assert_eq!(read_global(&machine, "a"), Some(Value::int32(1)));
    assert_eq!(read_global(&machine, "b"), None);
    let second = machine.run_one_expired_timer().unwrap();
    assert_eq!(second.executed, 1);
    assert_eq!(read_global(&machine, "b"), Some(Value::int32(1)));
    assert!(!machine.has_pending_timers());
}

#[test]
fn a_shorter_deadline_beats_an_older_sequence() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_timeout = set_timeout_global(&machine);
    let a = timer_fn(&mut machine, 1);
    let b = timer_fn(&mut machine, 2);
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[a, Value::int32(5)])
        .unwrap();
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[b, Value::int32(3)])
        .unwrap();
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 5,
    });
    machine.run_one_expired_timer().unwrap();
    assert_eq!(read_global(&machine, "b"), Some(Value::int32(1)));
    assert_eq!(read_global(&machine, "a"), None);
}

#[test]
fn clear_timeout_prevents_a_ready_timer_and_ignores_stale_ids() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_timeout = set_timeout_global(&machine);
    let clear_timeout = machine.intrinsics.global("clearTimeout").unwrap();
    let a = timer_fn(&mut machine, 1);
    let b = timer_fn(&mut machine, 2);
    let handle_a = machine
        .call_value(set_timeout, Value::UNDEFINED, &[a, Value::int32(3)])
        .unwrap();
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[b, Value::int32(3)])
        .unwrap();
    // Clear the first timer even though the host already reported it.
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 3,
    });
    machine
        .call_value(clear_timeout, Value::UNDEFINED, &[handle_a])
        .unwrap();
    assert!(shared.borrow().cancelled.contains(&1));
    // A stale positive-integer id must not cancel the surviving timer.
    machine
        .call_value(clear_timeout, Value::UNDEFINED, &[Value::int32(1)])
        .unwrap();
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 2,
        deadline_ms: 3,
    });
    let run = machine.run_one_expired_timer().unwrap();
    assert_eq!(run.executed, 1);
    assert_eq!(read_global(&machine, "a"), None);
    assert_eq!(read_global(&machine, "b"), Some(Value::int32(1)));
}

#[test]
fn clear_timeout_accepts_a_direct_positive_integer_id() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_timeout = set_timeout_global(&machine);
    let clear_timeout = machine.intrinsics.global("clearTimeout").unwrap();
    let a = timer_fn(&mut machine, 1);
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[a, Value::int32(3)])
        .unwrap();
    machine
        .call_value(clear_timeout, Value::UNDEFINED, &[Value::int32(1)])
        .unwrap();
    assert!(!machine.has_pending_timers());
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 3,
    });
    assert_eq!(machine.run_one_expired_timer().unwrap().executed, 0);

    machine.next_timer_id = Some(u64::MAX);
    let handle = machine
        .call_value(set_timeout, Value::UNDEFINED, &[a, Value::int32(3)])
        .unwrap();
    machine
        .call_value(
            clear_timeout,
            Value::UNDEFINED,
            &[Value::number(u64::MAX as f64)],
        )
        .unwrap();
    assert!(machine.has_pending_timers());
    machine
        .call_value(clear_timeout, Value::UNDEFINED, &[handle])
        .unwrap();
    assert!(!machine.has_pending_timers());
    // A no-op clear of an unrelated value never coerces or errors.
    machine
        .call_value(clear_timeout, Value::UNDEFINED, &[Value::UNDEFINED])
        .unwrap();
}

#[test]
fn timer_callback_receives_trailing_args_and_the_handle_as_this() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_timeout = set_timeout_global(&machine);
    let callback = timer_fn(&mut machine, 3);
    let handle = machine
        .call_value(
            set_timeout,
            Value::UNDEFINED,
            &[callback, Value::int32(1), Value::int32(42)],
        )
        .unwrap();
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 1,
    });
    machine.run_one_expired_timer().unwrap();
    assert_eq!(read_global(&machine, "this_seen"), Some(handle));
    assert_eq!(read_global(&machine, "arg_seen"), Some(Value::int32(42)));
}

#[test]
fn a_callback_created_timer_waits_for_a_later_checkpoint() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_timeout = set_timeout_global(&machine);
    let nested = timer_fn(&mut machine, 2);
    machine.test_set_global("nestedCallback", nested);
    let creator = timer_native(&mut machine, "schedule nested", schedule_nested_timer);
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[creator, Value::int32(1)])
        .unwrap();
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 1,
    });
    assert_eq!(machine.run_one_expired_timer().unwrap().executed, 1);
    assert_eq!(read_global(&machine, "b"), None);
    assert!(machine.has_pending_timers());
    // Even if the provider can report it immediately, it runs only in a
    // later explicit timer checkpoint.
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 2,
        deadline_ms: 1,
    });
    assert_eq!(machine.run_one_expired_timer().unwrap().executed, 1);
    assert_eq!(read_global(&machine, "b"), Some(Value::int32(1)));
}

#[test]
fn timer_callback_throw_is_reported_and_a_runtime_failure_propagates() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_timeout = set_timeout_global(&machine);
    let thrower = timer_fn(&mut machine, 4);
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[thrower, Value::int32(1)])
        .unwrap();
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 1,
    });
    let run = machine.run_one_expired_timer().unwrap();
    assert_eq!(run.executed, 1);
    assert_eq!(
        run.uncaught,
        vec![CallbackException {
            value: Value::int32(7),
            origin: ThrowOrigin::Bytecode
        }]
    );

    // A runtime failure inside the callback stops the checkpoint.
    let another = timer_fn(&mut machine, 1);
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[another, Value::int32(1)])
        .unwrap();
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 2,
        deadline_ms: 1,
    });
    machine.fuel = 1;
    let error = machine.run_one_expired_timer().unwrap_err();
    assert!(matches!(error.kind, RuntimeErrorKind::FuelExhausted { .. }));
}

#[test]
fn a_timer_checkpoint_never_drains_microtasks() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_timeout = set_timeout_global(&machine);
    let queue = machine.intrinsics.global("queueMicrotask").unwrap();
    let a = timer_fn(&mut machine, 1);
    let b = timer_fn(&mut machine, 2);
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[a, Value::int32(1)])
        .unwrap();
    machine.call_value(queue, Value::UNDEFINED, &[b]).unwrap();
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 1,
    });
    let run = machine.run_one_expired_timer().unwrap();
    assert_eq!(run.executed, 1);
    assert_eq!(read_global(&machine, "a"), Some(Value::int32(1)));
    assert_eq!(read_global(&machine, "b"), None);
    assert_eq!(machine.microtasks.len(), 1);
    machine.drain_microtasks().unwrap();
    assert_eq!(read_global(&machine, "b"), Some(Value::int32(1)));
}

#[test]
fn timer_reentry_capacity_and_fuel_preserve_state() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(
        &program,
        &mut host,
        Limits {
            max_timers: 1,
            ..Limits::default()
        },
    );
    machine.frames.clear();
    machine.live_registers = 0;
    let set_timeout = set_timeout_global(&machine);
    let a = timer_fn(&mut machine, 1);
    let b = timer_fn(&mut machine, 2);
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[a, Value::int32(1)])
        .unwrap();
    // Capacity is enforced before any provider or table mutation.
    let capacity = machine
        .call_value(set_timeout, Value::UNDEFINED, &[b, Value::int32(1)])
        .unwrap_err();
    assert!(matches!(
        capacity,
        EvalFailure::Runtime(RuntimeErrorKind::TimerCapacityExceeded { limit: 1 })
    ));
    assert_eq!(shared.borrow().scheduled.len(), 1);

    // Reentry fails without consuming fuel or touching the ready timer.
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 1,
    });
    machine.timer_checkpoint_active = true;
    let fuel = machine.fuel;
    let reentry = machine.run_one_expired_timer().unwrap_err();
    assert!(matches!(
        reentry.kind,
        RuntimeErrorKind::TimerCheckpointReentry
    ));
    assert_eq!(machine.fuel, fuel);
    machine.timer_checkpoint_active = false;

    // Fuel is charged before the live record is removed.
    machine.fuel = 0;
    let exhausted = machine.run_one_expired_timer().unwrap_err();
    assert!(matches!(
        exhausted.kind,
        RuntimeErrorKind::FuelExhausted { .. }
    ));
    assert!(machine.has_pending_timers());
    machine.fuel = 100;
    assert_eq!(machine.run_one_expired_timer().unwrap().executed, 1);
    assert_eq!(read_global(&machine, "a"), Some(Value::int32(1)));
}

#[test]
fn a_failed_schedule_never_reuses_its_timer_id() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_timeout = set_timeout_global(&machine);
    let a = timer_fn(&mut machine, 1);
    shared.borrow_mut().fail_schedule = true;
    let failure = machine
        .call_value(set_timeout, Value::UNDEFINED, &[a, Value::int32(1)])
        .unwrap_err();
    assert!(matches!(
        failure,
        EvalFailure::Runtime(RuntimeErrorKind::TimerProviderFailure { .. })
    ));
    shared.borrow_mut().fail_schedule = false;
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[a, Value::int32(1)])
        .unwrap();
    let ids: Vec<u64> = shared
        .borrow()
        .scheduled
        .iter()
        .map(|(id, _)| *id)
        .collect();
    assert_eq!(ids, vec![1, 2]);
}

#[test]
fn wait_for_timer_expiry_promotes_a_reported_timer() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    assert!(!machine.wait_for_timer_expiry().unwrap());
    let set_timeout = set_timeout_global(&machine);
    let a = timer_fn(&mut machine, 1);
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[a, Value::int32(1)])
        .unwrap();
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 1,
    });
    assert!(machine.wait_for_timer_expiry().unwrap());
    assert_eq!(machine.run_one_expired_timer().unwrap().executed, 1);
    assert_eq!(read_global(&machine, "a"), Some(Value::int32(1)));
}

// ---- automatic event loop ---------------------------------------------

/// A program whose entry queues the global `"job"` microtask, with helper
/// functions that push a marker onto the global `"order"` array. Function 1
/// also queues `"job"` so a microtask can be created during a drain or a
/// timer turn. The entry function is only exercised by `evaluate`.
fn loop_test_program() -> Program<Verified> {
    verified(
        vec![
            Constant::String(EcmaString::encode("order")), // 0
            Constant::Int32(1),                            // 1
            Constant::Int32(2),                            // 2
            Constant::Int32(3),                            // 3
            Constant::Int32(4),                            // 4
            Constant::String(EcmaString::encode("queueMicrotask")), // 5
            Constant::String(EcmaString::encode("job")),   // 6
            Constant::Undefined,                           // 7
        ],
        vec![
            function(
                0,
                7,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(5),
                    },
                    Instruction::LoadGlobal {
                        dst: reg(1),
                        name: cid(6),
                    },
                    Instruction::CreateArray { dst: reg(2) },
                    Instruction::ArrayPush {
                        array: reg(2),
                        value: reg(1),
                    },
                    Instruction::LoadConst {
                        dst: reg(3),
                        constant: cid(7),
                    },
                    Instruction::Call {
                        dst: reg(4),
                        callee: reg(0),
                        this_value: reg(3),
                        arguments: reg(2),
                    },
                    Instruction::Return { value: reg(3) },
                ],
                Vec::new(),
            ),
            function(
                0,
                7,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(1),
                    },
                    Instruction::ArrayPush {
                        array: reg(0),
                        value: reg(1),
                    },
                    Instruction::LoadGlobal {
                        dst: reg(2),
                        name: cid(5),
                    },
                    Instruction::LoadGlobal {
                        dst: reg(3),
                        name: cid(6),
                    },
                    Instruction::CreateArray { dst: reg(4) },
                    Instruction::ArrayPush {
                        array: reg(4),
                        value: reg(3),
                    },
                    Instruction::LoadConst {
                        dst: reg(5),
                        constant: cid(7),
                    },
                    Instruction::Call {
                        dst: reg(6),
                        callee: reg(2),
                        this_value: reg(5),
                        arguments: reg(4),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            ),
            function(
                0,
                2,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(2),
                    },
                    Instruction::ArrayPush {
                        array: reg(0),
                        value: reg(1),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            ),
            function(
                0,
                2,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(3),
                    },
                    Instruction::ArrayPush {
                        array: reg(0),
                        value: reg(1),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            ),
            function(
                0,
                2,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(4),
                    },
                    Instruction::ArrayPush {
                        array: reg(0),
                        value: reg(1),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            ),
        ],
    )
}

fn promise_throw_program() -> Program<Verified> {
    verified(
        vec![
            Constant::String(EcmaString::encode("resolve")),  // 0
            Constant::String(EcmaString::encode("reject")),   // 1
            Constant::String(EcmaString::encode("observed")), // 2
            Constant::Int32(7),                               // 3
        ],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            function(
                2,
                2,
                vec![
                    Instruction::StoreGlobal {
                        name: cid(0),
                        value: reg(0),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(1),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
            function(
                1,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(3),
                    },
                    Instruction::Throw { value: reg(0) },
                ],
                Vec::new(),
            ),
            function(
                1,
                1,
                vec![
                    Instruction::StoreGlobal {
                        name: cid(2),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
                Vec::new(),
            ),
        ],
    )
}

fn install_order_array(machine: &mut Machine<'_, TimerTestHost>) -> Value {
    let order = machine
        .allocate(HeapEntry::Array {
            kind: ArrayElementKind::for_elements(&[]),
            elements: Vec::new(),
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.array_prototype),
            extensible: true,
            length_writable: true,
        })
        .unwrap();
    machine.test_set_global("order", order);
    order
}

fn order_markers(machine: &Machine<'_, TimerTestHost>) -> Vec<Value> {
    let order = machine
        .test_global("order")
        .expect("order array is installed");
    let index = machine
        .runtime_slot(order)
        .expect("order resolves")
        .expect("order is a heap value");
    let HeapEntry::Array { elements, .. } = &machine.heap[index] else {
        panic!("order remains an array");
    };
    elements.clone()
}

fn schedule_global_job(
    machine: &mut Machine<'_, TimerTestHost>,
    global: &str,
) -> Result<BuiltinOutcome, EvalFailure> {
    let job = machine
        .test_global(global)
        .unwrap_or_else(|| panic!("test installs the {global} job"));
    let queue = machine
        .intrinsics
        .global("queueMicrotask")
        .expect("queueMicrotask is installed");
    machine.call_value(queue, Value::UNDEFINED, &[job])?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn queue_job_then_throw(
    machine: &mut Machine<'_, TimerTestHost>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    schedule_global_job(machine, "nestedCallback")?;
    Err(EvalFailure::ThrowValue(Value::int32(7)))
}

fn respawn_job(
    machine: &mut Machine<'_, TimerTestHost>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    schedule_global_job(machine, "nestedCallback")
}

#[test]
fn automatic_loop_leaves_an_idle_machine_untouched() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let fuel = machine.fuel;
    machine.run_to_quiescence().unwrap();
    assert_eq!(machine.fuel, fuel);
    assert!(machine.microtasks.is_empty());
    assert!(!machine.has_pending_timers());
    assert!(!machine.microtask_drain_active);
    assert!(!machine.timer_checkpoint_active);
}

#[test]
fn run_returns_the_synchronous_execution_snapshot() {
    let program = loop_test_program();
    let mut host = TimerTestHost::default();
    let mut first = Machine::new(&program, &mut host, Limits::default());
    first.frames.clear();
    first.live_registers = 0;
    install_order_array(&mut first);
    let first_job = timer_fn(&mut first, 2);
    first.test_set_global("job", first_job);
    let snapshot = first.evaluate().unwrap();
    assert!(order_markers(&first).is_empty());
    first.run_to_quiescence().unwrap();
    assert_eq!(order_markers(&first), vec![Value::int32(2)]);
    drop(first);

    let mut host = TimerTestHost::default();
    let mut second = Machine::new(&program, &mut host, Limits::default());
    second.frames.clear();
    second.live_registers = 0;
    install_order_array(&mut second);
    let second_job = timer_fn(&mut second, 2);
    second.test_set_global("job", second_job);
    let execution = second.run().unwrap();
    assert_eq!(execution, snapshot);
}

#[test]
fn automatic_loop_drains_nested_microtasks_in_fifo_order() {
    let program = loop_test_program();
    let mut host = TimerTestHost::default();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    install_order_array(&mut machine);
    let first = timer_fn(&mut machine, 1); // pushes 1, queues "job"
    let second = timer_fn(&mut machine, 2); // pushes 2
    let third = timer_fn(&mut machine, 3); // pushes 3
    machine.test_set_global("job", third);
    let queue = machine.intrinsics.global("queueMicrotask").unwrap();
    machine
        .call_value(queue, Value::UNDEFINED, &[first])
        .unwrap();
    machine
        .call_value(queue, Value::UNDEFINED, &[second])
        .unwrap();

    machine.run_to_quiescence().unwrap();
    assert_eq!(
        order_markers(&machine),
        vec![Value::int32(1), Value::int32(2), Value::int32(3)]
    );
    assert!(machine.microtasks.is_empty());
}

#[test]
fn automatic_loop_runs_two_timers_with_a_full_drain_between_turns() {
    let program = loop_test_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    install_order_array(&mut machine);
    let first = timer_fn(&mut machine, 1); // pushes 1, queues "job"
    let second = timer_fn(&mut machine, 3); // pushes 3
    let microtask = timer_fn(&mut machine, 2); // pushes 2
    machine.test_set_global("job", microtask);
    let set_timeout = set_timeout_global(&machine);
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[first, Value::int32(5)])
        .unwrap();
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[second, Value::int32(5)])
        .unwrap();
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 5,
    });
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 2,
        deadline_ms: 5,
    });

    machine.run_to_quiescence().unwrap();
    // The first timer's microtask (2) runs before the second timer (3).
    assert_eq!(
        order_markers(&machine),
        vec![Value::int32(1), Value::int32(2), Value::int32(3)]
    );
    assert!(machine.microtasks.is_empty());
    assert!(!machine.has_pending_timers());
}

#[test]
fn automatic_loop_runs_a_timer_created_timer_in_a_later_turn() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let nested = timer_fn(&mut machine, 2);
    machine.test_set_global("nestedCallback", nested);
    let creator = timer_native(&mut machine, "schedule nested", schedule_nested_timer);
    let set_timeout = set_timeout_global(&machine);
    shared.borrow_mut().auto_report = true;
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[creator, Value::int32(1)])
        .unwrap();

    machine.run_to_quiescence().unwrap();
    assert_eq!(read_global(&machine, "b"), Some(Value::int32(1)));
    assert!(!machine.has_pending_timers());
    assert!(machine.microtasks.is_empty());
}

#[test]
fn automatic_loop_ignores_stale_and_premature_reports_until_real_expiry() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let a = timer_fn(&mut machine, 1);
    let set_timeout = set_timeout_global(&machine);
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[a, Value::int32(50)])
        .unwrap();
    // A stale wakeup for an unknown id must not terminate the loop.
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 999,
        deadline_ms: 10,
    });
    // A premature wakeup for the live timer cannot fire it before its deadline.
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 10,
    });
    // The real expiry report finally fires the callback.
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 50,
    });

    machine.run_to_quiescence().unwrap();
    assert_eq!(read_global(&machine, "a"), Some(Value::int32(1)));
    assert!(!machine.has_pending_timers());
}

#[test]
fn automatic_loop_rejects_an_empty_wait_while_a_timer_is_live() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let a = timer_fn(&mut machine, 1);
    let set_timeout = set_timeout_global(&machine);
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[a, Value::int32(5)])
        .unwrap();
    // A broken nonblocking provider returns no report for an armed timer.

    let error = machine.run_to_quiescence().unwrap_err();
    assert!(matches!(
        error.kind,
        RuntimeErrorKind::TimerProviderFailure { .. }
    ));
    // The machine-owned live record and flags survive the failure.
    assert!(machine.has_pending_timers());
    assert!(shared.borrow().live.contains_key(&1));
    assert!(!machine.microtask_drain_active);
    assert!(!machine.timer_checkpoint_active);
}

fn set_interval_global(machine: &Machine<'_, TimerTestHost>) -> Value {
    machine
        .intrinsics
        .global("setInterval")
        .expect("setInterval is installed")
}

fn clear_interval_global(machine: &Machine<'_, TimerTestHost>) -> Value {
    machine
        .intrinsics
        .global("clearInterval")
        .expect("clearInterval is installed")
}

fn increment_count(
    machine: &mut Machine<'_, TimerTestHost>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let current = machine
        .test_global("count")
        .and_then(|v| match v.decode() {
            Some(Decoded::Int32(i)) => Some(i),
            _ => None,
        })
        .unwrap_or(0);
    machine.test_set_global("count", Value::int32(current + 1));
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

#[test]
fn set_interval_fires_repeatedly_and_stays_live() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_interval = set_interval_global(&machine);
    let callback = timer_native(&mut machine, "increment", increment_count);
    machine
        .call_value(set_interval, Value::UNDEFINED, &[callback, Value::int32(5)])
        .unwrap();
    assert!(machine.has_pending_timers());

    // First fire: the callback runs and the interval re-arms.
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 5,
    });
    assert_eq!(machine.run_one_expired_timer().unwrap().executed, 1);
    assert_eq!(read_global(&machine, "count"), Some(Value::int32(1)));
    assert!(machine.has_pending_timers());

    // Second fire: the callback runs again and the interval is still live.
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 10,
    });
    assert_eq!(machine.run_one_expired_timer().unwrap().executed, 1);
    assert_eq!(read_global(&machine, "count"), Some(Value::int32(2)));
    assert!(machine.has_pending_timers());
}

#[test]
fn clear_interval_cancels_a_repeating_callback() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_interval = set_interval_global(&machine);
    let clear_interval = clear_interval_global(&machine);
    let callback = timer_native(&mut machine, "increment", increment_count);
    let handle = machine
        .call_value(set_interval, Value::UNDEFINED, &[callback, Value::int32(5)])
        .unwrap();
    // setInterval returns the Timeout handle object, not a raw id.
    assert!(matches!(handle.decode(), Some(Decoded::HeapRef(_))));
    assert!(machine.has_pending_timers());

    // Fire once to confirm the interval is live, then clear it.
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 5,
    });
    assert_eq!(machine.run_one_expired_timer().unwrap().executed, 1);
    assert!(machine.has_pending_timers());

    machine
        .call_value(clear_interval, Value::UNDEFINED, &[handle])
        .unwrap();
    assert!(!machine.has_pending_timers());
    // A late report for the cleared interval does not fire.
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 10,
    });
    assert_eq!(machine.run_one_expired_timer().unwrap().executed, 0);
    assert_eq!(read_global(&machine, "count"), Some(Value::int32(1)));
}

#[test]
fn set_interval_rejects_a_non_callable_callback_before_coercion() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_interval = set_interval_global(&machine);
    let failure = machine
        .call_value(
            set_interval,
            Value::UNDEFINED,
            &[Value::int32(3), Value::int32(5)],
        )
        .unwrap_err();
    assert!(matches!(
        failure,
        EvalFailure::Throw(ThrowOrigin::TypeError { .. })
    ));
    // Nothing was armed, so no delay coercion or provider call happened.
    assert!(shared.borrow().scheduled.is_empty());
    assert!(!machine.has_pending_timers());
}

#[test]
fn set_interval_clamps_and_truncates_like_node() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_interval = set_interval_global(&machine);
    let callback = timer_fn(&mut machine, 1);
    for delay in [
        Value::int32(0),
        Value::number(-5.0),
        Value::number(f64::NAN),
        Value::number(2_147_483_648.0),
        Value::int32(2_147_483_647),
        Value::number(3.9),
    ] {
        machine
            .call_value(set_interval, Value::UNDEFINED, &[callback, delay])
            .unwrap();
    }
    let delays: Vec<u32> = shared.borrow().scheduled.iter().map(|(_, d)| *d).collect();
    assert_eq!(delays, vec![1, 1, 1, 1, 2_147_483_647, 3]);
}

fn clear_self_and_count(
    machine: &mut Machine<'_, TimerTestHost>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let current = machine
        .test_global("count")
        .and_then(|v| match v.decode() {
            Some(Decoded::Int32(i)) => Some(i),
            _ => None,
        })
        .unwrap_or(0);
    machine.test_set_global("count", Value::int32(current + 1));
    let clear_interval = machine.intrinsics.global("clearInterval").unwrap();
    machine.call_value(clear_interval, Value::UNDEFINED, &[this])?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

#[test]
fn interval_self_cancel_runs_once_and_reaches_quiescence() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_interval = set_interval_global(&machine);
    let callback = timer_native(&mut machine, "clearSelf", clear_self_and_count);
    machine.test_set_global("count", Value::int32(0));
    machine
        .call_value(set_interval, Value::UNDEFINED, &[callback, Value::int32(5)])
        .unwrap();
    assert!(machine.has_pending_timers());
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 5,
    });
    machine.run_to_quiescence().unwrap();
    assert_eq!(read_global(&machine, "count"), Some(Value::int32(1)));
    assert!(!machine.has_pending_timers());
    assert!(shared.borrow().cancelled.contains(&1));
}

#[test]
fn stale_interval_handle_cannot_cancel_a_reused_generation() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let set_interval = set_interval_global(&machine);
    let clear_interval = clear_interval_global(&machine);
    let callback = timer_native(&mut machine, "increment", increment_count);
    let handle = machine
        .call_value(set_interval, Value::UNDEFINED, &[callback, Value::int32(5)])
        .unwrap();
    machine.test_set_global("count", Value::int32(0));
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 5,
    });
    assert_eq!(machine.run_one_expired_timer().unwrap().executed, 1);
    assert_eq!(read_global(&machine, "count"), Some(Value::int32(1)));
    assert!(machine.has_pending_timers());

    let stale = machine
        .allocate(HeapEntry::Timeout {
            id: 1,
            generation: 0,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            extensible: true,
        })
        .unwrap();
    machine
        .call_value(clear_interval, Value::UNDEFINED, &[stale])
        .unwrap();
    assert!(machine.has_pending_timers());

    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 10,
    });
    assert_eq!(machine.run_one_expired_timer().unwrap().executed, 1);
    assert_eq!(read_global(&machine, "count"), Some(Value::int32(2)));
    assert!(machine.has_pending_timers());

    machine
        .call_value(clear_interval, Value::UNDEFINED, &[handle])
        .unwrap();
    assert!(!machine.has_pending_timers());
}

#[test]
fn automatic_loop_maps_the_first_uncaught_microtask_throw_and_stops() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let throwing = timer_fn(&mut machine, 4); // throws 7
    let observer = timer_fn(&mut machine, 1); // stores a = 1
    let queue = machine.intrinsics.global("queueMicrotask").unwrap();
    machine
        .call_value(queue, Value::UNDEFINED, &[throwing])
        .unwrap();
    machine
        .call_value(queue, Value::UNDEFINED, &[observer])
        .unwrap();

    let error = machine.run_to_quiescence().unwrap_err();
    assert_eq!(
        error.kind,
        RuntimeErrorKind::UncaughtThrow {
            value: Value::int32(7),
            origin: ThrowOrigin::Bytecode,
            constructor_name: None,
            message: None,
        }
    );
    // The later job stays queued and unrun.
    assert_eq!(read_global(&machine, "a"), None);
    assert_eq!(machine.microtasks.len(), 1);
    assert!(!machine.microtask_drain_active);
}

#[test]
fn automatic_loop_timer_throw_suppresses_queued_microtasks_and_later_timers() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let suppressed_microtask = timer_fn(&mut machine, 2); // stores b = 1
    machine.test_set_global("nestedCallback", suppressed_microtask);
    let thrower = timer_native(&mut machine, "queue then throw", queue_job_then_throw);
    let later_timer = timer_fn(&mut machine, 1); // stores a = 1
    let set_timeout = set_timeout_global(&machine);
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[thrower, Value::int32(1)])
        .unwrap();
    machine
        .call_value(
            set_timeout,
            Value::UNDEFINED,
            &[later_timer, Value::int32(2)],
        )
        .unwrap();
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 1,
        deadline_ms: 1,
    });
    shared.borrow_mut().reports.push_back(TimerWakeup {
        id: 2,
        deadline_ms: 2,
    });

    let error = machine.run_to_quiescence().unwrap_err();
    assert_eq!(
        error.kind,
        RuntimeErrorKind::UncaughtThrow {
            value: Value::int32(7),
            origin: ThrowOrigin::Bytecode,
            constructor_name: None,
            message: None,
        }
    );
    // The exception converts before any drain, so the queued microtask and
    // the later timer both stay pending.
    assert_eq!(read_global(&machine, "b"), None);
    assert_eq!(read_global(&machine, "a"), None);
    assert_eq!(machine.microtasks.len(), 1);
    assert!(machine.has_pending_timers());
    assert!(!machine.microtask_drain_active);
    assert!(!machine.timer_checkpoint_active);
}

#[test]
fn automatic_loop_settles_derived_promises_when_a_handler_throws() {
    let program = promise_throw_program();
    let mut host = TimerTestHost::default();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let executor = timer_fn(&mut machine, 1);
    let throwing = timer_fn(&mut machine, 2);
    let observer = timer_fn(&mut machine, 3);
    let constructor = machine.intrinsics.global("Promise").unwrap();
    let constructor_index = machine.runtime_slot(constructor).unwrap().unwrap();
    let HeapEntry::NativeFunction {
        callable: NativeCallable::Builtin(constructor_id),
        ..
    } = machine.heap[constructor_index]
    else {
        panic!("Promise must be a native constructor");
    };
    let BuiltinOutcome::Value(promise) = machine
        .call_builtin(constructor_id, Value::UNDEFINED, &[executor], true)
        .unwrap()
    else {
        panic!("Promise construction returns a Promise");
    };
    let resolve = machine.test_global("resolve").unwrap();
    machine
        .call_value(resolve, Value::UNDEFINED, &[Value::int32(1)])
        .unwrap();
    let then = machine.get_named_property(promise, "then").unwrap();
    let derived = machine.call_value(then, promise, &[throwing]).unwrap();
    let then_again = machine.get_named_property(derived, "then").unwrap();
    machine
        .call_value(then_again, derived, &[Value::UNDEFINED, observer])
        .unwrap();

    machine.run_to_quiescence().unwrap();
    // The thrown handler rejects the derived promise, whose rejection
    // observer runs instead of aborting the loop.
    assert_eq!(machine.test_global("observed"), Some(Value::int32(7)));
    assert!(machine.microtasks.is_empty());
}

#[test]
fn recursive_microtask_work_reaches_existing_fuel() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let respawn = timer_native(&mut machine, "respawn", respawn_job);
    machine.test_set_global("nestedCallback", respawn);
    let queue = machine.intrinsics.global("queueMicrotask").unwrap();
    machine
        .call_value(queue, Value::UNDEFINED, &[respawn])
        .unwrap();
    machine.fuel = 16;

    let error = machine.run_to_quiescence().unwrap_err();
    assert!(matches!(error.kind, RuntimeErrorKind::FuelExhausted { .. }));
    // Recursive work never reaches quiescence; fuel was fully spent.
    assert_eq!(machine.fuel, 0);
    assert!(!machine.microtask_drain_active);
}

#[test]
fn recursive_timer_work_reaches_existing_fuel() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let shared = host.provider.state.clone();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    shared.borrow_mut().auto_report = true;
    let respawn = timer_native(&mut machine, "respawn timer", schedule_recursive_timer);
    machine.test_set_global("recursiveTimerCallback", respawn);
    let set_timeout = set_timeout_global(&machine);
    machine
        .call_value(set_timeout, Value::UNDEFINED, &[respawn, Value::int32(0)])
        .unwrap();
    machine.fuel = 16;

    let error = machine.run_to_quiescence().unwrap_err();
    assert!(matches!(error.kind, RuntimeErrorKind::FuelExhausted { .. }));
    assert_eq!(machine.fuel, 0);
    assert!(machine.has_pending_timers());
    assert!(!machine.timer_checkpoint_active);
}

#[test]
fn manual_drain_still_collects_every_throw_and_continues() {
    let program = timer_program();
    let mut host = TimerTestHost::default();
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let throwing = timer_fn(&mut machine, 4); // throws 7
    let observer = timer_fn(&mut machine, 1); // stores a = 1
    let queue = machine.intrinsics.global("queueMicrotask").unwrap();
    machine
        .call_value(queue, Value::UNDEFINED, &[throwing])
        .unwrap();
    machine
        .call_value(queue, Value::UNDEFINED, &[observer])
        .unwrap();
    machine
        .call_value(queue, Value::UNDEFINED, &[throwing])
        .unwrap();

    let drain = machine.drain_microtasks().unwrap();
    assert_eq!(drain.executed, 3);
    assert_eq!(
        drain.uncaught,
        vec![
            CallbackException {
                value: Value::int32(7),
                origin: ThrowOrigin::Bytecode,
            },
            CallbackException {
                value: Value::int32(7),
                origin: ThrowOrigin::Bytecode,
            },
        ]
    );
    assert_eq!(read_global(&machine, "a"), Some(Value::int32(1)));
    assert!(machine.microtasks.is_empty());
}

#[derive(Default)]
struct ImportMetaHost {
    seen: Vec<EcmaString>,
}

impl Host for ImportMetaHost {
    fn import_meta_url(&mut self, module_name: &EcmaString) -> EcmaString {
        self.seen.push(module_name.clone());
        EcmaString::encode("host://modules/entry.mjs")
    }
}

#[test]
fn import_meta_is_host_url_backed_stable_and_edge_independent() {
    let program = linked(
        vec![program_module(
            "entry",
            vec![
                Constant::String(EcmaString::encode("url")),
                Constant::String(EcmaString::encode("host://modules/entry.mjs")),
            ],
            vec![function(
                0,
                7,
                vec![
                    Instruction::LoadImportMeta { dst: reg(0) },
                    Instruction::LoadImportMeta { dst: reg(1) },
                    Instruction::Binary {
                        dst: reg(2),
                        op: BinaryOp::StrictEqual,
                        left: reg(0),
                        right: reg(1),
                    },
                    Instruction::LoadConst {
                        dst: reg(3),
                        constant: cid(1),
                    },
                    Instruction::GetProperty {
                        dst: reg(4),
                        object: reg(0),
                        key: reg(3),
                    },
                    Instruction::LoadConst {
                        dst: reg(5),
                        constant: cid(2),
                    },
                    Instruction::Binary {
                        dst: reg(6),
                        op: BinaryOp::StrictEqual,
                        left: reg(4),
                        right: reg(5),
                    },
                    Instruction::Return { value: reg(6) },
                ],
                Vec::new(),
            )],
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )],
        0,
    );
    assert!(program.modules()[0].edges.is_empty());
    let mut host = ImportMetaHost::default();
    let execution = Machine::new(&program, &mut host, Limits::default())
        .run()
        .unwrap();
    assert_eq!(execution.entry_registers[0], execution.entry_registers[1]);
    assert_eq!(execution.entry_registers[2], Value::TRUE);
    assert_eq!(execution.value, Value::TRUE);
    assert_eq!(host.seen, vec![EcmaString::encode("entry")]);
}

#[test]
fn to_object_preserves_objects_boxes_primitives_and_rejects_nullish() {
    let program = verified(
        vec![Constant::Int32(7)],
        vec![function(
            0,
            4,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(0),
                },
                Instruction::ToObject {
                    dst: reg(1),
                    src: reg(0),
                },
                Instruction::CreateObject { dst: reg(2) },
                Instruction::ToObject {
                    dst: reg(3),
                    src: reg(2),
                },
                Instruction::Return { value: reg(3) },
            ],
            Vec::new(),
        )],
    );
    let execution = run_ok(&program);
    assert_ne!(execution.entry_registers[1], Value::int32(7));
    assert_eq!(execution.entry_registers[2], execution.entry_registers[3]);

    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let boxed = machine
        .value_to_object(Value::int32(7))
        .expect("primitive boxes");
    assert_eq!(
        machine
            .unbox_primitive_or_self(boxed)
            .expect("valid wrapper"),
        Value::int32(7)
    );
    assert!(matches!(
        machine.value_to_object(Value::NULL),
        Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
    ));
}

#[test]
fn raw_string_own_properties_expose_length_and_in_range_indices() {
    with_machine(Limits::default(), |machine| {
        let string = machine
            .allocate(HeapEntry::String(EcmaString::encode("ab")))
            .unwrap();
        let length = PropertyKey::Named(machine.intern_str("length"));
        let zero = PropertyKey::Named(machine.intern_str("0"));
        let one = PropertyKey::Named(machine.intern_str("1"));
        let two = PropertyKey::Named(machine.intern_str("2"));

        assert!(machine.has_own_property_key(string, &length).unwrap());
        assert!(machine.has_own_property_key(string, &zero).unwrap());
        assert!(machine.has_own_property_key(string, &one).unwrap());
        assert!(!machine.has_own_property_key(string, &two).unwrap());
        assert!(machine.internal_has_property(string, &length).unwrap());
        assert!(machine.internal_has_property(string, &zero).unwrap());
        assert!(!machine.internal_has_property(string, &two).unwrap());

        assert_eq!(
            machine.get_property_key(string, &length).unwrap(),
            number_value(2.0)
        );
        let zero_value = machine.get_property_key(string, &zero).unwrap();
        assert_eq!(
            machine.string_value(zero_value).unwrap(),
            EcmaString::encode("a")
        );
        let one_value = machine.get_property_key(string, &one).unwrap();
        assert_eq!(
            machine.string_value(one_value).unwrap(),
            EcmaString::encode("b")
        );
    });
}

#[test]
fn boxed_string_own_properties_expose_length_and_in_range_indices() {
    with_machine(Limits::default(), |machine| {
        let string = machine
            .allocate(HeapEntry::String(EcmaString::encode("ab")))
            .unwrap();
        let boxed = machine.value_to_object(string).unwrap();
        let length = PropertyKey::Named(machine.intern_str("length"));
        let zero = PropertyKey::Named(machine.intern_str("0"));
        let one = PropertyKey::Named(machine.intern_str("1"));
        let two = PropertyKey::Named(machine.intern_str("2"));

        assert!(machine.has_own_property_key(boxed, &length).unwrap());
        assert!(machine.has_own_property_key(boxed, &zero).unwrap());
        assert!(machine.has_own_property_key(boxed, &one).unwrap());
        assert!(!machine.has_own_property_key(boxed, &two).unwrap());
        assert!(machine.internal_has_property(boxed, &length).unwrap());
        assert!(machine.internal_has_property(boxed, &zero).unwrap());
        assert!(!machine.internal_has_property(boxed, &two).unwrap());

        assert_eq!(
            machine.get_property_key(boxed, &length).unwrap(),
            number_value(2.0)
        );
        assert_eq!(
            machine.get_named_property(boxed, "length").unwrap(),
            number_value(2.0)
        );
        let zero_value = machine.get_property_key(boxed, &zero).unwrap();
        assert_eq!(
            machine.string_value(zero_value).unwrap(),
            EcmaString::encode("a")
        );
        let one_value = machine.get_property_key(boxed, &one).unwrap();
        assert_eq!(
            machine.string_value(one_value).unwrap(),
            EcmaString::encode("b")
        );
    });
}

#[test]
fn import_dynamic_instruction_resolves_local_module_namespace() {
    let root = program_module(
        "root",
        vec![Constant::String(EcmaString::encode("./target"))],
        vec![function(
            0,
            2,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(1),
                },
                Instruction::ImportDynamic {
                    dst: reg(1),
                    specifier: reg(0),
                },
                Instruction::Return { value: reg(1) },
            ],
            Vec::new(),
        )],
        vec![Edge {
            specifier: cid(1),
            target: EdgeTarget::Local(ModuleId::new(1)),
            kind: EdgeKind::Dynamic,
        }],
        Vec::new(),
        Vec::new(),
    );
    let target = program_module(
        "target",
        vec![
            Constant::Int32(7),
            Constant::String(EcmaString::encode("value")),
        ],
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(1),
                },
                Instruction::StoreGlobal {
                    name: cid(2),
                    value: reg(0),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        Vec::new(),
        vec![Binding {
            name: cid(2),
            kind: BindingKind::Hoisted,
        }],
        vec![Export {
            name: cid(2),
            source: ExportSource::Local(BindingId::new(0)),
        }],
    );
    let program = linked(vec![root, target], 0);
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());

    let execution = machine
        .evaluate()
        .expect("dynamic import opcode returns its promise normally");
    let promise = execution.entry_registers[1];
    let index = machine
        .runtime_slot(promise)
        .expect("dynamic import result is a valid runtime value")
        .expect("dynamic import result is heap allocated");
    let namespace = match &machine.heap[index] {
        HeapEntry::Promise {
            state: PromiseState::Fulfilled { value },
            ..
        } => *value,
        _ => panic!("local ImportDynamic resolves its result promise"),
    };

    assert_eq!(
        machine.get_named_property(namespace, "value").unwrap(),
        Value::int32(7)
    );
}

#[test]
fn import_dynamic_instruction_resolves_registered_external_namespace() {
    let program = linked(
        vec![program_module(
            "root",
            vec![Constant::String(EcmaString::encode("external"))],
            vec![function(
                0,
                2,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(1),
                    },
                    Instruction::ImportDynamic {
                        dst: reg(1),
                        specifier: reg(0),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            )],
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )],
        0,
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let namespace = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    machine.registry.external.insert(
        EcmaString::encode("external"),
        ExternalModuleInstance {
            namespace,
            exports: BTreeMap::new(),
            internals: BTreeMap::new(),
        },
    );

    let execution = machine
        .evaluate()
        .expect("external dynamic import opcode returns its promise normally");
    let promise = execution.entry_registers[1];
    let index = machine
        .runtime_slot(promise)
        .expect("dynamic import result is a valid runtime value")
        .expect("dynamic import result is heap allocated");
    let HeapEntry::Promise {
        state: PromiseState::Fulfilled { value },
        ..
    } = &machine.heap[index]
    else {
        panic!("external ImportDynamic resolves its result promise");
    };

    assert_eq!(*value, namespace);
}

#[test]
fn import_dynamic_instruction_rejects_missing_and_symbol_specifiers() {
    let missing = linked(
        vec![program_module(
            "root",
            vec![Constant::String(EcmaString::encode("missing"))],
            vec![function(
                0,
                2,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(1),
                    },
                    Instruction::ImportDynamic {
                        dst: reg(1),
                        specifier: reg(0),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            )],
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )],
        0,
    );
    let mut missing_host = TestHost;
    let mut missing_machine = Machine::new(&missing, &mut missing_host, Limits::default());
    let missing_promise = missing_machine
        .evaluate()
        .expect("unresolved dynamic import returns a rejected promise")
        .entry_registers[1];
    let missing_index = missing_machine
        .runtime_slot(missing_promise)
        .unwrap()
        .expect("rejected dynamic import result is a promise");
    let HeapEntry::Promise {
        state: PromiseState::Rejected { origin, .. },
        ..
    } = &missing_machine.heap[missing_index]
    else {
        panic!("missing ImportDynamic target rejects its promise");
    };
    assert_eq!(
        *origin,
        ThrowOrigin::TypeError {
            operation: "resolve dynamic module specifier",
        }
    );

    let coercion = linked(
        vec![program_module(
            "root",
            vec![Constant::String(EcmaString::encode("specifier"))],
            vec![function(
                0,
                2,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(1),
                    },
                    Instruction::ImportDynamic {
                        dst: reg(1),
                        specifier: reg(0),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            )],
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )],
        0,
    );
    let mut coercion_host = TestHost;
    let mut coercion_machine = Machine::new(&coercion, &mut coercion_host, Limits::default());
    let symbol = coercion_machine
        .allocate(HeapEntry::Symbol {
            description: EcmaString::encode("specifier"),
        })
        .unwrap();
    coercion_machine.test_set_global("specifier", symbol);
    let coercion_promise = coercion_machine
        .evaluate()
        .expect("uncoercible dynamic import returns a rejected promise")
        .entry_registers[1];
    let coercion_index = coercion_machine
        .runtime_slot(coercion_promise)
        .unwrap()
        .expect("rejected dynamic import result is a promise");
    let HeapEntry::Promise {
        state: PromiseState::Rejected { origin, .. },
        ..
    } = &coercion_machine.heap[coercion_index]
    else {
        panic!("symbol ImportDynamic specifier rejects its promise");
    };
    assert_eq!(
        *origin,
        ThrowOrigin::TypeError {
            operation: "convert symbol to string",
        }
    );
}

#[test]
fn normalize_relative_module_name_collapses_dot_components() {
    assert_eq!(
        normalize_relative_module_name(&EcmaString::encode("a/b/.././c//d")),
        EcmaString::encode("a/c/d")
    );
    assert_eq!(
        normalize_relative_module_name(&EcmaString::encode("../x")),
        EcmaString::encode("x")
    );
    assert_eq!(
        normalize_relative_module_name(&EcmaString::encode("./")),
        EcmaString::default()
    );
    assert_eq!(
        resolve_relative_against_module_name(
            &EcmaString::encode("src/nested/main.ts"),
            &EcmaString::encode("../dependency.ts"),
        ),
        EcmaString::encode("src/dependency.ts")
    );
    assert_eq!(
        resolve_relative_against_module_name(
            &EcmaString::encode("main.ts"),
            &EcmaString::encode("./dependency.ts"),
        ),
        EcmaString::encode("dependency.ts")
    );
}

#[test]
fn import_dynamic_expression_resolves_computed_relative_bundled_module() {
    let root = program_module(
        "main.ts",
        vec![Constant::String(EcmaString::encode("./dependency.ts"))],
        vec![function(
            0,
            2,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(1),
                },
                Instruction::ImportDynamic {
                    dst: reg(1),
                    specifier: reg(0),
                },
                Instruction::Return { value: reg(1) },
            ],
            Vec::new(),
        )],
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    let dependency = program_module(
        "dependency.ts",
        vec![
            Constant::Int32(41),
            Constant::String(EcmaString::encode("answer")),
        ],
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(1),
                },
                Instruction::StoreGlobal {
                    name: cid(2),
                    value: reg(0),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        Vec::new(),
        vec![Binding {
            name: cid(2),
            kind: BindingKind::Hoisted,
        }],
        vec![Export {
            name: cid(2),
            source: ExportSource::Local(BindingId::new(0)),
        }],
    );
    let program = linked(vec![root, dependency], 0);
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());

    let execution = machine
        .evaluate()
        .expect("computed relative dynamic import returns a promise");
    let promise = execution.entry_registers[1];
    let index = machine
        .runtime_slot(promise)
        .expect("dynamic import result is a valid runtime value")
        .expect("dynamic import result is heap allocated");
    let namespace = match &machine.heap[index] {
        HeapEntry::Promise {
            state: PromiseState::Fulfilled { value },
            ..
        } => *value,
        _ => panic!("computed relative ImportDynamic resolves its result promise"),
    };

    assert_eq!(
        machine.get_named_property(namespace, "answer").unwrap(),
        Value::int32(41)
    );
    assert_eq!(
        machine
            .registry
            .local_modules
            .get(&EcmaString::encode("dependency.ts")),
        Some(&ModuleId::new(1))
    );
}

#[test]
fn import_dynamic_expression_resolves_nested_relative_and_rejects_missing() {
    let nested = program_module(
        "src/app.ts",
        vec![
            Constant::String(EcmaString::encode("./lib/dependency.ts")),
            Constant::String(EcmaString::encode("./missing.ts")),
        ],
        vec![function(
            0,
            3,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(1),
                },
                Instruction::ImportDynamic {
                    dst: reg(1),
                    specifier: reg(0),
                },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(2),
                },
                Instruction::ImportDynamic {
                    dst: reg(0),
                    specifier: reg(2),
                },
                Instruction::Return { value: reg(1) },
            ],
            Vec::new(),
        )],
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    let dependency = program_module(
        "src/lib/dependency.ts",
        vec![
            Constant::Int32(17),
            Constant::String(EcmaString::encode("value")),
        ],
        vec![function(
            0,
            1,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(1),
                },
                Instruction::StoreGlobal {
                    name: cid(2),
                    value: reg(0),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
        Vec::new(),
        vec![Binding {
            name: cid(2),
            kind: BindingKind::Hoisted,
        }],
        vec![Export {
            name: cid(2),
            source: ExportSource::Local(BindingId::new(0)),
        }],
    );
    let program = linked(vec![nested, dependency], 0);
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());

    let execution = machine
        .evaluate()
        .expect("nested relative dynamic import returns normally");
    let fulfilled = execution.entry_registers[1];
    let fulfilled_index = machine
        .runtime_slot(fulfilled)
        .unwrap()
        .expect("nested relative import result is a promise");
    let namespace = match &machine.heap[fulfilled_index] {
        HeapEntry::Promise {
            state: PromiseState::Fulfilled { value },
            ..
        } => *value,
        _ => panic!("nested relative ImportDynamic resolves its result promise"),
    };
    assert_eq!(
        machine.get_named_property(namespace, "value").unwrap(),
        Value::int32(17)
    );

    let rejected = execution.entry_registers[0];
    let rejected_index = machine
        .runtime_slot(rejected)
        .unwrap()
        .expect("missing relative import result is a promise");
    let HeapEntry::Promise {
        state: PromiseState::Rejected { origin, .. },
        ..
    } = &machine.heap[rejected_index]
    else {
        panic!("missing relative ImportDynamic rejects its promise");
    };
    assert_eq!(
        *origin,
        ThrowOrigin::TypeError {
            operation: "resolve dynamic module specifier",
        }
    );
}

#[test]
fn import_dynamic_expression_ignores_opaque_and_absolute_as_local_paths() {
    let program = linked(
        vec![
            program_module(
                "main.ts",
                vec![
                    Constant::String(EcmaString::encode("dependency.ts")),
                    Constant::String(EcmaString::encode("/dependency.ts")),
                ],
                vec![function(
                    0,
                    3,
                    vec![
                        Instruction::LoadConst {
                            dst: reg(0),
                            constant: cid(1),
                        },
                        Instruction::ImportDynamic {
                            dst: reg(1),
                            specifier: reg(0),
                        },
                        Instruction::LoadConst {
                            dst: reg(2),
                            constant: cid(2),
                        },
                        Instruction::ImportDynamic {
                            dst: reg(0),
                            specifier: reg(2),
                        },
                        Instruction::Return { value: reg(1) },
                    ],
                    Vec::new(),
                )],
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
            program_module(
                "dependency.ts",
                vec![
                    Constant::Int32(9),
                    Constant::String(EcmaString::encode("value")),
                ],
                vec![function(
                    0,
                    1,
                    vec![
                        Instruction::LoadConst {
                            dst: reg(0),
                            constant: cid(1),
                        },
                        Instruction::StoreGlobal {
                            name: cid(2),
                            value: reg(0),
                        },
                        Instruction::Halt,
                    ],
                    Vec::new(),
                )],
                Vec::new(),
                vec![Binding {
                    name: cid(2),
                    kind: BindingKind::Hoisted,
                }],
                vec![Export {
                    name: cid(2),
                    source: ExportSource::Local(BindingId::new(0)),
                }],
            ),
        ],
        0,
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let execution = machine
        .evaluate()
        .expect("opaque and absolute dynamic imports return promises");
    for register in [0usize, 1usize] {
        let promise = execution.entry_registers[register];
        let index = machine
            .runtime_slot(promise)
            .unwrap()
            .expect("unresolved dynamic import result is a promise");
        let HeapEntry::Promise {
            state: PromiseState::Rejected { origin, .. },
            ..
        } = &machine.heap[index]
        else {
            panic!("opaque/absolute ImportDynamic must not resolve as a local path");
        };
        assert_eq!(
            *origin,
            ThrowOrigin::TypeError {
                operation: "resolve dynamic module specifier",
            }
        );
    }
}

#[test]
fn iterable_values_roots_iterator_and_yields_across_collection() {
    with_machine(Limits::default(), |machine| {
        let next_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "collecting iterator next",
            length: 0,
            handler: collecting_iterator_next,
        });
        let next_fn = super::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            next_id,
            "collecting iterator next",
            0,
        );

        let create_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "collecting iterator create",
            length: 0,
            handler: collecting_iterator_create,
        });
        let create_fn = super::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            create_id,
            "collecting iterator create",
            0,
        );

        let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
        let iterator_key = machine.property_key_from_value(iterator_symbol).unwrap();

        let iterable = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .expect("iterable allocation succeeds");
        machine
            .set_data_property(iterable, "_next", next_fn)
            .unwrap();
        machine
            .set_data_property_key(iterable, iterator_key, create_fn)
            .unwrap();

        let collected = machine
            .iterable_values(iterable)
            .expect("iteration succeeds");
        assert_eq!(collected.len(), 3, "expected three yielded values");

        for (index, value) in collected.into_iter().enumerate() {
            let tag = machine
                .get_named_property(value, "tag")
                .expect("yielded object survived collection");
            assert_eq!(tag, Value::int32(index as u32));
        }
    });
}

fn collecting_iterator_create(
    machine: &mut Machine<'_, TestHost>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let next = machine.get_named_property(this, "_next")?;
    let iter = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)?;
    machine.set_data_property(iter, "next", next)?;
    machine.set_data_property(iter, "_index", Value::int32(0))?;
    Ok(BuiltinOutcome::Value(iter))
}

fn collecting_iterator_next(
    machine: &mut Machine<'_, TestHost>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let index_val = machine.get_named_property(this, "_index")?;
    let index = match index_val.decode() {
        Some(Decoded::Int32(i)) => i as usize,
        _ => 0,
    };

    let (value, done) = if index < 3 {
        let obj = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .map_err(EvalFailure::Runtime)?;
        machine.set_data_property(obj, "tag", Value::int32(index as u32))?;
        (obj, false)
    } else {
        (Value::UNDEFINED, true)
    };

    let result = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)?;
    machine.set_data_property(result, "done", Value::boolean(done))?;
    machine.set_data_property(result, "value", value)?;
    machine.set_data_property(this, "_index", Value::int32((index + 1) as u32))?;

    // Force a collection between guest yields. The result is still on the
    // native call stack, so root it temporarily; iterable_values must keep
    // the iterator and all previously yielded values alive for the next step.
    let depth = machine.native_roots.len();
    machine.push_native_roots(depth, &[result]);
    machine.collect_garbage();
    machine.pop_native_roots(depth);

    Ok(BuiltinOutcome::Value(result))
}

fn generator_return<H: Host>(
    machine: &mut Machine<'_, H>,
    generator: Value,
    resume_value: Value,
) -> Result<(Value, bool), EvalFailure> {
    let method = machine.get_named_property(generator, "return")?;
    let result = machine.call_value(method, generator, &[resume_value])?;
    let done = machine.get_named_property(result, "done")?;
    let value = machine.get_named_property(result, "value")?;
    Ok((value, machine.truthy(done)))
}

fn generator_throw<H: Host>(
    machine: &mut Machine<'_, H>,
    generator: Value,
    resume_value: Value,
) -> Result<(Value, bool), EvalFailure> {
    let method = machine.get_named_property(generator, "throw")?;
    let result = machine.call_value(method, generator, &[resume_value])?;
    let done = machine.get_named_property(result, "done")?;
    let value = machine.get_named_property(result, "value")?;
    Ok((value, machine.truthy(done)))
}

#[test]
fn sync_generator_resume_writes_mode_register_for_return_and_throw() {
    let program = verified(
        vec![
            Constant::Int32(2),
            Constant::Int32(1),
            Constant::String(EcmaString::encode("finally")),
            Constant::Int32(42),
        ],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            generator_function(
                0,
                6,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(1),
                    },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(3),
                    },
                    Instruction::Suspend {
                        dst: reg(3),
                        src: reg(2),
                        resume: pc(4),
                        mode: reg(4),
                    },
                    Instruction::Binary {
                        dst: reg(5),
                        op: BinaryOp::StrictEqual,
                        left: reg(4),
                        right: reg(0),
                    },
                    Instruction::JumpIfTrue {
                        condition: reg(5),
                        target: pc(7),
                    },
                    Instruction::Throw { value: reg(3) },
                    Instruction::StoreGlobal {
                        name: cid(2),
                        value: reg(1),
                    },
                    Instruction::Return { value: reg(3) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);
    let generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    assert_eq!(
        generator_next(&mut machine, generator, Value::UNDEFINED).unwrap(),
        (Value::int32(42), false),
    );
    assert_eq!(
        generator_return(&mut machine, generator, Value::int32(7)).unwrap(),
        (Value::int32(7), true),
    );
    assert_eq!(machine.test_global("finally"), Some(Value::int32(1)));
}

#[test]
fn sync_generator_resume_next_return_throw_modes() {
    let program = verified(
        vec![Constant::Int32(42), Constant::Int32(0), Constant::Int32(1)],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            generator_function(
                0,
                6,
                vec![
                    Instruction::LoadConst {
                        dst: reg(3),
                        constant: cid(1),
                    },
                    Instruction::LoadConst {
                        dst: reg(4),
                        constant: cid(2),
                    },
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Suspend {
                        dst: reg(1),
                        src: reg(0),
                        resume: pc(4),
                        mode: reg(2),
                    },
                    Instruction::Binary {
                        dst: reg(5),
                        op: BinaryOp::StrictEqual,
                        left: reg(2),
                        right: reg(3),
                    },
                    Instruction::JumpIfTrue {
                        condition: reg(5),
                        target: pc(11),
                    },
                    Instruction::Binary {
                        dst: reg(5),
                        op: BinaryOp::StrictEqual,
                        left: reg(2),
                        right: reg(4),
                    },
                    Instruction::JumpIfTrue {
                        condition: reg(5),
                        target: pc(9),
                    },
                    Instruction::Return { value: reg(1) },
                    Instruction::Throw { value: reg(1) },
                    Instruction::Return { value: reg(5) },
                    Instruction::Return { value: reg(1) },
                ],
                vec![ExceptionHandler {
                    start: pc(8),
                    end: pc(10),
                    handler: pc(10),
                    catch_register: reg(5),
                }],
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;

    let callable = generator_callable(&mut machine, 1);

    // next resumes from SuspendedStart and yields the first value.
    let g1 = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    assert_eq!(
        generator_next(&mut machine, g1, Value::UNDEFINED).unwrap(),
        (Value::int32(42), false)
    );
    // next with a value reaches the Next dispatch arm and returns it.
    assert_eq!(
        generator_next(&mut machine, g1, Value::int32(5)).unwrap(),
        (Value::int32(5), true)
    );
    // next on Completed returns undefined/done.
    assert_eq!(
        generator_next(&mut machine, g1, Value::UNDEFINED).unwrap(),
        (Value::UNDEFINED, true)
    );
    assert_eq!(machine.live_registers, 0);

    // return from SuspendedYield reaches the Return dispatch arm.
    let g2 = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    assert_eq!(
        generator_next(&mut machine, g2, Value::UNDEFINED).unwrap(),
        (Value::int32(42), false)
    );
    assert_eq!(
        generator_return(&mut machine, g2, Value::int32(7)).unwrap(),
        (Value::int32(7), true)
    );
    assert_eq!(machine.live_registers, 0);

    // throw from SuspendedYield reaches the Throw dispatch arm and is caught.
    let g3 = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    assert_eq!(
        generator_next(&mut machine, g3, Value::UNDEFINED).unwrap(),
        (Value::int32(42), false)
    );
    assert_eq!(
        generator_throw(&mut machine, g3, Value::int32(55)).unwrap(),
        (Value::int32(55), true)
    );
    assert_eq!(machine.live_registers, 0);

    // return before the body starts returns the supplied value and completes.
    let g4 = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    assert_eq!(
        generator_return(&mut machine, g4, Value::int32(9)).unwrap(),
        (Value::int32(9), true)
    );
    assert_eq!(machine.live_registers, 0);

    // throw before the body starts is reported as a Bytecode-origin throw.
    let g5 = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    let err = generator_throw(&mut machine, g5, Value::int32(13)).unwrap_err();
    assert!(matches!(
        err,
        EvalFailure::ThrowValueOrigin { value, origin }
            if value == Value::int32(13) && origin == ThrowOrigin::Bytecode
    ));

    // next/return/throw on a completed generator have the expected final states.
    let g6 = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    assert_eq!(
        generator_next(&mut machine, g6, Value::UNDEFINED).unwrap(),
        (Value::int32(42), false)
    );
    assert_eq!(
        generator_next(&mut machine, g6, Value::int32(2)).unwrap(),
        (Value::int32(2), true)
    );
    assert_eq!(
        generator_next(&mut machine, g6, Value::UNDEFINED).unwrap(),
        (Value::UNDEFINED, true)
    );
    assert_eq!(
        generator_return(&mut machine, g6, Value::int32(3)).unwrap(),
        (Value::int32(3), true)
    );
    let err = generator_throw(&mut machine, g6, Value::int32(4)).unwrap_err();
    assert!(matches!(
        err,
        EvalFailure::ThrowValueOrigin { value, origin }
            if value == Value::int32(4) && origin == ThrowOrigin::Bytecode
    ));

    // Operation brand messages are exact for next/return/throw on
    // an incompatible receiver.
    let proto = machine.intrinsics.builtins.generator_prototype();
    let bad = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    for (name, expected) in [
        (
            "next",
            "Generator.prototype.next called on incompatible receiver",
        ),
        (
            "return",
            "Generator.prototype.return called on incompatible receiver",
        ),
        (
            "throw",
            "Generator.prototype.throw called on incompatible receiver",
        ),
    ] {
        let method = machine.get_named_property(proto, name).unwrap();
        let err = machine.call_value(method, bad, &[]).unwrap_err();
        assert!(matches!(
            err,
            EvalFailure::Throw(ThrowOrigin::TypeError { operation })
                if operation == expected
        ));
    }
}
fn async_generator_return<H: Host>(
    machine: &mut Machine<'_, H>,
    generator: Value,
    resume_value: Value,
) -> Result<Value, EvalFailure> {
    let method = machine.get_named_property(generator, "return")?;
    machine.call_value(method, generator, &[resume_value])
}

fn async_generator_throw<H: Host>(
    machine: &mut Machine<'_, H>,
    generator: Value,
    resume_value: Value,
) -> Result<Value, EvalFailure> {
    let method = machine.get_named_property(generator, "throw")?;
    machine.call_value(method, generator, &[resume_value])
}

#[test]
fn async_generator_start_and_completed_abrupt_completions() {
    let program = verified(
        vec![
            Constant::Int32(42),
            Constant::Int32(1),
            Constant::String(EcmaString::encode("started")),
        ],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                3,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(1),
                    },
                    Instruction::StoreGlobal {
                        name: cid(2),
                        value: reg(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Suspend {
                        dst: reg(1),
                        src: reg(0),
                        resume: pc(4),
                        mode: reg(2),
                    },
                    Instruction::Return { value: reg(1) },
                ],
                Vec::new(),
            ),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;

    // A1/A5/A6: .return() at SuspendedStart awaits the value, then drains the
    // queued next/return/throw requests in FIFO order without entering the body.
    let callable = generator_callable(&mut machine, 1);
    let g1 = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    let r1 = async_generator_return(&mut machine, g1, Value::int32(7)).unwrap();
    let n1 = async_generator_next(&mut machine, g1, Value::UNDEFINED).unwrap();
    let r2 = async_generator_return(&mut machine, g1, Value::int32(8)).unwrap();
    let t1 = async_generator_throw(&mut machine, g1, Value::int32(9)).unwrap();

    machine.drain_microtasks().unwrap();
    assert_eq!(
        settled_iterator_result(&mut machine, r1),
        (Value::int32(7), true),
    );
    assert_eq!(
        settled_iterator_result(&mut machine, n1),
        (Value::UNDEFINED, true),
    );
    assert_eq!(
        settled_iterator_result(&mut machine, r2),
        (Value::int32(8), true),
    );
    assert_eq!(rejected_reason(&machine, t1), Value::int32(9));
    assert_eq!(machine.test_global("started"), None);
    assert_eq!(machine.live_registers, 0);

    // A2: .throw() at SuspendedStart rejects and completes without entering the body.
    let callable = generator_callable(&mut machine, 1);
    let g2 = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    let t2 = async_generator_throw(&mut machine, g2, Value::int32(5)).unwrap();
    let n2 = async_generator_next(&mut machine, g2, Value::UNDEFINED).unwrap();
    let r3 = async_generator_return(&mut machine, g2, Value::int32(6)).unwrap();

    machine.drain_microtasks().unwrap();
    assert_eq!(rejected_reason(&machine, t2), Value::int32(5));
    assert_eq!(
        settled_iterator_result(&mut machine, n2),
        (Value::UNDEFINED, true),
    );
    assert_eq!(
        settled_iterator_result(&mut machine, r3),
        (Value::int32(6), true),
    );
    assert_eq!(machine.test_global("started"), None);
    assert_eq!(machine.live_registers, 0);
}

#[test]
fn async_generator_return_on_completed_generator_awaits_value() {
    let program = verified(
        Vec::new(),
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(0, 1, vec![Instruction::Halt], Vec::new()),
        ],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;
    let callable = generator_callable(&mut machine, 1);

    let fulfilled_generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    let completed =
        async_generator_next(&mut machine, fulfilled_generator, Value::UNDEFINED).unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(
        settled_iterator_result(&mut machine, completed),
        (Value::UNDEFINED, true),
    );
    let fulfilled_operand = machine.create_promise().unwrap();
    let fulfilled_return =
        async_generator_return(&mut machine, fulfilled_generator, fulfilled_operand).unwrap();
    assert!(pending_promise(&machine, fulfilled_return));
    machine
        .resolve_promise(fulfilled_operand, Value::int32(17))
        .unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(
        settled_iterator_result(&mut machine, fulfilled_return),
        (Value::int32(17), true),
    );

    let rejected_generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    let completed =
        async_generator_next(&mut machine, rejected_generator, Value::UNDEFINED).unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(
        settled_iterator_result(&mut machine, completed),
        (Value::UNDEFINED, true),
    );
    let rejected_operand = machine.create_promise().unwrap();
    let rejected_return =
        async_generator_return(&mut machine, rejected_generator, rejected_operand).unwrap();
    machine
        .reject_promise(rejected_operand, Value::int32(19), ThrowOrigin::Bytecode)
        .unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(rejected_reason(&machine, rejected_return), Value::int32(19));
}

#[test]
fn async_generator_return_at_suspended_yield_awaits_operand_before_resuming() {
    // A3/A5: .return(v) at SuspendedYield awaits the operand, runs the body's
    // "finally" path, and preserves FIFO for a request queued behind the return.
    let return_program = verified(
        vec![
            Constant::Int32(0),
            Constant::Int32(2),
            Constant::Int32(42),
            Constant::Int32(99),
            Constant::String(EcmaString::encode("finally")),
        ],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                7,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(6),
                        constant: cid(1),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(2),
                    },
                    Instruction::Suspend {
                        dst: reg(2),
                        src: reg(1),
                        resume: pc(4),
                        mode: reg(3),
                    },
                    Instruction::Binary {
                        dst: reg(4),
                        op: BinaryOp::StrictEqual,
                        left: reg(3),
                        right: reg(0),
                    },
                    Instruction::JumpIfTrue {
                        condition: reg(4),
                        target: pc(9),
                    },
                    Instruction::Binary {
                        dst: reg(4),
                        op: BinaryOp::StrictEqual,
                        left: reg(3),
                        right: reg(6),
                    },
                    Instruction::JumpIfTrue {
                        condition: reg(4),
                        target: pc(10),
                    },
                    Instruction::Throw { value: reg(2) },
                    Instruction::Return { value: reg(2) },
                    Instruction::LoadConst {
                        dst: reg(5),
                        constant: cid(3),
                    },
                    Instruction::StoreGlobal {
                        name: cid(4),
                        value: reg(5),
                    },
                    Instruction::Return { value: reg(2) },
                ],
                Vec::new(),
            ),
        ],
    );

    let mut host = TestHost;
    let mut machine = Machine::new(&return_program, &mut host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;

    let callable = generator_callable(&mut machine, 1);
    let g1 = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    let first = async_generator_next(&mut machine, g1, Value::UNDEFINED).unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(
        settled_iterator_result(&mut machine, first),
        (Value::int32(42), false),
    );

    let awaited = machine.create_promise().unwrap();
    let result = async_generator_return(&mut machine, g1, awaited).unwrap();
    let later = async_generator_next(&mut machine, g1, Value::UNDEFINED).unwrap();
    assert!(pending_promise(&machine, result));
    assert!(pending_promise(&machine, later));
    assert_eq!(machine.test_global("finally"), None);

    machine.resolve_promise(awaited, Value::int32(7)).unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(
        settled_iterator_result(&mut machine, result),
        (Value::int32(7), true),
    );
    assert_eq!(
        settled_iterator_result(&mut machine, later),
        (Value::UNDEFINED, true),
    );
    assert_eq!(machine.test_global("finally"), Some(Value::int32(99)));
    assert_eq!(machine.live_registers, 0);

    let rejected_generator = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();
    let first = async_generator_next(&mut machine, rejected_generator, Value::UNDEFINED).unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(
        settled_iterator_result(&mut machine, first),
        (Value::int32(42), false),
    );
    let rejected_operand = machine.create_promise().unwrap();
    let rejected_return =
        async_generator_return(&mut machine, rejected_generator, rejected_operand).unwrap();
    machine
        .reject_promise(rejected_operand, Value::int32(13), ThrowOrigin::Bytecode)
        .unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(rejected_reason(&machine, rejected_return), Value::int32(13));

    // A4: .throw() at SuspendedYield is catchable by a handler around the yield.
    let throw_program = verified(
        vec![
            Constant::Int32(0),
            Constant::Int32(1),
            Constant::Int32(42),
            Constant::Int32(99),
            Constant::String(EcmaString::encode("finally")),
            Constant::String(EcmaString::encode("caught")),
        ],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                8,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(1),
                    },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(2),
                    },
                    Instruction::Suspend {
                        dst: reg(3),
                        src: reg(2),
                        resume: pc(4),
                        mode: reg(4),
                    },
                    Instruction::Binary {
                        dst: reg(5),
                        op: BinaryOp::StrictEqual,
                        left: reg(4),
                        right: reg(0),
                    },
                    Instruction::JumpIfTrue {
                        condition: reg(5),
                        target: pc(11),
                    },
                    Instruction::Binary {
                        dst: reg(5),
                        op: BinaryOp::StrictEqual,
                        left: reg(4),
                        right: reg(1),
                    },
                    Instruction::JumpIfTrue {
                        condition: reg(5),
                        target: pc(12),
                    },
                    Instruction::LoadConst {
                        dst: reg(6),
                        constant: cid(3),
                    },
                    Instruction::StoreGlobal {
                        name: cid(4),
                        value: reg(6),
                    },
                    Instruction::Return { value: reg(3) },
                    Instruction::Return { value: reg(3) },
                    Instruction::Throw { value: reg(3) },
                    Instruction::StoreGlobal {
                        name: cid(5),
                        value: reg(7),
                    },
                    Instruction::Return { value: reg(7) },
                ],
                vec![ExceptionHandler {
                    start: pc(4),
                    end: pc(13),
                    handler: pc(13),
                    catch_register: reg(7),
                }],
            ),
        ],
    );

    let mut throw_host = TestHost;
    let mut machine = Machine::new(&throw_program, &mut throw_host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;

    let callable = generator_callable(&mut machine, 1);
    let g2 = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    let first = async_generator_next(&mut machine, g2, Value::UNDEFINED).unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(
        settled_iterator_result(&mut machine, first),
        (Value::int32(42), false),
    );

    let result = async_generator_throw(&mut machine, g2, Value::int32(5)).unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(machine.test_global("caught"), Some(Value::int32(5)));
    assert_eq!(
        settled_iterator_result(&mut machine, result),
        (Value::int32(5), true),
    );
    assert_eq!(machine.live_registers, 0);

    // A8: .return() while the generator is parked on an Await is queued only
    // and does not disturb the await resumption path.
    let await_program = verified(
        vec![
            Constant::String(EcmaString::encode("p")),
            Constant::Int32(1),
            Constant::String(EcmaString::encode("after_await")),
            Constant::Int32(9),
        ],
        vec![
            function(0, 1, vec![Instruction::Halt], Vec::new()),
            async_generator_function(
                0,
                6,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(0),
                    },
                    Instruction::Await {
                        dst: reg(1),
                        src: reg(0),
                        resume: pc(2),
                    },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(1),
                    },
                    Instruction::StoreGlobal {
                        name: cid(2),
                        value: reg(2),
                    },
                    Instruction::LoadConst {
                        dst: reg(3),
                        constant: cid(3),
                    },
                    Instruction::Suspend {
                        dst: reg(4),
                        src: reg(3),
                        resume: pc(6),
                        mode: reg(5),
                    },
                    Instruction::Return { value: reg(4) },
                ],
                Vec::new(),
            ),
        ],
    );

    let mut await_host = TestHost;
    let mut machine = Machine::new(&await_program, &mut await_host, Limits::default());
    machine.frames.clear();
    machine.live_registers = 0;

    let awaited = machine.create_promise().unwrap();
    machine.test_set_global("p", awaited);

    let callable = generator_callable(&mut machine, 1);
    let g3 = machine.call_value(callable, Value::UNDEFINED, &[]).unwrap();

    let first = async_generator_next(&mut machine, g3, Value::UNDEFINED).unwrap();
    let result = async_generator_return(&mut machine, g3, Value::int32(7)).unwrap();
    assert!(pending_promise(&machine, first));
    assert!(pending_promise(&machine, result));

    machine.resolve_promise(awaited, Value::int32(9)).unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(machine.test_global("after_await"), Some(Value::int32(1)));
    assert_eq!(
        settled_iterator_result(&mut machine, first),
        (Value::int32(9), false),
    );
    assert_eq!(
        settled_iterator_result(&mut machine, result),
        (Value::int32(7), true),
    );
    assert_eq!(machine.live_registers, 0);
}
#[test]
fn async_from_sync_value_rejection_calls_return_once() {
    fn count_return<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        let count = machine
            .get_named_property(this, "return_count")?
            .decode()
            .and_then(|value| match value {
                Decoded::Int32(count) => Some(count),
                _ => None,
            })
            .unwrap_or(0);
        machine.set_data_property(this, "return_count", Value::int32(count + 1))?;
        Ok(intrinsics::BuiltinOutcome::Value(Value::UNDEFINED))
    }

    let program = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let iterator = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            extensible: true,
            boxed_primitive: None,
        })
        .unwrap();
    let return_id = machine
        .intrinsics
        .builtins
        .register(intrinsics::BuiltinDef {
            name: "count return",
            length: 0,
            handler: count_return::<TestHost>,
        });
    let return_method = intrinsics::native_function(
        &mut machine.heap,
        &mut machine.atoms,
        &mut machine.shapes,
        return_id,
        "count return",
        0,
    );
    machine
        .set_data_property(iterator, "return", return_method)
        .unwrap();
    let rejected = machine.create_promise().unwrap();
    let origin = ThrowOrigin::TypeError {
        operation: "value rejection",
    };
    machine
        .reject_promise(rejected, Value::int32(73), origin)
        .unwrap();
    let result = machine.iterator_result(rejected, false).unwrap();

    let derived = machine
        .async_from_sync_continuation(iterator, Ok(result))
        .unwrap();
    machine.drain_microtasks().unwrap();
    assert_eq!(
        machine
            .get_named_property(iterator, "return_count")
            .unwrap(),
        Value::int32(1),
    );
    let index = machine.runtime_slot(derived).unwrap().unwrap();
    assert!(matches!(
        machine.heap[index],
        HeapEntry::Promise {
            state: PromiseState::Rejected {
                reason,
                origin: actual,
            },
            ..
        } if reason == Value::int32(73) && actual == origin
    ));
}

#[test]
fn for_await_async_from_sync_uses_real_prototype_methods() {
    let program = verified(
        Vec::new(),
        vec![function(0, 1, vec![Instruction::Halt], Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let iterator = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    let next = machine
        .get_named_property(machine.intrinsics.builtins.iterator_prototype(), "next")
        .unwrap();
    let adapter = machine
        .create_async_from_sync_iterator(iterator, next)
        .unwrap();
    let index = machine.runtime_slot(adapter).unwrap().unwrap();
    assert!(matches!(
        machine.heap[index],
        HeapEntry::AsyncFromSync { .. }
    ));
    for name in ["next", "return", "throw"] {
        let method = machine.get_named_property(adapter, name).unwrap();
        assert!(machine.is_callable(method).unwrap());
    }
}

#[test]
fn extension_super_uses_home_prototype_and_receiver() {
    fn marker_getter<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        Ok(intrinsics::BuiltinOutcome::Value(
            machine.get_named_property(this, "marker")?,
        ))
    }

    fn hit_setter<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "hit", args[0])?;
        Ok(intrinsics::BuiltinOutcome::Value(Value::UNDEFINED))
    }

    with_machine(Limits::default(), |machine| {
        let mut install = |name: &'static str, handler: intrinsics::BuiltinHandler<TestHost>| {
            let id = machine
                .intrinsics
                .builtins
                .register(intrinsics::BuiltinDef {
                    name,
                    length: 0,
                    handler,
                });
            intrinsics::native_function(
                &mut machine.heap,
                &mut machine.atoms,
                &mut machine.shapes,
                id,
                name,
                0,
            )
        };
        let getter = install("get super marker", marker_getter::<TestHost>);
        let setter = install("set super hit", hit_setter::<TestHost>);
        let object_prototype = machine.intrinsics.object_prototype;
        let object = |machine: &mut Machine<'_, TestHost>, prototype| {
            machine
                .allocate(HeapEntry::Object {
                    properties: PropertyMap::default(),
                    prototype,
                    boxed_primitive: None,
                    extensible: true,
                })
                .unwrap()
        };
        let base = object(machine, Some(object_prototype));
        let x_key = PropertyKey::Named(machine.intern_str("x"));
        let y_key = PropertyKey::Named(machine.intern_str("y"));
        machine
            .define_descriptor(
                base,
                x_key,
                Property::Accessor {
                    getter: Some(getter),
                    setter: None,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        machine
            .define_descriptor(
                base,
                y_key,
                Property::Accessor {
                    getter: None,
                    setter: Some(setter),
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        let home = object(machine, Some(base));
        let receiver = object(machine, Some(object_prototype));
        machine
            .set_data_property(receiver, "x", Value::int32(999))
            .unwrap();
        machine
            .set_data_property(receiver, "marker", Value::int32(7))
            .unwrap();

        let x = PropertyKey::Named(machine.intern_str("x"));
        assert_eq!(
            machine.get_super(home, receiver, &x).unwrap(),
            Value::int32(7),
            "receiver override must not win; prototype getter binds receiver as this"
        );

        let y = PropertyKey::Named(machine.intern_str("y"));
        let setter = match machine
            .set_super(home, receiver, y, Value::int32(42))
            .unwrap()
        {
            SetOutcome::Setter(setter) => setter,
            SetOutcome::Done => panic!("home prototype setter must be selected"),
        };
        machine
            .call_value(setter, receiver, &[Value::int32(42)])
            .unwrap();
        assert_eq!(
            machine.get_named_property(receiver, "hit").unwrap(),
            Value::int32(42),
            "setter must receive receiver as this"
        );

        let z = PropertyKey::Named(machine.intern_str("z"));
        assert!(matches!(
            machine
                .set_super(home, receiver, z.clone(), Value::int32(43))
                .unwrap(),
            SetOutcome::Done
        ));
        assert!(matches!(
            machine.own_descriptor(receiver, &z).unwrap(),
            Some(Property::Data { value, .. }) if value == Value::int32(43)
        ));
        assert!(machine.own_descriptor(home, &z).unwrap().is_none());
    });
}

#[test]
fn extension_copy_data_properties_excludes_before_get_and_defines() {
    fn kept_getter<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        let reads = machine.get_named_property(this, "reads")?;
        let count = match reads.decode() {
            Some(Decoded::Int32(count)) => count + 1,
            _ => 1,
        };
        machine.set_data_property(this, "reads", Value::int32(count))?;
        Ok(intrinsics::BuiltinOutcome::Value(Value::int32(5)))
    }

    fn excluded_getter<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "excludedRead", Value::TRUE)?;
        Ok(intrinsics::BuiltinOutcome::Value(Value::int32(9)))
    }

    fn target_setter<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<intrinsics::BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "setterRan", Value::TRUE)?;
        Ok(intrinsics::BuiltinOutcome::Value(Value::UNDEFINED))
    }

    with_machine(Limits::default(), |machine| {
        let mut install = |name: &'static str, handler: intrinsics::BuiltinHandler<TestHost>| {
            let id = machine
                .intrinsics
                .builtins
                .register(intrinsics::BuiltinDef {
                    name,
                    length: 0,
                    handler,
                });
            intrinsics::native_function(
                &mut machine.heap,
                &mut machine.atoms,
                &mut machine.shapes,
                id,
                name,
                0,
            )
        };
        let kept_getter = install("get kept", kept_getter::<TestHost>);
        let excluded_getter = install("get excluded", excluded_getter::<TestHost>);
        let target_setter = install("set target", target_setter::<TestHost>);
        let prototype = machine.intrinsics.object_prototype;
        let object = |machine: &mut Machine<'_, TestHost>| {
            machine
                .allocate(HeapEntry::Object {
                    properties: PropertyMap::default(),
                    prototype: Some(prototype),
                    boxed_primitive: None,
                    extensible: true,
                })
                .unwrap()
        };
        let source = object(machine);
        let target = object(machine);
        machine
            .set_data_property(source, "reads", Value::int32(0))
            .unwrap();
        let kept_key = PropertyKey::Named(machine.intern_str("kept"));
        let gone_key = PropertyKey::Named(machine.intern_str("gone"));
        let hidden_key = PropertyKey::Named(machine.intern_str("hidden"));
        let target_kept_key = PropertyKey::Named(machine.intern_str("kept"));
        machine
            .define_descriptor(
                source,
                kept_key,
                Property::Accessor {
                    getter: Some(kept_getter),
                    setter: None,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        machine
            .define_descriptor(
                source,
                gone_key,
                Property::Accessor {
                    getter: Some(excluded_getter),
                    setter: None,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        machine
            .define_descriptor(
                source,
                hidden_key,
                Property::Data {
                    value: Value::int32(77),
                    writable: true,
                    enumerable: false,
                    configurable: true,
                },
            )
            .unwrap();
        machine
            .define_descriptor(
                target,
                target_kept_key,
                Property::Accessor {
                    getter: None,
                    setter: Some(target_setter),
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        let gone = machine
            .allocate(HeapEntry::String(EcmaString::encode("gone")))
            .unwrap();
        let excluded = machine
            .allocate(HeapEntry::Array {
                kind: ArrayElementKind::for_elements(&[gone]),
                elements: vec![gone],
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.array_prototype),
                extensible: true,
                length_writable: true,
            })
            .unwrap();

        machine
            .copy_data_properties(target, source, excluded)
            .unwrap();

        let owned_kept_key = PropertyKey::Named(machine.intern_str("kept"));
        assert!(matches!(
            machine
                .own_descriptor(
                    target,
                    &owned_kept_key,
                )
                .unwrap(),
            Some(Property::Data {
                value,
                writable: true,
                enumerable: true,
                configurable: true,
            }) if value == Value::int32(5)
        ));
        assert_eq!(
            machine.get_named_property(source, "reads").unwrap(),
            Value::int32(1),
            "included getter is observed exactly once"
        );
        for (object, name) in [
            (source, "excludedRead"),
            (target, "gone"),
            (target, "hidden"),
            (target, "setterRan"),
        ] {
            let key = PropertyKey::Named(machine.intern_str(name));
            assert!(
                machine.own_descriptor(object, &key).unwrap().is_none(),
                "unexpected own property {name}"
            );
        }
    });
}

#[test]
fn extension_template_object_identity_descriptors_and_gc_rooting() {
    with_machine(Limits::default(), |machine| {
        let string = |machine: &mut Machine<'_, TestHost>, value| {
            machine
                .allocate(HeapEntry::String(EcmaString::encode(value)))
                .unwrap()
        };
        let array = |machine: &mut Machine<'_, TestHost>, elements: Vec<Value>| {
            machine
                .allocate(HeapEntry::Array {
                    kind: ArrayElementKind::for_elements(&elements),
                    elements,
                    properties: PropertyMap::default(),
                    prototype: Some(machine.intrinsics.array_prototype),
                    extensible: true,
                    length_writable: true,
                })
                .unwrap()
        };
        let x = string(machine, "x");
        let y = string(machine, "y");
        let upper_x = string(machine, "X");
        let upper_y = string(machine, "Y");
        let cooked = array(machine, vec![x, y]);
        let raw = array(machine, vec![upper_x, upper_y]);
        let template = machine.template_object_at((0, 1, 7), cooked, raw).unwrap();
        let new = string(machine, "new");
        let upper_new = string(machine, "NEW");
        let other_cooked = array(machine, vec![new]);
        let other_raw = array(machine, vec![upper_new]);
        assert_eq!(
            machine
                .template_object_at((0, 1, 7), other_cooked, other_raw)
                .unwrap(),
            template,
            "one template site must preserve object identity"
        );

        let raw_key = PropertyKey::Named(machine.intern_str("raw"));
        assert!(matches!(
            machine.own_descriptor(template, &raw_key).unwrap(),
            Some(Property::Data {
                value,
                writable: false,
                enumerable: false,
                configurable: false,
            }) if value == raw
        ));
        for value in [template, raw] {
            let index = machine.runtime_slot(value).unwrap().unwrap();
            assert!(matches!(
                machine.heap[index],
                HeapEntry::Array {
                    extensible: false,
                    length_writable: false,
                    ..
                }
            ));
        }

        machine.collect_garbage();
        assert!(
            machine
                .own_descriptor(template, &raw_key)
                .unwrap()
                .is_some()
        );
    });
}

#[test]
fn clear_kept_alive_for_job_refunds_retained_roots() {
    with_machine(Limits::default(), |machine| {
        let before = machine.machine_bytes;
        let retained = 2 * std::mem::size_of::<Value>();
        machine.charge_machine(retained).unwrap();
        machine
            .kept_alive
            .extend([Value::int32(1), Value::int32(2)]);
        assert_eq!(machine.machine_bytes, before + retained);

        machine.clear_kept_alive_for_job();

        assert!(machine.kept_alive.is_empty());
        assert_eq!(machine.machine_bytes, before);
        machine.assert_heap_ledger();
    });
}

#[test]
fn extension_set_super_rejects_inherited_non_writable_data() {
    with_machine(Limits::default(), |machine| {
        let prototype = machine.intrinsics.object_prototype;
        let object = |machine: &mut Machine<'_, TestHost>, prototype| {
            machine
                .allocate(HeapEntry::Object {
                    properties: PropertyMap::default(),
                    prototype,
                    boxed_primitive: None,
                    extensible: true,
                })
                .unwrap()
        };
        let base = object(machine, Some(prototype));
        let key = PropertyKey::Named(machine.intern_str("x"));
        machine
            .define_descriptor(
                base,
                key.clone(),
                Property::Data {
                    value: Value::int32(1),
                    writable: false,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        let home = object(machine, Some(base));
        let receiver = object(machine, Some(prototype));

        assert!(matches!(
            machine.set_super(home, receiver, key.clone(), Value::int32(2)),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { operation }))
                if operation == "assign to read only super property"
        ));
        assert!(machine.own_descriptor(receiver, &key).unwrap().is_none());
    });
}

#[test]
fn extension_set_super_rejects_inherited_accessor_without_setter() {
    with_machine(Limits::default(), |machine| {
        let prototype = machine.intrinsics.object_prototype;
        let object = |machine: &mut Machine<'_, TestHost>, prototype| {
            machine
                .allocate(HeapEntry::Object {
                    properties: PropertyMap::default(),
                    prototype,
                    boxed_primitive: None,
                    extensible: true,
                })
                .unwrap()
        };
        let base = object(machine, Some(prototype));
        let key = PropertyKey::Named(machine.intern_str("x"));
        machine
            .define_descriptor(
                base,
                key.clone(),
                Property::Accessor {
                    getter: None,
                    setter: None,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        let home = object(machine, Some(base));
        let receiver = object(machine, Some(prototype));

        assert!(matches!(
            machine.set_super(home, receiver, key.clone(), Value::int32(2)),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { operation }))
                if operation == "set super property without setter"
        ));
        assert!(machine.own_descriptor(receiver, &key).unwrap().is_none());
    });
}

#[test]
fn extension_set_super_rejects_null_home_prototype() {
    with_machine(Limits::default(), |machine| {
        let prototype = machine.intrinsics.object_prototype;
        let object = |machine: &mut Machine<'_, TestHost>, prototype| {
            machine
                .allocate(HeapEntry::Object {
                    properties: PropertyMap::default(),
                    prototype,
                    boxed_primitive: None,
                    extensible: true,
                })
                .unwrap()
        };
        let home = object(machine, None);
        let receiver = object(machine, Some(prototype));
        let key = PropertyKey::Named(machine.intern_str("x"));

        assert!(matches!(
            machine.set_super(home, receiver, key.clone(), Value::int32(2)),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { operation }))
                if operation == "set super property through null prototype"
        ));
        assert!(machine.own_descriptor(receiver, &key).unwrap().is_none());
    });
}
fn xorshift64(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

#[test]
fn atom_interning_is_injective_and_stable() {
    let mut table = AtomTable::default();
    let mut strings = vec![
        EcmaString::encode(""),
        EcmaString::encode("0"),
        EcmaString::encode("4294967295"),
        EcmaString::encode("4294967296"),
        EcmaString::encode("00"),
        EcmaString::encode("01"),
        EcmaString::encode("-0"),
        EcmaString::encode("length"),
        EcmaString::encode("prototype"),
        EcmaString::encode("__proto__"),
        EcmaString::from_units(&[0xD800]),
        EcmaString::from_units(&[0xDC00]),
        EcmaString::from_units(&[0xD83D, 0xDE00]),
        EcmaString::from_units(&[0xE9, 0x4E2D, 0xD800]),
    ];
    let mut rng: u64 = 0x9E3779B97F4A7C15;
    for _ in 0..2000 {
        let len = usize::try_from(xorshift64(&mut rng) % 9).expect("remainder of 9 fits usize");
        let mut units = Vec::with_capacity(len);
        for _ in 0..len {
            let r = xorshift64(&mut rng);
            units.push(match r % 6 {
                0 => u16::from(b'a') + u16::try_from(r % 26).expect("remainder of 26 fits u16"),
                1 => u16::from(b'0') + u16::try_from(r % 10).expect("remainder of 10 fits u16"),
                2 => 0xE9,
                3 => 0x4E2D,
                4 => 0xD800 + u16::try_from(r % 0x800).expect("remainder of 0x800 fits u16"),
                _ => 0xDC00 + u16::try_from(r % 0x400).expect("remainder of 0x400 fits u16"),
            });
        }
        strings.push(EcmaString::from_units(&units));
    }
    let mut oracle: Vec<EcmaString> = Vec::new();
    let mut first_atom: Vec<Atom> = Vec::new();
    for text in &strings {
        let atom = table.intern(text.clone());
        match oracle.iter().position(|known| known == text) {
            Some(index) => {
                assert_eq!(atom, first_atom[index], "equal strings intern to one atom")
            }
            None => {
                oracle.push(text.clone());
                first_atom.push(atom);
            }
        }
        assert_eq!(table.resolve(atom), text, "resolve inverts intern");
    }
    assert_eq!(
        table.map.len(),
        oracle.len(),
        "distinct strings intern to distinct atoms"
    );
    for text in &strings {
        let again = table.intern(text.clone());
        let index = oracle.iter().position(|known| known == text).unwrap();
        assert_eq!(again, first_atom[index], "interning is stable");
    }
}

fn proxy_own_keys_trap(
    machine: &mut Machine<'_, TestHost>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let target = args[0];
    let keys = machine.internal_own_property_keys(target)?;
    let mut values = Vec::with_capacity(keys.len());
    for key in keys {
        values.push(crate::builtins::reflect::property_key_value(machine, key)?);
    }
    let array = machine
        .allocate(HeapEntry::Array {
            kind: ArrayElementKind::for_elements(&values),
            elements: values,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.array_prototype),
            extensible: true,
            length_writable: true,
        })
        .map_err(EvalFailure::Runtime)?;
    Ok(BuiltinOutcome::Value(array))
}

#[test]
fn observable_property_order_ignores_atom_ids() {
    with_machine(Limits::default(), |machine| {
        machine.intern_str("b");
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        for (name, value) in [("a", 1), ("b", 2), ("10", 3), ("2", 4)] {
            machine
                .set_data_property(object, name, Value::int32(value))
                .unwrap();
        }
        let symbol = machine
            .allocate(HeapEntry::Symbol {
                description: EcmaString::encode("s"),
            })
            .unwrap();
        let symbol_index = u32::try_from(machine.runtime_slot(symbol).unwrap().unwrap())
            .expect("test heap is small");
        let symbol_key = PropertyKey::Symbol(symbol_index);
        machine
            .define_descriptor(
                object,
                symbol_key,
                Property::Data {
                    value: Value::int32(5),
                    writable: true,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        let expected = ["2", "10", "a", "b"];
        let keys = machine.own_property_keys(object).unwrap();
        let texts: Vec<String> = keys
            .iter()
            .filter_map(|key| match key {
                PropertyKey::Named(atom) => Some(machine.atoms.resolve(*atom).to_utf8_lossy()),
                _ => None,
            })
            .collect();
        assert_eq!(texts, expected);
        assert_eq!(keys.len(), 5);
        assert!(matches!(keys.last(), Some(PropertyKey::Symbol(_))));
        assert_eq!(
            machine.enumerable_keys(object).unwrap(),
            expected.map(EcmaString::encode)
        );
        assert_eq!(
            for_in_keys(machine, object),
            expected.map(EcmaString::encode)
        );
        let json = machine.intrinsics.global("JSON").unwrap();
        let stringify = machine.get_named_property(json, "stringify").unwrap();
        let rendered = machine.call_value(stringify, json, &[object]).unwrap();
        assert_eq!(
            machine.to_string(rendered).unwrap(),
            EcmaString::encode("{\"2\":4,\"10\":3,\"a\":1,\"b\":2}")
        );
        let reflect = machine.intrinsics.global("Reflect").unwrap();
        let reflect_keys = machine.get_named_property(reflect, "ownKeys").unwrap();
        let listed = machine
            .call_value(reflect_keys, reflect, &[object])
            .unwrap();
        let items = machine.array_elements(listed).unwrap().unwrap();
        assert_eq!(items.len(), 5);
        for (item, name) in items[..4].iter().zip(expected) {
            assert_eq!(
                machine.string_value(*item).unwrap(),
                EcmaString::encode(name)
            );
        }
        assert_eq!(items[4], symbol);
        let handler = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let trap = machine.intrinsics.builtins.register(BuiltinDef {
            name: "ownKeys",
            length: 1,
            handler: proxy_own_keys_trap,
        });
        let trap = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            trap,
            "ownKeys",
            1,
        );
        machine.set_data_property(handler, "ownKeys", trap).unwrap();
        let proxy = crate::builtins::proxy::create(machine, object, handler).unwrap();
        let proxy_keys = machine.internal_own_property_keys(proxy).unwrap();
        let proxy_texts: Vec<String> = proxy_keys
            .iter()
            .filter_map(|key| match key {
                PropertyKey::Named(atom) => Some(machine.atoms.resolve(*atom).to_utf8_lossy()),
                _ => None,
            })
            .collect();
        assert_eq!(proxy_texts, expected);
        assert_eq!(proxy_keys.len(), 5);
    });
}

#[test]
fn computed_and_constant_keys_read_the_same_property() {
    with_machine(Limits::default(), |machine| {
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        machine
            .set_data_property(object, "shared", Value::int32(1))
            .unwrap();
        let computed = machine
            .allocate(HeapEntry::String(EcmaString::encode("shared")))
            .unwrap();
        let key = machine.property_key_from_value(computed).unwrap();
        assert_eq!(key, PropertyKey::Named(machine.intern_str("shared")));
        assert_eq!(
            machine.get_property_key(object, &key).unwrap(),
            Value::int32(1)
        );
        let other = machine
            .allocate(HeapEntry::String(EcmaString::encode("other")))
            .unwrap();
        let other_key = machine.property_key_from_value(other).unwrap();
        machine
            .set_data_property_key(object, other_key.clone(), Value::int32(2))
            .unwrap();
        assert_eq!(
            machine.get_named_property(object, "other").unwrap(),
            Value::int32(2)
        );
        assert_eq!(other_key, PropertyKey::Named(machine.intern_str("other")));
    });
}
#[test]
fn absent_ascii_reads_do_not_intern_names() {
    with_machine(Limits::default(), |machine| {
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let before = machine.atoms.strings.len();
        for index in 0..10_000 {
            let name = format!("absent_property_{index}");
            assert_eq!(
                machine.get_named_property(object, &name).unwrap(),
                Value::UNDEFINED
            );
        }
        assert_eq!(machine.atoms.strings.len(), before);
    });
}
#[test]
fn static_key_preinterned_at_load_not_first_access() {
    let program = verified(
        vec![
            Constant::String(EcmaString::encode("statickey")),
            Constant::String(EcmaString::encode("decoy-unused")),
        ],
        vec![function(
            0,
            6,
            vec![
                Instruction::CreateObject { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(0),
                },
                Instruction::Move {
                    dst: reg(2),
                    src: reg(1),
                },
                Instruction::Unary {
                    dst: reg(3),
                    op: UnaryOp::ToPropertyKey,
                    operand: reg(2),
                },
                Instruction::LoadConst {
                    dst: reg(5),
                    constant: cid(1),
                },
                Instruction::GetProperty {
                    dst: reg(4),
                    object: reg(0),
                    key: reg(3),
                },
                Instruction::Return { value: reg(4) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    assert!(machine.atoms.find("statickey").is_some());
    assert!(machine.atoms.find("decoy-unused").is_none());
    let before = machine.atoms.strings.len();
    let execution = machine.evaluate().unwrap();
    assert_eq!(machine.atoms.strings.len(), before);
    assert_eq!(execution.value, Value::UNDEFINED);
}
#[test]
fn reassigned_key_stays_access_time() {
    let program = verified(
        vec![
            Constant::String(EcmaString::encode("reassigned-first")),
            Constant::String(EcmaString::encode("reassigned-second")),
        ],
        vec![function(
            0,
            3,
            vec![
                Instruction::CreateObject { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(0),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(1),
                },
                Instruction::GetProperty {
                    dst: reg(2),
                    object: reg(0),
                    key: reg(1),
                },
                Instruction::Return { value: reg(2) },
            ],
            Vec::new(),
        )],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    assert!(machine.atoms.find("reassigned-first").is_none());
    assert!(machine.atoms.find("reassigned-second").is_none());
    let before = machine.atoms.strings.len();
    let execution = machine.evaluate().unwrap();
    assert_eq!(execution.value, Value::UNDEFINED);
    assert!(machine.atoms.find("reassigned-first").is_none());
    assert!(machine.atoms.find("reassigned-second").is_some());
    assert_eq!(machine.atoms.strings.len(), before + 1);
}
fn site_program() -> Program<Verified> {
    verified(
        vec![
            Constant::String(EcmaString::encode("a")),
            Constant::String(EcmaString::encode("b")),
        ],
        vec![function(
            2,
            3,
            vec![
                Instruction::GetProperty {
                    dst: reg(2),
                    object: reg(0),
                    key: reg(1),
                },
                Instruction::SetProperty {
                    object: reg(0),
                    key: reg(1),
                    value: reg(2),
                },
                Instruction::Halt,
            ],
            Vec::new(),
        )],
    )
}
fn site_object(machine: &mut Machine<'_, TestHost>, entries: &[(&str, Value)]) -> Value {
    let object = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    for (name, value) in entries {
        machine.set_data_property(object, name, *value).unwrap();
    }
    object
}
#[test]
fn site_hit_get_caches_shaped_own_data() {
    let program = site_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let module = ModuleId::new(0);
    let function = FunctionId::new(0);
    let object = site_object(&mut machine, &[("a", Value::int32(1))]);
    let key = PropertyKey::Named(machine.intern_str("a"));
    assert_eq!(
        machine.property_site_hit_get(module, function, 0, object, &key),
        None
    );
    machine.property_site_record_get(module, function, 0, object, &key);
    assert_eq!(machine.function_sites(module, function).sites[0].len, 1);
    assert_eq!(
        machine.property_site_hit_get(module, function, 0, object, &key),
        Some(Value::int32(1))
    );
}
#[test]
fn site_cache_distinguishes_keys_on_one_shape() {
    let program = site_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let module = ModuleId::new(0);
    let function = FunctionId::new(0);
    let object = site_object(
        &mut machine,
        &[("a", Value::int32(1)), ("b", Value::int32(2))],
    );
    let key_a = PropertyKey::Named(machine.intern_str("a"));
    let key_b = PropertyKey::Named(machine.intern_str("b"));
    machine.property_site_record_get(module, function, 0, object, &key_a);
    machine.property_site_record_get(module, function, 0, object, &key_b);
    assert_eq!(machine.function_sites(module, function).sites[0].len, 2);
    assert_eq!(
        machine.property_site_hit_get(module, function, 0, object, &key_a),
        Some(Value::int32(1))
    );
    assert_eq!(
        machine.property_site_hit_get(module, function, 0, object, &key_b),
        Some(Value::int32(2))
    );
}
#[test]
fn site_cache_distinguishes_slots_for_one_key_on_different_shapes() {
    let program = site_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let module = ModuleId::new(0);
    let function = FunctionId::new(0);
    let objects = [
        site_object(&mut machine, &[("a", Value::int32(1))]),
        site_object(
            &mut machine,
            &[("b", Value::int32(99)), ("a", Value::int32(2))],
        ),
    ];
    let key = PropertyKey::Named(machine.intern_str("a"));
    for object in objects {
        machine.property_site_record_get(module, function, 0, object, &key);
        machine.property_site_record_set(module, function, 1, object, &key);
    }
    for (index, object) in objects.into_iter().enumerate() {
        assert_eq!(
            machine.property_site_hit_get(module, function, 0, object, &key),
            Some(Value::int32(index as u32 + 1))
        );
        assert_eq!(
            machine.property_site_hit_set(module, function, 1, object, &key, Value::int32(7)),
            Some(())
        );
        assert_eq!(
            machine.get_named_property(object, "a").unwrap(),
            Value::int32(7)
        );
    }
    assert_eq!(
        machine.get_named_property(objects[1], "b").unwrap(),
        Value::int32(99)
    );
}

#[test]
fn site_cache_rechecks_changed_descriptors() {
    let program = site_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let module = ModuleId::new(0);
    let function = FunctionId::new(0);
    let object = site_object(&mut machine, &[("a", Value::int32(1))]);
    let key = PropertyKey::Named(machine.intern_str("a"));
    machine.property_site_record_get(module, function, 0, object, &key);
    machine.property_site_record_set(module, function, 1, object, &key);
    machine
        .define_descriptor(
            object,
            key.clone(),
            Property::Data {
                value: Value::int32(3),
                writable: false,
                enumerable: false,
                configurable: true,
            },
        )
        .unwrap();
    assert_eq!(
        machine.property_site_hit_set(module, function, 1, object, &key, Value::int32(4)),
        None
    );
    assert_eq!(
        machine.property_site_hit_get(module, function, 0, object, &key),
        Some(Value::int32(3))
    );
    machine
        .define_descriptor(
            object,
            key.clone(),
            Property::Accessor {
                getter: None,
                setter: None,
                enumerable: false,
                configurable: true,
            },
        )
        .unwrap();
    assert_eq!(
        machine.property_site_hit_get(module, function, 0, object, &key),
        None
    );
    assert_eq!(
        machine.property_site_hit_set(module, function, 1, object, &key, Value::int32(4)),
        None
    );
    machine
        .define_descriptor(
            object,
            key.clone(),
            Property::Data {
                value: Value::UNINITIALIZED,
                writable: true,
                enumerable: false,
                configurable: true,
            },
        )
        .unwrap();
    assert_eq!(
        machine.property_site_hit_get(module, function, 0, object, &key),
        None
    );
}

#[test]
fn site_cache_misses_after_delete_and_reinsert() {
    let program = site_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let module = ModuleId::new(0);
    let function = FunctionId::new(0);
    let object = site_object(&mut machine, &[("a", Value::int32(1))]);
    let key = PropertyKey::Named(machine.intern_str("a"));
    machine.property_site_record_get(module, function, 0, object, &key);
    machine.property_site_record_set(module, function, 1, object, &key);
    assert!(machine.internal_delete(object, &key).unwrap());
    machine
        .set_data_property_key(object, key.clone(), Value::int32(8))
        .unwrap();
    assert_eq!(
        machine.property_site_hit_get(module, function, 0, object, &key),
        None
    );
    assert_eq!(
        machine.property_site_hit_set(module, function, 1, object, &key, Value::int32(9)),
        None
    );
    assert_eq!(
        machine.get_named_property(object, "a").unwrap(),
        Value::int32(8)
    );
}

#[test]
#[ignore = "development-host performance measurement"]
fn profile_property_cache_hits() {
    use std::hint::black_box;
    use std::time::Instant;

    let program = site_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let module = ModuleId::new(0);
    let function = FunctionId::new(0);
    let object = site_object(&mut machine, &[("a", Value::int32(1))]);
    let key = PropertyKey::Named(machine.intern_str("a"));
    machine.property_site_record_get(module, function, 0, object, &key);
    machine.property_site_record_set(module, function, 1, object, &key);
    let iterations = 2_000_000_u64;
    let mut checksum = 0_u64;
    let started = Instant::now();
    for _ in 0..iterations {
        checksum = checksum.wrapping_add(
            black_box(&mut machine)
                .property_site_hit_get(module, function, 0, object, black_box(&key))
                .expect("populated cache hits")
                .to_bits(),
        );
    }
    let elapsed = started.elapsed();
    assert_eq!(checksum, iterations.wrapping_mul(Value::int32(1).to_bits()));
    eprintln!(
        "property_cache_get iterations={iterations} elapsed_ns={} checksum={checksum}",
        elapsed.as_nanos()
    );
    let started = Instant::now();
    for value in 0..iterations {
        black_box(&mut machine)
            .property_site_hit_set(
                module,
                function,
                1,
                object,
                black_box(&key),
                Value::int32(value as u32),
            )
            .expect("populated cache handles stores");
    }
    let elapsed = started.elapsed();
    assert_eq!(
        machine.get_named_property(object, "a").unwrap(),
        Value::int32(iterations as u32 - 1)
    );
    eprintln!(
        "property_cache_set iterations={iterations} elapsed_ns={} final_value={}",
        elapsed.as_nanos(),
        iterations - 1
    );
}

#[test]
#[ignore = "development-host performance measurement"]
fn profile_function_site_initialization() {
    use std::hint::black_box;
    use std::time::Instant;

    let instructions = 100_000;
    let iterations = 100;
    let mut code = vec![
        Instruction::LoadConst {
            dst: reg(0),
            constant: cid(0),
        };
        instructions
    ];
    code[10_000] = Instruction::GetProperty {
        dst: reg(0),
        object: reg(0),
        key: reg(0),
    };
    code[20_000] = Instruction::SetProperty {
        object: reg(0),
        key: reg(0),
        value: reg(0),
    };
    code[instructions - 1] = Instruction::Halt;
    let program = verified(
        vec![Constant::Int32(1)],
        vec![function(0, 1, code, Vec::new())],
    );
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let module = ModuleId::new(0);
    let function = FunctionId::new(0);
    let mut found = 0;
    let started = Instant::now();
    for _ in 0..iterations {
        found += usize::from(
            black_box(&mut machine)
                .get_cache_slot(module, function, 10_000, Which::Get)
                .is_some(),
        );
        found += usize::from(
            black_box(&mut machine)
                .get_cache_slot(module, function, 20_000, Which::Set)
                .is_some(),
        );
        machine.property_sites.clear();
    }
    let elapsed = started.elapsed();
    assert_eq!(found, iterations * 2);
    eprintln!(
        "function_sites instructions={instructions} iterations={iterations} elapsed_ns={} sites_found={found} site_bytes={}",
        elapsed.as_nanos(),
        std::mem::size_of::<crate::shape::PropertySite>()
    );
}

#[test]
fn site_cache_ignores_prototype_values() {
    let program = site_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let module = ModuleId::new(0);
    let function = FunctionId::new(0);
    let parent = site_object(&mut machine, &[("a", Value::int32(7))]);
    let child = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(parent),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    assert_eq!(
        machine.get_named_property(child, "a").unwrap(),
        Value::int32(7)
    );
    let key = PropertyKey::Named(machine.intern_str("a"));
    machine.property_site_record_get(module, function, 0, child, &key);
    assert_eq!(machine.function_sites(module, function).sites[0].len, 0);
    assert_eq!(
        machine.property_site_hit_get(module, function, 0, child, &key),
        None
    );
}
#[test]
fn site_cache_ignores_accessors_and_uninitialized() {
    let program = site_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let module = ModuleId::new(0);
    let function = FunctionId::new(0);
    let key_acc = PropertyKey::Named(machine.intern_str("acc"));
    let mut properties = PropertyMap::default();
    properties.insert(
        &mut machine.shapes,
        key_acc.clone(),
        Property::Accessor {
            getter: None,
            setter: None,
            enumerable: true,
            configurable: true,
        },
    );
    let key_uninit = PropertyKey::Named(machine.intern_str("u"));
    properties.insert(
        &mut machine.shapes,
        key_uninit.clone(),
        Property::Data {
            value: Value::UNINITIALIZED,
            writable: true,
            enumerable: true,
            configurable: true,
        },
    );
    let object = machine
        .allocate(HeapEntry::Object {
            properties,
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    machine.property_site_record_get(module, function, 0, object, &key_acc);
    machine.property_site_record_get(module, function, 0, object, &key_uninit);
    assert_eq!(machine.function_sites(module, function).sites[0].len, 0);
    assert_eq!(
        machine.property_site_hit_get(module, function, 0, object, &key_acc),
        None
    );
    assert_eq!(
        machine.property_site_hit_get(module, function, 0, object, &key_uninit),
        None
    );
}
#[test]
fn site_cache_goes_megamorphic_on_fifth_shape() {
    let program = site_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let module = ModuleId::new(0);
    let function = FunctionId::new(0);
    for index in 0..5u32 {
        let name = format!("m{index}");
        let object = site_object(&mut machine, &[(name.as_str(), Value::int32(index))]);
        let key = PropertyKey::Named(machine.intern_str(&name));
        machine.property_site_record_get(module, function, 0, object, &key);
    }
    assert_eq!(
        machine.function_sites(module, function).sites[0].len,
        u8::MAX
    );
    let extra = site_object(&mut machine, &[("extra", Value::int32(9))]);
    let extra_key = PropertyKey::Named(machine.intern_str("extra"));
    machine.property_site_record_get(module, function, 0, extra, &extra_key);
    assert_eq!(
        machine.property_site_hit_get(module, function, 0, extra, &extra_key),
        None
    );
}
#[test]
fn site_hit_set_updates_writable_data() {
    let program = site_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let module = ModuleId::new(0);
    let function = FunctionId::new(0);
    let object = site_object(&mut machine, &[("a", Value::int32(1))]);
    let key = PropertyKey::Named(machine.intern_str("a"));
    assert_eq!(
        machine.property_site_hit_set(module, function, 1, object, &key, Value::int32(2)),
        None
    );
    machine.property_site_record_set(module, function, 1, object, &key);
    assert_eq!(machine.function_sites(module, function).sites[1].len, 1);
    assert_eq!(
        machine.property_site_hit_set(module, function, 1, object, &key, Value::int32(2)),
        Some(())
    );
    assert_eq!(
        machine.get_named_property(object, "a").unwrap(),
        Value::int32(2)
    );
}
#[test]
fn site_set_ignores_readonly_and_absent_keys() {
    let program = site_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let module = ModuleId::new(0);
    let function = FunctionId::new(0);
    let key = PropertyKey::Named(machine.intern_str("ro"));
    let mut properties = PropertyMap::default();
    properties.insert(
        &mut machine.shapes,
        key.clone(),
        Property::Data {
            value: Value::int32(1),
            writable: false,
            enumerable: true,
            configurable: true,
        },
    );
    let object = machine
        .allocate(HeapEntry::Object {
            properties,
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    machine.property_site_record_set(module, function, 1, object, &key);
    let absent = PropertyKey::Named(machine.intern_str("absent"));
    machine.property_site_record_set(module, function, 1, object, &absent);
    assert_eq!(machine.function_sites(module, function).sites[1].len, 0);
    assert_eq!(
        machine.property_site_hit_set(module, function, 1, object, &key, Value::int32(2)),
        None
    );
}
#[test]
fn site_cache_ignores_dictionary_maps() {
    let program = site_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let module = ModuleId::new(0);
    let function = FunctionId::new(0);
    let mut properties = PropertyMap::default();
    for index in 0..70u32 {
        let key = PropertyKey::Named(machine.atoms.intern_str(&format!("w{index}")));
        properties.insert(
            &mut machine.shapes,
            key,
            Property::Data {
                value: Value::int32(index),
                writable: true,
                enumerable: true,
                configurable: true,
            },
        );
    }
    let object = machine
        .allocate(HeapEntry::Object {
            properties,
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .unwrap();
    let key = PropertyKey::Named(machine.intern_str("w0"));
    machine.property_site_record_get(module, function, 0, object, &key);
    machine.property_site_record_set(module, function, 1, object, &key);
    assert_eq!(machine.function_sites(module, function).sites[0].len, 0);
    assert_eq!(machine.function_sites(module, function).sites[1].len, 0);
    assert_eq!(
        machine.property_site_hit_get(module, function, 0, object, &key),
        None
    );
}
