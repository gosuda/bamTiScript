//! S11 integration tests (IT1-IT19): the Proxy/Reflect canonical
//! internal-method cutover.
//!
//! Each test drives one user-observable surface end to end through the
//! canonical `internal_*` heads. Trap handlers are plain `fn` pointers (the
//! builtin registration surface), so per-test state travels through static
//! atomic stamp logs and handler-object properties, never through captures.

use std::sync::atomic::{AtomicUsize, Ordering};

use bamts_bytecode::{
    Constant, ConstantId, EcmaString, Function, FunctionFlags, FunctionId, Instruction, Module,
    ModuleId, Program, ProgramModule, Register, Verified,
};
use bamts_native::{Decoded, Value};

use crate::builtins::property_descriptor::PropertyDescriptor;
use crate::builtins::proxy;
use crate::builtins::test_support::{TestHost, ordinary_object};
use crate::intrinsics::{BuiltinDef, BuiltinOutcome, native_function};
use crate::{
    EvalFailure, HeapEntry, Host, Limits, Machine, Property, PropertyKey, PropertyMap,
    RuntimeErrorKind, ThrowOrigin,
};

/// The concrete trap signature every test handler coerces to.
type Trap =
    fn(&mut Machine<'_, TestHost>, Value, &[Value], bool) -> Result<BuiltinOutcome, EvalFailure>;

// ---------------------------------------------------------------------------
// Stamp logs: ordered, atomic, allocation-free trap observation.
// ---------------------------------------------------------------------------

const LOG_CAPACITY: usize = 64;

/// Ordered trap-call log backed by atomics. Each `stamp` records one op at the
/// next cursor slot; `recorded` replays the ops in stamp order. Tests are
/// single-threaded, so `SeqCst` is purely belt-and-braces.
struct StampLog {
    cursor: AtomicUsize,
    slots: [AtomicUsize; LOG_CAPACITY],
}

impl StampLog {
    const fn new() -> Self {
        Self {
            cursor: AtomicUsize::new(0),
            slots: [const { AtomicUsize::new(usize::MAX) }; LOG_CAPACITY],
        }
    }

    fn stamp(&self, op: usize) {
        let slot = self.cursor.fetch_add(1, Ordering::SeqCst);
        assert!(slot < LOG_CAPACITY, "stamp log overflow");
        self.slots[slot].store(op, Ordering::SeqCst);
    }

    fn recorded(&self) -> Vec<usize> {
        (0..self.cursor.load(Ordering::SeqCst))
            .map(|slot| self.slots[slot].load(Ordering::SeqCst))
            .collect()
    }

    fn reset(&self) {
        self.cursor.store(0, Ordering::SeqCst);
    }
}

/// Replays one stamp log and fails with the observed sequence on mismatch.
fn assert_logged(log: &StampLog, expected: &[usize]) {
    assert_eq!(&log.recorded(), expected, "trap stamp sequence");
}

// Op codes shared by the stamp logs.
const OP_GET: usize = 1;
const OP_SET: usize = 2;
const OP_HAS: usize = 3;
const OP_DELETE: usize = 4;
const OP_GOPD: usize = 5;
const OP_OWN_KEYS: usize = 6;
const OP_IS_EXTENSIBLE: usize = 7;
const OP_PREVENT_EXTENSIONS: usize = 8;
const OP_GET_PROTO: usize = 9;
const OP_SET_PROTO: usize = 10;
const OP_DEFINE: usize = 11;
const OP_APPLY: usize = 12;
const OP_CONSTRUCT: usize = 13;
const OP_OUTER: usize = 14;
const OP_INNER: usize = 15;
const OP_REVOKED: usize = 16;
const OP_SIBLING_THROWN: usize = 17;

// ---------------------------------------------------------------------------
// Harness.
// ---------------------------------------------------------------------------

fn with_machine(test: impl FnOnce(&mut Machine<'_, TestHost>)) {
    with_machine_limits(Limits::default(), test);
}

fn with_machine_limits(limits: Limits, test: impl FnOnce(&mut Machine<'_, TestHost>)) {
    let program = program_fixture();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, limits);
    test(&mut machine);
}

fn program_fixture() -> Program<Verified> {
    let code = Module::new(
        vec![Constant::String(EcmaString::encode("<s11-it>"))],
        vec![
            Function::new(
                None,
                0,
                0,
                1,
                FunctionFlags::default(),
                vec![Instruction::Halt],
                Vec::new(),
            ),
            Function::new(
                None,
                0,
                0,
                1,
                FunctionFlags {
                    is_constructable: true,
                    ..FunctionFlags::default()
                },
                vec![Instruction::Halt],
                Vec::new(),
            ),
        ],
        FunctionId::new(0),
    )
    .verify()
    .expect("valid test module");
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
    .expect("valid test program")
}

/// Builds a program with `constants` and `functions`; function 0 is the entry.
fn verified(mut constants: Vec<Constant>, functions: Vec<Function>) -> Program<Verified> {
    let name = ConstantId::new(constants.len() as u32);
    constants.push(Constant::String(EcmaString::encode("<s11-bytecode>")));
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
    .expect("valid test program")
}

fn function(parameters: u32, registers: u32, code: Vec<Instruction>) -> Function {
    Function::new(
        None,
        0,
        parameters,
        registers,
        FunctionFlags::default(),
        code,
        Vec::new(),
    )
}
fn allocate_string<H: Host>(machine: &mut Machine<'_, H>, value: &str) -> Value {
    machine
        .allocate(HeapEntry::String(EcmaString::encode(value)))
        .map_err(EvalFailure::Runtime)
        .expect("string allocation succeeds")
}

fn allocate_array<H: Host>(machine: &mut Machine<'_, H>, elements: Vec<Value>) -> Value {
    machine
        .allocate(HeapEntry::Array {
            elements,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            extensible: true,
            length_writable: true,
        })
        .map_err(EvalFailure::Runtime)
        .expect("array allocation succeeds")
}

fn data_property<H: Host>(machine: &mut Machine<'_, H>, object: Value, name: &str, value: Value) {
    let key = key(machine, name);
    machine
        .define_descriptor(
            object,
            key,
            Property::Data {
                value,
                writable: true,
                enumerable: true,
                configurable: true,
            },
        )
        .expect("data property definition succeeds");
}

fn fixed_data_property<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    name: &str,
    value: Value,
) {
    let key = key(machine, name);
    machine
        .define_descriptor(
            object,
            key,
            Property::Data {
                value,
                writable: false,
                enumerable: true,
                configurable: false,
            },
        )
        .expect("fixed data property definition succeeds");
}

/// Plain (callable, non-constructable) builtin with a `fn`-pointer handler.
fn native(
    machine: &mut Machine<'_, TestHost>,
    name: &'static str,
    length: u32,
    handler: Trap,
) -> Value {
    let id = machine.intrinsics.builtins.register(BuiltinDef {
        name,
        length,
        handler,
    });
    native_function(&mut machine.heap, &mut machine.atoms, id, name, length)
}

/// Callable-and-constructable builtin (construct targets for ProxyCreate).
fn native_ctor(
    machine: &mut Machine<'_, TestHost>,
    name: &'static str,
    length: u32,
    handler: Trap,
) -> Value {
    let id = machine
        .intrinsics
        .builtins
        .register_constructor(BuiltinDef {
            name,
            length,
            handler,
        });
    native_function(&mut machine.heap, &mut machine.atoms, id, name, length)
}

fn global_method(machine: &mut Machine<'_, TestHost>, namespace: &str, name: &str) -> Value {
    let object = machine
        .intrinsics
        .global(namespace)
        .unwrap_or_else(|| panic!("{namespace} is installed"));
    machine
        .get_named_property(object, name)
        .unwrap_or_else(|_| panic!("{namespace}.{name} is installed"))
}

fn reflect(
    machine: &mut Machine<'_, TestHost>,
    method: &str,
    args: &[Value],
) -> Result<Value, EvalFailure> {
    let function = global_method(machine, "Reflect", method);
    machine.call_value(function, Value::UNDEFINED, args)
}

fn object_static(
    machine: &mut Machine<'_, TestHost>,
    method: &str,
    args: &[Value],
) -> Result<Value, EvalFailure> {
    let function = global_method(machine, "Object", method);
    machine.call_value(function, Value::UNDEFINED, args)
}

fn reg(raw: u32) -> Register {
    Register::new(raw)
}

fn cid(raw: u32) -> ConstantId {
    ConstantId::new(raw)
}

fn key<H: Host>(machine: &mut Machine<'_, H>, name: &str) -> PropertyKey {
    PropertyKey::Named(machine.intern_str(name))
}

/// Builds a descriptor object a gOPD trap can return, mirroring
/// FromPropertyDescriptor.
fn descriptor_reply<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    writable: Value,
    enumerable: bool,
    configurable: Value,
) -> Value {
    let object = ordinary_object(machine);
    let fields = [
        ("value", value),
        ("writable", writable),
        ("enumerable", Value::boolean(enumerable)),
        ("configurable", configurable),
    ];
    for (name, field) in fields {
        data_property(machine, object, name, field);
    }
    object
}

fn key_text(machine: &Machine<'_, TestHost>, value: Value) -> Option<String> {
    machine
        .string_value(value)
        .map(|name| name.to_utf8_lossy().to_string())
}

fn is_type_error<T>(result: &Result<T, EvalFailure>) -> bool {
    matches!(
        result,
        Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
    )
}

fn is_call_depth<T>(result: &Result<T, EvalFailure>) -> bool {
    matches!(
        result,
        Err(EvalFailure::Runtime(
            RuntimeErrorKind::CallDepthExceeded { .. }
        ))
    )
}

/// `Proxy.revocable` through the installed global; returns (proxy, revoker).
fn revocable_pair(
    machine: &mut Machine<'_, TestHost>,
    target: Value,
    handler: Value,
) -> (Value, Value) {
    let revocable = global_method(machine, "Proxy", "revocable");
    let record = machine
        .call_value(revocable, Value::UNDEFINED, &[target, handler])
        .expect("Proxy.revocable succeeds");
    let proxy = machine.get_named_property(record, "proxy").unwrap();
    let revoker = machine.get_named_property(record, "revoke").unwrap();
    (proxy, revoker)
}

/// A chain of `depth` transparent proxies forwarding target-side to `target`.
fn transparent_chain(machine: &mut Machine<'_, TestHost>, depth: usize, target: Value) -> Value {
    let handler = ordinary_object(machine);
    let mut current = target;
    for _ in 0..depth {
        current = proxy::create(machine, current, handler).expect("proxy creation succeeds");
    }
    current
}

/// An inert constructable builtin: constructing returns a fresh object.
fn it17_native_target(machine: &mut Machine<'_, TestHost>) -> Value {
    fn handler<H: Host>(
        machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        if !constructing {
            return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
        }
        let instance = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .map_err(EvalFailure::Runtime)?;
        Ok(BuiltinOutcome::Value(instance))
    }
    native_ctor(machine, "it17 target", 0, handler)
}

// ---------------------------------------------------------------------------
// IT1: bytecode property ops fire exactly their one trap.
// ---------------------------------------------------------------------------

static IT1_GET: StampLog = StampLog::new();
static IT1_SET: StampLog = StampLog::new();
static IT1_DELETE: StampLog = StampLog::new();
static IT1_HAS: StampLog = StampLog::new();

fn it1_get<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    IT1_GET.stamp(OP_GET);
    assert!(
        machine
            .string_value(args[1])
            .is_some_and(|name| name.eq_ascii("x")),
        "bytecode get must consult the trap with the requested key"
    );
    Ok(BuiltinOutcome::Value(Value::int32(42)))
}

fn it1_set<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    IT1_SET.stamp(OP_SET);
    assert_eq!(args[2], Value::int32(5), "bytecode set forwards the value");
    assert!(
        machine
            .string_value(args[1])
            .is_some_and(|name| name.eq_ascii("x"))
    );
    Ok(BuiltinOutcome::Value(Value::TRUE))
}

fn it1_delete<H: Host>(
    _machine: &mut Machine<'_, H>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    IT1_DELETE.stamp(OP_DELETE);
    Ok(BuiltinOutcome::Value(Value::TRUE))
}

fn it1_has<H: Host>(
    _machine: &mut Machine<'_, H>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    IT1_HAS.stamp(OP_HAS);
    Ok(BuiltinOutcome::Value(Value::TRUE))
}

#[test]
fn it01_bytecode_property_ops_fire_exactly_their_trap() {
    with_machine(|machine| {
        let target = ordinary_object(machine);
        let handler = ordinary_object(machine);
        let get = native(machine, "it1 get", 3, it1_get);
        data_property(machine, handler, "get", get);
        let set = native(machine, "it1 set", 4, it1_set);
        data_property(machine, handler, "set", set);
        let delete = native(machine, "it1 delete", 2, it1_delete);
        data_property(machine, handler, "deleteProperty", delete);
        let has = native(machine, "it1 has", 2, it1_has);
        data_property(machine, handler, "has", has);
        let proxy_value = proxy::create(machine, target, handler).unwrap();

        let x = key(machine, "x");

        // GetProperty.
        assert_eq!(
            machine.internal_get(proxy_value, &x, proxy_value).unwrap(),
            Value::int32(42)
        );
        // SetProperty (the trap accepts, so the strict wrapper stays silent).
        assert!(
            machine
                .internal_set(proxy_value, x.clone(), Value::int32(5), proxy_value)
                .unwrap()
        );
        // DeleteProperty.
        assert!(machine.internal_delete(proxy_value, &x).unwrap());
        // `in`.
        assert!(machine.internal_has_property(proxy_value, &x).unwrap());

        assert_logged(&IT1_GET, &[OP_GET]);
        assert_logged(&IT1_SET, &[OP_SET]);
        assert_logged(&IT1_DELETE, &[OP_DELETE]);
        assert_logged(&IT1_HAS, &[OP_HAS]);
    });
}

// ---------------------------------------------------------------------------
// IT2: a Proxy prototype preserves the original receiver across get/set/has.
// ---------------------------------------------------------------------------

static IT2: StampLog = StampLog::new();

fn it2_get<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    IT2.stamp(OP_GET);
    machine.set_data_property(this, "seenGetReceiver", args[2])?;
    Ok(BuiltinOutcome::Value(Value::int32(7)))
}

fn it2_set<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    IT2.stamp(OP_SET);
    machine.set_data_property(this, "seenSetReceiver", args[3])?;
    Ok(BuiltinOutcome::Value(Value::TRUE))
}

fn it2_has<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    IT2.stamp(OP_HAS);
    machine.set_data_property(this, "seenHasKey", args[1])?;
    Ok(BuiltinOutcome::Value(Value::TRUE))
}

#[test]
fn it02_proxy_prototype_traps_see_the_original_receiver() {
    with_machine(|machine| {
        let proto_target = ordinary_object(machine);
        let handler = ordinary_object(machine);
        let get = native(machine, "it2 get", 3, it2_get);
        data_property(machine, handler, "get", get);
        let set = native(machine, "it2 set", 4, it2_set);
        data_property(machine, handler, "set", set);
        let has = native(machine, "it2 has", 2, it2_has);
        data_property(machine, handler, "has", has);
        let proto = proxy::create(machine, proto_target, handler).unwrap();

        let instance = ordinary_object(machine);
        machine
            .internal_set_prototype_of(instance, Some(proto))
            .unwrap();

        let x = key(machine, "x");
        // chain and the trap must observe `instance`, never the proxy.
        assert_eq!(
            machine.internal_get(instance, &x, instance).unwrap(),
            Value::int32(7)
        );
        let seen_get = machine
            .get_named_property(handler, "seenGetReceiver")
            .unwrap();
        assert_eq!(seen_get, instance);
        // `instance.x = 9`.
        assert!(
            machine
                .internal_set(instance, x.clone(), Value::int32(9), instance)
                .unwrap()
        );
        let seen_set = machine
            .get_named_property(handler, "seenSetReceiver")
            .unwrap();
        assert_eq!(seen_set, instance);
        // `x in instance`.
        assert!(machine.internal_has_property(instance, &x).unwrap());
        let seen_key = machine.get_named_property(handler, "seenHasKey").unwrap();
        assert_eq!(key_text(machine, seen_key), Some("x".to_string()));
        assert_logged(&IT2, &[OP_GET, OP_SET, OP_HAS]);

        // The engine's for-in enumerates own enumerable keys only; the
        // prototype proxy must not observe phantom keys.
        assert!(machine.enumerable_keys(instance).unwrap().is_empty());
        assert_logged(&IT2, &[OP_GET, OP_SET, OP_HAS]);
    });
}

// ---------------------------------------------------------------------------
// IT3: for-in over a proxy orders ownKeys, per-key descriptors, then gets.
// ---------------------------------------------------------------------------

static IT3: StampLog = StampLog::new();

#[test]
fn it03_for_in_over_proxy_orders_own_keys_descriptors_gets() {
    with_machine(|machine| {
        let target = ordinary_object(machine);
        let a_key = key(machine, "a");
        machine
            .define_descriptor(
                target,
                a_key,
                Property::Data {
                    value: Value::int32(1),
                    writable: true,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        let hidden_key = key(machine, "hidden");
        machine
            .define_descriptor(
                target,
                hidden_key,
                Property::Data {
                    value: Value::int32(2),
                    writable: true,
                    enumerable: false,
                    configurable: true,
                },
            )
            .unwrap();

        let handler = ordinary_object(machine);
        let own_keys = native(
            machine,
            "it3 ownKeys",
            1,
            |machine, _this, _args, _constructing| {
                IT3.stamp(OP_OWN_KEYS);
                // [a, hidden] — the hidden key is filtered by enumerability
                // later, via [[GetOwnProperty]].
                let a = allocate_string(machine, "a");
                let hidden = allocate_string(machine, "hidden");
                Ok(BuiltinOutcome::Value(allocate_array(
                    machine,
                    vec![a, hidden],
                )))
            },
        );
        data_property(machine, handler, "ownKeys", own_keys);
        let gopd = native(
            machine,
            "it3 gOPD",
            2,
            |machine, _this, args, _constructing| {
                IT3.stamp(OP_GOPD);
                // Report a full descriptor mirroring the target's attributes
                // for the requested key; hiding is not an option here.
                let enumerable = machine
                    .string_value(args[1])
                    .is_some_and(|name| name.eq_ascii("a"));
                let value = Value::int32(1);
                let writable = Value::TRUE;
                let configurable = Value::TRUE;
                Ok(BuiltinOutcome::Value(descriptor_reply(
                    machine,
                    value,
                    writable,
                    enumerable,
                    configurable,
                )))
            },
        );
        data_property(machine, handler, "getOwnPropertyDescriptor", gopd);
        let get = native(
            machine,
            "it3 get",
            3,
            |_machine, _this, _args, _constructing| {
                IT3.stamp(OP_GET);
                Ok(BuiltinOutcome::Value(Value::int32(1)))
            },
        );
        data_property(machine, handler, "get", get);
        let proxy_value = proxy::create(machine, target, handler).unwrap();

        // for-in: ownKeys, then [[GetOwnProperty]] per key (the enumerability
        // filter), then the loop-body get per surviving key.
        let names = machine.enumerable_keys(proxy_value).unwrap();
        assert_eq!(names.len(), 1);
        assert!(names[0].eq_ascii("a"));
        assert_logged(&IT3, &[OP_OWN_KEYS, OP_GOPD, OP_GOPD]);
        let a = key(machine, "a");
        IT3.reset();
        machine.internal_get(proxy_value, &a, proxy_value).unwrap();
        assert_logged(&IT3, &[OP_GET]);
    });
}

// ---------------------------------------------------------------------------
// IT4: Object integrity statics route to traps in specification order.
// ---------------------------------------------------------------------------

static IT4: StampLog = StampLog::new();

fn it4_is_extensible<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    IT4.stamp(OP_IS_EXTENSIBLE);
    // Agree with the target: the trap reports the target's real extensibility.
    let extensible = machine.internal_is_extensible(args[0])?;
    Ok(BuiltinOutcome::Value(Value::boolean(extensible)))
}

fn it4_own_keys<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    IT4.stamp(OP_OWN_KEYS);
    // Report the target's own keys, materialized as an array.
    let keys = machine.internal_own_property_keys(args[0])?;
    let values = keys
        .iter()
        .map(|key| match key {
            PropertyKey::Named(name) => Ok(machine
                .allocate(HeapEntry::String(machine.atoms.resolve(*name).clone()))
                .map_err(EvalFailure::Runtime)?),
            PropertyKey::Symbol(_) | PropertyKey::Private(_) => {
                Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "it4 ownKeys symbol",
                }))
            }
        })
        .collect::<Result<Vec<_>, EvalFailure>>()?;
    Ok(BuiltinOutcome::Value(allocate_array(machine, values)))
}

fn it4_gopd<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    IT4.stamp(OP_GOPD);
    // Report the target's real descriptor for the requested key.
    let key = machine.property_key_from_value(args[1])?;
    let descriptor = machine
        .internal_get_own_property(args[0], &key)?
        .expect("it4 target holds the probed key");
    let value = descriptor.value.expect("data descriptor value");
    Ok(BuiltinOutcome::Value(descriptor_reply(
        machine,
        value,
        Value::boolean(descriptor.writable.unwrap_or(false)),
        descriptor.enumerable.unwrap_or(false),
        Value::boolean(descriptor.configurable.unwrap_or(false)),
    )))
}

fn it4_prevent_extensions<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    IT4.stamp(OP_PREVENT_EXTENSIONS);
    // A true result requires the target to actually become non-extensible.
    machine.internal_prevent_extensions(args[0])?;
    Ok(BuiltinOutcome::Value(Value::TRUE))
}

fn it4_define<H: Host>(
    _machine: &mut Machine<'_, H>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    IT4.stamp(OP_DEFINE);
    Ok(BuiltinOutcome::Value(Value::TRUE))
}

/// Installs the ordered integrity traps on `handler`.
fn it4_install(machine: &mut Machine<'_, TestHost>, handler: Value) {
    let is_extensible = native(machine, "it4 isExtensible", 1, it4_is_extensible);
    data_property(machine, handler, "isExtensible", is_extensible);
    let own_keys = native(machine, "it4 ownKeys", 1, it4_own_keys);
    data_property(machine, handler, "ownKeys", own_keys);
    let gopd = native(machine, "it4 gOPD", 2, it4_gopd);
    data_property(machine, handler, "getOwnPropertyDescriptor", gopd);
    let prevent = native(machine, "it4 preventExtensions", 1, it4_prevent_extensions);
    data_property(machine, handler, "preventExtensions", prevent);
}

#[test]
fn it04_object_integrity_statics_route_to_traps_in_order() {
    with_machine(|machine| {
        // isSealed on an extensible proxy: IsExtensible answers first.
        let handler = ordinary_object(machine);
        it4_install(machine, handler);
        let fresh = ordinary_object(machine);
        let proxy_value = proxy::create(machine, fresh, handler).unwrap();
        assert_eq!(
            object_static(machine, "isSealed", &[proxy_value]).unwrap(),
            Value::FALSE
        );
        assert_logged(&IT4, &[OP_IS_EXTENSIBLE]);

        // Sealed: non-extensible target, non-configurable key; the integrity
        // walk goes ownKeys then one descriptor per key, in that order.
        IT4.reset();
        let sealed_target = ordinary_object(machine);
        fixed_data_property(machine, sealed_target, "a", Value::int32(1));
        machine.internal_prevent_extensions(sealed_target).unwrap();
        let sealed_handler = ordinary_object(machine);
        it4_install(machine, sealed_handler);
        let sealed = proxy::create(machine, sealed_target, sealed_handler).unwrap();
        assert_eq!(
            object_static(machine, "isSealed", &[sealed]).unwrap(),
            Value::TRUE
        );
        assert_logged(&IT4, &[OP_IS_EXTENSIBLE, OP_OWN_KEYS, OP_GOPD]);

        // Frozen: same walk, writable:false makes it frozen.
        IT4.reset();
        let frozen_target = ordinary_object(machine);
        fixed_data_property(machine, frozen_target, "a", Value::int32(1));
        machine.internal_prevent_extensions(frozen_target).unwrap();
        let frozen_handler = ordinary_object(machine);
        it4_install(machine, frozen_handler);
        let frozen = proxy::create(machine, frozen_target, frozen_handler).unwrap();
        assert_eq!(
            object_static(machine, "isFrozen", &[frozen]).unwrap(),
            Value::TRUE
        );
        assert_logged(&IT4, &[OP_IS_EXTENSIBLE, OP_OWN_KEYS, OP_GOPD]);

        // Object.seal must run the per-key defineProperty redefinitions
        // through the proxy (SetIntegrityLevel), not flip a flag.
        IT4.reset();
        let seal_target = ordinary_object(machine);
        // Already non-configurable: the engine treats setting_config_false on
        // a configurable target property as fatal, so sealing redefines an
        // existing fixed key.
        fixed_data_property(machine, seal_target, "k", Value::int32(1));
        let seal_handler = ordinary_object(machine);
        let seal_prevent = native(machine, "it4 seal pE", 1, it4_prevent_extensions);
        data_property(machine, seal_handler, "preventExtensions", seal_prevent);
        let seal_define = native(machine, "it4 seal define", 3, it4_define);
        data_property(machine, seal_handler, "defineProperty", seal_define);
        let seal_keys = native(machine, "it4 seal ownKeys", 1, it4_own_keys);
        data_property(machine, seal_handler, "ownKeys", seal_keys);
        let sealable = proxy::create(machine, seal_target, seal_handler).unwrap();
        assert_eq!(
            object_static(machine, "seal", &[sealable]).unwrap(),
            sealable
        );
        assert!(
            IT4.recorded()
                .starts_with(&[OP_PREVENT_EXTENSIONS, OP_OWN_KEYS, OP_DEFINE]),
            "seal must preventExtensions then redefine each key, got {:?}",
            IT4.recorded()
        );

        // Revoked proxies surface a TypeError, never a boolean.
        let fresh1 = ordinary_object(machine);
        let fresh2 = ordinary_object(machine);
        let (revoked, revoker) = revocable_pair(machine, fresh1, fresh2);
        machine.call_value(revoker, Value::UNDEFINED, &[]).unwrap();
        let sealed_result = object_static(machine, "isSealed", &[revoked]);
        assert!(
            is_type_error(&sealed_result),
            "revoked proxy is a TypeError"
        );
        let frozen_result = object_static(machine, "isFrozen", &[revoked]);
        assert!(
            is_type_error(&frozen_result),
            "revoked proxy is a TypeError"
        );
    });
}

// ---------------------------------------------------------------------------
// IT5: Object.assign reads a proxy source and writes a proxy target.
// ---------------------------------------------------------------------------

static IT5_GET: StampLog = StampLog::new();
static IT5_SET: StampLog = StampLog::new();

#[test]
fn it05_object_assign_routes_proxy_source_and_target() {
    with_machine(|machine| {
        // Source proxy: ownKeys -> [a], gOPD falls back to the target
        // descriptor (enumerable), get observes the read.
        let source_target = ordinary_object(machine);
        data_property(machine, source_target, "a", Value::int32(42));
        let source_handler = ordinary_object(machine);
        let source_keys = native(
            machine,
            "it5 ownKeys",
            1,
            |machine, _this, _args, _constructing| {
                let a = allocate_string(machine, "a");
                Ok(BuiltinOutcome::Value(allocate_array(machine, vec![a])))
            },
        );
        data_property(machine, source_handler, "ownKeys", source_keys);
        let source_gopd = native(
            machine,
            "it5 gOPD",
            2,
            |machine, _this, _args, _constructing| {
                Ok(BuiltinOutcome::Value(descriptor_reply(
                    machine,
                    Value::int32(42),
                    Value::TRUE,
                    true,
                    Value::TRUE,
                )))
            },
        );
        data_property(
            machine,
            source_handler,
            "getOwnPropertyDescriptor",
            source_gopd,
        );
        let source_get = native(
            machine,
            "it5 get",
            3,
            |machine, this, args, _constructing| {
                IT5_GET.stamp(OP_GET);
                machine.set_data_property(this, "seenGetKey", args[1])?;
                Ok(BuiltinOutcome::Value(Value::int32(42)))
            },
        );
        data_property(machine, source_handler, "get", source_get);
        let source = proxy::create(machine, source_target, source_handler).unwrap();

        // Plain destination: the assigned value lands.
        let destination = ordinary_object(machine);
        object_static(machine, "assign", &[destination, source]).unwrap();
        assert_eq!(
            machine.get_named_property(destination, "a").unwrap(),
            Value::int32(42)
        );
        assert_logged(&IT5_GET, &[OP_GET]);

        // Proxy destination whose set trap accepts: the trap observes the key.
        IT5_GET.reset();
        let set_handler = ordinary_object(machine);
        let accepting_set = native(
            machine,
            "it5 set",
            4,
            |machine, this, args, _constructing| {
                IT5_SET.stamp(OP_SET);
                machine.set_data_property(this, "seenSetKey", args[1])?;
                machine.set_data_property(this, "seenSetValue", args[2])?;
                Ok(BuiltinOutcome::Value(Value::TRUE))
            },
        );
        data_property(machine, set_handler, "set", accepting_set);
        let fresh = ordinary_object(machine);
        let accepting = proxy::create(machine, fresh, set_handler).unwrap();
        object_static(machine, "assign", &[accepting, source]).unwrap();
        assert_logged(&IT5_SET, &[OP_SET]);
        let seen_key = machine
            .get_named_property(set_handler, "seenSetKey")
            .unwrap();
        assert_eq!(key_text(machine, seen_key), Some("a".to_string()));
        let seen_value = machine
            .get_named_property(set_handler, "seenSetValue")
            .unwrap();
        assert_eq!(seen_value, Value::int32(42));

        // Proxy destination whose set trap refuses: assign throws (strict).
        IT5_SET.reset();
        let refusing_handler = ordinary_object(machine);
        let refusing_set = native(
            machine,
            "it5 set false",
            4,
            |_machine, _this, _args, _constructing| {
                IT5_SET.stamp(OP_SET);
                Ok(BuiltinOutcome::Value(Value::FALSE))
            },
        );
        data_property(machine, refusing_handler, "set", refusing_set);
        let fresh = ordinary_object(machine);
        let refusing = proxy::create(machine, fresh, refusing_handler).unwrap();
        let result = object_static(machine, "assign", &[refusing, source]);
        assert!(is_type_error(&result), "false set trap throws in assign");
        assert_logged(&IT5_SET, &[OP_SET]);
    });
}

// ---------------------------------------------------------------------------
// IT6: every call/construct entry routes proxies; revokers are idempotent.
// ---------------------------------------------------------------------------

static IT6: StampLog = StampLog::new();

fn it6_apply<H: Host>(
    _machine: &mut Machine<'_, H>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    IT6.stamp(OP_APPLY);
    Ok(BuiltinOutcome::Value(Value::int32(1)))
}

fn it6_construct<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    IT6.stamp(OP_CONSTRUCT);
    machine.set_data_property(this, "seenNewTarget", args[2])?;
    let arguments = machine.array_elements(args[1])?.unwrap_or_default();
    let instance = machine.internal_construct(args[0], &arguments, args[2])?;
    Ok(BuiltinOutcome::Value(instance))
}

/// Inert callable/constructable builtin used as a proxy target.
fn it6_native_ctor(
    machine: &mut Machine<'_, TestHost>,
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !constructing {
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    }
    let instance = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            extensible: true,
            boxed_primitive: None,
        })
        .map_err(EvalFailure::Runtime)?;
    Ok(BuiltinOutcome::Value(instance))
}

#[test]
fn it06_call_and_construct_entries_route_proxies() {
    // Engine entries: call_value and construct_value, plus revoker idempotence.
    with_machine(|machine| {
        let callable_target = native(
            machine,
            "it6 target",
            0,
            |machine, _this, _args, constructing| it6_native_ctor(machine, constructing),
        );
        let handler = ordinary_object(machine);
        let apply = native(machine, "it6 apply", 3, it6_apply);
        data_property(machine, handler, "apply", apply);
        let proxy_value = proxy::create(machine, callable_target, handler).unwrap();
        assert_eq!(
            machine
                .call_value(proxy_value, Value::UNDEFINED, &[])
                .unwrap(),
            Value::int32(1)
        );
        assert_logged(&IT6, &[OP_APPLY]);

        IT6.reset();
        let construct_handler = ordinary_object(machine);
        let construct = native(machine, "it6 construct", 3, it6_construct);
        data_property(machine, construct_handler, "construct", construct);
        let construct_target = it17_native_target(machine);
        let constructable = proxy::create(machine, construct_target, construct_handler).unwrap();
        let instance = machine.construct_value(constructable, &[]).unwrap();
        assert!(machine.is_object(instance));
        let seen = machine
            .get_named_property(construct_handler, "seenNewTarget")
            .unwrap();
        assert_eq!(seen, constructable);
        assert_logged(&IT6, &[OP_CONSTRUCT]);

        let fresh = ordinary_object(machine);
        let (revoked_proxy, revoker) = revocable_pair(machine, callable_target, fresh);
        assert_eq!(
            machine.call_value(revoker, Value::UNDEFINED, &[]).unwrap(),
            Value::UNDEFINED
        );
        assert_eq!(
            machine.call_value(revoker, Value::UNDEFINED, &[]).unwrap(),
            Value::UNDEFINED
        );
        let dead_key = key(machine, "x");
        let dead = machine.internal_get(revoked_proxy, &dead_key, revoked_proxy);
        assert!(is_type_error(&dead), "revoked proxy is dead after one call");
    });

    // Bytecode Call routes through the execute_call proxy arm.
    IT6.reset();
    let program = call_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let callable_target = native(
        &mut machine,
        "it6 call target",
        0,
        |machine, _this, _args, constructing| it6_native_ctor(machine, constructing),
    );
    let handler = ordinary_object(&mut machine);
    let apply = native(&mut machine, "it6 apply 2", 3, it6_apply);
    data_property(&mut machine, handler, "apply", apply);
    let proxy_value = proxy::create(&mut machine, callable_target, handler).unwrap();
    machine.test_set_global("p", proxy_value);
    let execution = machine.evaluate().unwrap();
    assert_eq!(execution.value, Value::int32(1));
    assert_logged(&IT6, &[OP_APPLY]);

    // Bytecode Construct: the trap observes new_target === the proxy.
    IT6.reset();
    let program = construct_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let construct_handler = ordinary_object(&mut machine);
    let construct = native(&mut machine, "it6 construct 2", 3, it6_construct);
    data_property(&mut machine, construct_handler, "construct", construct);
    let construct_target = it17_native_target(&mut machine);
    let constructable = proxy::create(&mut machine, construct_target, construct_handler).unwrap();
    machine.test_set_global("p", constructable);
    let execution = machine.evaluate().unwrap();
    assert_ne!(execution.value, Value::UNDEFINED);
    let seen = machine
        .get_named_property(construct_handler, "seenNewTarget")
        .unwrap();
    assert_eq!(seen, constructable);
    assert_logged(&IT6, &[OP_CONSTRUCT]);
}

fn call_program() -> Program<Verified> {
    verified(
        vec![Constant::String(EcmaString::encode("p"))],
        vec![function(
            0,
            6,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(0),
                },
                Instruction::LoadThis { dst: reg(3) },
                Instruction::CreateArray { dst: reg(1) },
                Instruction::Call {
                    dst: reg(2),
                    callee: reg(0),
                    this_value: reg(3),
                    arguments: reg(1),
                },
                Instruction::Return { value: reg(2) },
            ],
        )],
    )
}

fn construct_program() -> Program<Verified> {
    verified(
        vec![Constant::String(EcmaString::encode("p"))],
        vec![function(
            0,
            5,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(0),
                },
                Instruction::CreateArray { dst: reg(1) },
                Instruction::Construct {
                    dst: reg(2),
                    callee: reg(0),
                    arguments: reg(1),
                },
                Instruction::Return { value: reg(2) },
            ],
        )],
    )
}

// ---------------------------------------------------------------------------
// IT7: instanceof with a proxy right-hand side.
// ---------------------------------------------------------------------------

static IT7_GET: StampLog = StampLog::new();
static IT7_GPO: StampLog = StampLog::new();

#[test]
fn it07_instanceof_proxy_rhs_reads_prototype_and_hops() {
    with_machine(|machine| {
        // The constructor proxy answers the `prototype` get.
        let ctor_handler = ordinary_object(machine);
        let ctor_get = native(
            machine,
            "it7 get",
            3,
            |machine, this, args, _constructing| {
                let is_prototype = machine
                    .string_value(args[1])
                    .is_some_and(|name| name.eq_ascii("prototype"));
                if !is_prototype {
                    return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
                }
                IT7_GET.stamp(OP_GET);
                machine.set_data_property(this, "prototypeSeen", Value::TRUE)?;
                Ok(BuiltinOutcome::Value(
                    machine.get_named_property(this, "proto")?,
                ))
            },
        );
        data_property(machine, ctor_handler, "get", ctor_get);
        let ctor_target = native(
            machine,
            "it7 ctor",
            0,
            |_machine, _this, _args, _constructing| Ok(BuiltinOutcome::Value(Value::UNDEFINED)),
        );
        let ctor = proxy::create(machine, ctor_target, ctor_handler).unwrap();

        // The instance's prototype chain crosses two proxy hops; each hop's
        // [[GetPrototypeOf]] lands on a proxy and fires the trap.
        let terminal = ordinary_object(machine);
        let hop_two_handler = ordinary_object(machine);
        let hop_one_handler = ordinary_object(machine);
        let hop_two_target = ordinary_object(machine);
        let hop_one_target = ordinary_object(machine);
        let hop_two = proxy::create(machine, hop_two_target, hop_two_handler).unwrap();
        let hop_one = proxy::create(machine, hop_one_target, hop_one_handler).unwrap();
        for (handler, next) in [(hop_two_handler, terminal), (hop_one_handler, hop_two)] {
            let gpo = native(
                machine,
                "it7 gpo",
                1,
                |machine, this, _args, _constructing| {
                    IT7_GPO.stamp(OP_GET_PROTO);
                    Ok(BuiltinOutcome::Value(
                        machine.get_named_property(this, "next")?,
                    ))
                },
            );
            data_property(machine, handler, "getPrototypeOf", gpo);
            data_property(machine, handler, "next", next);
        }
        let instance = ordinary_object(machine);
        machine
            .internal_set_prototype_of(instance, Some(hop_one))
            .unwrap();
        data_property(machine, ctor_handler, "proto", terminal);
        // The set-prototype cycle guard walks the new chain; only the
        // instanceof walk itself is under observation here.
        IT7_GPO.reset();

        assert!(machine.instance_of(instance, ctor).unwrap());
        assert_logged(&IT7_GET, &[OP_GET]);
        assert_logged(&IT7_GPO, &[OP_GET_PROTO, OP_GET_PROTO]);
    });
}

// ---------------------------------------------------------------------------
// IT8: super[key] get/set across a proxy home chain keeps the receiver.
// ---------------------------------------------------------------------------

static IT8_GET: StampLog = StampLog::new();
static IT8_SET: StampLog = StampLog::new();

#[test]
fn it08_super_property_proxy_chain_preserves_receiver() {
    with_machine(|machine| {
        let handler = ordinary_object(machine);
        let get = native(
            machine,
            "it8 get",
            3,
            |machine, this, args, _constructing| {
                IT8_GET.stamp(OP_GET);
                machine.set_data_property(this, "seenGetReceiver", args[2])?;
                Ok(BuiltinOutcome::Value(Value::int32(7)))
            },
        );
        data_property(machine, handler, "get", get);
        let set = native(
            machine,
            "it8 set",
            4,
            |machine, this, args, _constructing| {
                IT8_SET.stamp(OP_SET);
                machine.set_data_property(this, "seenSetReceiver", args[3])?;
                Ok(BuiltinOutcome::Value(Value::TRUE))
            },
        );
        data_property(machine, handler, "set", set);
        let fresh = ordinary_object(machine);
        let home_base = proxy::create(machine, fresh, handler).unwrap();

        let home = ordinary_object(machine);
        machine
            .internal_set_prototype_of(home, Some(home_base))
            .unwrap();
        // super_base resolves the home's [[GetPrototypeOf]] — the proxy head.
        let base = machine.super_base(home).unwrap();
        assert_eq!(base, home_base);
        let x = key(machine, "x");
        let receiver = ordinary_object(machine);
        assert_eq!(
            machine.internal_get(base, &x, receiver).unwrap(),
            Value::int32(7)
        );
        let seen_get = machine
            .get_named_property(handler, "seenGetReceiver")
            .unwrap();
        assert_eq!(seen_get, receiver);
        assert!(
            machine
                .internal_set(base, x, Value::int32(9), receiver)
                .unwrap()
        );
        let seen_set = machine
            .get_named_property(handler, "seenSetReceiver")
            .unwrap();
        assert_eq!(seen_set, receiver);
        assert_logged(&IT8_GET, &[OP_GET]);
        assert_logged(&IT8_SET, &[OP_SET]);
    });
}

// ---------------------------------------------------------------------------
// IT9: each Reflect method fires exactly its one named trap.
// ---------------------------------------------------------------------------

static IT9: StampLog = StampLog::new();

/// Generic IT9 trap: the handler object carries `op` (the stamp code) and
/// `reply` (the trap result), because fn-pointer traps cannot capture.
fn it9_trap<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let op = machine.get_named_property(this, "op")?;
    let op = match op.decode() {
        Some(Decoded::Int32(raw)) => raw as usize,
        other => panic!("it9 op must be an int32, got {other:?}"),
    };
    IT9.stamp(op);
    Ok(BuiltinOutcome::Value(
        machine.get_named_property(this, "reply")?,
    ))
}

#[test]
fn it09_each_reflect_method_fires_exactly_one_trap() {
    with_machine(|machine| {
        let callable = native(
            machine,
            "it9 callable",
            0,
            |_machine, _this, _args, _constructing| Ok(BuiltinOutcome::Value(Value::UNDEFINED)),
        );
        let constructable = it17_native_target(machine);

        // Each case gets a fresh proxy whose handler carries only the trap
        // under test; the stamp log must contain exactly that trap.
        struct Case {
            method: &'static str,
            trap: &'static str,
            op: usize,
            reply: Value,
            prep: fn(&mut Machine<'_, TestHost>, Value),
        }
        let nothing = |_: &mut Machine<'_, TestHost>, _: Value| {};
        let cases = [
            Case {
                method: "get",
                trap: "get",
                op: OP_GET,
                reply: Value::TRUE,
                prep: nothing,
            },
            Case {
                method: "set",
                trap: "set",
                op: OP_SET,
                reply: Value::TRUE,
                prep: nothing,
            },
            Case {
                method: "has",
                trap: "has",
                op: OP_HAS,
                reply: Value::TRUE,
                prep: nothing,
            },
            Case {
                method: "deleteProperty",
                trap: "deleteProperty",
                op: OP_DELETE,
                reply: Value::TRUE,
                prep: nothing,
            },
            Case {
                method: "getOwnPropertyDescriptor",
                trap: "getOwnPropertyDescriptor",
                op: OP_GOPD,
                reply: Value::UNDEFINED,
                prep: nothing,
            },
            Case {
                method: "getPrototypeOf",
                trap: "getPrototypeOf",
                op: OP_GET_PROTO,
                reply: Value::NULL,
                prep: nothing,
            },
            Case {
                method: "setPrototypeOf",
                trap: "setPrototypeOf",
                op: OP_SET_PROTO,
                reply: Value::TRUE,
                prep: nothing,
            },
            Case {
                method: "isExtensible",
                trap: "isExtensible",
                op: OP_IS_EXTENSIBLE,
                reply: Value::TRUE,
                prep: nothing,
            },
            Case {
                method: "ownKeys",
                trap: "ownKeys",
                op: OP_OWN_KEYS,
                reply: Value::UNDEFINED,
                prep: nothing,
            },
            Case {
                method: "preventExtensions",
                trap: "preventExtensions",
                op: OP_PREVENT_EXTENSIONS,
                reply: Value::TRUE,
                prep: |machine: &mut Machine<'_, TestHost>, target: Value| {
                    // The trap's true result must agree with the target.
                    machine.internal_prevent_extensions(target).unwrap();
                },
            },
        ];
        for case in cases.iter() {
            IT9.reset();
            let target = ordinary_object(machine);
            (case.prep)(machine, target);
            let handler = ordinary_object(machine);
            data_property(machine, handler, "op", Value::int32(case.op as u32));
            let reply = if case.method == "ownKeys" {
                allocate_array(machine, Vec::new())
            } else {
                case.reply
            };
            data_property(machine, handler, "reply", reply);
            let trap = native(machine, "it9 trap", 1, it9_trap);
            data_property(machine, handler, case.trap, trap);
            let proxy_value = proxy::create(machine, target, handler).unwrap();
            let arg_key = allocate_string(machine, "x");
            let args: Vec<Value> = match case.method {
                "get" => vec![proxy_value, arg_key],
                "set" => vec![proxy_value, arg_key, Value::int32(1)],
                "has" | "deleteProperty" | "getOwnPropertyDescriptor" => vec![proxy_value, arg_key],
                "setPrototypeOf" => vec![proxy_value, Value::NULL],
                "getPrototypeOf" | "isExtensible" | "ownKeys" | "preventExtensions" => {
                    vec![proxy_value]
                }
                other => unreachable!("unexpected Reflect case {other}"),
            };
            let result = reflect(machine, case.method, &args).unwrap();
            if case.method != "ownKeys" {
                let expected = if case.method == "get" {
                    Value::TRUE
                } else {
                    case.reply
                };
                assert_eq!(result, expected, "Reflect.{} result", case.method);
            }
            assert_logged(&IT9, &[case.op]);
        }

        // get returns the trap's value.
        IT9.reset();
        let handler = ordinary_object(machine);
        let get = native(
            machine,
            "it9 get 42",
            3,
            |_machine, _this, _args, _constructing| {
                IT9.stamp(OP_GET);
                Ok(BuiltinOutcome::Value(Value::int32(42)))
            },
        );
        data_property(machine, handler, "get", get);
        let fresh = ordinary_object(machine);
        let proxy_value = proxy::create(machine, fresh, handler).unwrap();
        let arg_key = allocate_string(machine, "x");
        assert_eq!(
            reflect(machine, "get", &[proxy_value, arg_key]).unwrap(),
            Value::int32(42)
        );
        assert_logged(&IT9, &[OP_GET]);

        // getOwnPropertyDescriptor returns the absence the trap reported.
        IT9.reset();
        let handler = ordinary_object(machine);
        let gopd = native(
            machine,
            "it9 gOPD undefined",
            2,
            |_machine, _this, _args, _constructing| {
                IT9.stamp(OP_GOPD);
                Ok(BuiltinOutcome::Value(Value::UNDEFINED))
            },
        );
        data_property(machine, handler, "getOwnPropertyDescriptor", gopd);
        let fresh = ordinary_object(machine);
        let proxy_value = proxy::create(machine, fresh, handler).unwrap();
        let arg_key = allocate_string(machine, "x");
        assert_eq!(
            reflect(machine, "getOwnPropertyDescriptor", &[proxy_value, arg_key]).unwrap(),
            Value::UNDEFINED
        );
        assert_logged(&IT9, &[OP_GOPD]);

        // getPrototypeOf forwards the trap's null.
        IT9.reset();
        let handler = ordinary_object(machine);
        let gpo = native(
            machine,
            "it9 gpo null",
            1,
            |_machine, _this, _args, _constructing| {
                IT9.stamp(OP_GET_PROTO);
                Ok(BuiltinOutcome::Value(Value::NULL))
            },
        );
        data_property(machine, handler, "getPrototypeOf", gpo);
        let fresh = ordinary_object(machine);
        let proxy_value = proxy::create(machine, fresh, handler).unwrap();
        assert_eq!(
            reflect(machine, "getPrototypeOf", &[proxy_value]).unwrap(),
            Value::NULL
        );
        assert_logged(&IT9, &[OP_GET_PROTO]);

        // ownKeys preserves the trap's order verbatim.
        IT9.reset();
        let handler = ordinary_object(machine);
        let own_keys = native(
            machine,
            "it9 ownKeys order",
            1,
            |machine, _this, _args, _constructing| {
                IT9.stamp(OP_OWN_KEYS);
                let b = allocate_string(machine, "b");
                let a = allocate_string(machine, "a");
                Ok(BuiltinOutcome::Value(allocate_array(machine, vec![b, a])))
            },
        );
        data_property(machine, handler, "ownKeys", own_keys);
        let fresh = ordinary_object(machine);
        let proxy_value = proxy::create(machine, fresh, handler).unwrap();
        let keys = reflect(machine, "ownKeys", &[proxy_value]).unwrap();
        let elements = machine.array_elements(keys).unwrap().unwrap();
        let names: Vec<Option<String>> = elements
            .iter()
            .map(|value| key_text(machine, *value))
            .collect();
        assert_eq!(names, vec![Some("b".to_string()), Some("a".to_string())]);
        assert_logged(&IT9, &[OP_OWN_KEYS]);

        // Reflect.apply and Reflect.construct reach their traps exactly once.
        IT9.reset();
        let handler = ordinary_object(machine);
        let apply = native(
            machine,
            "it9 apply",
            3,
            |_machine, _this, _args, _constructing| {
                IT9.stamp(OP_APPLY);
                Ok(BuiltinOutcome::Value(Value::int32(1)))
            },
        );
        data_property(machine, handler, "apply", apply);
        let apply_proxy = proxy::create(machine, callable, handler).unwrap();
        let args_array = allocate_array(machine, Vec::new());
        assert_eq!(
            reflect(
                machine,
                "apply",
                &[apply_proxy, Value::UNDEFINED, args_array]
            )
            .unwrap(),
            Value::int32(1)
        );
        assert_logged(&IT9, &[OP_APPLY]);

        IT9.reset();
        let handler = ordinary_object(machine);
        let construct = native(
            machine,
            "it9 construct",
            3,
            |machine, _this, args, _constructing| {
                IT9.stamp(OP_CONSTRUCT);
                let arguments = machine.array_elements(args[1])?.unwrap_or_default();
                let instance = machine.internal_construct(args[0], &arguments, args[2])?;
                Ok(BuiltinOutcome::Value(instance))
            },
        );
        data_property(machine, handler, "construct", construct);
        let construct_proxy = proxy::create(machine, constructable, handler).unwrap();
        let args_array = allocate_array(machine, Vec::new());
        let constructed = reflect(machine, "construct", &[construct_proxy, args_array]).unwrap();
        assert!(machine.is_object(constructed));
        assert_logged(&IT9, &[OP_CONSTRUCT]);

        // defineProperty: trap true over a frozen fixed property is a fatal
        // invariant violation, not a success.
        IT9.reset();
        let frozen_target = ordinary_object(machine);
        fixed_data_property(machine, frozen_target, "x", Value::int32(1));
        let handler = ordinary_object(machine);
        let define = native(
            machine,
            "it9 define",
            3,
            |_machine, _this, _args, _constructing| {
                IT9.stamp(OP_DEFINE);
                Ok(BuiltinOutcome::Value(Value::TRUE))
            },
        );
        data_property(machine, handler, "defineProperty", define);
        let proxy_value = proxy::create(machine, frozen_target, handler).unwrap();
        let descriptor = ordinary_object(machine);
        data_property(machine, descriptor, "value", Value::int32(999));
        data_property(machine, descriptor, "writable", Value::TRUE);
        data_property(machine, descriptor, "enumerable", Value::TRUE);
        data_property(machine, descriptor, "configurable", Value::TRUE);
        let arg_key = allocate_string(machine, "x");
        let result = reflect(
            machine,
            "defineProperty",
            &[proxy_value, arg_key, descriptor],
        );
        assert!(
            is_type_error(&result),
            "defineProperty true against frozen non-writable data throws"
        );
        assert_logged(&IT9, &[OP_DEFINE]);
    });
}

// ---------------------------------------------------------------------------
// IT10: Reflect reports false where strict paths throw.
// ---------------------------------------------------------------------------

static IT10: StampLog = StampLog::new();

#[test]
fn it10_reflect_reports_false_where_strict_paths_throw() {
    with_machine(|machine| {
        // set trap refusing: Reflect.set yields false, strict writes throw.
        let refusing_handler = ordinary_object(machine);
        let refusing_set = native(
            machine,
            "it10 set false",
            4,
            |_machine, _this, _args, _constructing| {
                IT10.stamp(OP_SET);
                Ok(BuiltinOutcome::Value(Value::FALSE))
            },
        );
        data_property(machine, refusing_handler, "set", refusing_set);
        let fresh = ordinary_object(machine);
        let refusing = proxy::create(machine, fresh, refusing_handler).unwrap();

        let arg_key = allocate_string(machine, "x");
        let reflected = reflect(machine, "set", &[refusing, arg_key, Value::int32(1)]);
        assert_eq!(reflected.unwrap(), Value::FALSE);
        let strict = machine.set_data_property(refusing, "x", Value::int32(1));
        assert!(is_type_error(&strict), "strict assignment throws on false");
        let source = ordinary_object(machine);
        data_property(machine, source, "a", Value::int32(1));
        let assigned = object_static(machine, "assign", &[refusing, source]);
        assert!(is_type_error(&assigned), "Object.assign throws on false");
        assert_logged(&IT10, &[OP_SET, OP_SET, OP_SET]);

        // defineProperty trap refusing: Reflect.defineProperty yields false,
        // it never throws.
        IT10.reset();
        let define_handler = ordinary_object(machine);
        let refusing_define = native(
            machine,
            "it10 define false",
            3,
            |_machine, _this, _args, _constructing| {
                IT10.stamp(OP_DEFINE);
                Ok(BuiltinOutcome::Value(Value::FALSE))
            },
        );
        data_property(machine, define_handler, "defineProperty", refusing_define);
        let fresh = ordinary_object(machine);
        let define_proxy = proxy::create(machine, fresh, define_handler).unwrap();
        let descriptor = ordinary_object(machine);
        data_property(machine, descriptor, "value", Value::int32(1));
        let arg_key = allocate_string(machine, "x");
        let result = reflect(
            machine,
            "defineProperty",
            &[define_proxy, arg_key, descriptor],
        )
        .unwrap();
        assert_eq!(result, Value::FALSE);
        assert_logged(&IT10, &[OP_DEFINE]);
    });
}

// ---------------------------------------------------------------------------
// IT11: Reflect.set with a distinct receiver.
// ---------------------------------------------------------------------------

#[test]
fn it11_reflect_set_receiver_matrix_matches_descriptor_algebra() {
    with_machine(|machine| {
        let fresh1 = ordinary_object(machine);
        let fresh2 = ordinary_object(machine);
        let x = key(machine, "x");
        let proxy_value = proxy::create(machine, fresh1, fresh2).unwrap();
        let arg_key = allocate_string(machine, "x");

        // (a) writable non-configurable data: value updates, attributes stay.
        let receiver = ordinary_object(machine);
        machine
            .define_descriptor(
                receiver,
                x.clone(),
                Property::Data {
                    value: Value::int32(100),
                    writable: true,
                    enumerable: true,
                    configurable: false,
                },
            )
            .unwrap();
        assert_eq!(
            reflect(
                machine,
                "set",
                &[proxy_value, arg_key, Value::int32(7), receiver]
            )
            .unwrap(),
            Value::TRUE
        );
        assert_eq!(
            machine.get_named_property(receiver, "x").unwrap(),
            Value::int32(7)
        );
        let descriptor = machine
            .internal_get_own_property(receiver, &x)
            .unwrap()
            .expect("receiver keeps its own property");
        assert_eq!(descriptor.writable, Some(true));
        assert_eq!(descriptor.configurable, Some(false));
        assert_eq!(descriptor.enumerable, Some(true));

        // (b) non-writable data: false, value untouched.
        let receiver = ordinary_object(machine);
        machine
            .define_descriptor(
                receiver,
                x.clone(),
                Property::Data {
                    value: Value::int32(100),
                    writable: false,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        assert_eq!(
            reflect(
                machine,
                "set",
                &[proxy_value, arg_key, Value::int32(7), receiver]
            )
            .unwrap(),
            Value::FALSE
        );
        assert_eq!(
            machine.get_named_property(receiver, "x").unwrap(),
            Value::int32(100)
        );

        // (c) setterless accessor: false.
        let receiver = ordinary_object(machine);
        let getter = native(
            machine,
            "it11 getter",
            0,
            |_machine, _this, _args, _constructing| Ok(BuiltinOutcome::Value(Value::int32(1))),
        );
        machine
            .define_descriptor(
                receiver,
                x.clone(),
                Property::Accessor {
                    getter: Some(getter),
                    setter: None,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        assert_eq!(
            reflect(
                machine,
                "set",
                &[proxy_value, arg_key, Value::int32(7), receiver]
            )
            .unwrap(),
            Value::FALSE
        );

        // (d) absent property: a fully attributed data property is created.
        let receiver = ordinary_object(machine);
        assert_eq!(
            reflect(
                machine,
                "set",
                &[proxy_value, arg_key, Value::int32(7), receiver]
            )
            .unwrap(),
            Value::TRUE
        );
        let descriptor = machine
            .internal_get_own_property(receiver, &x)
            .unwrap()
            .expect("created property is own");
        match machine
            .own_descriptor(receiver, &x)
            .unwrap()
            .expect("own property present")
        {
            Property::Data {
                value,
                writable,
                enumerable,
                configurable,
            } => {
                assert_eq!(value, Value::int32(7));
                assert!(writable && enumerable && configurable);
            }
            Property::Accessor { .. } => panic!("created property must be data"),
        }
        assert_eq!(descriptor.value, Some(Value::int32(7)));

        // (e) non-object receiver: false.
        for primitive in [Value::NULL, Value::UNDEFINED, Value::int32(1)] {
            assert_eq!(
                reflect(
                    machine,
                    "set",
                    &[proxy_value, arg_key, Value::int32(7), primitive]
                )
                .unwrap(),
                Value::FALSE
            );
        }
    });
}

// ---------------------------------------------------------------------------
// IT12: nested-trap re-entry and mid-trap revocation are safe.
// ---------------------------------------------------------------------------

static IT12: StampLog = StampLog::new();

#[test]
fn it12_nested_trap_reentry_and_midtrap_revocation_are_safe() {
    with_machine(|machine| {
        let handler = ordinary_object(machine);
        let get = native(
            machine,
            "it12 get",
            3,
            |machine, this, args, _constructing| {
                let name = machine.string_value(args[1]);
                if name.is_some_and(|name| name.eq_ascii("y")) {
                    IT12.stamp(OP_INNER);
                    return Ok(BuiltinOutcome::Value(Value::int32(7)));
                }
                IT12.stamp(OP_OUTER);
                // Re-enter the same proxy: no borrow is held across the trap.
                let self_proxy = machine.get_named_property(this, "self")?;
                let y_key = key(machine, "y");
                let inner = machine.internal_get(self_proxy, &y_key, args[2])?;
                assert_eq!(inner, Value::int32(7));
                // Revoke a sibling proxy mid-trap.
                let sibling = machine.get_named_property(this, "sibling")?;
                let revoker = machine.get_named_property(this, "siblingRevoke")?;
                machine.call_value(revoker, Value::UNDEFINED, &[])?;
                IT12.stamp(OP_REVOKED);
                let z_key = key(machine, "z");
                let dead = machine.internal_get(sibling, &z_key, sibling);
                assert!(is_type_error(&dead), "sibling dies mid-trap");
                IT12.stamp(OP_SIBLING_THROWN);
                Ok(BuiltinOutcome::Value(Value::int32(42)))
            },
        );
        data_property(machine, handler, "get", get);
        let fresh = ordinary_object(machine);
        let proxy_value = proxy::create(machine, fresh, handler).unwrap();
        data_property(machine, handler, "self", proxy_value);
        let fresh1 = ordinary_object(machine);
        let fresh2 = ordinary_object(machine);
        let (sibling, sibling_revoker) = revocable_pair(machine, fresh1, fresh2);
        data_property(machine, handler, "sibling", sibling);
        data_property(machine, handler, "siblingRevoke", sibling_revoker);

        let x_key = key(machine, "x");
        let result = machine
            .internal_get(proxy_value, &x_key, proxy_value)
            .unwrap();
        assert_eq!(result, Value::int32(42));
        assert_logged(&IT12, &[OP_OUTER, OP_INNER, OP_REVOKED, OP_SIBLING_THROWN]);
    });
}

// ---------------------------------------------------------------------------
// IT13: the revoker's GC edge keeps the target until revocation.
// ---------------------------------------------------------------------------

#[test]
fn it13_revoker_edge_keeps_target_until_revoke() {
    with_machine(|machine| {
        let target = ordinary_object(machine);
        let fresh = ordinary_object(machine);
        let (_proxy_value, revoker) = revocable_pair(machine, target, fresh);
        // Only the revoker stays rooted (via the global object).
        machine.test_set_global("r", revoker);
        let target_slot = machine.runtime_slot(target).unwrap().unwrap();

        machine.collect_garbage();
        assert!(
            !matches!(machine.heap[target_slot], HeapEntry::Vacant),
            "revoker -> proxy -> target keeps the target alive"
        );

        machine.call_value(revoker, Value::UNDEFINED, &[]).unwrap();
        machine.collect_garbage();
        assert!(
            matches!(machine.heap[target_slot], HeapEntry::Vacant),
            "revocation releases the target for collection"
        );
    });
}

// ---------------------------------------------------------------------------
// IT14: specification-order pins for ownKeys and getOwnPropertyDescriptor.
// ---------------------------------------------------------------------------

static IT14_EXTENSIBLE: StampLog = StampLog::new();
static IT14_OWN_KEYS: StampLog = StampLog::new();
static IT14_GOPD_TARGET: StampLog = StampLog::new();

#[test]
fn it14_spec_order_pins_is_extensible_then_target_keys() {
    with_machine(|machine| {
        // §10.5.11: with the target itself a proxy, IsExtensible on the target
        // must be observed before the target's ownKeys.
        let inner_handler = ordinary_object(machine);
        let inner_ie = native(
            machine,
            "it14 IE",
            1,
            |_machine, _this, _args, _constructing| {
                IT14_EXTENSIBLE.stamp(OP_IS_EXTENSIBLE);
                Ok(BuiltinOutcome::Value(Value::TRUE))
            },
        );
        data_property(machine, inner_handler, "isExtensible", inner_ie);
        let inner_ok = native(
            machine,
            "it14 OK",
            1,
            |machine, _this, _args, _constructing| {
                IT14_OWN_KEYS.stamp(OP_OWN_KEYS);
                Ok(BuiltinOutcome::Value(allocate_array(machine, Vec::new())))
            },
        );
        data_property(machine, inner_handler, "ownKeys", inner_ok);
        let inner_fresh = ordinary_object(machine);
        let inner = proxy::create(machine, inner_fresh, inner_handler).unwrap();

        let outer_handler = ordinary_object(machine);
        let outer_ok = native(
            machine,
            "it14 outer OK",
            1,
            |machine, _this, _args, _constructing| {
                Ok(BuiltinOutcome::Value(allocate_array(machine, Vec::new())))
            },
        );
        data_property(machine, outer_handler, "ownKeys", outer_ok);
        let outer = proxy::create(machine, inner, outer_handler).unwrap();

        let keys = machine.internal_own_property_keys(outer).unwrap();
        assert!(keys.is_empty());
        assert_logged(&IT14_EXTENSIBLE, &[OP_IS_EXTENSIBLE]);
        assert_logged(&IT14_OWN_KEYS, &[OP_OWN_KEYS]);

        // §10.5.5: trap undefined + target descriptor undefined returns early
        // without IsExtensible. The early-return target is itself a proxy
        // whose isExtensible trap would stamp if consulted.
        let probe_handler = ordinary_object(machine);
        let probe_ie = native(
            machine,
            "it14 probe IE",
            1,
            |_machine, _this, _args, _constructing| {
                IT14_GOPD_TARGET.stamp(OP_IS_EXTENSIBLE);
                Ok(BuiltinOutcome::Value(Value::TRUE))
            },
        );
        data_property(machine, probe_handler, "isExtensible", probe_ie);
        let probe_fresh = ordinary_object(machine);
        let probe = proxy::create(machine, probe_fresh, probe_handler).unwrap();
        let early_handler = ordinary_object(machine);
        let early_gopd = native(
            machine,
            "it14 gOPD undefined",
            2,
            |_machine, _this, _args, _constructing| Ok(BuiltinOutcome::Value(Value::UNDEFINED)),
        );
        data_property(
            machine,
            early_handler,
            "getOwnPropertyDescriptor",
            early_gopd,
        );
        let early = proxy::create(machine, probe, early_handler).unwrap();

        let absent_key = key(machine, "x");
        let absent = machine
            .internal_get_own_property(early, &absent_key)
            .unwrap();
        assert!(absent.is_none());
        assert!(IT14_GOPD_TARGET.recorded().is_empty());
    });
}

// ---------------------------------------------------------------------------
// IT15: revoked-proxy TypeError surfaces through bytecode resolve_failure.
// ---------------------------------------------------------------------------

#[test]
fn it15_revoked_proxy_failure_surfaces_through_bytecode() {
    let program = call_program();
    let mut host = TestHost;
    let mut machine = Machine::new(&program, &mut host, Limits::default());
    let callable = native(
        &mut machine,
        "it15 target",
        0,
        |_machine, _this, _args, _constructing| Ok(BuiltinOutcome::Value(Value::UNDEFINED)),
    );
    let fresh = ordinary_object(&mut machine);
    let (proxy_value, revoker) = revocable_pair(&mut machine, callable, fresh);
    machine.call_value(revoker, Value::UNDEFINED, &[]).unwrap();
    machine.test_set_global("p", proxy_value);

    let error = machine.run().unwrap_err();
    assert!(
        matches!(
            error.kind,
            RuntimeErrorKind::UncaughtThrow {
                origin: ThrowOrigin::TypeError { .. },
                ..
            }
        ),
        "revoked call is an uncaught TypeError, got {:?}",
        error.kind
    );
}

// ---------------------------------------------------------------------------
// IT16: constructing a proxy over a non-constructor never fires the trap.
// ---------------------------------------------------------------------------

static IT16_CONSTRUCT: StampLog = StampLog::new();

#[test]
fn it16_non_constructor_proxy_rejects_construct_before_trap() {
    with_machine(|machine| {
        let reflect_get = global_method(machine, "Reflect", "get");
        let prototype_method = machine
            .get_named_property(machine.intrinsics.builtins.array_prototype(), "map")
            .unwrap();
        let getter = native(
            machine,
            "it16 getter",
            0,
            |_machine, _this, _args, _constructing| Ok(BuiltinOutcome::Value(Value::int32(1))),
        );
        let accessor_holder = ordinary_object(machine);
        let x_key = key(machine, "x");
        machine
            .define_descriptor(
                accessor_holder,
                x_key.clone(),
                Property::Accessor {
                    getter: Some(getter),
                    setter: None,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        let accessor = match machine
            .own_descriptor(accessor_holder, &x_key)
            .unwrap()
            .expect("accessor is own")
        {
            Property::Accessor { getter, .. } => getter.expect("getter present"),
            Property::Data { .. } => panic!("expected accessor"),
        };

        for target in [reflect_get, prototype_method, accessor] {
            assert!(!machine.is_constructor(target).unwrap());
            let handler = ordinary_object(machine);
            let construct = native(
                machine,
                "it16 construct",
                3,
                |machine, _this, _args, _constructing| {
                    IT16_CONSTRUCT.stamp(OP_CONSTRUCT);
                    Ok(BuiltinOutcome::Value(ordinary_object(machine)))
                },
            );
            data_property(machine, handler, "construct", construct);
            let proxy_value = proxy::create(machine, target, handler).unwrap();
            assert!(!machine.is_constructor(proxy_value).unwrap());
            let result = machine.construct_value(proxy_value, &[]);
            assert!(
                is_type_error(&result),
                "non-constructable target rejects new before the trap"
            );
            assert!(
                IT16_CONSTRUCT.recorded().is_empty(),
                "the construct trap must never run"
            );
        }
    });
}

// ---------------------------------------------------------------------------
// IT17: constructable targets forward new_target through the proxy.
// ---------------------------------------------------------------------------

static IT17_CONSTRUCT: StampLog = StampLog::new();

fn it17_construct_trap<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    IT17_CONSTRUCT.stamp(OP_CONSTRUCT);
    let arguments = machine.array_elements(args[1])?.unwrap_or_default();
    let global = machine.intrinsics.global("globalThis").unwrap();
    machine.set_data_property(global, "it17NewTarget", args[2])?;
    let instance = machine.internal_construct(args[0], &arguments, args[2])?;
    Ok(BuiltinOutcome::Value(instance))
}

#[test]
fn it17_constructable_targets_forward_new_target_through_proxy() {
    with_machine(|machine| {
        let user_class_prototype = ordinary_object(machine);
        let user_class = machine
            .allocate(HeapEntry::Function {
                module: ModuleId::new(0),
                function: FunctionId::new(1),
                captures: Vec::new(),
                context: None,
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.function_prototype),
                extensible: true,
            })
            .map_err(EvalFailure::Runtime)
            .unwrap();
        let prototype_key = key(machine, "prototype");
        machine
            .define_descriptor(
                user_class,
                prototype_key,
                Property::Data {
                    value: user_class_prototype,
                    writable: true,
                    enumerable: false,
                    configurable: false,
                },
            )
            .unwrap();
        let bound_base = it17_native_target(machine);
        let bind = machine.get_named_property(bound_base, "bind").unwrap();
        let bound = machine
            .call_value(bind, bound_base, &[Value::NULL])
            .unwrap();

        let map = machine.intrinsics.global("Map").unwrap();
        let array_global = machine.intrinsics.global("Array").unwrap();
        for target in [map, array_global, user_class, bound] {
            IT17_CONSTRUCT.reset();
            assert!(machine.is_constructor(target).unwrap());
            let handler = ordinary_object(machine);
            let construct = native(machine, "it17 construct", 3, it17_construct_trap);
            data_property(machine, handler, "construct", construct);
            let proxy_value = proxy::create(machine, target, handler).unwrap();
            assert!(machine.is_constructor(proxy_value).unwrap());

            let instance = machine.construct_value(proxy_value, &[]).unwrap();
            assert!(machine.is_object(instance));
            assert_logged(&IT17_CONSTRUCT, &[OP_CONSTRUCT]);
            let global = machine.intrinsics.global("globalThis").unwrap();
            let seen = machine.get_named_property(global, "it17NewTarget").unwrap();
            assert_eq!(seen, proxy_value, "new_target identity forwards");

            IT17_CONSTRUCT.reset();
            let args_array = allocate_array(machine, Vec::new());
            let constructed = reflect(machine, "construct", &[proxy_value, args_array]).unwrap();
            assert!(machine.is_object(constructed));
            assert_logged(&IT17_CONSTRUCT, &[OP_CONSTRUCT]);
        }
    });
}

// ---------------------------------------------------------------------------
// IT18: constructability sweep over every installed global.
// ---------------------------------------------------------------------------

#[test]
fn it18_constructability_expected_table_sweep() {
    with_machine(|machine| {
        // Expected [[Construct]] presence per installed global, derived from
        // the B1 production registration census: every
        // install_constructor_function site is true; every plain function
        // and namespace object is false.
        const CONSTRUCTABLE: &[&str] = &[
            "Object",
            "Array",
            "ArrayBuffer",
            "Boolean",
            "DataView",
            "Date",
            "Error",
            "EvalError",
            "RangeError",
            "ReferenceError",
            "SyntaxError",
            "TypeError",
            "URIError",
            "AggregateError",
            "SuppressedError",
            "Map",
            "Number",
            "Promise",
            "RegExp",
            "Set",
            "String",
            "WeakMap",
            "WeakRef",
            "WeakSet",
            "Proxy",
            "DisposableStack",
            "AsyncDisposableStack",
            "Int8Array",
            "Uint8Array",
            "Uint8ClampedArray",
            "Int16Array",
            "Uint16Array",
            "Int32Array",
            "Uint32Array",
            "Float16Array",
            "Float32Array",
            "Float64Array",
            "BigInt64Array",
            "BigUint64Array",
            "BigInt",
            "Symbol",
        ];
        const NON_CONSTRUCTABLE: &[&str] = &[
            "Reflect",
            "Math",
            "JSON",
            "Atomics",
            "console",
            "process",
            "globalThis",
            "global",
            "Infinity",
            "NaN",
            "queueMicrotask",
            "parseInt",
            "parseFloat",
            "isNaN",
            "isFinite",
            "encodeURI",
            "encodeURIComponent",
            "decodeURI",
            "decodeURIComponent",
            "escape",
            "unescape",
            "structuredClone",
        ];
        for name in CONSTRUCTABLE {
            let value = machine
                .intrinsics
                .global(name)
                .unwrap_or_else(|| panic!("{name} is installed"));
            assert!(
                machine.is_constructor(value).unwrap(),
                "{name} must be constructable"
            );
        }
        for name in NON_CONSTRUCTABLE {
            let value = machine
                .intrinsics
                .global(name)
                .unwrap_or_else(|| panic!("{name} is installed"));
            assert!(
                !machine.is_constructor(value).unwrap(),
                "{name} must not be constructable"
            );
        }

        // Every function-valued own property of every swept namespace object
        // is a plain method: Reflect, Object, Math, JSON, and Atomics hold no
        // constructors.
        for namespace in ["Reflect", "Object", "Math", "JSON", "Atomics"] {
            let object = machine.intrinsics.global(namespace).unwrap();
            for object_key in machine.internal_own_property_keys(object).unwrap() {
                let property = machine.get_property_key(object, &object_key).unwrap();
                if machine.is_callable(property).unwrap() {
                    assert!(
                        !machine.is_constructor(property).unwrap(),
                        "{namespace} own callable must not be constructable"
                    );
                }
            }
        }
    });
}

// ---------------------------------------------------------------------------
// IT19: proxy dispatch depth matrix.
// ---------------------------------------------------------------------------

#[test]
fn it19_proxy_depth_matrix_is_charged_and_balanced() {
    // The 1500-deep chain recurses deep into the interpreter; give this test a
    // generous native stack.
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(it19_body)
        .expect("depth test thread spawns")
        .join()
        .expect("depth test completes");
}

fn it19_body() {
    macro_rules! assert_depth {
        ($op:expr) => {
            assert!(
                is_call_depth(&$op),
                "proxy entry must depth-fail by kind, got {:?}",
                $op
            );
        };
    }

    // (a) Every proxy entry fails with CallDepthExceeded once the 12-deep
    // chain outruns the 8-frame ceiling.
    let limits = Limits {
        max_call_depth: 8,
        ..Limits::default()
    };
    with_machine_limits(limits, |machine| {
        let target = it17_native_target(machine);
        let chain = transparent_chain(machine, 12, target);
        let x = key(machine, "x");
        let descriptor = PropertyDescriptor {
            value: Some(Value::int32(1)),
            writable: Some(true),
            enumerable: Some(true),
            configurable: Some(true),
            ..PropertyDescriptor::default()
        };
        assert_depth!(machine.internal_get(chain, &x, chain));
        assert_depth!(machine.internal_set(chain, x.clone(), Value::int32(1), chain));
        assert_depth!(machine.internal_delete(chain, &x));
        assert_depth!(machine.internal_has_property(chain, &x));
        assert_depth!(machine.internal_own_property_keys(chain));
        assert_depth!(machine.internal_get_own_property(chain, &x));
        assert_depth!(machine.internal_define_own_property(chain, x.clone(), descriptor));
        assert_depth!(machine.internal_get_prototype_of(chain));
        assert_depth!(machine.internal_set_prototype_of(chain, None));
        assert_depth!(machine.internal_is_extensible(chain));
        assert_depth!(machine.internal_prevent_extensions(chain));
        assert_depth!(machine.call_value(chain, Value::UNDEFINED, &[]));
        assert_depth!(machine.construct_value(chain, &[]));
        // Balanced: the failures released every charged slot.
        assert_eq!(machine.native_depth, 0);
    });

    // raised ceiling the same ~1500-deep chain succeeds (per D6).
    with_machine_limits(Limits::default(), |machine| {
        let target = it17_native_target(machine);
        let chain = transparent_chain(machine, 100, target);
        let x = key(machine, "x");
        let result = machine.internal_get(chain, &x, chain);
        assert!(is_call_depth(&result));
        assert_eq!(machine.native_depth, 0);
    });
    let raised = Limits {
        max_call_depth: 4096,
        ..Limits::default()
    };
    with_machine_limits(raised, |machine| {
        let target = it17_native_target(machine);
        let chain = transparent_chain(machine, 1500, target);
        let x = key(machine, "x");
        assert_eq!(
            machine.internal_get(chain, &x, chain).unwrap(),
            Value::UNDEFINED
        );
        assert_eq!(machine.native_depth, 0);
    });

    // (c) native_depth balance after success, throwing trap, and revocation.
    with_machine(|machine| {
        let handler = ordinary_object(machine);
        let get = native(
            machine,
            "it19 get",
            3,
            |_machine, _this, _args, _constructing| Ok(BuiltinOutcome::Value(Value::int32(1))),
        );
        data_property(machine, handler, "get", get);
        let fresh = ordinary_object(machine);
        let chain = transparent_chain(machine, 3, fresh);
        let x = key(machine, "x");
        let front = proxy::create(machine, chain, handler).unwrap();
        assert_eq!(
            machine.internal_get(front, &x, front).unwrap(),
            Value::int32(1)
        );
        assert_eq!(machine.native_depth, 0);

        let throwing = ordinary_object(machine);
        let throwing_get = native(
            machine,
            "it19 get throw",
            3,
            |_machine, _this, _args, _constructing| {
                Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "it19 trap throw",
                }))
            },
        );
        data_property(machine, throwing, "get", throwing_get);
        let fresh = ordinary_object(machine);
        let throwing_proxy = proxy::create(machine, fresh, throwing).unwrap();
        let result = machine.internal_get(throwing_proxy, &x, throwing_proxy);
        assert!(is_type_error(&result));
        assert_eq!(machine.native_depth, 0);

        let fresh1 = ordinary_object(machine);
        let fresh2 = ordinary_object(machine);
        let (revoked, revoker) = revocable_pair(machine, fresh1, fresh2);
        machine.call_value(revoker, Value::UNDEFINED, &[]).unwrap();
        let dead = machine.internal_get(revoked, &x, revoked);
        assert!(is_type_error(&dead));
        assert_eq!(machine.native_depth, 0);
    });
}
