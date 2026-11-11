use bamts_bytecode::{
    Constant, ConstantId, EcmaString, Function, FunctionFlags, FunctionId, Instruction, Module,
    ModuleId, Program, ProgramModule, Verified,
};
use bamts_native::{Decoded, Value};

use crate::intrinsics::{BuiltinDef, BuiltinOutcome, native_function};
use crate::{EvalFailure, HeapEntry, Host, Machine, PropertyMap};

#[derive(Default)]
pub(crate) struct TestHost;

impl Host for TestHost {}

pub(super) fn blank_program(name: &str) -> Program<Verified> {
    program(name, FunctionFlags::default())
}

pub(super) fn constructable_program(name: &str) -> Program<Verified> {
    program(
        name,
        FunctionFlags {
            is_constructable: true,
            ..FunctionFlags::default()
        },
    )
}

fn program(name: &str, flags: FunctionFlags) -> Program<Verified> {
    let code = Module::new(
        vec![Constant::String(EcmaString::encode(name))],
        vec![Function::new(
            None,
            0,
            0,
            1,
            flags,
            vec![Instruction::Halt],
            Vec::new(),
        )],
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

pub(crate) fn ordinary_object<H: Host>(machine: &mut Machine<'_, H>) -> Value {
    machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            extensible: true,
            boxed_primitive: None,
        })
        .expect("object allocation succeeds")
}

fn custom_iterator_next<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let values = machine.get_named_property(this, "_values")?;
    let index_val = machine.get_named_property(this, "_index")?;
    let elements = machine.array_elements(values)?.unwrap_or_default();
    let index = match index_val.decode() {
        Some(Decoded::Int32(i)) => i as usize,
        Some(Decoded::Number(n)) => n as usize,
        _ => 0,
    };
    let result = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            extensible: true,
            boxed_primitive: None,
        })
        .map_err(EvalFailure::Runtime)?;
    if index >= elements.len() {
        machine.set_data_property(result, "done", Value::TRUE)?;
        machine.set_data_property(result, "value", Value::UNDEFINED)?;
    } else {
        machine.set_data_property(result, "done", Value::FALSE)?;
        machine.set_data_property(result, "value", elements[index])?;
        machine.set_data_property(this, "_index", Value::int32((index + 1) as u32))?;
    }
    Ok(BuiltinOutcome::Value(result))
}

fn custom_iterator_create<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let iter = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            extensible: true,
            boxed_primitive: None,
        })
        .map_err(EvalFailure::Runtime)?;
    let values = machine.get_named_property(this, "_values")?;
    let next = machine.get_named_property(this, "_next")?;
    machine.set_data_property(iter, "_values", values)?;
    machine.set_data_property(iter, "_index", Value::int32(0))?;
    machine.set_data_property(iter, "next", next)?;
    Ok(BuiltinOutcome::Value(iter))
}

/// Builds an object with a custom `Symbol.iterator` that yields `values` in order.
pub(super) fn custom_iterable<H: Host>(machine: &mut Machine<'_, H>, values: Vec<Value>) -> Value {
    let next_id = machine.intrinsics.builtins.register(BuiltinDef {
        name: "custom next",
        length: 0,
        handler: custom_iterator_next::<H>,
    });
    let next_fn = native_function(&mut machine.heap, &mut machine.atoms, &mut machine.shapes, next_id,
    "custom next",
    0,);
    let create_id = machine.intrinsics.builtins.register(BuiltinDef {
        name: "custom iterator",
        length: 0,
        handler: custom_iterator_create::<H>,
    });
    let create_fn = native_function(&mut machine.heap, &mut machine.atoms, &mut machine.shapes, create_id,
    "custom iterator",
    0,);
    let iterable = ordinary_object(machine);
    let values_array = super::allocate_array(machine, values).expect("array allocation succeeds");
    machine
        .set_data_property(iterable, "_values", values_array)
        .expect("values install succeeds");
    machine
        .set_data_property(iterable, "_next", next_fn)
        .expect("next install succeeds");
    let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
    let iterator_key = machine
        .property_key_from_value(iterator_symbol)
        .expect("Symbol.iterator is a property key");
    machine
        .set_data_property_key(iterable, iterator_key, create_fn)
        .expect("iterator install succeeds");
    iterable
}
