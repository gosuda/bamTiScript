use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, Value};

use crate::intrinsics::{self, BuiltinDef, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap};

pub(crate) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let object_prototype = builtins.object_prototype();
    let console = object(heap, object_prototype);
    for (name, handler) in [
        ("log", console_log::<H> as _),
        ("warn", console_warn::<H> as _),
        ("error", console_error::<H> as _),
        ("debug", console_debug::<H> as _),
        ("info", console_info::<H> as _),
    ] {
        let function = register(
            heap,
            atoms,
            shapes,
            builtins,
            BuiltinDef {
                name,
                length: 0,
                handler,
            },
        );
        put(heap, atoms, shapes, console, name, function);
    }

    let stdout = stream(heap, atoms, shapes, builtins, "stdout", stdout_write::<H>);
    let stderr = stream(heap, atoms, shapes, builtins, "stderr", stderr_write::<H>);
    let env = intrinsics::push(
        heap,
        HeapEntry::ProcessEnv {
            prototype: Some(object_prototype),
            extensible: true,
        },
    );
    let argv = intrinsics::push(
        heap,
        HeapEntry::Array {
            elements: Vec::new(),
            properties: PropertyMap::default(),
            prototype: Some(builtins.array_prototype()),
            extensible: true,
            length_writable: true,
        },
    );
    let versions = object(heap, object_prototype);
    put_text(heap, atoms, shapes, versions, "node", "24.18.0");

    let process = object(heap, object_prototype);
    put(heap, atoms, shapes, process, "stdout", stdout);
    put(heap, atoms, shapes, process, "stderr", stderr);
    put(heap, atoms, shapes, process, "env", env);
    put(heap, atoms, shapes, process, "argv", argv);
    put_text(
        heap,
        atoms,
        shapes,
        process,
        "platform",
        std::env::consts::OS,
    );
    put_text(heap, atoms, shapes, process, "version", "v24.18.0");
    put(heap, atoms, shapes, process, "versions", versions);
    for (name, length, handler) in [
        ("exit", 1, process_exit::<H> as _),
        ("nextTick", 1, process_next_tick::<H> as _),
    ] {
        let function = register(
            heap,
            atoms,
            shapes,
            builtins,
            BuiltinDef {
                name,
                length,
                handler,
            },
        );
        put(heap, atoms, shapes, process, name, function);
    }

    let print_fn = register(
        heap,
        atoms,
        shapes,
        builtins,
        BuiltinDef {
            name: "print",
            length: 1,
            handler: print_fn::<H> as _,
        },
    );
    globals.insert(EcmaString::encode("print"), print_fn);
    globals.insert(EcmaString::encode("console"), console);
    globals.insert(EcmaString::encode("process"), process);

    let global_this = object(heap, object_prototype);
    for (name, value) in globals.iter() {
        if name.eq_ascii("Infinity") {
            crate::intrinsics::builtins::define_frozen_data(
                heap,
                atoms,
                shapes,
                global_this,
                "Infinity",
                *value,
            );
        } else if name.eq_ascii("NaN") {
            crate::intrinsics::builtins::define_frozen_data(
                heap,
                atoms,
                shapes,
                global_this,
                "NaN",
                *value,
            );
        } else if name.eq_ascii("undefined") {
            crate::intrinsics::builtins::define_frozen_data(
                heap,
                atoms,
                shapes,
                global_this,
                "undefined",
                *value,
            );
        } else {
            define_global_data(heap, atoms, shapes, global_this, name.clone(), *value);
        }
    }
    define_global_data(
        heap,
        atoms,
        shapes,
        global_this,
        EcmaString::encode("globalThis"),
        global_this,
    );
    define_global_data(
        heap,
        atoms,
        shapes,
        global_this,
        EcmaString::encode("global"),
        global_this,
    );
    globals.insert(EcmaString::encode("global"), global_this);
    globals.insert(EcmaString::encode("globalThis"), global_this);
}
fn stream<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    builtins: &mut BuiltinTable<H>,
    name: &'static str,
    handler: crate::intrinsics::BuiltinHandler<H>,
) -> Value {
    let stream = object(heap, builtins.object_prototype());
    let write = register(
        heap,
        atoms,
        shapes,
        builtins,
        BuiltinDef {
            name: "write",
            length: 1,
            handler,
        },
    );
    put(heap, atoms, shapes, stream, "write", write);
    put_text(heap, atoms, shapes, stream, "_name", name);
    stream
}

fn register<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    builtins: &mut BuiltinTable<H>,
    definition: BuiltinDef<H>,
) -> Value {
    let id = builtins.register(definition);
    let installed = builtins.get(id);
    intrinsics::native_function(heap, atoms, shapes, id, installed.name, installed.length)
}

fn object(heap: &mut Vec<HeapEntry>, prototype: Value) -> Value {
    intrinsics::push(
        heap,
        HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(prototype),
            boxed_primitive: None,
            extensible: true,
        },
    )
}
fn put(
    heap: &mut [HeapEntry],
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    object: Value,
    name: &str,
    value: Value,
) {
    put_ecma(heap, atoms, shapes, object, EcmaString::encode(name), value);
}

fn define_data(
    heap: &mut [HeapEntry],
    shapes: &mut crate::ShapeTable,
    object: Value,
    key: PropertyKey,
    property: Property,
) {
    let index = heap_index(object);
    let properties = match &mut heap[index] {
        HeapEntry::Object { properties, .. }
        | HeapEntry::Array { properties, .. }
        | HeapEntry::NativeFunction { properties, .. } => properties,
        _ => unreachable!("host object installation target owns properties"),
    };
    properties.insert(shapes, key, property);
}

fn put_ecma(
    heap: &mut [HeapEntry],
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    object: Value,
    name: EcmaString,
    value: Value,
) {
    define_data(
        heap,
        shapes,
        object,
        PropertyKey::Named(atoms.intern(name)),
        Property::Data {
            value,
            writable: true,
            enumerable: true,
            configurable: true,
        },
    );
}

fn define_global_data(
    heap: &mut [HeapEntry],
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    object: Value,
    name: EcmaString,
    value: Value,
) {
    define_data(
        heap,
        shapes,
        object,
        PropertyKey::Named(atoms.intern(name)),
        Property::Data {
            value,
            writable: true,
            enumerable: false,
            configurable: true,
        },
    );
}

fn put_text(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    object: Value,
    name: &str,
    text: &str,
) {
    let value = intrinsics::push(heap, HeapEntry::String(EcmaString::encode(text)));
    put(heap, atoms, shapes, object, name, value);
}

fn heap_index(value: Value) -> usize {
    let Some(Decoded::HeapRef(id)) = value.decode() else {
        unreachable!("installer values are heap references");
    };
    id.slot() as usize - 1
}

fn console_log<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    console_write(machine, args, false)
}

fn console_warn<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    console_write(machine, args, true)
}

fn console_error<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    console_warn(machine, this, args, constructing)
}

fn console_debug<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    console_log(machine, this, args, constructing)
}

fn console_info<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    console_log(machine, this, args, constructing)
}

fn console_write<H: Host>(
    machine: &mut Machine<'_, H>,
    args: &[Value],
    stderr: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let mut line = String::new();
    for (index, value) in args.iter().copied().enumerate() {
        if index != 0 {
            line.push(' ');
        }
        line.push_str(&machine.console_format(value, true, 0)?);
    }
    line.push('\n');
    let line = EcmaString::encode(&line);
    if stderr {
        machine.host.write_stderr(&text_bytes_lossy(&line));
    } else {
        machine.host.write_stdout(&text_bytes_lossy(&line));
    }
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn print_fn<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let text = machine.to_string(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    machine.host.write_stdout(&text_bytes_lossy(&text));
    machine.host.write_stdout(b"\n");
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn stdout_write<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let text = machine.to_string(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    machine.host.write_stdout(&text_bytes_lossy(&text));
    Ok(BuiltinOutcome::Value(Value::TRUE))
}

fn stderr_write<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let text = machine.to_string(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    machine.host.write_stderr(&text_bytes_lossy(&text));
    Ok(BuiltinOutcome::Value(Value::TRUE))
}

fn process_exit<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let code = args
        .first()
        .copied()
        .and_then(Value::as_int32)
        .map_or_else(|| machine.host.exit_code().unwrap_or(0), |raw| raw as i32);
    machine.host.set_exit_code(code);
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn process_next_tick<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let Some((&callback, rest)) = args.split_first() else {
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    };
    machine
        .call_value(callback, Value::UNDEFINED, rest)
        .map(BuiltinOutcome::Value)
}
/// Node's `util.inspect` default `maxArrayLength` — show at most this many
/// elements of an Array or typed array, then append `... N more items`.
/// A `Uint8Array` is a bulk buffer, so unbounded formatting turns a 10 MB
/// log line into hundreds of megabytes of string allocation.
const INSPECT_MAX_ITEMS: usize = 100;

/// Joins formatted element strings, capping at [`INSPECT_MAX_ITEMS`] and
/// appending a `... N more items` marker like Node's `util.inspect`.
fn join_bounded(parts: Vec<String>, total: usize) -> String {
    if total <= INSPECT_MAX_ITEMS {
        parts.join(", ")
    } else {
        let remaining = total - INSPECT_MAX_ITEMS;
        format!("{}, ... {remaining} more items", parts.join(", "))
    }
}

impl<H: Host> Machine<'_, H> {
    fn console_format(
        &self,
        value: Value,
        top_level: bool,
        depth: usize,
    ) -> Result<String, EvalFailure> {
        match value.decode() {
            Some(Decoded::Undefined | Decoded::Uninitialized | Decoded::Hole) | None => {
                Ok("undefined".to_owned())
            }
            Some(Decoded::Null) => Ok("null".to_owned()),
            Some(Decoded::Boolean(value)) => Ok(value.to_string()),
            Some(Decoded::Int32(value)) => Ok((value as i32).to_string()),
            Some(Decoded::Number(value)) => Ok(crate::format_number(value)),
            Some(Decoded::HeapRef(_)) => {
                let index = self
                    .runtime_slot(value)
                    .map_err(EvalFailure::Runtime)?
                    .ok_or(EvalFailure::Runtime(
                        crate::RuntimeErrorKind::InvalidValue { value },
                    ))?;
                match &self.heap[index] {
                    HeapEntry::Vacant => {
                        unreachable!("runtime_slot rejects vacant heap entries")
                    }
                    HeapEntry::String(text) if top_level => Ok(env_value_text_lossy(text)),
                    HeapEntry::String(text) => Ok(quote(text)),
                    HeapEntry::BigInt(text) => Ok(format!("{text}n")),
                    HeapEntry::Symbol { description } => {
                        Ok(format!("Symbol({})", env_value_text_lossy(description)))
                    }
                    HeapEntry::PrivateName { description } => Ok(format!(
                        "PrivateName({})",
                        env_value_text_lossy(description)
                    )),
                    HeapEntry::Array { elements, .. } => {
                        if depth >= 2 {
                            return Ok("[Array]".to_owned());
                        }
                        let total = elements.len();
                        let take = total.min(INSPECT_MAX_ITEMS);
                        let mut parts = Vec::with_capacity(take);
                        for element in &elements[..take] {
                            if *element == Value::HOLE {
                                parts.push("<1 empty item>".to_owned());
                            } else {
                                parts.push(self.console_format(*element, false, depth + 1)?);
                            }
                        }
                        Ok(format!("[ {} ]", join_bounded(parts, total)))
                    }
                    HeapEntry::TypedArray { kind, .. } => {
                        if depth >= 2 {
                            return Ok(format!("[{}]", kind.name()));
                        }
                        let (_, total, values) =
                            crate::intrinsics::builtins::typedarray_all::debug_elements(
                                self,
                                value,
                                INSPECT_MAX_ITEMS,
                            )?;
                        Ok(format!(
                            "{}({}) [ {} ]",
                            kind.name(),
                            total,
                            join_bounded(values, total)
                        ))
                    }
                    HeapEntry::ArrayBuffer { .. } => Ok("[ArrayBuffer]".to_owned()),
                    HeapEntry::SharedArrayBuffer { .. } => Ok("[SharedArrayBuffer]".to_owned()),
                    HeapEntry::DataView { .. } => Ok("[DataView]".to_owned()),
                    HeapEntry::Object { properties, .. }
                    | HeapEntry::Script { properties, .. }
                    | HeapEntry::Date { properties, .. }
                    | HeapEntry::Temporal { properties, .. }
                    | HeapEntry::Intl { properties, .. }
                    | HeapEntry::BuiltinIterator { properties, .. }
                    | HeapEntry::Collection { properties, .. }
                    | HeapEntry::Generator { properties, .. }
                    | HeapEntry::AsyncGenerator { properties, .. }
                    | HeapEntry::AsyncFromSync { properties, .. }
                    | HeapEntry::Promise { properties, .. }
                    | HeapEntry::DisposableStack { properties, .. }
                    | HeapEntry::Timeout { properties, .. } => {
                        if depth >= 2 {
                            return Ok("[Object]".to_owned());
                        }
                        let mut parts = Vec::new();
                        for (key, property) in properties.iter(&self.shapes) {
                            let (
                                PropertyKey::Named(name),
                                Property::Data {
                                    value,
                                    enumerable: true,
                                    ..
                                },
                            ) = (key, property)
                            else {
                                continue;
                            };
                            parts.push(format!(
                                "{}: {}",
                                inspect_key(self.atoms.resolve(*name)),
                                self.console_format(*value, false, depth + 1)?
                            ));
                        }
                        Ok(format!("{{ {} }}", parts.join(", ")))
                    }
                    HeapEntry::Proxy { record } => {
                        let _ = record;
                        if self.is_callable(value)? {
                            Ok("[Function]".to_owned())
                        } else {
                            Ok("{}".to_owned())
                        }
                    }
                    HeapEntry::ProxyRevoker { .. } => Ok("[Function]".to_owned()),
                    HeapEntry::NativeFunction { .. } | HeapEntry::Function { .. } => {
                        Ok("[Function]".to_owned())
                    }
                    HeapEntry::RegExp { pattern, flags, .. } => Ok(format!(
                        "/{}/{}",
                        env_value_text_lossy(pattern),
                        env_value_text_lossy(flags),
                    )),
                    HeapEntry::Iterator { .. }
                    | HeapEntry::ProcessEnv { .. }
                    | HeapEntry::ModuleNamespace { .. }
                    | HeapEntry::ExternalModuleNamespace { .. }
                    | HeapEntry::HashState { .. }
                    | HeapEntry::PromiseResolver { .. }
                    | HeapEntry::PromiseAll { .. }
                    | HeapEntry::AsyncActivation { .. }
                    | HeapEntry::PromiseAllElement { .. }
                    | HeapEntry::WeakRef { .. }
                    | HeapEntry::FinalizationRegistry { .. } => Ok("{}".to_owned()),
                }
            }
        }
    }
}

fn quote(text: &EcmaString) -> String {
    let text = env_value_text_lossy(text);
    let escaped = text.replace('\\', "\\\\").replace('\'', "\\'");
    format!("'{escaped}'")
}

fn inspect_key(key: &EcmaString) -> String {
    let text = env_value_text_lossy(key);
    let mut chars = text.chars();
    let identifier = chars
        .next()
        .is_some_and(|first| first == '_' || first == '$' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch == '$' || ch.is_ascii_alphanumeric());
    if identifier { text } else { quote(key) }
}

pub(crate) fn text_bytes_lossy(text: &EcmaString) -> Vec<u8> {
    text.to_utf8_lossy().into_bytes()
}

pub(crate) fn env_value_text_lossy(text: &EcmaString) -> String {
    text.to_utf8_lossy()
}

#[cfg(test)]
mod tests {
    use bamts_bytecode::{
        Constant, ConstantId, EcmaString, Function, FunctionFlags, FunctionId, Instruction, Module,
        ModuleId, Program, ProgramModule, Verified,
    };
    use bamts_native::Value;

    use crate::{HeapEntry, Host, Limits, Machine, PropertyMap};

    struct TestHost;
    impl Host for TestHost {}

    fn blank_program() -> Program<Verified> {
        let code = Module::new(
            vec![Constant::String(EcmaString::encode("test"))],
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

    fn make_uint8array(machine: &mut Machine<'_, TestHost>, bytes: Vec<u8>) -> Value {
        let byte_length = bytes.len();
        let handle = crate::intrinsics::builtins::arraybuffer::ArrayBufferHandle::allocate(
            machine,
            byte_length,
            None,
        )
        .expect("allocation succeeds");
        handle
            .with_bytes_mut(machine, |target| target.copy_from_slice(&bytes))
            .expect("bytes copy succeeds");
        machine
            .allocate(HeapEntry::TypedArray {
                kind: crate::intrinsics::builtins::typedarray_all::ElementKind::Uint8,
                buffer: handle.value(),
                byte_offset: 0,
                byte_length: crate::intrinsics::builtins::typedarray_all::LengthSlot::Fixed(
                    byte_length,
                ),
                array_length: crate::intrinsics::builtins::typedarray_all::LengthSlot::Fixed(
                    byte_length,
                ),
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.builtins.typed_array_prototype(
                    crate::intrinsics::builtins::typedarray_all::ElementKind::Uint8,
                )),
                extensible: true,
            })
            .expect("allocation succeeds")
    }

    fn make_array(machine: &mut Machine<'_, TestHost>, elements: Vec<Value>) -> Value {
        machine
            .allocate(HeapEntry::Array {
                elements,
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.array_prototype),
                extensible: true,
                length_writable: true,
            })
            .expect("allocation succeeds")
    }

    #[test]
    fn small_uint8array_format_is_unchanged() {
        let program = blank_program();
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let value = make_uint8array(&mut machine, vec![10, 20, 30]);
        assert_eq!(
            machine.console_format(value, true, 0).unwrap(),
            "Uint8Array(3) [ 10, 20, 30 ]"
        );
    }

    #[test]
    fn large_uint8array_format_is_bounded() {
        let program = blank_program();
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let value = make_uint8array(&mut machine, vec![0u8; 150]);
        let formatted = machine.console_format(value, true, 0).unwrap();
        assert!(
            formatted.starts_with("Uint8Array(150) [ "),
            "got: {formatted}"
        );
        assert!(
            formatted.ends_with("... 50 more items ]"),
            "got: {formatted}"
        );
        // 100 shown elements produce 99 inter-element commas plus 1 before the
        // marker — proving only the prefix was formatted, not all 150.
        assert_eq!(formatted.matches(',').count(), 100);
    }

    #[test]
    fn small_array_format_is_unchanged() {
        let program = blank_program();
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let value = make_array(
            &mut machine,
            vec![Value::int32(1), Value::int32(2), Value::int32(3)],
        );
        assert_eq!(
            machine.console_format(value, true, 0).unwrap(),
            "[ 1, 2, 3 ]"
        );
    }

    #[test]
    fn large_array_format_is_bounded() {
        let program = blank_program();
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let elements: Vec<Value> = (0..150).map(|_| Value::int32(0)).collect();
        let value = make_array(&mut machine, elements);
        let formatted = machine.console_format(value, true, 0).unwrap();
        assert!(formatted.starts_with("[ "), "got: {formatted}");
        assert!(
            formatted.ends_with("... 50 more items ]"),
            "got: {formatted}"
        );
        assert_eq!(formatted.matches(',').count(), 100);
    }

    #[test]
    fn exactly_cap_elements_are_not_truncated() {
        let program = blank_program();
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let bytes: Vec<u8> = (0..100u8).collect();
        let value = make_uint8array(&mut machine, bytes);
        let formatted = machine.console_format(value, true, 0).unwrap();
        assert!(!formatted.contains("more items"));
        assert!(formatted.starts_with("Uint8Array(100) [ "));
    }
}
