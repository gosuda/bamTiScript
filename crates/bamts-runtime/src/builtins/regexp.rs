use std::collections::BTreeMap;
use std::ops::Range;
use std::rc::Rc;

use bamts_bytecode::EcmaString;
use bamts_native::Value;

use super::annex_b::record_legacy_match;
use super::regexp_protocol::{flags_getter, test, to_length};
use super::regexp_v::{CompiledV, create_result_property, execution_failure};
use super::string_edge::is_regexp;
use super::{
    allocate_array, allocate_string, define_data, install_constructor_function, install_function,
    type_error, with_roots,
};
use crate::intrinsics::regexp::{Match, canonical_flags};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap};

/// How many compiled patterns the machine keeps. A program's hot loop uses few.
const COMPILE_CACHE_ENTRIES: usize = 8;

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = super::super::ordinary_prototype(heap, builtins.object_prototype());
    let constructor =
        install_constructor_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "RegExp", length: 2, handler: constructor::<H> });
    builtins.set_constructor_prototype(heap, atoms, shapes, constructor, prototype);
    for (name, length, handler) in [
        ("exec", 1, exec::<H> as BuiltinHandler<H>),
        ("test", 1, test::<H>),
        ("toString", 0, to_string::<H>),
    ] {
        let function = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: name, length: length, handler: handler });
        define_data(heap, atoms, shapes, prototype, name, function);
    }
    let source_get = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "get source", length: 0, handler: source_getter::<H> });
    define_getter(heap, atoms, shapes, prototype, "source", source_get);
    let flags_get = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "get flags", length: 0, handler: flags_getter::<H> });
    define_getter(heap, atoms, shapes, prototype, "flags", flags_get);
    super::regexp_protocol::install(heap, atoms, shapes, builtins, prototype, constructor);
    builtins.set_regexp_prototype(prototype);
    globals.insert(EcmaString::encode("RegExp"), constructor);
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let pattern = args.first().copied().unwrap_or(Value::UNDEFINED);
    let flags = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    with_roots(machine, &[pattern, flags], |machine, depth| {
        let pattern_is_regexp = is_regexp(machine, pattern)?;
        let new_target = machine.current_new_target();
        let active = machine
            .intrinsics
            .global("RegExp")
            .expect("RegExp is installed");
        if new_target == Value::UNDEFINED && pattern_is_regexp && flags == Value::UNDEFINED {
            let pattern_constructor = machine.get_named_property(pattern, "constructor")?;
            if pattern_constructor == active {
                return Ok(pattern);
            }
        }
        let (source, flags) = if let Some((source, original)) = regexp_parts(machine, pattern) {
            let flags = if flags == Value::UNDEFINED {
                allocate_string(machine, original)?
            } else {
                flags
            };
            (allocate_string(machine, source)?, flags)
        } else if pattern_is_regexp {
            let source = machine.get_named_property(pattern, "source")?;
            let flags = if flags == Value::UNDEFINED {
                machine.get_named_property(pattern, "flags")?
            } else {
                flags
            };
            (source, flags)
        } else {
            (pattern, flags)
        };
        super::keep_root(machine, depth, source);
        super::keep_root(machine, depth, flags);
        let default_prototype = machine.intrinsics.regexp_prototype();
        let prototype = if new_target == Value::UNDEFINED {
            default_prototype
        } else {
            let candidate = machine.get_named_property(new_target, "prototype")?;
            if machine.is_object(candidate) {
                candidate
            } else {
                default_prototype
            }
        };
        super::keep_root(machine, depth, prototype);
        regexp_initialize(machine, prototype, source, flags)
    })
    .map(BuiltinOutcome::Value)
}

/// `RegExpAlloc` and `RegExpInitialize` together. The two conversions run after
/// the prototype is read, and a bad pattern or flag is a `SyntaxError`.
fn regexp_initialize<H: Host>(
    machine: &mut Machine<'_, H>,
    prototype: Value,
    source: Value,
    flags: Value,
) -> Result<Value, EvalFailure> {
    let pattern = if source == Value::UNDEFINED {
        EcmaString::default()
    } else {
        machine.coerce_string_observable(source)?
    };
    let flags = if flags == Value::UNDEFINED {
        EcmaString::default()
    } else {
        machine.coerce_string_observable(flags)?
    };
    compile(machine, &pattern, &flags)?;
    let properties = initial_regexp_properties(&mut machine.atoms, &mut machine.shapes);
    machine
        .allocate(HeapEntry::RegExp {
            pattern,
            flags,
            properties,
            prototype: Some(prototype),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)
}

/// `RegExpCreate`, for the String methods that take a pattern.
pub(super) fn regexp_create<H: Host>(
    machine: &mut Machine<'_, H>,
    source: Value,
    flags: Value,
) -> Result<Value, EvalFailure> {
    let prototype = machine.intrinsics.regexp_prototype();
    regexp_initialize(machine, prototype, source, flags)
}

fn uses_extended_flags(flags: &EcmaString) -> bool {
    flags
        .as_units()
        .iter()
        .any(|&unit| matches!(unit, 0x0064 | 0x0075 | 0x0076))
}

pub(crate) fn canonical_regexp_flags(flags: &EcmaString) -> EcmaString {
    if uses_extended_flags(flags) {
        super::regexp_v::VFlags::parse(flags)
            .map(|parsed| parsed.canonical())
            .unwrap_or_else(|_| flags.clone())
    } else {
        canonical_flags(flags)
    }
}

pub(super) fn compile<H: Host>(
    machine: &mut Machine<'_, H>,
    pattern: &EcmaString,
    flags: &EcmaString,
) -> Result<Rc<CompiledV>, EvalFailure> {
    let cached = machine
        .regexp_cache
        .iter()
        .position(|(source, options, _)| source == pattern && options == flags);
    if let Some(position) = cached {
        let entry = machine.regexp_cache.remove(position);
        let compiled = Rc::clone(&entry.2);
        machine.regexp_cache.insert(0, entry);
        return Ok(compiled);
    }
    let compiled = Rc::new(super::regexp_v::compile(machine, pattern, flags)?);
    machine.regexp_cache.truncate(COMPILE_CACHE_ENTRIES - 1);
    machine
        .regexp_cache
        .insert(0, (pattern.clone(), flags.clone(), Rc::clone(&compiled)));
    Ok(compiled)
}

/// Build the initial own-property map for a newly constructed RegExp.
/// ECMA-262 §22.2.3.3: only `lastIndex` is an own data property.
/// Called from the constructor, the bytecode literal path, and the native
/// helper path so all three agree by construction.
pub(crate) fn initial_regexp_properties(atoms: &mut crate::AtomTable, shapes: &mut crate::ShapeTable) -> PropertyMap {
    let mut properties = PropertyMap::default();
    properties.insert(
        shapes,
        PropertyKey::Named(atoms.intern_str("lastIndex")),
        Property::Data {
            value: Value::int32(0),
            writable: true,
            enumerable: false,
            configurable: false,
        },
    );
    properties
}

pub(super) fn regexp_parts<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Option<(EcmaString, EcmaString)> {
    let index = machine.runtime_slot(value).ok().flatten()?;
    match &machine.heap[index] {
        HeapEntry::RegExp { pattern, flags, .. } => Some((pattern.clone(), flags.clone())),
        _ => None,
    }
}

/// `RegExpBuiltinExec` up to the point of building a result. `lastIndex` is read
/// first even when it will not be used, and a coercion it triggers can recompile
/// the receiver, so the pattern and flags are read after it.
pub(super) fn execute<H: Host>(
    machine: &mut Machine<'_, H>,
    regexp: Value,
    input: &EcmaString,
) -> Result<Option<Match>, EvalFailure> {
    let incompatible = || type_error("RegExp method called on incompatible receiver");
    regexp_parts(machine, regexp).ok_or_else(incompatible)?;
    let last_index = machine.get_named_property(regexp, "lastIndex")?;
    let last_index = to_length(machine, last_index)?;
    let (pattern, flags) = regexp_parts(machine, regexp).ok_or_else(incompatible)?;
    let compiled = compile(machine, &pattern, &flags)?;
    let engine_flags = compiled.engine_regex().flags();
    let uses_last_index = engine_flags.global || engine_flags.sticky;
    let start = if uses_last_index { last_index } else { 0 };
    let matched = compiled.exec(input, start).map_err(execution_failure)?;
    if let Some(ref matched) = matched {
        record_legacy_match(machine, input, matched)?;
    }
    if uses_last_index {
        let next = matched.as_ref().map_or(0, |value| value.range.end);
        machine.set_data_property(regexp, "lastIndex", crate::number_value(next as f64))?;
    }
    Ok(matched)
}

/// `RegExpBuiltinExec`.
pub(super) fn builtin_exec<H: Host>(
    machine: &mut Machine<'_, H>,
    regexp: Value,
    input: &EcmaString,
) -> Result<Value, EvalFailure> {
    let Some(matched) = execute(machine, regexp, input)? else {
        return Ok(Value::NULL);
    };
    match_array_for(machine, regexp, input, matched)
}

fn exec<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    regexp_parts(machine, this)
        .ok_or_else(|| type_error("RegExp method called on incompatible receiver"))?;
    let input =
        machine.coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    Ok(BuiltinOutcome::Value(builtin_exec(machine, this, &input)?))
}

fn to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !machine.is_object(this) {
        return Err(type_error("RegExp.prototype.toString requires an object"));
    }
    let source = machine.get_named_property(this, "source")?;
    let source = machine.coerce_string_observable(source)?;
    let flags = machine.get_named_property(this, "flags")?;
    let flags = machine.coerce_string_observable(flags)?;
    let mut output = bamts_bytecode::EcmaStringBuilder::new();
    output.push_unit(u16::from(b'/'));
    for &unit in source.as_units() {
        output.push_unit(unit);
    }
    output.push_unit(u16::from(b'/'));
    for &unit in flags.as_units() {
        output.push_unit(unit);
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}

fn source_getter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !machine.is_object(this) {
        return Err(type_error(
            "RegExp.prototype.source getter requires an object",
        ));
    }
    if let Some((pattern, _)) = regexp_parts(machine, this) {
        return Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            canonical_source(&pattern),
        )?));
    }
    if this == machine.intrinsics.regexp_prototype() {
        return Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            EcmaString::encode("(?:)"),
        )?));
    }
    Err(type_error(
        "RegExp.prototype.source getter called on incompatible receiver",
    ))
}

pub(super) fn define_getter(
    heap: &mut [HeapEntry],
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    object: Value,
    name: &str,
    getter: Value,
) {
    let HeapEntry::Object { properties, .. } = &mut heap[super::heap_index(object)] else {
        panic!("accessor target must be an ordinary object");
    };
    properties.insert(
        shapes,
        PropertyKey::Named(atoms.intern_str(name)),
        Property::Accessor {
            getter: Some(getter),
            setter: None,
            enumerable: false,
            configurable: true,
        },
    );
}

pub(super) fn match_array_for<H: Host>(
    machine: &mut Machine<'_, H>,
    regexp: Value,
    input: &EcmaString,
    matched: Match,
) -> Result<Value, EvalFailure> {
    if let Some((pattern, flags)) = regexp_parts(machine, regexp)
        && uses_extended_flags(&flags)
    {
        let compiled = compile(machine, &pattern, &flags)?;
        return super::regexp_v::match_array(machine, input, &compiled, &matched);
    }
    match_array(machine, input, matched)
}

pub(super) fn match_array<H: Host>(
    machine: &mut Machine<'_, H>,
    input: &EcmaString,
    matched: Match,
) -> Result<Value, EvalFailure> {
    let mut values = Vec::with_capacity(matched.captures.len());
    for capture in &matched.captures {
        values.push(match capture {
            Some(range) => allocate_string(machine, slice_units(input, range.clone()))?,
            None => Value::UNDEFINED,
        });
    }
    let array = allocate_array(machine, values)?;
    create_result_property(
        machine,
        array,
        "index",
        crate::number_value(matched.range.start as f64),
    )?;
    let input_value = allocate_string(machine, input.clone())?;
    create_result_property(machine, array, "input", input_value)?;
    if matched.named.is_empty() {
        create_result_property(machine, array, "groups", Value::UNDEFINED)?;
    } else {
        let groups = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: None,
                extensible: true,
                boxed_primitive: None,
            })
            .map_err(EvalFailure::Runtime)?;
        for (name, range) in matched.named {
            let value = match range {
                Some(range) => allocate_string(machine, slice_units(input, range))?,
                None => Value::UNDEFINED,
            };
            create_result_property(machine, groups, &name, value)?;
        }
        create_result_property(machine, array, "groups", groups)?;
    }
    Ok(array)
}

pub(super) fn slice_units(input: &EcmaString, range: Range<usize>) -> EcmaString {
    input.slice_units(range).unwrap_or_default()
}
pub(crate) fn canonical_source(pattern: &EcmaString) -> EcmaString {
    let mut escaped = bamts_bytecode::EcmaStringBuilder::new();
    append_canonical_source(pattern, &mut escaped);
    escaped.finish()
}

fn append_canonical_source(pattern: &EcmaString, output: &mut bamts_bytecode::EcmaStringBuilder) {
    if pattern.is_empty() {
        output.push_utf8("(?:)");
        return;
    }

    let mut previous_was_escape = false;
    let mut in_character_class = false;
    for &unit in pattern.as_units() {
        match unit {
            0x005B if !previous_was_escape => {
                in_character_class = true;
                output.push_unit(unit);
            }
            0x005D if !previous_was_escape => {
                in_character_class = false;
                output.push_unit(unit);
            }
            0x002F if !previous_was_escape && !in_character_class => output.push_utf8("\\/"),
            0x000A => output.push_utf8("\\n"),
            0x000D => output.push_utf8("\\r"),
            0x2028 => output.push_utf8("\\u2028"),
            0x2029 => output.push_utf8("\\u2029"),
            _ => output.push_unit(unit),
        }
        previous_was_escape = unit == 0x005C && !previous_was_escape;
    }
}

#[cfg(test)]
mod tests {
    use bamts_bytecode::{
        AccessorKind, BinaryOp, Constant, ConstantId, Function, FunctionFlags, FunctionId,
        Instruction, Module, ModuleId, Program, ProgramModule, Register, Verified,
    };

    use super::super::test_support::{TestHost, blank_program};
    use super::*;
    use crate::Limits;
    use crate::intrinsics::{BuiltinDef, native_function};

    fn construct_regexp(machine: &mut Machine<'_, TestHost>, pattern: &str, flags: &str) -> Value {
        let constructor = machine.intrinsics.global("RegExp").expect("RegExp exists");
        let pattern = machine
            .allocate(HeapEntry::String(EcmaString::encode(pattern)))
            .unwrap();
        let flags = machine
            .allocate(HeapEntry::String(EcmaString::encode(flags)))
            .unwrap();
        let index = machine.runtime_slot(constructor).unwrap().unwrap();
        let HeapEntry::NativeFunction {
            callable: crate::NativeCallable::Builtin(id),
            ..
        } = machine.heap[index]
        else {
            panic!("RegExp constructor is native")
        };
        let BuiltinOutcome::Value(value) = machine
            .call_builtin(id, Value::UNDEFINED, &[pattern, flags], true)
            .unwrap()
        else {
            panic!("RegExp constructor returns a value")
        };
        value
    }

    #[test]
    fn sticky_last_index_is_a_utf16_code_unit_offset() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "x", "y");
        machine
            .set_data_property(regexp, "lastIndex", Value::int32(2))
            .unwrap();

        let matched = execute(&mut machine, regexp, &EcmaString::encode("😀x"))
            .unwrap()
            .unwrap();

        assert_eq!(matched.range, 2..3);
        assert_eq!(
            machine.get_named_property(regexp, "lastIndex").unwrap(),
            Value::int32(3)
        );
    }

    #[test]
    fn exec_index_after_astral_prefix_is_a_code_unit_offset() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "x", "");
        let input = EcmaString::encode("😀x");
        let matched = execute(&mut machine, regexp, &input).unwrap().unwrap();

        let result = match_array(&mut machine, &input, matched).unwrap();

        assert_eq!(
            machine.get_named_property(result, "index").unwrap(),
            Value::int32(2)
        );
    }

    #[test]
    fn source_escapes_solidus_and_line_terminator() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        for (pattern, expected) in [("/", "\\/"), ("\n", "\\n")] {
            let regexp = construct_regexp(&mut machine, pattern, "");
            let source = machine.get_named_property(regexp, "source").unwrap();
            assert_eq!(
                machine.to_string(source).unwrap(),
                EcmaString::encode(expected)
            );
        }
    }

    /// Builds a program that materializes a RegExp via `Instruction::CreateRegExp`
    /// (the literal bytecode path, which stores the raw pattern with no own
    /// `source` property), reads `.source`, and returns `source === expected`.
    fn literal_source_program(pattern: &str, flags: &str, expected: &str) -> Program<Verified> {
        let mut constants = vec![
            Constant::String(EcmaString::encode(pattern)),
            Constant::String(EcmaString::encode(flags)),
            Constant::String(EcmaString::encode("source")),
            Constant::String(EcmaString::encode(expected)),
        ];
        let name = ConstantId::new(constants.len() as u32);
        constants.push(Constant::String(EcmaString::encode("<test>")));
        let code = Module::new(
            constants,
            vec![Function::new(
                None,
                0,
                0,
                5,
                FunctionFlags::default(),
                vec![
                    Instruction::CreateRegExp {
                        dst: Register::new(0),
                        pattern: ConstantId::new(0),
                        flags: ConstantId::new(1),
                    },
                    Instruction::LoadConst {
                        dst: Register::new(1),
                        constant: ConstantId::new(2),
                    },
                    Instruction::GetProperty {
                        dst: Register::new(2),
                        object: Register::new(0),
                        key: Register::new(1),
                    },
                    Instruction::LoadConst {
                        dst: Register::new(3),
                        constant: ConstantId::new(3),
                    },
                    Instruction::Binary {
                        dst: Register::new(4),
                        op: BinaryOp::StrictEqual,
                        left: Register::new(2),
                        right: Register::new(3),
                    },
                    Instruction::Return {
                        value: Register::new(4),
                    },
                ],
                Vec::new(),
            )],
            FunctionId::new(0),
        )
        .verify()
        .expect("valid test module");
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

    /// Builds a program that materializes a RegExp via `Instruction::CreateRegExp`
    /// (the literal bytecode path) and returns the RegExp value itself, so the
    /// caller can inspect its own properties. Unlike `literal_source_program`,
    /// which returns a boolean comparison, this yields the live heap entry.
    fn literal_regexp_program(pattern: &str, flags: &str) -> Program<Verified> {
        let mut constants = vec![
            Constant::String(EcmaString::encode(pattern)),
            Constant::String(EcmaString::encode(flags)),
        ];
        let name = ConstantId::new(constants.len() as u32);
        constants.push(Constant::String(EcmaString::encode("<test>")));
        let code = Module::new(
            constants,
            vec![Function::new(
                None,
                0,
                0,
                1,
                FunctionFlags::default(),
                vec![
                    Instruction::CreateRegExp {
                        dst: Register::new(0),
                        pattern: ConstantId::new(0),
                        flags: ConstantId::new(1),
                    },
                    Instruction::Return {
                        value: Register::new(0),
                    },
                ],
                Vec::new(),
            )],
            FunctionId::new(0),
        )
        .verify()
        .expect("valid test module");
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

    #[test]
    fn source_and_to_string_preserve_rou3_character_class_solidus() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        for (pattern, source, string) in [
            (
                r"^/users/(?<id>[^/]+)/?$",
                r"^\/users\/(?<id>[^/]+)\/?$",
                r"/^\/users\/(?<id>[^/]+)\/?$/",
            ),
            (
                r"^\/users\/(?<id>[^\/]+)\/?$",
                r"^\/users\/(?<id>[^\/]+)\/?$",
                r"/^\/users\/(?<id>[^\/]+)\/?$/",
            ),
            (r"\/", r"\/", r"/\//"),
        ] {
            let regexp = construct_regexp(&mut machine, pattern, "");
            let source_value = machine.get_named_property(regexp, "source").unwrap();
            assert_eq!(
                machine.to_string(source_value).unwrap(),
                EcmaString::encode(source)
            );

            let BuiltinOutcome::Value(string_value) =
                to_string(&mut machine, regexp, &[], false).unwrap()
            else {
                panic!("RegExp toString returns a value");
            };
            assert_eq!(
                machine.to_string(string_value).unwrap(),
                EcmaString::encode(string)
            );
        }
    }

    #[test]
    fn literal_source_is_canonicalized() {
        // The literal bytecode path (`Instruction::CreateRegExp`) stores the raw
        // pattern and owns no `source` data property, so `.source` must be
        // canonicalized at read time rather than at allocation. A solidus and a
        // line terminator both exercise the shared canonicalizer; the program
        // returns `re.source === expected`, proving the literal path no longer
        // leaks the raw pattern (which would differ from the constructor).
        for (pattern, flags, expected) in [
            ("/", "", "\\/"),
            ("\n", "", "\\n"),
            (
                r"^/users/(?<id>[^/]+)/?$",
                "",
                r"^\/users\/(?<id>[^/]+)\/?$",
            ),
        ] {
            let program = literal_source_program(pattern, flags, expected);
            let mut host = TestHost;
            let execution = Machine::new(&program, &mut host, Limits::default())
                .run()
                .unwrap();
            assert_eq!(execution.value, Value::TRUE);
        }

        // The ASCII fast path (`get_named_property` -> `own_get_ascii`) hits the
        // other source fallback on a `CreateRegExp`-shaped RegExp (empty own
        // properties), confirming both read paths share one canonicalizer.
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let regexp = machine
            .allocate(HeapEntry::RegExp {
                pattern: EcmaString::encode("/"),
                flags: EcmaString::default(),
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.regexp_prototype()),
                extensible: true,
            })
            .unwrap();
        let source = machine.get_named_property(regexp, "source").unwrap();
        assert_eq!(
            machine.to_string(source).unwrap(),
            EcmaString::encode("\\/")
        );
    }

    #[test]
    fn literal_and_constructed_regexp_have_same_own_properties() {
        // ECMA-262 §22.2.6 defines `source` and `flags` as accessor properties
        // on RegExp.prototype, not own data properties on instances. Only
        // `lastIndex` is an own data property (§22.2.3.3). Both construction
        // paths — `new RegExp("x")` via the constructor and `/x/` via
        // `Instruction::CreateRegExp` — must install exactly the own-property
        // map from `initial_regexp_properties`, so the two cannot drift.

        // --- Constructed side: the `new RegExp("x", "i")` path ---
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut constructed_machine = Machine::new(&module, &mut host, Limits::default());
        let constructed = construct_regexp(&mut constructed_machine, "x", "i");
        let constructed_keys = constructed_machine.own_property_keys(constructed).unwrap();

        // --- Literal side: actually execute `Instruction::CreateRegExp` ---
        // `evaluate` (not `run`) keeps the machine alive so the returned
        // RegExp's heap entry can be inspected below.
        let program = literal_regexp_program("x", "i");
        let mut host = TestHost;
        let mut literal_machine = Machine::new(&program, &mut host, Limits::default());
        let execution = literal_machine
            .evaluate()
            .expect("literal program evaluates");
        let literal = execution.value;
        let literal_keys = literal_machine.own_property_keys(literal).unwrap();

        // --- Parity: both paths must produce the same own-property keys ---
        // Atom ids are per-machine, so the comparison runs on resolved text.
        let texts = |machine: &Machine<'_, TestHost>, keys: &[PropertyKey]| {
            keys.iter()
                .map(|key| match key {
                    PropertyKey::Named(atom) => machine.atoms.resolve(*atom).to_utf8_lossy(),
                    _ => String::new(),
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(
            texts(&constructed_machine, &constructed_keys),
            texts(&literal_machine, &literal_keys),
            "new RegExp('x') and /x/ must have the same own-property set"
        );

        // --- Source of truth: both paths must match `initial_regexp_properties`
        // ---
        // Comparing against the shared helper (not a hand-copied duplicate)
        // means the test's expected set drifts with the helper. If a call
        // site stops using the helper, this assertion catches the divergence.
        let expected = initial_regexp_properties(&mut constructed_machine.atoms, &mut constructed_machine.shapes);
        let expected_keys: Vec<PropertyKey> = expected.iter(&constructed_machine.shapes).map(|(k, _)| k.clone()).collect();
        assert_eq!(
            texts(&constructed_machine, &constructed_keys),
            texts(&constructed_machine, &expected_keys),
            "constructor must install exactly `initial_regexp_properties`"
        );
        assert_eq!(
            texts(&literal_machine, &literal_keys),
            texts(&constructed_machine, &expected_keys),
            "CreateRegExp must install exactly `initial_regexp_properties`"
        );

        // --- ECMA-262 oracle: `lastIndex` is the only own data property ---
        // This independent assertion is what makes the test catch mutations
        // to `initial_regexp_properties` itself — if the helper gains a property
        // or flips a descriptor flag, the spec-mandated shape breaks. Under
        // the old hand-copied version a descriptor-only change (e.g. flipping
        // `enumerable`) would have passed silently because only keys were
        // compared.
        assert_eq!(
            texts(&constructed_machine, &constructed_keys),
            ["lastIndex"],
            "ECMA-262 §22.2.3.3: lastIndex is the only own property"
        );

        // Verify the full descriptor on both paths, not just the key set.
        // A descriptor-only mutation (flipping `enumerable`) changes no keys
        // but breaks the spec-mandated attribute.
        for (label, machine, regexp) in [
            ("constructed", &mut constructed_machine, constructed),
            ("literal", &mut literal_machine, literal),
        ] {
            let keys = machine.own_property_keys(regexp).unwrap();
            assert_eq!(
                texts(machine, &keys),
                ["lastIndex"],
                "{label} owns exactly lastIndex"
            );
            let index = machine.runtime_slot(regexp).unwrap().unwrap();
            let HeapEntry::RegExp { properties, .. } = &machine.heap[index] else {
                panic!("{label} is a RegExp");
            };
            let Property::Data {
                value,
                writable,
                enumerable,
                configurable,
            } = properties
                .get(&machine.shapes, &keys[0])
                .unwrap_or_else(|| panic!("{label} owns lastIndex"))
            else {
                panic!("{label} lastIndex is a data property");
            };
            assert_eq!(*value, Value::int32(0), "{label} lastIndex value");
            assert!(*writable, "{label} lastIndex writable");
            assert!(!*enumerable, "{label} lastIndex non-enumerable");
            assert!(!*configurable, "{label} lastIndex non-configurable");
        }

        // Neither should own `source` or `flags` — those are prototype
        // accessors.
        for key in &constructed_keys {
            if let PropertyKey::Named(name) = key {
                let text = constructed_machine.atoms.resolve(*name).to_utf8_lossy();
                assert!(
                    text != "source" && text != "flags",
                    "constructed RegExp must not own '{text}'"
                );
            }
        }
    }

    #[test]
    fn flags_getter_and_to_string_use_canonical_ordering() {
        // The flags accessor must canonicalize the stored flag string into
        // the standard gimsuy order without recompiling the pattern. A
        // regex constructed with out-of-order flags ("mig") must report
        // "gim" — the same output the old compile-based path produced.
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        // "mig" is valid but non-canonical; canonical order is "gim".
        let regexp = construct_regexp(&mut machine, "x", "mig");
        let BuiltinOutcome::Value(flags_value) =
            flags_getter(&mut machine, regexp, &[], false).unwrap()
        else {
            panic!("flags_getter returns a value");
        };
        assert_eq!(
            machine.to_string(flags_value).unwrap(),
            EcmaString::encode("gim"),
            "flags_getter must return flags in canonical gimsuy order"
        );
        let BuiltinOutcome::Value(stringified) =
            to_string(&mut machine, regexp, &[], false).unwrap()
        else {
            panic!("to_string returns a value");
        };
        assert_eq!(
            machine.to_string(stringified).unwrap(),
            EcmaString::encode("/x/gim"),
            "RegExp toString must use canonical flag order"
        );

        // Also verify the full flag set in reverse order ("yusmig") → "gimsuy".
        let all_flags = construct_regexp(&mut machine, "x", "yusmig");
        let BuiltinOutcome::Value(all_value) =
            flags_getter(&mut machine, all_flags, &[], false).unwrap()
        else {
            panic!("flags_getter returns a value");
        };
        assert_eq!(
            machine.to_string(all_value).unwrap(),
            EcmaString::encode("gimsuy"),
            "flags_getter must return all flags in canonical gimsuy order"
        );
    }
    fn throw_prototype_getter<H: Host>(
        _machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(type_error("throwing prototype getter"))
    }

    #[test]
    fn constructor_uses_new_target_prototype() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let regexp_prototype = machine.intrinsics.regexp_prototype();

        // Build a custom prototype that inherits from RegExp.prototype.
        let custom_prototype =
            super::super::ordinary_runtime(&mut machine, Some(regexp_prototype)).unwrap();
        machine
            .set_data_property(custom_prototype, "marker", Value::int32(123))
            .unwrap();

        // Build a new_target with .prototype set to the custom prototype.
        let new_target = super::super::ordinary_runtime(&mut machine, None).unwrap();
        machine
            .set_data_property(new_target, "prototype", custom_prototype)
            .unwrap();

        let regexp_id = machine.intrinsics.builtins.id_named("RegExp").unwrap();
        let BuiltinOutcome::Value(instance) = machine
            .call_builtin_with_new_target(regexp_id, Value::UNDEFINED, &[], true, new_target)
            .unwrap()
        else {
            panic!("RegExp construct returns a value");
        };

        assert_eq!(
            machine.internal_get_prototype_of(instance).unwrap(),
            Some(custom_prototype),
            "subclass instance must inherit the custom prototype"
        );
        assert_eq!(
            machine.get_named_property(instance, "marker").unwrap(),
            Value::int32(123),
            "custom prototype methods must be visible on the instance"
        );
    }

    #[test]
    fn constructor_falls_back_to_default_for_non_object_prototype() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let regexp_prototype = machine.intrinsics.regexp_prototype();

        // A new_target whose .prototype is a primitive must fall back to
        // %RegExp.prototype%.
        let new_target = super::super::ordinary_runtime(&mut machine, None).unwrap();
        machine
            .set_data_property(new_target, "prototype", Value::int32(42))
            .unwrap();

        let regexp_id = machine.intrinsics.builtins.id_named("RegExp").unwrap();
        let BuiltinOutcome::Value(instance) = machine
            .call_builtin_with_new_target(regexp_id, Value::UNDEFINED, &[], true, new_target)
            .unwrap()
        else {
            panic!("RegExp construct returns a value");
        };

        assert_eq!(
            machine.internal_get_prototype_of(instance).unwrap(),
            Some(regexp_prototype),
            "non-object newTarget.prototype must fall back to %RegExp.prototype%"
        );
    }

    #[test]
    fn constructor_propagates_throwing_prototype_getter() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        // Install a getter on new_target.prototype that throws.
        let getter = install_function(&mut machine.heap, &mut machine.atoms, &mut machine.shapes, &mut machine.intrinsics.builtins, crate::intrinsics::BuiltinDef { name: "throwing prototype getter", length: 0, handler: throw_prototype_getter::<TestHost> });
        let new_target = super::super::ordinary_runtime(&mut machine, None).unwrap();
        let prototype_key = PropertyKey::Named(machine.intern_str("prototype"));
        machine
            .define_accessor(new_target, prototype_key, getter, AccessorKind::Getter)
            .unwrap();

        let regexp_id = machine.intrinsics.builtins.id_named("RegExp").unwrap();
        let result = machine.call_builtin_with_new_target(
            regexp_id,
            Value::UNDEFINED,
            &[],
            true,
            new_target,
        );

        assert!(
            matches!(result, Err(EvalFailure::Throw(_))),
            "throwing newTarget.prototype getter must propagate"
        );
    }

    fn call_regexp_method(
        machine: &mut Machine<'_, TestHost>,
        regexp: Value,
        name: &str,
        args: &[Value],
    ) -> Value {
        let method = machine
            .get_named_property(machine.intrinsics.regexp_prototype(), name)
            .unwrap_or_else(|_| panic!("{name} is installed"));
        machine
            .call_value(method, regexp, args)
            .unwrap_or_else(|error| panic!("{name} call failed: {error:?}"))
    }

    fn test_function(
        machine: &mut Machine<'_, TestHost>,
        name: &'static str,
        handler: BuiltinHandler<TestHost>,
    ) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name,
            length: 1,
            handler,
        });
        native_function(&mut machine.heap, &mut machine.atoms, &mut machine.shapes, id, name, 1)
    }

    fn counting_exec_override(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "overrideSeen", Value::boolean(true))?;
        Ok(BuiltinOutcome::Value(Value::NULL))
    }

    #[test]
    fn builtin_exec_does_not_reenter_through_prototype_exec() {
        let module = blank_program("<exec no recurse>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "a", "");
        let input = machine
            .allocate(HeapEntry::String(EcmaString::encode("a")))
            .unwrap();
        let result = call_regexp_method(&mut machine, regexp, "exec", &[input]);
        assert_ne!(result, Value::NULL);
        let capture = machine.get_named_property(result, "0").expect("capture 0");
        assert_eq!(machine.to_string(capture).unwrap(), EcmaString::encode("a"));
    }

    #[test]
    fn test_honours_own_exec_override() {
        let module = blank_program("<test exec override>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let regexp = construct_regexp(&mut machine, "a", "");
        let override_fn = test_function(
            &mut machine,
            "counting exec override",
            counting_exec_override,
        );
        machine
            .set_data_property(regexp, "exec", override_fn)
            .expect("override installed");
        let input = machine
            .allocate(HeapEntry::String(EcmaString::encode("a")))
            .unwrap();
        let result = call_regexp_method(&mut machine, regexp, "test", &[input]);
        assert_eq!(result, Value::boolean(false));
        assert_eq!(
            machine.get_named_property(regexp, "overrideSeen").unwrap(),
            Value::boolean(true)
        );
    }

    #[test]
    fn test_honours_subclass_prototype_exec_override() {
        let module = blank_program("<subclass exec override>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let regexp_prototype = machine.intrinsics.regexp_prototype();
        let custom_prototype =
            super::super::ordinary_runtime(&mut machine, Some(regexp_prototype)).unwrap();
        let override_fn = test_function(
            &mut machine,
            "subclass exec override",
            counting_exec_override,
        );
        machine
            .set_data_property(custom_prototype, "exec", override_fn)
            .expect("prototype override installed");
        let new_target = super::super::ordinary_runtime(&mut machine, None).unwrap();
        machine
            .set_data_property(new_target, "prototype", custom_prototype)
            .expect("subclass prototype wired");
        let regexp_id = machine.intrinsics.builtins.id_named("RegExp").unwrap();
        let BuiltinOutcome::Value(regexp) = machine
            .call_builtin_with_new_target(regexp_id, Value::UNDEFINED, &[], true, new_target)
            .expect("subclass construct succeeds")
        else {
            panic!("expected RegExp instance");
        };
        let input = machine
            .allocate(HeapEntry::String(EcmaString::encode("a")))
            .unwrap();
        let result = call_regexp_method(&mut machine, regexp, "test", &[input]);
        assert_eq!(result, Value::boolean(false));
        assert_eq!(
            machine.get_named_property(regexp, "overrideSeen").unwrap(),
            Value::boolean(true)
        );
    }
}
