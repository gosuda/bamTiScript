use std::{collections::BTreeMap, mem};

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, Value};

use crate::intrinsics::{self, BuiltinDef, BuiltinOutcome, BuiltinTable};
use crate::{
    EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap, ThrowOrigin,
};

pub(crate) struct InstalledModule {
    pub(crate) specifier: EcmaString,
    pub(crate) namespace: Value,
    pub(crate) exports: Vec<(EcmaString, Value)>,
    pub(crate) internals: BTreeMap<&'static str, Value>,
}

pub(crate) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    builtins: &mut BuiltinTable<H>,
    object_prototype: Value,
    script_compiler: bool,
) -> Vec<InstalledModule> {
    let util_specifier = EcmaString::encode("node:util");
    let util_namespace = intrinsics::push(
        heap,
        HeapEntry::ExternalModuleNamespace {
            specifier: util_specifier.clone(),
        },
    );
    let parse_args = register(heap, atoms, shapes, builtins, BuiltinDef { name: "parseArgs", length: 0, handler: parse_args::<H> });

    let crypto_specifier = EcmaString::encode("node:crypto");
    let crypto_namespace = intrinsics::push(
        heap,
        HeapEntry::ExternalModuleNamespace {
            specifier: crypto_specifier.clone(),
        },
    );
    let create_hash = register(heap, atoms, shapes, builtins, BuiltinDef { name: "createHash", length: 2, handler: create_hash::<H> });
    let hash_update = register(heap, atoms, shapes, builtins, BuiltinDef { name: "update", length: 2, handler: hash_update::<H> });
    let hash_digest = register(heap, atoms, shapes, builtins, BuiltinDef { name: "digest", length: 1, handler: hash_digest::<H> });

    let mut modules = vec![
        InstalledModule {
            specifier: util_specifier,
            namespace: util_namespace,
            exports: vec![(EcmaString::encode("parseArgs"), parse_args)],
            internals: BTreeMap::new(),
        },
        InstalledModule {
            specifier: crypto_specifier,
            namespace: crypto_namespace,
            exports: vec![(EcmaString::encode("createHash"), create_hash)],
            internals: BTreeMap::from([("hash.update", hash_update), ("hash.digest", hash_digest)]),
        },
    ];
    if script_compiler {
        modules.push(crate::vm::install(heap, atoms, shapes, builtins, object_prototype));
    }
    modules
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

#[derive(Clone, Copy, Eq, PartialEq)]
enum OptionType {
    String,
    Boolean,
}

#[derive(Clone)]
struct OptionSpec {
    kind: OptionType,
    multiple: bool,
    default: Option<Value>,
}

struct ParseConfig {
    args: Vec<String>,
    options: BTreeMap<String, OptionSpec>,
    shorts: BTreeMap<char, String>,
    strict: bool,
    allow_positionals: bool,
    allow_negative: bool,
    tokens: bool,
}

struct ParsedToken {
    kind: &'static str,
    index: usize,
    name: Option<String>,
    raw_name: Option<String>,
    value: Option<String>,
    inline_value: Option<bool>,
}

fn type_error(operation: &'static str) -> EvalFailure {
    EvalFailure::Throw(ThrowOrigin::TypeError { operation })
}

fn strict_host_text(text: &EcmaString, operation: &'static str) -> Result<String, EvalFailure> {
    text.to_utf8_strict().map_err(|_| type_error(operation))
}

fn parse_args<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(type_error("construct util.parseArgs"));
    }
    let config = parse_config(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let mut values = BTreeMap::<String, Value>::new();
    let mut positionals = Vec::new();
    let mut tokens = Vec::new();
    let mut index = 0;
    let mut terminated = false;

    while index < config.args.len() {
        let raw = &config.args[index];
        if !terminated && raw == "--" {
            tokens.push(ParsedToken {
                kind: "option-terminator",
                index,
                name: None,
                raw_name: None,
                value: None,
                inline_value: None,
            });
            terminated = true;
            index += 1;
            continue;
        }
        if !terminated && raw.starts_with("--") && raw.len() > 2 {
            let (raw_name, inline) = raw
                .split_once('=')
                .map_or((raw.as_str(), None), |(name, value)| (name, Some(value)));
            let spelled = &raw_name[2..];
            let negative = config.allow_negative
                && spelled.starts_with("no-")
                && config
                    .options
                    .get(&spelled[3..])
                    .is_some_and(|spec| spec.kind == OptionType::Boolean);
            let name = if negative { &spelled[3..] } else { spelled };
            let spec = config.options.get(name);
            if config.strict && spec.is_none() {
                return Err(type_error("unknown parseArgs option"));
            }
            let kind = spec.map(|spec| spec.kind).unwrap_or_else(|| {
                if inline.is_some() {
                    OptionType::String
                } else {
                    OptionType::Boolean
                }
            });
            let (value, token_value, inline_value) = match kind {
                OptionType::Boolean => {
                    if let Some(text) = inline {
                        if config.strict {
                            return Err(type_error("boolean parseArgs option has a value"));
                        }
                        let text = text.to_owned();
                        (alloc_string(machine, &text)?, Some(text), Some(true))
                    } else {
                        (Value::boolean(!negative), None, None)
                    }
                }
                OptionType::String => {
                    let (text, inline_value) = if let Some(text) = inline {
                        (text.to_owned(), Some(true))
                    } else {
                        index += 1;
                        let Some(text) = config.args.get(index) else {
                            return Err(type_error("string parseArgs option is missing its value"));
                        };
                        if config.strict && text.starts_with('-') {
                            return Err(type_error("ERR_PARSE_ARGS_INVALID_OPTION_VALUE"));
                        }
                        (text.clone(), Some(false))
                    };
                    let value = alloc_string(machine, &text)?;
                    (value, Some(text), inline_value)
                }
            };
            store_option(machine, &mut values, name, spec, value)?;
            tokens.push(ParsedToken {
                kind: "option",
                index: if inline_value == Some(false) {
                    index - 1
                } else {
                    index
                },
                name: Some(name.to_owned()),
                raw_name: Some(raw_name.to_owned()),
                value: token_value,
                inline_value,
            });
            index += 1;
            continue;
        }
        if !terminated && raw.starts_with('-') && raw != "-" {
            let chars: Vec<char> = raw[1..].chars().collect();
            let mut offset = 0;
            while offset < chars.len() {
                let short = chars[offset];
                let Some(name) = config.shorts.get(&short) else {
                    if config.strict {
                        return Err(type_error("unknown parseArgs short option"));
                    }
                    let name = short.to_string();
                    store_option(machine, &mut values, &name, None, Value::TRUE)?;
                    tokens.push(option_token(index, name, format!("-{short}"), None, None));
                    offset += 1;
                    continue;
                };
                let spec = &config.options[name];
                match spec.kind {
                    OptionType::Boolean => {
                        store_option(machine, &mut values, name, Some(spec), Value::TRUE)?;
                        tokens.push(option_token(
                            index,
                            name.clone(),
                            format!("-{short}"),
                            None,
                            None,
                        ));
                        offset += 1;
                    }
                    OptionType::String => {
                        let rest: String = chars[offset + 1..].iter().collect();
                        let (text, inline_value) = if rest.is_empty() {
                            index += 1;
                            let Some(text) = config.args.get(index) else {
                                return Err(type_error(
                                    "string parseArgs option is missing its value",
                                ));
                            };
                            if config.strict && text.starts_with('-') {
                                return Err(type_error("ERR_PARSE_ARGS_INVALID_OPTION_VALUE"));
                            }
                            (text.clone(), false)
                        } else {
                            (rest, true)
                        };
                        let value = alloc_string(machine, &text)?;
                        store_option(machine, &mut values, name, Some(spec), value)?;
                        tokens.push(option_token(
                            if inline_value { index } else { index - 1 },
                            name.clone(),
                            format!("-{short}"),
                            Some(text),
                            Some(inline_value),
                        ));
                        break;
                    }
                }
            }
            index += 1;
            continue;
        }
        if !config.allow_positionals {
            return Err(type_error("unexpected parseArgs positional"));
        }
        positionals.push(raw.clone());
        tokens.push(ParsedToken {
            kind: "positional",
            index,
            name: None,
            raw_name: None,
            value: Some(raw.clone()),
            inline_value: None,
        });
        index += 1;
    }

    for (name, spec) in &config.options {
        if !values.contains_key(name)
            && let Some(default) = spec.default
        {
            values.insert(name.clone(), default);
        }
    }

    let values_object = alloc_object(machine, None)?;
    for (name, value) in values {
        put(machine, values_object, &name, value)?;
    }
    let positionals = alloc_string_array(machine, positionals)?;
    let result = alloc_object(machine, Some(machine.intrinsics.object_prototype))?;
    put(machine, result, "values", values_object)?;
    put(machine, result, "positionals", positionals)?;
    if config.tokens {
        let token_array = alloc_token_array(machine, tokens)?;
        put(machine, result, "tokens", token_array)?;
    }
    Ok(BuiltinOutcome::Value(result))
}

fn parse_config<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<ParseConfig, EvalFailure> {
    let config = if value == Value::UNDEFINED {
        None
    } else {
        Some(object_properties(machine, value)?)
    };
    let property = |name: &str| {
        config
            .as_ref()
            .and_then(|properties| properties.get(name))
            .copied()
    };
    let strict = optional_boolean(machine, property("strict"), true)?;
    let allow_positionals = optional_boolean(machine, property("allowPositionals"), !strict)?;
    let allow_negative = optional_boolean(machine, property("allowNegative"), false)?;
    let tokens = optional_boolean(machine, property("tokens"), false)?;
    let args = match property("args") {
        Some(value) => string_array(machine, value)?,
        None => machine.host.argv().iter().skip(2).cloned().collect(),
    };
    let mut options = BTreeMap::new();
    let mut shorts = BTreeMap::new();
    if let Some(options_value) = property("options") {
        for (name, descriptor) in object_properties(machine, options_value)? {
            let descriptor = object_properties(machine, descriptor)?;
            let kind = match descriptor
                .get("type")
                .and_then(|value| machine.string_text(*value))
            {
                Some(text) if text.eq_ascii("string") => OptionType::String,
                Some(text) if text.eq_ascii("boolean") => OptionType::Boolean,
                _ => {
                    return Err(type_error(
                        "parseArgs option type must be string or boolean",
                    ));
                }
            };
            let multiple = optional_boolean(machine, descriptor.get("multiple").copied(), false)?;
            if let Some(value) = descriptor.get("short").copied() {
                let Some(text) = machine.string_text(value) else {
                    return Err(type_error("parseArgs short option must be a string"));
                };
                let text =
                    strict_host_text(text, "parseArgs short option must be well-formed UTF-16")?;
                let mut chars = text.chars();
                let Some(short) = chars.next().filter(|_| chars.next().is_none()) else {
                    return Err(type_error("parseArgs short option must be one character"));
                };
                if shorts.insert(short, name.clone()).is_some() {
                    return Err(type_error("duplicate parseArgs short option"));
                }
            }
            let default = descriptor
                .get("default")
                .copied()
                .filter(|value| *value != Value::UNDEFINED);
            if let Some(default) = default {
                validate_default(machine, default, kind, multiple)?;
            }
            options.insert(
                name,
                OptionSpec {
                    kind,
                    multiple,
                    default,
                },
            );
        }
    }
    Ok(ParseConfig {
        args,
        options,
        shorts,
        strict,
        allow_positionals,
        allow_negative,
        tokens,
    })
}

fn object_properties<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<BTreeMap<String, Value>, EvalFailure> {
    let Some(index) = machine.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
        return Err(type_error("parseArgs configuration must be an object"));
    };
    let HeapEntry::Object { properties, .. } = &machine.heap[index] else {
        return Err(type_error("parseArgs configuration must be an object"));
    };
    let keys: Vec<PropertyKey> = properties.iter(&machine.shapes).map(|(key, _)| key.clone()).collect();
    let mut result = BTreeMap::new();
    for key in keys {
        let PropertyKey::Named(name) = &key else {
            continue;
        };
        let name = strict_host_text(
            machine.atoms.resolve(*name),
            "parseArgs option name must be well-formed UTF-16",
        )?;
        let property_value = machine.get_property_key(value, &key)?;
        result.insert(name, property_value);
    }
    Ok(result)
}

fn optional_boolean<H: Host>(
    machine: &Machine<'_, H>,
    value: Option<Value>,
    default: bool,
) -> Result<bool, EvalFailure> {
    match value {
        None => Ok(default),
        Some(value) => match value.decode() {
            Some(Decoded::Boolean(value)) => Ok(value),
            _ => {
                let _ = machine;
                Err(type_error(
                    "parseArgs boolean configuration has the wrong type",
                ))
            }
        },
    }
}

fn string_array<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<Vec<String>, EvalFailure> {
    let Some(index) = machine.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
        return Err(type_error("parseArgs args must be a string array"));
    };
    let HeapEntry::Array { elements, .. } = &machine.heap[index] else {
        return Err(type_error("parseArgs args must be a string array"));
    };
    elements
        .iter()
        .map(|value| {
            machine
                .string_text(*value)
                .ok_or_else(|| type_error("parseArgs args must contain strings"))
                .and_then(|text| {
                    strict_host_text(text, "parseArgs args must be well-formed UTF-16")
                })
        })
        .collect()
}

fn validate_default<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
    kind: OptionType,
    multiple: bool,
) -> Result<(), EvalFailure> {
    if multiple {
        let Some(index) = machine.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
            return Err(type_error("parseArgs multiple default must be an array"));
        };
        let HeapEntry::Array { elements, .. } = &machine.heap[index] else {
            return Err(type_error("parseArgs multiple default must be an array"));
        };
        for value in elements {
            validate_scalar(machine, *value, kind)?;
        }
        return Ok(());
    }
    validate_scalar(machine, value, kind)
}

fn validate_scalar<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
    kind: OptionType,
) -> Result<(), EvalFailure> {
    let valid = match kind {
        OptionType::String => machine.string_text(value).is_some(),
        OptionType::Boolean => matches!(value.decode(), Some(Decoded::Boolean(_))),
    };
    valid
        .then_some(())
        .ok_or_else(|| type_error("parseArgs default has the wrong type"))
}

fn store_option<H: Host>(
    machine: &mut Machine<'_, H>,
    values: &mut BTreeMap<String, Value>,
    name: &str,
    spec: Option<&OptionSpec>,
    value: Value,
) -> Result<(), EvalFailure> {
    if !spec.is_some_and(|spec| spec.multiple) {
        values.insert(name.to_owned(), value);
        return Ok(());
    }
    let array = match values.get(name).copied() {
        Some(array) => array,
        None => {
            let array = alloc_array(machine, Vec::new())?;
            values.insert(name.to_owned(), array);
            array
        }
    };
    let index = machine
        .runtime_slot(array)
        .map_err(EvalFailure::Runtime)?
        .expect("allocated array is a runtime slot");
    machine
        .charge_slot(index, std::mem::size_of::<Value>())
        .map_err(EvalFailure::Runtime)?;
    let HeapEntry::Array { elements, .. } = &mut machine.heap[index] else {
        unreachable!()
    };
    elements.push(value);
    Ok(())
}

fn option_token(
    index: usize,
    name: String,
    raw_name: String,
    value: Option<String>,
    inline_value: Option<bool>,
) -> ParsedToken {
    ParsedToken {
        kind: "option",
        index,
        name: Some(name),
        raw_name: Some(raw_name),
        value,
        inline_value,
    }
}

fn alloc_token_array<H: Host>(
    machine: &mut Machine<'_, H>,
    tokens: Vec<ParsedToken>,
) -> Result<Value, EvalFailure> {
    let mut values = Vec::with_capacity(tokens.len());
    for token in tokens {
        let object = alloc_object(machine, Some(machine.intrinsics.object_prototype))?;
        let kind = alloc_string(machine, token.kind)?;
        put(machine, object, "kind", kind)?;
        put(
            machine,
            object,
            "index",
            crate::number_value(token.index as f64),
        )?;
        if let Some(name) = token.name {
            let name = alloc_string(machine, &name)?;
            put(machine, object, "name", name)?;
        }
        if let Some(raw_name) = token.raw_name {
            let raw_name = alloc_string(machine, &raw_name)?;
            put(machine, object, "rawName", raw_name)?;
        }
        if token.kind == "option" {
            let value = token
                .value
                .as_deref()
                .map_or(Ok(Value::UNDEFINED), |text| alloc_string(machine, text))?;
            put(machine, object, "value", value)?;
            put(
                machine,
                object,
                "inlineValue",
                token.inline_value.map_or(Value::UNDEFINED, Value::boolean),
            )?;
        } else if token.kind == "positional" {
            let value = alloc_string(
                machine,
                token.value.as_deref().expect("positional token has value"),
            )?;
            put(machine, object, "value", value)?;
        }
        values.push(object);
    }
    alloc_array(machine, values)
}

fn alloc_string_array<H: Host>(
    machine: &mut Machine<'_, H>,
    values: Vec<String>,
) -> Result<Value, EvalFailure> {
    let values = values
        .into_iter()
        .map(|value| alloc_string(machine, &value))
        .collect::<Result<Vec<_>, _>>()?;
    alloc_array(machine, values)
}

fn alloc_string<H: Host>(machine: &mut Machine<'_, H>, value: &str) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::String(EcmaString::encode(value)))
        .map_err(EvalFailure::Runtime)
}

fn alloc_array<H: Host>(
    machine: &mut Machine<'_, H>,
    elements: Vec<Value>,
) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::Array {
            elements,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.array_prototype),
            extensible: true,
            length_writable: true,
        })
        .map_err(EvalFailure::Runtime)
}

fn alloc_object<H: Host>(
    machine: &mut Machine<'_, H>,
    prototype: Option<Value>,
) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype,
            boxed_primitive: None,
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)
}

fn put<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    name: &str,
    value: Value,
) -> Result<(), EvalFailure> {
    let key = PropertyKey::Named(machine.intern_str(name));
    let index = machine
        .runtime_slot(object)
        .map_err(EvalFailure::Runtime)?
        .expect("new object is a runtime slot");
    let properties = match &mut machine.heap[index] {
        HeapEntry::Object { properties, .. } | HeapEntry::Array { properties, .. } => properties,
        _ => unreachable!("external module result is object-like"),
    };
    properties.insert(
        &mut machine.shapes,
        key,
        Property::Data {
            value,
            writable: true,
            enumerable: true,
            configurable: true,
        },
    );
    Ok(())
}

fn create_hash<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing || args.get(1).is_some_and(|value| *value != Value::UNDEFINED) {
        return Err(type_error("unsupported crypto.createHash options"));
    }
    let Some(algorithm) = args
        .first()
        .and_then(|value| machine.string_text(*value))
        .map(|text| {
            strict_host_text(
                text,
                "crypto.createHash algorithm must be well-formed UTF-16",
            )
        })
        .transpose()?
    else {
        return Err(type_error("crypto.createHash algorithm must be a string"));
    };
    if machine.host.hash(&algorithm, &[]).is_none() {
        return Err(type_error("unsupported hash algorithm"));
    }
    let crypto = machine
        .registry
        .external
        .iter()
        .find_map(|(specifier, module)| specifier.eq_ascii("node:crypto").then_some(module))
        .expect("node:crypto is installed");
    let update = crypto.internals["hash.update"];
    let digest = crypto.internals["hash.digest"];
    let value = machine
        .allocate(HeapEntry::HashState {
            algorithm,
            data: Vec::new(),
            digested: false,
            update,
            digest,
        })
        .map_err(EvalFailure::Runtime)?;
    Ok(BuiltinOutcome::Value(value))
}

fn hash_update<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(type_error("construct hash.update"));
    }
    let Some(text) = args
        .first()
        .and_then(|value| machine.string_text(*value))
        .map(EcmaString::to_utf8_lossy)
    else {
        return Err(type_error("hash.update data must be a string"));
    };
    let encoding = match args.get(1).copied() {
        None | Some(Value::UNDEFINED) => "utf8".to_owned(),
        Some(value) => machine
            .string_text(value)
            .ok_or_else(|| type_error("hash.update encoding must be a string"))
            .and_then(|text| strict_host_text(text, "hash.update encoding must be ASCII"))?,
    };
    let bytes = decode_input(&text, &encoding)?;
    let Some(index) = machine.runtime_slot(this).map_err(EvalFailure::Runtime)? else {
        return Err(type_error("invalid hash receiver"));
    };
    let HeapEntry::HashState { digested, .. } = &machine.heap[index] else {
        return Err(type_error("invalid hash receiver"));
    };
    if *digested {
        return Err(type_error("hash already digested"));
    }
    machine
        .charge_slot(index, bytes.len())
        .map_err(EvalFailure::Runtime)?;
    let HeapEntry::HashState { data, .. } = &mut machine.heap[index] else {
        unreachable!()
    };
    data.extend_from_slice(&bytes);
    Ok(BuiltinOutcome::Value(this))
}

fn hash_digest<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(type_error("construct hash.digest"));
    }
    let Some(encoding) = args
        .first()
        .and_then(|value| machine.string_text(*value))
        .map(|text| strict_host_text(text, "hash.digest encoding must be ASCII"))
        .transpose()?
    else {
        return Err(type_error(
            "hash.digest without a string encoding is unsupported",
        ));
    };
    validate_output_encoding(&encoding)?;
    let Some(index) = machine.runtime_slot(this).map_err(EvalFailure::Runtime)? else {
        return Err(type_error("invalid hash receiver"));
    };
    let (algorithm, data) = match &mut machine.heap[index] {
        HeapEntry::HashState {
            algorithm,
            data,
            digested,
            ..
        } => {
            if *digested {
                return Err(type_error("hash already digested"));
            }
            *digested = true;
            (algorithm.clone(), mem::take(data))
        }
        _ => return Err(type_error("invalid hash receiver")),
    };
    machine.refund_slot(index, data.len());
    let digest = machine
        .host
        .hash(&algorithm, &data)
        .ok_or_else(|| type_error("unsupported hash algorithm"))?;
    let encoded = encode_output(&digest, &encoding);
    Ok(BuiltinOutcome::Value(alloc_string(machine, &encoded)?))
}

fn decode_input(text: &str, encoding: &str) -> Result<Vec<u8>, EvalFailure> {
    match encoding.to_ascii_lowercase().as_str() {
        "utf8" | "utf-8" => Ok(text.as_bytes().to_vec()),
        "hex" => decode_hex(text),
        "base64" => decode_base64(text, false),
        "base64url" => decode_base64(text, true),
        _ => Err(type_error("unsupported hash input encoding")),
    }
}

fn validate_output_encoding(encoding: &str) -> Result<(), EvalFailure> {
    match encoding.to_ascii_lowercase().as_str() {
        "hex" | "base64" | "base64url" => Ok(()),
        _ => Err(type_error("unsupported hash digest encoding")),
    }
}

fn encode_output(bytes: &[u8], encoding: &str) -> String {
    match encoding.to_ascii_lowercase().as_str() {
        "hex" => bytes.iter().map(|byte| format!("{byte:02x}")).collect(),
        "base64" => encode_base64(bytes, false),
        "base64url" => encode_base64(bytes, true),
        _ => unreachable!("output encoding was validated"),
    }
}

fn decode_hex(text: &str) -> Result<Vec<u8>, EvalFailure> {
    if !text.is_ascii() || !text.len().is_multiple_of(2) {
        return Err(type_error("invalid hexadecimal hash input"));
    }
    text.as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let digits = std::str::from_utf8(pair)
                .map_err(|_| type_error("invalid hexadecimal hash input"))?;
            u8::from_str_radix(digits, 16).map_err(|_| type_error("invalid hexadecimal hash input"))
        })
        .collect()
}

fn encode_base64(bytes: &[u8], url: bool) -> String {
    let alphabet = if url {
        b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
    } else {
        b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
    };
    let mut output = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for chunk in bytes.chunks(3) {
        let value = (u32::from(chunk[0]) << 16)
            | (u32::from(*chunk.get(1).unwrap_or(&0)) << 8)
            | u32::from(*chunk.get(2).unwrap_or(&0));
        output.push(alphabet[((value >> 18) & 63) as usize] as char);
        output.push(alphabet[((value >> 12) & 63) as usize] as char);
        if chunk.len() > 1 {
            output.push(alphabet[((value >> 6) & 63) as usize] as char);
        } else if !url {
            output.push('=');
        }
        if chunk.len() > 2 {
            output.push(alphabet[(value & 63) as usize] as char);
        } else if !url {
            output.push('=');
        }
    }
    output
}

fn decode_base64(text: &str, _url: bool) -> Result<Vec<u8>, EvalFailure> {
    let mut sextets = Vec::new();
    for byte in text.bytes() {
        if byte == b'=' {
            break;
        }
        let value = match byte {
            b'A'..=b'Z' => byte - b'A',
            b'a'..=b'z' => byte - b'a' + 26,
            b'0'..=b'9' => byte - b'0' + 52,
            b'+' => 62,
            b'/' => 63,
            b'-' => 62,
            b'_' => 63,
            b'\r' | b'\n' | b' ' | b'\t' => continue,
            _ => return Err(type_error("invalid base64 hash input")),
        };
        sextets.push(value);
    }
    if sextets.len() % 4 == 1 {
        return Err(type_error("invalid base64 hash input"));
    }
    let mut output = Vec::with_capacity(sextets.len() * 3 / 4);
    for chunk in sextets.chunks(4) {
        let value = (u32::from(chunk[0]) << 18)
            | (u32::from(*chunk.get(1).unwrap_or(&0)) << 12)
            | (u32::from(*chunk.get(2).unwrap_or(&0)) << 6)
            | u32::from(*chunk.get(3).unwrap_or(&0));
        output.push((value >> 16) as u8);
        if chunk.len() > 2 {
            output.push((value >> 8) as u8);
        }
        if chunk.len() > 3 {
            output.push(value as u8);
        }
    }
    Ok(output)
}

#[cfg(test)]
mod tests {
    use bamts_bytecode::{
        Binding, BindingKind, Constant, ConstantId, Edge, EdgeId, EdgeKind, EdgeTarget, Function,
        FunctionFlags, FunctionId, Instruction, Module, ModuleId, Program, ProgramModule, Register,
        Verified,
    };
    use bamts_native::{AbiError, Completion, CompletionTag, NativeEntryTable, ShadowFrame};

    use super::*;
    use crate::{Limits, NativeEngine, RuntimeErrorKind};

    #[derive(Default)]
    struct EchoHost;

    impl Host for EchoHost {
        fn hash(&mut self, algorithm: &str, data: &[u8]) -> Option<Vec<u8>> {
            (algorithm == "echo").then(|| data.to_vec())
        }
    }

    struct NoEntries;

    impl NativeEntryTable for NoEntries {
        fn program_bytes(&self) -> &[u8] {
            &[]
        }

        fn invoke(
            &self,
            module_id: u32,
            function_id: u32,
            _frame: &mut ShadowFrame,
            _out: &mut Completion,
        ) -> Result<CompletionTag, AbiError> {
            Err(AbiError::UnknownFunction {
                module_id,
                function_id,
            })
        }
    }

    fn reg(value: u32) -> Register {
        Register::new(value)
    }

    fn cid(value: u32) -> ConstantId {
        ConstantId::new(value)
    }

    fn function(registers: u32, code: Vec<Instruction>) -> Function {
        Function::new(
            None,
            0,
            0,
            registers,
            FunctionFlags::default(),
            code,
            Vec::new(),
        )
    }

    fn program(
        constants: Vec<Constant>,
        function: Function,
        edges: Vec<Edge>,
        bindings: Vec<Binding>,
    ) -> Program<Verified> {
        let code = Module::new(constants, vec![function], FunctionId::new(0))
            .verify()
            .expect("external-module fixture verifies");
        Program::link(
            vec![ProgramModule {
                name: cid(0),
                code,
                edges,
                bindings,
                exports: Vec::new(),
            }],
            ModuleId::new(0),
        )
        .expect("external-module fixture links")
    }

    fn external_edge(specifier: u32) -> Edge {
        Edge {
            specifier: cid(specifier),
            target: EdgeTarget::External,
            kind: EdgeKind::Static,
        }
    }

    fn machine_value(machine: &Machine<'_, EchoHost>, object: Value, name: &str) -> Value {
        let index = machine
            .runtime_slot(object)
            .expect("valid runtime value")
            .expect("object has a runtime slot");
        machine
            .own_data_property(index, name)
            .unwrap_or(Value::UNDEFINED)
    }

    fn array_values(machine: &Machine<'_, EchoHost>, value: Value) -> Vec<Value> {
        let index = machine.runtime_slot(value).unwrap().unwrap();
        let HeapEntry::Array { elements, .. } = &machine.heap[index] else {
            panic!("expected array")
        };
        elements.clone()
    }

    fn text(machine: &Machine<'_, EchoHost>, value: Value) -> String {
        machine
            .string_text(value)
            .expect("expected string")
            .to_utf8_strict()
            .expect("test string is well-formed UTF-16")
    }

    fn call_parse_args(
        machine: &mut Machine<'_, EchoHost>,
        config: Value,
    ) -> Result<Value, EvalFailure> {
        let BuiltinOutcome::Value(value) = parse_args(machine, Value::UNDEFINED, &[config], false)?
        else {
            unreachable!()
        };
        Ok(value)
    }

    fn descriptor(
        machine: &mut Machine<'_, EchoHost>,
        kind: &str,
        short: Option<&str>,
        multiple: bool,
        default: Option<Value>,
    ) -> Value {
        let object = alloc_object(machine, Some(machine.intrinsics.object_prototype)).unwrap();
        let kind = alloc_string(machine, kind).unwrap();
        put(machine, object, "type", kind).unwrap();
        if let Some(short) = short {
            let short = alloc_string(machine, short).unwrap();
            put(machine, object, "short", short).unwrap();
        }
        if multiple {
            put(machine, object, "multiple", Value::TRUE).unwrap();
        }
        if let Some(default) = default {
            put(machine, object, "default", default).unwrap();
        }
        object
    }

    fn config(
        machine: &mut Machine<'_, EchoHost>,
        args: &[&str],
        descriptors: &[(&str, Value)],
        flags: &[(&str, bool)],
    ) -> Value {
        let config = alloc_object(machine, Some(machine.intrinsics.object_prototype)).unwrap();
        let args = alloc_string_array(machine, args.iter().map(|arg| (*arg).to_owned()).collect())
            .unwrap();
        put(machine, config, "args", args).unwrap();
        let options = alloc_object(machine, Some(machine.intrinsics.object_prototype)).unwrap();
        for (name, descriptor) in descriptors {
            put(machine, options, name, *descriptor).unwrap();
        }
        put(machine, config, "options", options).unwrap();
        for (name, enabled) in flags {
            put(machine, config, name, Value::boolean(*enabled)).unwrap();
        }
        config
    }

    fn blank_program() -> Program<Verified> {
        program(
            vec![Constant::String(EcmaString::encode("main"))],
            function(0, vec![Instruction::Halt]),
            Vec::new(),
            Vec::new(),
        )
    }

    #[test]
    fn named_default_and_namespace_imports_share_external_cells() {
        let program = program(
            vec![
                Constant::String(EcmaString::encode("main")),
                Constant::String(EcmaString::encode("node:util")),
                Constant::String(EcmaString::encode("parseArgs")),
                Constant::String(EcmaString::encode("default")),
                Constant::String(EcmaString::encode("util")),
            ],
            function(1, vec![Instruction::Halt]),
            vec![external_edge(1)],
            vec![
                Binding {
                    name: cid(2),
                    kind: BindingKind::Imported {
                        edge: EdgeId::new(0),
                        name: cid(2),
                    },
                },
                Binding {
                    name: cid(3),
                    kind: BindingKind::Imported {
                        edge: EdgeId::new(0),
                        name: cid(3),
                    },
                },
                Binding {
                    name: cid(4),
                    kind: BindingKind::Namespace {
                        edge: EdgeId::new(0),
                    },
                },
            ],
        );
        let mut host = EchoHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        machine.instantiate_modules().unwrap();
        let bindings = &machine.registry.modules[0].binding_cells;
        let named = machine.registry.cells[bindings[0].unwrap().0].value;
        let default = machine.registry.cells[bindings[1].unwrap().0].value;
        let namespace = machine.registry.cells[bindings[2].unwrap().0].value;
        assert_eq!(default, namespace);
        let namespace_index = machine.runtime_slot(namespace).unwrap().unwrap();
        let parse_args_key = PropertyKey::Named(machine.intern_str("parseArgs"));
        assert!(matches!(
            machine.own_get(namespace_index, &parse_args_key),
            Some(crate::Found::Value(value)) if value == named
        ));
    }

    #[test]
    fn unknown_external_module_keeps_typed_runtime_error() {
        let program = program(
            vec![
                Constant::String(EcmaString::encode("main")),
                Constant::String(EcmaString::encode("node:missing")),
            ],
            function(0, vec![Instruction::Halt]),
            vec![external_edge(1)],
            Vec::new(),
        );
        let mut host = EchoHost;
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
    fn node_globals_share_identity_and_report_pinned_version() {
        let program = blank_program();
        let mut host = EchoHost;
        let machine = Machine::new(&program, &mut host, Limits::default());
        let global = machine.intrinsics.global("global").unwrap();
        let global_this = machine.intrinsics.global("globalThis").unwrap();
        assert_eq!(global, global_this);
        let process = machine.intrinsics.global("process").unwrap();
        assert_eq!(
            text(&machine, machine_value(&machine, process, "version")),
            "v24.18.0"
        );
        let versions = machine_value(&machine, process, "versions");
        assert_eq!(
            text(&machine, machine_value(&machine, versions, "node")),
            "24.18.0"
        );
    }

    #[test]
    fn parse_args_reads_own_accessors_through_vm_get() {
        let program = blank_program();
        let mut host = EchoHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let config = config(&mut machine, &["positional"], &[], &[]);
        let boolean = machine.intrinsics.global("Boolean").unwrap();
        let index = machine.runtime_slot(config).unwrap().unwrap();
        let strict_key = PropertyKey::Named(machine.intern_str("strict"));
        let HeapEntry::Object { properties, .. } = &mut machine.heap[index] else {
            unreachable!()
        };
        properties.insert(
            &mut machine.shapes,
            strict_key,
            Property::Accessor {
                getter: Some(boolean),
                setter: None,
                enumerable: true,
                configurable: true,
            },
        );

        let result = call_parse_args(&mut machine, config).unwrap();
        let positionals = array_values(&machine, machine_value(&machine, result, "positionals"));
        assert_eq!(text(&machine, positionals[0]), "positional");
    }

    #[test]
    fn parse_args_defaults_strict_and_errors() {
        let program = blank_program();
        let mut host = EchoHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let default = alloc_string(&mut machine, "fallback").unwrap();
        let name = descriptor(&mut machine, "string", None, false, Some(default));
        let defaults_config = config(&mut machine, &[], &[("name", name)], &[]);
        let result = call_parse_args(&mut machine, defaults_config).unwrap();
        let values = machine_value(&machine, result, "values");
        assert_eq!(
            text(&machine, machine_value(&machine, values, "name")),
            "fallback"
        );
        let unknown = config(&mut machine, &["--unknown"], &[], &[]);
        assert!(matches!(
            call_parse_args(&mut machine, unknown),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        let positional = config(&mut machine, &["value"], &[], &[]);
        assert!(matches!(
            call_parse_args(&mut machine, positional),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        let loose = config(
            &mut machine,
            &["--other=value", "tail"],
            &[],
            &[("strict", false)],
        );
        let loose_result = call_parse_args(&mut machine, loose).unwrap();
        let loose_values = machine_value(&machine, loose_result, "values");
        assert_eq!(
            text(&machine, machine_value(&machine, loose_values, "other")),
            "value"
        );
        let loose_positionals = array_values(
            &machine,
            machine_value(&machine, loose_result, "positionals"),
        );
        assert_eq!(text(&machine, loose_positionals[0]), "tail");
        let string = descriptor(&mut machine, "string", None, false, None);
        let missing = config(&mut machine, &["--name"], &[("name", string)], &[]);
        assert!(matches!(
            call_parse_args(&mut machine, missing),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn parse_args_ignores_undefined_defaults_and_handles_boolean_inline_values() {
        let program = blank_program();
        let mut host = EchoHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());

        let absent_default = descriptor(&mut machine, "string", None, false, None);
        let undefined_default =
            descriptor(&mut machine, "string", None, false, Some(Value::UNDEFINED));
        let defaults = config(
            &mut machine,
            &[],
            &[("absent", absent_default), ("undefined", undefined_default)],
            &[],
        );
        let result = call_parse_args(&mut machine, defaults).unwrap();
        let values = machine_value(&machine, result, "values");
        let values_index = machine.runtime_slot(values).unwrap().unwrap();
        let absent_key = PropertyKey::Named(machine.intern_str("absent"));
        assert!(machine.own_get(values_index, &absent_key,).is_none());
        let undefined_key = PropertyKey::Named(machine.intern_str("undefined"));
        assert!(machine.own_get(values_index, &undefined_key,).is_none());

        let invalid_default = alloc_string(&mut machine, "invalid").unwrap();
        let boolean_with_invalid_default =
            descriptor(&mut machine, "boolean", None, false, Some(invalid_default));
        let invalid = config(
            &mut machine,
            &[],
            &[("boolean", boolean_with_invalid_default)],
            &[],
        );
        assert!(matches!(
            call_parse_args(&mut machine, invalid),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));

        let boolean = descriptor(&mut machine, "boolean", None, false, None);
        let loose = config(
            &mut machine,
            &["--boolean=false"],
            &[("boolean", boolean)],
            &[("strict", false)],
        );
        let result = call_parse_args(&mut machine, loose).unwrap();
        let values = machine_value(&machine, result, "values");
        assert_eq!(
            text(&machine, machine_value(&machine, values, "boolean")),
            "false"
        );

        let boolean = descriptor(&mut machine, "boolean", None, false, None);
        let strict = config(
            &mut machine,
            &["--boolean=false"],
            &[("boolean", boolean)],
            &[],
        );
        assert!(matches!(
            call_parse_args(&mut machine, strict),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn parse_args_short_multiple_negative_tokens_and_terminator() {
        let program = blank_program();
        let mut host = EchoHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let verbose = descriptor(&mut machine, "boolean", Some("v"), false, None);
        let tag = descriptor(&mut machine, "string", Some("t"), true, None);
        let color = descriptor(&mut machine, "boolean", None, false, None);
        let config = config(
            &mut machine,
            &["-v", "-ta", "-t", "b", "--no-color", "--", "tail"],
            &[("verbose", verbose), ("tag", tag), ("color", color)],
            &[
                ("allowNegative", true),
                ("allowPositionals", true),
                ("tokens", true),
            ],
        );
        let result = call_parse_args(&mut machine, config).unwrap();
        let values = machine_value(&machine, result, "values");
        assert_eq!(machine_value(&machine, values, "verbose"), Value::TRUE);
        assert_eq!(machine_value(&machine, values, "color"), Value::FALSE);
        let tags = array_values(&machine, machine_value(&machine, values, "tag"));
        assert_eq!(
            tags.iter()
                .map(|value| text(&machine, *value))
                .collect::<Vec<_>>(),
            ["a", "b"]
        );
        let positionals = array_values(&machine, machine_value(&machine, result, "positionals"));
        assert_eq!(text(&machine, positionals[0]), "tail");
        let tokens = array_values(&machine, machine_value(&machine, result, "tokens"));
        assert_eq!(tokens.len(), 6);
        assert_eq!(
            text(&machine, machine_value(&machine, tokens[4], "kind")),
            "option-terminator"
        );
        assert_eq!(
            text(&machine, machine_value(&machine, tokens[5], "kind")),
            "positional"
        );
    }

    #[test]
    fn repeated_parse_args_values_are_charged_before_retention() {
        let program = blank_program();
        let mut host = EchoHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let array = alloc_array(&mut machine, Vec::new()).unwrap();
        let mut values = BTreeMap::from([("tag".to_owned(), array)]);
        let spec = OptionSpec {
            kind: OptionType::String,
            multiple: true,
            default: None,
        };
        machine.limits.max_heap_bytes = machine.heap_bytes;

        assert!(matches!(
            store_option(
                &mut machine,
                &mut values,
                "tag",
                Some(&spec),
                Value::UNDEFINED,
            ),
            Err(EvalFailure::Runtime(
                RuntimeErrorKind::HeapByteLimitExceeded { .. }
            ))
        ));
        assert!(array_values(&machine, array).is_empty());
    }

    #[test]
    fn hash_update_digest_encodings_and_reuse_errors() {
        let program = blank_program();
        let mut host = EchoHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let algorithm = alloc_string(&mut machine, "echo").unwrap();
        let BuiltinOutcome::Value(hash) =
            create_hash(&mut machine, Value::UNDEFINED, &[algorithm], false).unwrap()
        else {
            unreachable!()
        };
        let hex_data = alloc_string(&mut machine, "6162").unwrap();
        let hex = alloc_string(&mut machine, "hex").unwrap();
        let BuiltinOutcome::Value(chained) =
            hash_update(&mut machine, hash, &[hex_data, hex], false).unwrap()
        else {
            unreachable!()
        };
        assert_eq!(chained, hash);
        let tail = alloc_string(&mut machine, "Yw").unwrap();
        let base64url = alloc_string(&mut machine, "base64url").unwrap();
        hash_update(&mut machine, hash, &[tail, base64url], false).unwrap();
        let output = alloc_string(&mut machine, "base64url").unwrap();
        let BuiltinOutcome::Value(digest) =
            hash_digest(&mut machine, hash, &[output], false).unwrap()
        else {
            unreachable!()
        };
        assert_eq!(text(&machine, digest), "YWJj");
        assert!(matches!(
            hash_digest(&mut machine, hash, &[output], false),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        assert!(matches!(
            hash_update(&mut machine, hash, &[tail], false),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        let bad_algorithm = alloc_string(&mut machine, "missing").unwrap();
        assert!(matches!(
            create_hash(&mut machine, Value::UNDEFINED, &[bad_algorithm], false),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        let fresh_algorithm = alloc_string(&mut machine, "echo").unwrap();
        let BuiltinOutcome::Value(fresh) =
            create_hash(&mut machine, Value::UNDEFINED, &[fresh_algorithm], false).unwrap()
        else {
            unreachable!()
        };
        let bad_encoding = alloc_string(&mut machine, "latin1").unwrap();
        assert!(matches!(
            hash_update(&mut machine, fresh, &[tail, bad_encoding], false),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        assert!(matches!(
            hash_digest(&mut machine, fresh, &[bad_encoding], false),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn hash_update_rejects_non_ascii_hex_input() {
        // "aéb" is 4 bytes ([0x61, 0xC3, 0xA9, 0x62]) — a multiple of two, so the
        // length guard passes, but the first byte pair [0x61, 0xC3] straddles a
        // UTF-8 boundary. Previously this panicked the runtime; it must surface
        // as a normal JS-visible TypeError instead.
        let program = blank_program();
        let mut host = EchoHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let algorithm = alloc_string(&mut machine, "echo").unwrap();
        let BuiltinOutcome::Value(hash) =
            create_hash(&mut machine, Value::UNDEFINED, &[algorithm], false).unwrap()
        else {
            unreachable!()
        };
        let non_ascii_hex = alloc_string(&mut machine, "aéb").unwrap();
        let hex = alloc_string(&mut machine, "hex").unwrap();
        assert!(matches!(
            hash_update(&mut machine, hash, &[non_ascii_hex, hex], false),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }
    #[test]
    fn hash_replaces_lone_surrogates_and_releases_digested_payload() {
        let program = blank_program();
        let mut host = EchoHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let algorithm = alloc_string(&mut machine, "echo").unwrap();
        let BuiltinOutcome::Value(hash) =
            create_hash(&mut machine, Value::UNDEFINED, &[algorithm], false).unwrap()
        else {
            unreachable!()
        };
        let index = machine.runtime_slot(hash).unwrap().unwrap();
        let retained_before_update = machine.slot_bytes[index];
        let lone_surrogate = machine
            .allocate(HeapEntry::String(EcmaString::from_units(&[0xd800])))
            .unwrap();
        hash_update(&mut machine, hash, &[lone_surrogate], false).unwrap();
        assert_eq!(
            machine.slot_bytes[index],
            retained_before_update + "\u{fffd}".len()
        );

        let output = alloc_string(&mut machine, "hex").unwrap();
        let BuiltinOutcome::Value(digest) =
            hash_digest(&mut machine, hash, &[output], false).unwrap()
        else {
            unreachable!()
        };
        assert_eq!(text(&machine, digest), "efbfbd");
        assert_eq!(machine.slot_bytes[index], retained_before_update);
        assert!(matches!(
            &machine.heap[index],
            HeapEntry::HashState { data, .. } if data.is_empty()
        ));
    }

    fn hash_program() -> Program<Verified> {
        let constants = vec![
            Constant::String(EcmaString::encode("main")),
            Constant::String(EcmaString::encode("node:crypto")),
            Constant::String(EcmaString::encode("createHash")),
            Constant::String(EcmaString::encode("echo")),
            Constant::String(EcmaString::encode("update")),
            Constant::String(EcmaString::encode("616263")),
            Constant::String(EcmaString::encode("hex")),
            Constant::String(EcmaString::encode("digest")),
        ];
        let code = vec![
            Instruction::LoadGlobal {
                dst: reg(0),
                name: cid(2),
            },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(3),
            },
            Instruction::CreateArray { dst: reg(2) },
            Instruction::ArrayPush {
                array: reg(2),
                value: reg(1),
            },
            Instruction::Call {
                dst: reg(3),
                callee: reg(0),
                this_value: reg(2),
                arguments: reg(2),
            },
            Instruction::LoadConst {
                dst: reg(4),
                constant: cid(4),
            },
            Instruction::GetProperty {
                dst: reg(5),
                object: reg(3),
                key: reg(4),
            },
            Instruction::LoadConst {
                dst: reg(6),
                constant: cid(5),
            },
            Instruction::LoadConst {
                dst: reg(7),
                constant: cid(6),
            },
            Instruction::CreateArray { dst: reg(8) },
            Instruction::ArrayPush {
                array: reg(8),
                value: reg(6),
            },
            Instruction::ArrayPush {
                array: reg(8),
                value: reg(7),
            },
            Instruction::Call {
                dst: reg(9),
                callee: reg(5),
                this_value: reg(3),
                arguments: reg(8),
            },
            Instruction::LoadConst {
                dst: reg(10),
                constant: cid(7),
            },
            Instruction::GetProperty {
                dst: reg(11),
                object: reg(3),
                key: reg(10),
            },
            Instruction::CreateArray { dst: reg(12) },
            Instruction::ArrayPush {
                array: reg(12),
                value: reg(7),
            },
            Instruction::Call {
                dst: reg(13),
                callee: reg(11),
                this_value: reg(3),
                arguments: reg(12),
            },
            Instruction::Return { value: reg(13) },
        ];
        program(
            constants,
            function(14, code),
            vec![external_edge(1)],
            vec![Binding {
                name: cid(2),
                kind: BindingKind::Imported {
                    edge: EdgeId::new(0),
                    name: cid(2),
                },
            }],
        )
    }

    #[test]
    fn external_hash_has_interpreter_native_parity() {
        let program = hash_program();
        let mut interpreter_host = EchoHost;
        let interpreter = Machine::new(&program, &mut interpreter_host, Limits::default())
            .run()
            .unwrap();
        let mut native_host = EchoHost;
        let native = NativeEngine::new(&program, &NoEntries, &mut native_host, Limits::default())
            .run()
            .unwrap();
        assert_eq!(interpreter.value, native.value);
        assert_eq!(interpreter.outcome, native.outcome);
        assert_eq!(interpreter.entry_registers, native.entry_registers);
    }
    #[test]
    fn parse_args_rejects_detached_dash_values_and_allows_inline() {
        let program = blank_program();
        let mut host = EchoHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let name = descriptor(&mut machine, "string", None, false, None);
        let file = descriptor(&mut machine, "string", Some("f"), false, None);

        let detached_long = config(&mut machine, &["--name", "-bar"], &[("name", name)], &[]);
        assert!(matches!(
            call_parse_args(&mut machine, detached_long),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));

        let detached_short = config(&mut machine, &["-f", "-bar"], &[("file", file)], &[]);
        assert!(matches!(
            call_parse_args(&mut machine, detached_short),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));

        let loose_long = config(
            &mut machine,
            &["--name", "-bar"],
            &[("name", name)],
            &[("strict", false)],
        );
        let result = call_parse_args(&mut machine, loose_long).unwrap();
        let values = machine_value(&machine, result, "values");
        assert_eq!(
            text(&machine, machine_value(&machine, values, "name")),
            "-bar"
        );

        let loose_short = config(
            &mut machine,
            &["-f", "-bar"],
            &[("file", file)],
            &[("strict", false)],
        );
        let result = call_parse_args(&mut machine, loose_short).unwrap();
        let values = machine_value(&machine, result, "values");
        assert_eq!(
            text(&machine, machine_value(&machine, values, "file")),
            "-bar"
        );

        let inline_long = config(&mut machine, &["--name=-bar"], &[("name", name)], &[]);
        let result = call_parse_args(&mut machine, inline_long).unwrap();
        let values = machine_value(&machine, result, "values");
        assert_eq!(
            text(&machine, machine_value(&machine, values, "name")),
            "-bar"
        );

        let inline_short = config(&mut machine, &["-f-bar"], &[("file", file)], &[]);
        let result = call_parse_args(&mut machine, inline_short).unwrap();
        let values = machine_value(&machine, result, "values");
        assert_eq!(
            text(&machine, machine_value(&machine, values, "file")),
            "-bar"
        );
    }

    #[test]
    fn hash_base64_accepts_url_alphabet() {
        let program = blank_program();
        let mut host = EchoHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let algorithm = alloc_string(&mut machine, "echo").unwrap();
        let BuiltinOutcome::Value(hash) =
            create_hash(&mut machine, Value::UNDEFINED, &[algorithm], false).unwrap()
        else {
            unreachable!()
        };
        // 0xFB 0xFF standard base64 is "+/8=" and base64url is "-_8=".
        let data = alloc_string(&mut machine, "-_8=").unwrap();
        let base64 = alloc_string(&mut machine, "base64").unwrap();
        hash_update(&mut machine, hash, &[data, base64], false).unwrap();
        let output = alloc_string(&mut machine, "base64").unwrap();
        let BuiltinOutcome::Value(digest) =
            hash_digest(&mut machine, hash, &[output], false).unwrap()
        else {
            unreachable!()
        };
        assert_eq!(text(&machine, digest), "+/8=");
    }
}
