//! Complete `JSON` namespace semantics for the C8.1 gate.
//!
//! This module owns the edge-closing behavior of the C8.1 gate:
//!
//! - `JSON.parse` rebuilt on CreateDataProperty semantics: parsed objects and
//!   reviver write-backs define own properties instead of assigning, so
//!   prototype setters cannot observe or redirect JSON materialization.
//! - Reviver source-text access (tc39 proposal-json-parse-with-source, shipped
//!   in V8 12.4 / Firefox 144): the reviver receives a third `context`
//!   argument whose own `source` property carries the exact source slice of
//!   each unmodified primitive.
//! - `JSON.rawJSON` / `JSON.isRawJSON`. Written tests pin the brand check on a
//!   private-name marker no script-side object can forge: the brand is a
//!   `PropertyKey::Private` slot created at install time, stored only on the
//!   `JSON` namespace and on genuine raw-JSON objects; private names are
//!   invisible to every own-key reflection path from script.
//! - `JSON.stringify` with spec-ordered coercion (replacer before space),
//!   Number/String wrapper unwrapping for `space`, `toJSON` before the
//!   replacer, BigInt rejection, cycle detection, hole/undefined/function
//!   null-mapping, gap truncation, and lone-surrogate escaping.
//! - [`evaluate_json_module_source`], the machine-side helper for JSON module
//!   loading: it parses module source text into the fresh JSON tree that the
//!   default export of a JSON module namespace binds.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use bamts_bytecode::{EcmaString, EcmaStringBuilder};
use bamts_native::{Decoded, Value};

use super::{allocate_array, allocate_string, define_data, install_function, type_error};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap};

/// The JSON nesting where a machine that does not measure its native stack stops, as
/// in a test or an embedded script on a thread of unknown size. Each level is one
/// Rust frame, so this stays far below a small stack.
const UNMEASURED_JSON_DEPTH: usize = 256;

/// `space` never contributes more than ten indentation units (ECMA-262
/// clamp), and string gaps truncate to their first ten code units.
const MAX_GAP_UNITS: usize = 10;

/// Largest ToLength result; array-like JSON traversal snapshots this bound.
const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;

/// Whether one more level of a recursive JSON walk, `JSON.stringify` or a reviver,
/// passes the stack. A machine that measures its native stack stops only where that
/// stack is full, so both go at least as deep as in V8. The parser does not recurse.
fn json_nesting_overflows<H: Host>(machine: &Machine<'_, H>, depth: usize) -> bool {
    if machine.limits.max_stack_bytes == usize::MAX {
        depth >= UNMEASURED_JSON_DEPTH
    } else {
        machine.native_stack_overflows()
    }
}

/// The `RangeError` of a call that passes the stack, which the program can catch.
fn json_depth_error() -> EvalFailure {
    EvalFailure::Throw(crate::STACK_OVERFLOW)
}

fn syntax_error<H: Host>(machine: &mut Machine<'_, H>, message: String) -> EvalFailure {
    let id = machine
        .intrinsics
        .builtins
        .id_named("SyntaxError")
        .expect("SyntaxError installed");
    machine.throw_error(id, message)
}

/// Creates and installs the complete `JSON` namespace.
///
/// The namespace has one owner: this installer registers the standard methods,
/// anchors the raw-JSON brand, applies `@@toStringTag`, and publishes the
/// global only after the object is complete.
pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let json = super::push(
        heap,
        HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(builtins.object_prototype()),
            extensible: true,
            boxed_primitive: None,
        },
    );
    for (name, length, handler) in [
        (
            "parse",
            2,
            parse::<H> as crate::intrinsics::BuiltinHandler<H>,
        ),
        ("stringify", 3, stringify::<H>),
        ("rawJSON", 1, raw_json::<H>),
        ("isRawJSON", 1, is_raw_json::<H>),
    ] {
        let function = install_function(heap, atoms, builtins, name, length, handler);
        define_data(heap, atoms, json, name, function);
    }
    let brand_index = heap.len() as u32;
    let brand = super::push(
        heap,
        HeapEntry::PrivateName {
            description: EcmaString::encode("%JSON.rawJSON%"),
        },
    );
    let json_index = super::heap_index(json);
    let HeapEntry::Object { properties, .. } = &mut heap[json_index] else {
        panic!("JSON builtin installs a namespace object")
    };
    properties.insert(
        PropertyKey::Private(brand_index),
        Property::Data {
            value: brand,
            writable: false,
            enumerable: false,
            configurable: false,
        },
    );
    super::define_to_string_tag(heap, json, builtins.symbol_to_string_tag(), "JSON");
    globals.insert(EcmaString::encode("JSON"), json);
}

/// The slot of the raw-JSON brand private name and its heap value, recovered
/// from the `JSON` namespace on every use. Private-name keys never appear in
/// any script-visible key enumeration, so reviver and serializer code can
/// safely trust a presence check as a true internal slot.
fn raw_json_brand<H: Host>(machine: &Machine<'_, H>) -> Option<(u32, Value)> {
    let json = machine.intrinsics.global("JSON")?;
    let json_index = super::heap_index(json);
    let HeapEntry::Object { properties, .. } = &machine.heap[json_index] else {
        return None;
    };
    properties.iter().find_map(|(key, property)| {
        if let (PropertyKey::Private(slot), Property::Data { value, .. }) = (key, property) {
            Some((*slot, *value))
        } else {
            None
        }
    })
}

fn has_raw_json_brand<H: Host>(machine: &Machine<'_, H>, value: Value) -> bool {
    let Some((brand_slot, _)) = raw_json_brand(machine) else {
        return false;
    };
    let Ok(Some(index)) = machine.runtime_slot(value) else {
        return false;
    };
    // The brand alone is necessary but not sufficient: the JSON namespace
    // itself anchors the brand, so also require the frozen null-prototype
    // shape with an own `rawJSON` string. Scripts can satisfy the shape but
    // never the private key, so the conjunction is still unforgeable.
    let HeapEntry::Object {
        properties,
        prototype: None,
        extensible: false,
        ..
    } = &machine.heap[index]
    else {
        return false;
    };
    if !properties.contains_key(&PropertyKey::Private(brand_slot)) {
        return false;
    }
    let Some(Property::Data {
        value: text_value,
        writable: false,
        configurable: false,
        ..
    }) = properties.get_ascii(&machine.atoms, "rawJSON")
    else {
        return false;
    };
    machine.string_value(*text_value).is_some()
}

/// The verbatim text of a genuine raw-JSON object, without quoting.
fn raw_json_text<H: Host>(machine: &Machine<'_, H>, value: Value) -> Option<EcmaString> {
    if !has_raw_json_brand(machine, value) {
        return None;
    }
    let index = machine.runtime_slot(value).ok()??;
    let HeapEntry::Object { properties, .. } = &machine.heap[index] else {
        return None;
    };
    let Some(Property::Data {
        value: text_value, ..
    }) = properties.get_ascii(&machine.atoms, "rawJSON")
    else {
        return None;
    };
    machine.string_value(*text_value)
}

/// CreateDataPropertyOrThrow semantics: defines an own data property on the
/// target without consulting the prototype chain, so a setter installed on
/// `Object.prototype` or `Array.prototype` cannot observe JSON writes.
fn create_data_property<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    key: PropertyKey,
    value: Value,
) -> Result<(), EvalFailure> {
    machine.create_data_property_key(object, key, value)
}

fn length_of_array_like<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<usize, EvalFailure> {
    let length = machine.get_named_property(value, "length")?;
    let number = machine.coerce_number_observable(length)?;
    let number = match number.decode() {
        Some(Decoded::Int32(value)) => f64::from(value as i32),
        Some(Decoded::Number(value)) => value,
        _ => 0.0,
    };
    if number.is_nan() || number <= 0.0 {
        return Ok(0);
    }
    if !number.is_finite() {
        return Ok(MAX_SAFE_INTEGER as usize);
    }
    Ok((number.trunc()).min(MAX_SAFE_INTEGER) as usize)
}

// ---- JSON.rawJSON / JSON.isRawJSON ----------------------------------------

fn raw_json_error<H: Host>(machine: &mut Machine<'_, H>, message: &str) -> EvalFailure {
    syntax_error(
        machine,
        format!("JSON.rawJSON rejected its input: {message}"),
    )
}

fn raw_json<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let text =
        machine.coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let units = text.as_units();
    if units.is_empty()
        || matches!(units[0], 0x09 | 0x0A | 0x0D | 0x20)
        || matches!(units[units.len() - 1], 0x09 | 0x0A | 0x0D | 0x20)
    {
        return Err(raw_json_error(
            machine,
            "empty or whitespace-padded text is not valid raw JSON",
        ));
    }
    match parse_root(machine, &text)? {
        JsonNode::Primitive { .. } => {}
        JsonNode::Array { .. } | JsonNode::Object { .. } => {
            return Err(raw_json_error(
                machine,
                "objects and arrays are not valid raw JSON values",
            ));
        }
    }
    let (brand_slot, brand) =
        raw_json_brand(machine).expect("json_edge::install runs before any handler");
    let text_value = allocate_string(machine, text)?;
    let mut properties = PropertyMap::default();
    properties.insert(
        PropertyKey::Named(machine.intern_str("rawJSON")),
        Property::Data {
            value: text_value,
            writable: false,
            enumerable: true,
            configurable: false,
        },
    );
    properties.insert(
        PropertyKey::Private(brand_slot),
        Property::Data {
            value: brand,
            writable: false,
            enumerable: false,
            configurable: false,
        },
    );
    let object = machine
        .allocate(HeapEntry::Object {
            properties,
            prototype: None,
            extensible: false,
            boxed_primitive: None,
        })
        .map_err(EvalFailure::Runtime)?;
    Ok(BuiltinOutcome::Value(object))
}

fn is_raw_json<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = args.first().copied().unwrap_or(Value::UNDEFINED);
    Ok(BuiltinOutcome::Value(Value::boolean(has_raw_json_brand(
        machine, value,
    ))))
}

// ---- JSON.parse -----------------------------------------------------------

fn parse<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = machine.to_string(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let root = parse_root(machine, &source)?;
    // The reviver is only classified after the text parses, matching
    // evaluation order: a SyntaxError in the input preempts reviver handling.
    let reviver = match args.get(1).copied() {
        Some(value) if machine.is_callable(value)? => Some(value),
        _ => None,
    };
    let root_value = root.value();
    let Some(reviver) = reviver else {
        return Ok(BuiltinOutcome::Value(root_value));
    };
    let wrapper = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            extensible: true,
            boxed_primitive: None,
        })
        .map_err(EvalFailure::Runtime)?;
    let root_key = EcmaString::default();
    let root_atom = PropertyKey::Named(machine.intern(root_key.clone()));
    create_data_property(machine, wrapper, root_atom, root_value)?;
    let result = walk_reviver(
        machine,
        wrapper,
        root_key,
        Some(&root),
        reviver,
        source.as_units(),
        0,
    )?;
    Ok(BuiltinOutcome::Value(result))
}

/// Parses a complete JSON document, converting grammar failures into abrupt
/// `SyntaxError` completions while preserving runtime failures untouched.
fn parse_root<H: Host>(
    machine: &mut Machine<'_, H>,
    source: &EcmaString,
) -> Result<JsonNode, EvalFailure> {
    let mut parser = Parser::new(source.as_units());
    (|| -> ParseResult<JsonNode> {
        parser.ws();
        let root = parser.value(machine)?;
        parser.ws();
        if parser.pos != parser.source.len() {
            return Err(ParseFailure::Syntax(parser.error_unexpected()));
        }
        Ok(root)
    })()
    .map_err(|failure| parse_failure(machine, failure))
}

fn parse_failure<H: Host>(machine: &mut Machine<'_, H>, failure: ParseFailure) -> EvalFailure {
    match failure {
        ParseFailure::Runtime(error) => error,
        ParseFailure::Syntax(message) => syntax_error(machine, message),
    }
}

/// A parse-created subtree plus the data the reviver walk needs: the built
/// value, and for primitives the exact span of source that produced it.
enum JsonNode {
    Primitive {
        value: Value,
        source: (usize, usize),
    },
    Array {
        value: Value,
        children: Vec<JsonNode>,
    },
    Object {
        value: Value,
        children: Vec<(EcmaString, JsonNode)>,
    },
}

impl JsonNode {
    fn value(&self) -> Value {
        match self {
            JsonNode::Primitive { value, .. }
            | JsonNode::Array { value, .. }
            | JsonNode::Object { value, .. } => *value,
        }
    }

    fn primitive_source(&self) -> Option<(usize, usize)> {
        match self {
            JsonNode::Primitive { source, .. } => Some(*source),
            _ => None,
        }
    }

    /// Moves the children of this node into `pending`.
    fn release_children(&mut self, pending: &mut Vec<JsonNode>) {
        match self {
            JsonNode::Primitive { .. } => {}
            JsonNode::Array { children, .. } => pending.append(children),
            JsonNode::Object { children, .. } => {
                pending.extend(children.drain(..).map(|(_, node)| node));
            }
        }
    }
}

impl Drop for JsonNode {
    /// Drops the subtree from a list, not by recursion, so that a tree of any depth
    /// drops on a small stack.
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.release_children(&mut pending);
        while let Some(mut node) = pending.pop() {
            node.release_children(&mut pending);
        }
    }
}

/// An array or object that the parser has opened and not closed, with the members
/// that it has read.
enum OpenContainer {
    Array {
        values: Vec<Value>,
        children: Vec<JsonNode>,
    },
    /// `key` names the member that the parser reads next.
    Object {
        value: Value,
        children: Vec<(EcmaString, JsonNode)>,
        key: EcmaString,
    },
}

impl OpenContainer {
    fn push<H: Host>(&mut self, machine: &mut Machine<'_, H>, child: JsonNode) -> ParseResult<()> {
        match self {
            OpenContainer::Array { values, children } => {
                values.push(child.value());
                children.push(child);
            }
            OpenContainer::Object {
                value,
                children,
                key,
            } => {
                let key = std::mem::take(key);
                let atom = PropertyKey::Named(machine.intern(key.clone()));
                create_data_property(machine, *value, atom, child.value())
                    .map_err(ParseFailure::Runtime)?;
                // Mirror the property map: a duplicate key overwrites in place,
                // keeping its first-insertion position in enumeration order.
                match children.iter().position(|(name, _)| *name == key) {
                    Some(existing) => children[existing] = (key, child),
                    None => children.push((key, child)),
                }
            }
        }
        Ok(())
    }

    fn close<H: Host>(self, machine: &mut Machine<'_, H>) -> ParseResult<JsonNode> {
        match self {
            OpenContainer::Array { values, children } => {
                let value = allocate_array(machine, values).map_err(ParseFailure::Runtime)?;
                Ok(JsonNode::Array { value, children })
            }
            OpenContainer::Object {
                value, children, ..
            } => Ok(JsonNode::Object { value, children }),
        }
    }
}

/// InternalizeJSONProperty with source-text access. Keys and length are
/// enumerated from the live holder (a reviver may mutate `this` mid-walk);
/// the parse tree is consulted only to attach `context.source` to primitives
/// the parser itself produced. Once a live value no longer matches the
/// parse-created node, the node is dropped and no descendant sees a source
/// span. (Value-equal primitive rewrites are indistinguishable from
/// unmodified primitives here — the same approximation V8 makes when a
/// reviver writes back an equal primitive.)
#[allow(clippy::too_many_arguments)]
fn walk_reviver<H: Host>(
    machine: &mut Machine<'_, H>,
    holder: Value,
    key: EcmaString,
    node: Option<&JsonNode>,
    reviver: Value,
    source: &[u16],
    depth: usize,
) -> Result<Value, EvalFailure> {
    let property_key = PropertyKey::Named(machine.intern(key.clone()));
    let live = machine.get_property_key(holder, &property_key)?;
    let matched = node.is_some_and(|node| node.value() == live);
    let matched_node = if matched { node } else { None };
    if machine.array_elements(live)?.is_some() {
        if json_nesting_overflows(machine, depth) {
            return Err(json_depth_error());
        }
        let child_nodes: Option<&[JsonNode]> = match matched_node {
            Some(JsonNode::Array { children, .. }) => Some(children.as_slice()),
            _ => None,
        };
        // Spec walks the live holder: revivers may mutate `this` before a
        // later sibling is visited, so the length snapshot and each lookup
        // come from the holder. Nodes only supply source spans.
        let length = length_of_array_like(machine, live)?;
        for index in 0..length {
            let name = EcmaString::encode(&index.to_string());
            let child_node = child_nodes.and_then(|children| children.get(index));
            let child = walk_reviver(
                machine,
                live,
                name.clone(),
                child_node,
                reviver,
                source,
                depth + 1,
            )?;
            let key = PropertyKey::Named(machine.intern(name));
            if child == Value::UNDEFINED {
                machine.internal_delete(live, &key)?;
            } else {
                create_data_property(machine, live, key, child)?;
            }
        }
    } else if machine.is_object(live) {
        if json_nesting_overflows(machine, depth) {
            return Err(json_depth_error());
        }
        let child_nodes: Option<&[(EcmaString, JsonNode)]> = match matched_node {
            Some(JsonNode::Object { children, .. }) => Some(children.as_slice()),
            _ => None,
        };
        let names = machine.enumerable_keys(live)?;
        for name in names {
            let child_node = child_nodes.and_then(|children| {
                children
                    .iter()
                    .find(|(candidate, _)| *candidate == name)
                    .map(|(_, node)| node)
            });
            let child = walk_reviver(
                machine,
                live,
                name.clone(),
                child_node,
                reviver,
                source,
                depth + 1,
            )?;
            let key = PropertyKey::Named(machine.intern(name));
            if child == Value::UNDEFINED {
                machine.internal_delete(live, &key)?;
            } else {
                create_data_property(machine, live, key, child)?;
            }
        }
    }
    let context = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            extensible: true,
            boxed_primitive: None,
        })
        .map_err(EvalFailure::Runtime)?;
    if let Some(span) = matched_node.and_then(JsonNode::primitive_source) {
        let text = EcmaString::from_units(&source[span.0..span.1]);
        let text = allocate_string(machine, text)?;
        let source_key = PropertyKey::Named(machine.intern_str("source"));
        create_data_property(machine, context, source_key, text)?;
    }
    let name = allocate_string(machine, key)?;
    machine.call_value(reviver, holder, &[name, live, context])
}

/// Parses JSON module source text (for example a `… with { type: "json" }`
/// import) into the fresh JSON tree bound by the module's default export.
/// The parser is shared with `JSON.parse` minus the reviver; grammar failures
/// surface as abrupt `SyntaxError` completions, matching JSON module
/// evaluation.
#[cfg(test)]
pub(crate) fn evaluate_json_module_source<H: Host>(
    machine: &mut Machine<'_, H>,
    source: &EcmaString,
) -> Result<Value, EvalFailure> {
    Ok(parse_root(machine, source)?.value())
}

// ---- JSON.stringify -------------------------------------------------------

/// One run of `JSON.stringify`. It writes the whole text into one builder, so a
/// deep value costs time in proportion to its text.
struct Serializer<'a> {
    replacer: Option<Value>,
    property_list: Option<&'a [EcmaString]>,
    gap: &'a EcmaString,
    /// The objects that the serializer is inside. A value that is in it again is a
    /// cycle.
    stack: HashSet<Value>,
    output: EcmaStringBuilder,
}

/// What a property gives after `toJSON`, the replacer and the unwrapping of a
/// primitive wrapper, before it is written.
enum Serialized {
    /// `undefined`, a function or a symbol: an object leaves the property out, and
    /// an array writes `null`.
    Omitted,
    Text(EcmaString),
    Array(Value),
    Object(Value),
}

fn stringify<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = args.first().copied().unwrap_or(Value::UNDEFINED);
    let replacer = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let space = args.get(2).copied().unwrap_or(Value::UNDEFINED);

    // Step order is observable: the replacer is classified (and replacer
    // arrays are fully enumerated) before `space` is unwrapped and coerced.
    let mut replacer_function = None;
    let mut property_list = None;
    if machine.is_object(replacer) {
        if machine.is_callable(replacer)? {
            replacer_function = Some(replacer);
        } else if machine.array_elements(replacer)?.is_some() {
            let length = length_of_array_like(machine, replacer)?;
            let mut seen: BTreeSet<EcmaString> = BTreeSet::new();
            let mut list = Vec::new();
            for index in 0..length {
                let key = PropertyKey::Named(machine.intern_str(&index.to_string()));
                let item = machine.get_property_key(replacer, &key)?;
                let primitive = machine.unbox_primitive_or_self(item)?;
                let is_wrapper = machine.is_object(item) && primitive != item;
                let text = match primitive.decode() {
                    Some(Decoded::Int32(_)) if is_wrapper => {
                        Some(machine.coerce_string_observable(item)?.to_utf8_lossy())
                    }
                    Some(Decoded::Number(_)) if is_wrapper => {
                        Some(machine.coerce_string_observable(item)?.to_utf8_lossy())
                    }
                    Some(Decoded::Int32(number)) => Some((number as i32).to_string()),
                    Some(Decoded::Number(number)) => Some(crate::format_number(number)),
                    Some(Decoded::HeapRef(_))
                        if machine.string_value(primitive).is_some() && is_wrapper =>
                    {
                        Some(machine.coerce_string_observable(item)?.to_utf8_lossy())
                    }
                    Some(Decoded::HeapRef(_)) => machine
                        .string_value(primitive)
                        .map(|text| text.to_utf8_lossy()),
                    _ => None,
                };
                if let Some(text) = text {
                    let key = EcmaString::encode(&text);
                    if seen.insert(key.clone()) {
                        list.push(key);
                    }
                }
            }
            property_list = Some(list);
        }
    }

    // Number wrapper -> observable ToNumber, String wrapper -> observable
    // ToString; a plain object (or any other value) leaves the gap empty.
    let primitive_space = machine.unbox_primitive_or_self(space)?;
    let space_is_wrapper = machine.is_object(space) && primitive_space != space;
    let gap = match primitive_space.decode() {
        Some(Decoded::Int32(_)) | Some(Decoded::Number(_)) if space_is_wrapper => {
            let number = machine.coerce_number_observable(space)?;
            match number.decode() {
                Some(Decoded::Int32(number)) => gap_from_count(f64::from(number as i32)),
                Some(Decoded::Number(number)) => gap_from_count(number),
                _ => unreachable!("ToNumber returns a number"),
            }
        }
        Some(Decoded::Int32(number)) => gap_from_count(f64::from(number as i32)),
        Some(Decoded::Number(number)) => gap_from_count(number),
        Some(Decoded::HeapRef(_))
            if machine.string_value(primitive_space).is_some() && space_is_wrapper =>
        {
            gap_from_string(machine.coerce_string_observable(space)?)
        }
        Some(Decoded::HeapRef(_)) => machine
            .string_value(primitive_space)
            .map_or_else(EcmaString::default, gap_from_string),
        _ => EcmaString::default(),
    };

    let wrapper = machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            extensible: true,
            boxed_primitive: None,
        })
        .map_err(EvalFailure::Runtime)?;
    let root_key = EcmaString::default();
    let root_atom = PropertyKey::Named(machine.intern(root_key.clone()));
    create_data_property(machine, wrapper, root_atom, value)?;
    let mut serializer = Serializer {
        replacer: replacer_function,
        property_list: property_list.as_deref(),
        gap: &gap,
        stack: HashSet::new(),
        output: EcmaStringBuilder::new(),
    };
    match serializer.property(machine, wrapper, root_key, 0)? {
        Serialized::Omitted => Ok(BuiltinOutcome::Value(Value::UNDEFINED)),
        root => {
            serializer.write(machine, root, 0)?;
            let text = serializer.output.finish();
            Ok(BuiltinOutcome::Value(allocate_string(machine, text)?))
        }
    }
}

fn gap_from_count(number: f64) -> EcmaString {
    let count = if number.is_nan() || number <= 0.0 {
        0
    } else if !number.is_finite() {
        MAX_GAP_UNITS
    } else {
        (number.trunc() as usize).min(MAX_GAP_UNITS)
    };
    EcmaString::encode(&" ".repeat(count))
}

fn gap_from_string(text: EcmaString) -> EcmaString {
    text.slice_units(0..text.len_units().min(MAX_GAP_UNITS))
        .expect("range is bounded by the string length")
}

impl Serializer<'_> {
    /// SerializeJSONProperty up to its text: every step that the program can
    /// observe, in the order of the spec. An object writes the key of a member only
    /// when this gives more than [`Serialized::Omitted`].
    fn property<H: Host>(
        &self,
        machine: &mut Machine<'_, H>,
        holder: Value,
        key: EcmaString,
        depth: usize,
    ) -> Result<Serialized, EvalFailure> {
        if json_nesting_overflows(machine, depth) {
            return Err(json_depth_error());
        }
        let property_key = PropertyKey::Named(machine.intern(key.clone()));
        let mut value = machine.get_property_key(holder, &property_key)?;
        if machine.is_object(value) || super::bigint::is_bigint(machine, value)? {
            let to_json = machine.get_named_property(value, "toJSON")?;
            if machine.is_callable(to_json)? {
                let key_value = allocate_string(machine, key.clone())?;
                value = machine.call_value(to_json, value, &[key_value])?;
            }
        }
        if let Some(replacer) = self.replacer {
            let key_value = allocate_string(machine, key)?;
            value = machine.call_value(replacer, holder, &[key_value, value])?;
        }
        let value = machine.unbox_primitive_or_self(value)?;
        super::bigint::json_reject(machine, value)?;
        let text = |text: &str| Serialized::Text(EcmaString::encode(text));
        Ok(match value.decode() {
            Some(Decoded::Null) => text("null"),
            Some(Decoded::Boolean(value)) => text(if value { "true" } else { "false" }),
            Some(Decoded::Int32(value)) => text(&(value as i32).to_string()),
            Some(Decoded::Number(value)) if value.is_finite() => text(&crate::format_number(value)),
            Some(Decoded::Number(_)) => text("null"),
            Some(Decoded::HeapRef(_)) => {
                if let Some(string) = machine.string_value(value) {
                    Serialized::Text(quote(&string))
                } else if let Some(raw) = raw_json_text(machine, value) {
                    Serialized::Text(raw)
                } else if !machine.is_object(value) {
                    Serialized::Omitted
                } else {
                    let is_array = machine.array_elements(value)?.is_some();
                    if machine.is_callable(value)? && !is_array {
                        Serialized::Omitted
                    } else if is_array {
                        Serialized::Array(value)
                    } else {
                        Serialized::Object(value)
                    }
                }
            }
            Some(Decoded::Undefined | Decoded::Hole | Decoded::Uninitialized) | None => {
                Serialized::Omitted
            }
        })
    }

    /// Writes a value that [`Self::property`] gave at `depth`. An array element
    /// that was left out is `null`.
    fn write<H: Host>(
        &mut self,
        machine: &mut Machine<'_, H>,
        value: Serialized,
        depth: usize,
    ) -> Result<(), EvalFailure> {
        let (container, is_array) = match value {
            Serialized::Omitted => {
                self.output.push_utf8("null");
                return Ok(());
            }
            Serialized::Text(text) => {
                append(&mut self.output, &text);
                return Ok(());
            }
            Serialized::Array(array) => (array, true),
            Serialized::Object(object) => (object, false),
        };
        if !self.stack.insert(container) {
            return Err(type_error("Converting circular structure to JSON"));
        }
        let result = if is_array {
            self.array(machine, container, depth)
        } else {
            self.object(machine, container, depth)
        };
        self.stack.remove(&container);
        result
    }

    fn array<H: Host>(
        &mut self,
        machine: &mut Machine<'_, H>,
        array: Value,
        depth: usize,
    ) -> Result<(), EvalFailure> {
        let length = length_of_array_like(machine, array)?;
        self.output.push_unit(u16::from(b'['));
        for index in 0..length {
            self.open_member(index == 0, depth);
            let element = self.property(
                machine,
                array,
                EcmaString::encode(&index.to_string()),
                depth + 1,
            )?;
            self.write(machine, element, depth + 1)?;
        }
        self.close(b']', length != 0, depth);
        Ok(())
    }

    fn object<H: Host>(
        &mut self,
        machine: &mut Machine<'_, H>,
        object: Value,
        depth: usize,
    ) -> Result<(), EvalFailure> {
        let keys = self
            .property_list
            .map_or_else(|| machine.enumerable_keys(object), |keys| Ok(keys.to_vec()))?;
        self.output.push_unit(u16::from(b'{'));
        let mut empty = true;
        for key in keys {
            let member = self.property(machine, object, key.clone(), depth + 1)?;
            if matches!(member, Serialized::Omitted) {
                continue;
            }
            self.open_member(empty, depth);
            empty = false;
            append(&mut self.output, &quote(&key));
            self.output.push_unit(u16::from(b':'));
            if !self.gap.is_empty() {
                self.output.push_unit(u16::from(b' '));
            }
            self.write(machine, member, depth + 1)?;
        }
        self.close(b'}', !empty, depth);
        Ok(())
    }

    /// Writes what comes before a member of a container at `depth`: a comma after
    /// the first member, and with a gap a new line and the indent of the member.
    fn open_member(&mut self, first: bool, depth: usize) {
        if !first {
            self.output.push_unit(u16::from(b','));
        }
        if !self.gap.is_empty() {
            self.output.push_unit(u16::from(b'\n'));
            self.indent(depth + 1);
        }
    }

    /// Ends a container at `depth`. With a gap, the close of a container that has
    /// members goes on a new line at the indent of the container.
    fn close(&mut self, close: u8, has_members: bool, depth: usize) {
        if has_members && !self.gap.is_empty() {
            self.output.push_unit(u16::from(b'\n'));
            self.indent(depth);
        }
        self.output.push_unit(u16::from(close));
    }

    fn indent(&mut self, depth: usize) {
        for _ in 0..depth {
            append(&mut self.output, self.gap);
        }
    }
}

fn append(output: &mut EcmaStringBuilder, text: &EcmaString) {
    for &unit in text.as_units() {
        output.push_unit(unit);
    }
}

fn push_escape(output: &mut EcmaStringBuilder, escape: &str) {
    output.push_utf8(escape);
}

fn push_hex_escape(output: &mut EcmaStringBuilder, unit: u16) {
    output.push_utf8(&format!("\\u{unit:04x}"));
}

fn quote(text: &EcmaString) -> EcmaString {
    let mut output = EcmaStringBuilder::new();
    output.push_unit(u16::from(b'"'));
    let units = text.as_units();
    let mut offset = 0;
    while offset < units.len() {
        let unit = units[offset];
        match unit {
            0x0022 => push_escape(&mut output, "\\\""),
            0x005C => push_escape(&mut output, "\\\\"),
            0x0008 => push_escape(&mut output, "\\b"),
            0x000C => push_escape(&mut output, "\\f"),
            0x000A => push_escape(&mut output, "\\n"),
            0x000D => push_escape(&mut output, "\\r"),
            0x0009 => push_escape(&mut output, "\\t"),
            0x0000..=0x001F => push_hex_escape(&mut output, unit),
            0xD800..=0xDBFF
                if units
                    .get(offset + 1)
                    .is_some_and(|next| (0xDC00..=0xDFFF).contains(next)) =>
            {
                output.push_unit(unit);
                offset += 1;
                output.push_unit(units[offset]);
            }
            0xD800..=0xDFFF => push_hex_escape(&mut output, unit),
            _ => output.push_unit(unit),
        }
        offset += 1;
    }
    output.push_unit(u16::from(b'"'));
    output.finish()
}

// ---- edge parser -----------------------------------------------------------
//
// A recursive-descent JSON grammar over UTF-16 units that builds the value
// tree with CreateDataProperty semantics and records the source span of
// every primitive for reviver `context.source`.

struct Parser<'a> {
    source: &'a [u16],
    pos: usize,
}

enum ParseFailure {
    Syntax(String),
    Runtime(EvalFailure),
}

type ParseResult<T> = Result<T, ParseFailure>;

impl<'a> Parser<'a> {
    fn new(source: &'a [u16]) -> Self {
        Self { source, pos: 0 }
    }

    fn ws(&mut self) {
        while self
            .peek()
            .is_some_and(|unit| matches!(unit, 0x20 | 0x0A | 0x0D | 0x09))
        {
            self.pos += 1;
        }
    }

    fn peek(&self) -> Option<u16> {
        self.source.get(self.pos).copied()
    }

    /// Reads one JSON value. The arrays and objects that are open wait in a list, not
    /// on the Rust stack, so text of any depth parses, as in V8.
    fn value<H: Host>(&mut self, machine: &mut Machine<'_, H>) -> ParseResult<JsonNode> {
        let mut open: Vec<OpenContainer> = Vec::new();
        loop {
            self.ws();
            let mut node = match self.peek() {
                Some(unit) if unit == u16::from(b'[') => {
                    self.pos += 1;
                    self.ws();
                    if self.peek() != Some(u16::from(b']')) {
                        open.push(OpenContainer::Array {
                            values: Vec::new(),
                            children: Vec::new(),
                        });
                        continue;
                    }
                    self.pos += 1;
                    let value =
                        allocate_array(machine, Vec::new()).map_err(ParseFailure::Runtime)?;
                    JsonNode::Array {
                        value,
                        children: Vec::new(),
                    }
                }
                Some(unit) if unit == u16::from(b'{') => {
                    self.pos += 1;
                    self.ws();
                    let object = machine
                        .allocate(HeapEntry::Object {
                            properties: PropertyMap::default(),
                            prototype: Some(machine.intrinsics.object_prototype),
                            extensible: true,
                            boxed_primitive: None,
                        })
                        .map_err(EvalFailure::Runtime)
                        .map_err(ParseFailure::Runtime)?;
                    if self.peek() != Some(u16::from(b'}')) {
                        let key = self.member_key()?;
                        open.push(OpenContainer::Object {
                            value: object,
                            children: Vec::new(),
                            key,
                        });
                        continue;
                    }
                    self.pos += 1;
                    JsonNode::Object {
                        value: object,
                        children: Vec::new(),
                    }
                }
                _ => self.primitive(machine)?,
            };
            // `node` is the next member of the innermost open container. Close
            // every container that ends after it.
            loop {
                let Some(container) = open.last_mut() else {
                    return Ok(node);
                };
                container.push(machine, node)?;
                self.ws();
                let close = match container {
                    OpenContainer::Array { .. } => b']',
                    OpenContainer::Object { .. } => b'}',
                };
                match self.peek() {
                    Some(unit) if unit == u16::from(b',') => {
                        self.pos += 1;
                        self.ws();
                        if let OpenContainer::Object { key, .. } = container {
                            *key = self.member_key()?;
                        }
                        break;
                    }
                    Some(unit) if unit == u16::from(close) => {
                        self.pos += 1;
                        node = open.pop().expect("a container is open").close(machine)?;
                    }
                    _ => return Err(ParseFailure::Syntax(self.error_unexpected())),
                }
            }
        }
    }

    /// Reads the key of an object member and the `:` after it.
    fn member_key(&mut self) -> ParseResult<EcmaString> {
        if self.peek() != Some(u16::from(b'"')) {
            return Err(ParseFailure::Syntax(
                self.at("Expected property name or '}' in JSON"),
            ));
        }
        let key = self.string()?;
        self.ws();
        if self.peek() != Some(u16::from(b':')) {
            return Err(ParseFailure::Syntax(
                self.at("Expected ':' after property name in JSON"),
            ));
        }
        self.pos += 1;
        Ok(key)
    }

    fn primitive<H: Host>(&mut self, machine: &mut Machine<'_, H>) -> ParseResult<JsonNode> {
        let start = self.pos;
        match self.peek() {
            Some(unit) if unit == u16::from(b'n') => {
                self.literal("null")?;
                Ok(JsonNode::Primitive {
                    value: Value::NULL,
                    source: (start, self.pos),
                })
            }
            Some(unit) if unit == u16::from(b't') => {
                self.literal("true")?;
                Ok(JsonNode::Primitive {
                    value: Value::TRUE,
                    source: (start, self.pos),
                })
            }
            Some(unit) if unit == u16::from(b'f') => {
                self.literal("false")?;
                Ok(JsonNode::Primitive {
                    value: Value::FALSE,
                    source: (start, self.pos),
                })
            }
            Some(unit) if unit == u16::from(b'"') => self.string().and_then(|text| {
                allocate_string(machine, text)
                    .map(|value| JsonNode::Primitive {
                        value,
                        source: (start, self.pos),
                    })
                    .map_err(ParseFailure::Runtime)
            }),
            Some(unit)
                if unit == u16::from(b'-')
                    || (u16::from(b'0')..=u16::from(b'9')).contains(&unit) =>
            {
                self.number().map(|value| JsonNode::Primitive {
                    value,
                    source: (start, self.pos),
                })
            }
            _ => Err(ParseFailure::Syntax(self.error_unexpected())),
        }
    }

    fn literal(&mut self, literal: &str) -> ParseResult<()> {
        let matches = self.source[self.pos..]
            .iter()
            .zip(literal.bytes())
            .take(literal.len())
            .all(|(unit, byte)| *unit == u16::from(byte));
        if matches && self.source.len() >= self.pos + literal.len() {
            self.pos += literal.len();
            Ok(())
        } else {
            Err(ParseFailure::Syntax(self.error_unexpected()))
        }
    }

    fn string(&mut self) -> ParseResult<EcmaString> {
        self.pos += 1;
        let mut output = EcmaStringBuilder::new();
        loop {
            let Some(unit) = self.peek() else {
                return Err(ParseFailure::Syntax(self.at("Unterminated string in JSON")));
            };
            self.pos += 1;
            if unit == u16::from(b'"') {
                return Ok(output.finish());
            }
            if unit == u16::from(b'\\') {
                let Some(escape) = self.peek() else {
                    return Err(ParseFailure::Syntax(self.at("Unterminated string in JSON")));
                };
                self.pos += 1;
                match escape {
                    unit if unit == u16::from(b'"') => output.push_unit(u16::from(b'"')),
                    unit if unit == u16::from(b'\\') => output.push_unit(u16::from(b'\\')),
                    unit if unit == u16::from(b'/') => output.push_unit(u16::from(b'/')),
                    unit if unit == u16::from(b'b') => output.push_unit(0x0008),
                    unit if unit == u16::from(b'f') => output.push_unit(0x000C),
                    unit if unit == u16::from(b'n') => output.push_unit(0x000A),
                    unit if unit == u16::from(b'r') => output.push_unit(0x000D),
                    unit if unit == u16::from(b't') => output.push_unit(0x0009),
                    unit if unit == u16::from(b'u') => output.push_unit(self.hex_unit()?),
                    _ => return Err(ParseFailure::Syntax(self.error_unexpected())),
                }
            } else if unit <= 0x001F {
                return Err(ParseFailure::Syntax(self.error_unexpected()));
            } else {
                output.push_unit(unit);
            }
        }
    }

    fn hex_unit(&mut self) -> ParseResult<u16> {
        if self.pos + 4 > self.source.len() {
            return Err(ParseFailure::Syntax(self.error_unexpected()));
        }
        let mut value = 0_u16;
        for &unit in &self.source[self.pos..self.pos + 4] {
            let digit = match unit {
                unit if (u16::from(b'0')..=u16::from(b'9')).contains(&unit) => {
                    unit - u16::from(b'0')
                }
                unit if (u16::from(b'a')..=u16::from(b'f')).contains(&unit) => {
                    unit - u16::from(b'a') + 10
                }
                unit if (u16::from(b'A')..=u16::from(b'F')).contains(&unit) => {
                    unit - u16::from(b'A') + 10
                }
                _ => return Err(ParseFailure::Syntax(self.error_unexpected())),
            };
            value = value * 16 + digit;
        }
        self.pos += 4;
        Ok(value)
    }

    fn number(&mut self) -> ParseResult<Value> {
        let start = self.pos;
        if self.peek() == Some(u16::from(b'-')) {
            self.pos += 1;
        }
        if self.peek() == Some(u16::from(b'0')) {
            self.pos += 1;
            if self
                .peek()
                .is_some_and(|unit| (u16::from(b'0')..=u16::from(b'9')).contains(&unit))
            {
                return Err(ParseFailure::Syntax(self.at("Unexpected number in JSON")));
            }
        } else {
            self.digits()?;
        }
        if self.peek() == Some(u16::from(b'.')) {
            self.pos += 1;
            self.digits()?;
        }
        if self
            .peek()
            .is_some_and(|unit| unit == u16::from(b'e') || unit == u16::from(b'E'))
        {
            self.pos += 1;
            if self
                .peek()
                .is_some_and(|unit| unit == u16::from(b'+') || unit == u16::from(b'-'))
            {
                self.pos += 1;
            }
            self.digits()?;
        }
        let bytes: Vec<u8> = self.source[start..self.pos]
            .iter()
            .map(|unit| *unit as u8)
            .collect();
        let number = std::str::from_utf8(&bytes)
            .ok()
            .and_then(|text| text.parse::<f64>().ok())
            .ok_or_else(|| ParseFailure::Syntax(self.error_unexpected()))?;
        Ok(crate::number_value(number))
    }

    fn digits(&mut self) -> ParseResult<()> {
        let start = self.pos;
        while self
            .peek()
            .is_some_and(|unit| (u16::from(b'0')..=u16::from(b'9')).contains(&unit))
        {
            self.pos += 1;
        }
        (self.pos != start)
            .then_some(())
            .ok_or_else(|| ParseFailure::Syntax(self.error_unexpected()))
    }

    fn error_unexpected(&self) -> String {
        match self.peek() {
            None => self.at("Unexpected end of JSON input"),
            Some(unit) if unit <= 0x7F => self.at(&format!(
                "Unexpected token '{}' in JSON",
                char::from_u32(u32::from(unit)).expect("ASCII unit is scalar")
            )),
            Some(unit) => self.at(&format!("Unexpected code unit U+{unit:04X} in JSON")),
        }
    }

    fn at(&self, message: &str) -> String {
        let prefix = &self.source[..self.pos.min(self.source.len())];
        let line = prefix
            .iter()
            .filter(|unit| **unit == u16::from(b'\n'))
            .count()
            + 1;
        let column = prefix
            .iter()
            .rposition(|unit| *unit == u16::from(b'\n'))
            .map_or(prefix.len() + 1, |offset| prefix.len() - offset);
        format!(
            "{message} at position {} (line {line} column {column})",
            self.pos
        )
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, BuiltinHandler, native_function};
    use crate::{Limits, ThrowOrigin};

    macro_rules! test_machine {
        ($program:ident, $host:ident, $machine:ident) => {
            let $program = blank_program("<json-edge>");
            let mut $host = TestHost;
            let mut $machine = Machine::new(&$program, &mut $host, Limits::default());
            install(
                &mut $machine.heap,
                &mut $machine.atoms,
                &mut $machine.intrinsics.globals,
                &mut $machine.intrinsics.builtins,
            );
        };
    }

    fn global(machine: &mut Machine<'_, TestHost>, name: &str) -> Value {
        machine.intrinsics.global(name).expect("global exists")
    }

    fn method(machine: &mut Machine<'_, TestHost>, receiver: Value, name: &str) -> Value {
        machine
            .get_named_property(receiver, name)
            .expect("method exists")
    }

    fn text(machine: &mut Machine<'_, TestHost>, utf8: &str) -> Value {
        allocate_string(machine, EcmaString::encode(utf8)).expect("string allocation succeeds")
    }

    fn native(
        machine: &mut Machine<'_, TestHost>,
        name: &'static str,
        length: u32,
        handler: BuiltinHandler<TestHost>,
    ) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name,
            length,
            handler,
        });
        native_function(&mut machine.heap, &mut machine.atoms, id, name, length)
    }

    fn json_parse(
        machine: &mut Machine<'_, TestHost>,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let json = global(machine, "JSON");
        let parse = method(machine, json, "parse");
        machine.call_value(parse, json, args)
    }

    fn json_stringify(
        machine: &mut Machine<'_, TestHost>,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let json = global(machine, "JSON");
        let stringify = method(machine, json, "stringify");
        machine.call_value(stringify, json, args)
    }

    fn define_own(machine: &mut Machine<'_, TestHost>, object: Value, name: &str, value: Value) {
        let key = PropertyKey::Named(machine.intern_str(name));
        create_data_property(machine, object, key, value)
            .expect("own data property definition succeeds");
    }

    fn install_prototype_setter(
        machine: &mut Machine<'_, TestHost>,
        prototype: Value,
        name: &str,
        setter: Value,
    ) {
        let index = super::super::heap_index(prototype);
        let key = PropertyKey::Named(machine.intern_str(name));
        let properties = match &mut machine.heap[index] {
            HeapEntry::Object { properties, .. } | HeapEntry::Array { properties, .. } => {
                properties
            }
            _ => panic!("prototype must be an ordinary object"),
        };
        properties.insert(
            key,
            Property::Accessor {
                getter: None,
                setter: Some(setter),
                enumerable: true,
                configurable: true,
            },
        );
    }

    fn failing_setter(
        _: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(type_error("prototype setter must never be called by JSON"))
    }

    fn mark<H: Host>(machine: &mut Machine<'_, H>, name: &str) -> Result<(), EvalFailure> {
        let json = machine.intrinsics.global("JSON").expect("JSON exists");
        machine.set_data_property(json, name, Value::TRUE)
    }

    fn number_space_value_of(
        machine: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        mark(machine, "numberSpaceCoerced")?;
        Ok(BuiltinOutcome::Value(Value::int32(4)))
    }

    fn string_space_to_string(
        machine: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        mark(machine, "stringSpaceCoerced")?;
        Ok(BuiltinOutcome::Value(text(machine, "**")))
    }

    fn replacer_alpha_to_string(
        machine: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        mark(machine, "numberReplacerCoerced")?;
        Ok(BuiltinOutcome::Value(text(machine, "alpha")))
    }

    fn replacer_beta_to_string(
        machine: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        mark(machine, "stringReplacerCoerced")?;
        Ok(BuiltinOutcome::Value(text(machine, "beta")))
    }

    fn bigint_to_json(
        machine: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            EcmaString::encode("x"),
        )?))
    }

    fn descriptor_redefining_reviver(
        machine: &mut Machine<'_, TestHost>,
        holder: Value,
        args: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let key = machine
            .string_value(args[0])
            .expect("reviver key is a string")
            .to_utf8_lossy();
        if key == "a" {
            let b_key = PropertyKey::Named(machine.intern_str("b"));
            let index = super::super::heap_index(holder);
            let HeapEntry::Object { properties, .. } = &mut machine.heap[index] else {
                panic!("object member holder must be an object");
            };
            properties.insert(
                b_key,
                Property::Data {
                    value: Value::int32(7),
                    writable: false,
                    enumerable: false,
                    configurable: true,
                },
            );
        }
        Ok(BuiltinOutcome::Value(if key == "b" {
            Value::int32(9)
        } else {
            args.get(1).copied().unwrap_or(Value::UNDEFINED)
        }))
    }

    #[test]
    fn installer_exposes_edge_surface_with_expected_descriptors() {
        test_machine!(program, host, machine);
        let json = global(&mut machine, "JSON");
        for (name, length) in [
            ("parse", 2),
            ("stringify", 3),
            ("rawJSON", 1),
            ("isRawJSON", 1),
        ] {
            let function = method(&mut machine, json, name);
            assert!(machine.is_callable(function).expect("name lookup succeeds"));
            assert_eq!(
                machine
                    .get_named_property(function, "length")
                    .expect("length lookup succeeds"),
                Value::int32(length)
            );
            assert_eq!(
                machine
                    .get_named_property(function, "name")
                    .map(|name_value| {
                        machine
                            .string_value(name_value)
                            .expect("builtin name is a string")
                    })
                    .expect("name lookup succeeds"),
                EcmaString::encode(name)
            );
        }
        // Namespace methods are writable, non-enumerable, configurable.
        let index = super::super::heap_index(json);
        let HeapEntry::Object { properties, .. } = &machine.heap[index] else {
            panic!("JSON is a namespace object");
        };
        for name in ["parse", "stringify", "rawJSON", "isRawJSON"] {
            let Some(Property::Data {
                writable: true,
                enumerable: false,
                configurable: true,
                ..
            }) = properties.get_ascii(&machine.atoms, name)
            else {
                panic!("{name} must keep builtin data-property attributes");
            };
        }
    }

    #[test]
    fn parse_defines_own_properties_ignoring_prototype_setters() {
        test_machine!(program, host, machine);
        let setter = native(&mut machine, "hostileSetter", 1, failing_setter);
        let object_prototype = machine.intrinsics.object_prototype;
        install_prototype_setter(&mut machine, object_prototype, "x", setter);
        let source = text(&mut machine, "{\"x\":1}");
        let value = json_parse(&mut machine, &[source]).expect("prototype setter is bypassed");
        assert_eq!(
            machine
                .get_named_property(value, "x")
                .expect("own data property exists"),
            Value::int32(1)
        );
    }

    #[test]
    fn reviver_writeback_defines_own_properties_ignoring_prototype_setters() {
        test_machine!(program, host, machine);
        let setter = native(&mut machine, "hostileSetter", 1, failing_setter);
        let array_prototype = machine.intrinsics.array_prototype;
        install_prototype_setter(&mut machine, array_prototype, "0", setter);
        let source = text(&mut machine, "[1]");
        let reviver = native(
            &mut machine,
            "identityReviver",
            2,
            |_: &mut Machine<'_, TestHost>, _: Value, args: &[Value], _: bool| {
                Ok(BuiltinOutcome::Value(
                    args.get(1).copied().unwrap_or(Value::UNDEFINED),
                ))
            },
        );
        let value = json_parse(&mut machine, &[source, reviver])
            .expect("reviver write-back bypasses the setter");
        assert_eq!(
            machine
                .get_named_property(value, "0")
                .expect("element survives the write-back"),
            Value::int32(1)
        );
    }

    #[test]
    fn reviver_writeback_redefines_configurable_own_descriptor() {
        test_machine!(program, host, machine);
        let source = text(&mut machine, "{\"a\":1,\"b\":2}");
        let reviver = native(
            &mut machine,
            "descriptorRedefiningReviver",
            2,
            descriptor_redefining_reviver,
        );
        let value = json_parse(&mut machine, &[source, reviver])
            .expect("reviver redefines the configurable property");
        let key = PropertyKey::Named(machine.intern_str("b"));
        let Some(Property::Data {
            value: replacement,
            writable,
            enumerable,
            configurable,
        }) = machine.own_descriptor(value, &key).unwrap()
        else {
            panic!("reviver write-back must create a data property");
        };
        assert_eq!(replacement, Value::int32(9));
        assert!(writable && enumerable && configurable);
    }

    #[test]
    fn parse_reviver_receives_source_context_for_unmodified_primitives() {
        test_machine!(program, host, machine);
        let json = global(&mut machine, "JSON");
        let records = allocate_array(&mut machine, Vec::new()).expect("log array allocates");
        define_own(&mut machine, json, "edgeLog", records);
        let recorder = native(
            &mut machine,
            "sourceRecorder",
            3,
            |machine: &mut Machine<'_, TestHost>, _: Value, args: &[Value], _: bool| {
                let key = machine
                    .string_value(args[0])
                    .expect("reviver key is a string")
                    .to_utf8_lossy();
                let context = args.get(2).copied().unwrap_or(Value::UNDEFINED);
                let source = machine
                    .get_named_property(context, "source")
                    .expect("context lookup succeeds");
                let entry = match machine.string_value(source) {
                    Some(source) => format!("{key}<-{}", source.to_utf8_lossy()),
                    None => key,
                };
                let entry = allocate_string(machine, EcmaString::encode(&entry))?;
                let json = machine.intrinsics.global("JSON").expect("JSON exists");
                let log = machine.get_named_property(json, "edgeLog")?;
                let index = machine.array_elements(log)?.expect("log is an array").len();
                machine.set_data_property(log, &index.to_string(), entry)?;
                Ok(BuiltinOutcome::Value(
                    args.get(1).copied().unwrap_or(Value::UNDEFINED),
                ))
            },
        );
        let source = text(&mut machine, "{\"a\": [true, 0.5], \"b\": [1]}");
        let parse_function = method(&mut machine, json, "parse");
        let result = machine
            .call_value(parse_function, json, &[source, recorder])
            .expect("revived parse succeeds");
        let _ = result;
        let log = machine
            .get_named_property(json, "edgeLog")
            .expect("log exists");
        let entries: Vec<String> = machine
            .array_elements(log)
            .expect("log read succeeds")
            .expect("log is an array")
            .into_iter()
            .map(|entry| {
                machine
                    .string_value(entry)
                    .expect("entry is a string")
                    .to_utf8_lossy()
            })
            .collect();
        // Post-order walk: leaves first, then their holders, root last.
        // Primitives carry their exact source span; objects and arrays do not.
        assert_eq!(
            entries,
            vec![
                "0<-true".to_owned(),
                "1<-0.5".to_owned(),
                "a".to_owned(),
                "0<-1".to_owned(),
                "b".to_owned(),
                "".to_owned()
            ]
        );
    }

    #[test]
    fn parse_reviver_observes_modified_values_without_source() {
        test_machine!(program, host, machine);
        let json = global(&mut machine, "JSON");
        let records = allocate_array(&mut machine, Vec::new()).expect("log array allocates");
        define_own(&mut machine, json, "edgeLog", records);
        let recorder = native(
            &mut machine,
            "rewritingReviver",
            3,
            |machine: &mut Machine<'_, TestHost>, _: Value, args: &[Value], _: bool| {
                let key = machine
                    .string_value(args[0])
                    .expect("reviver key is a string")
                    .to_utf8_lossy();
                let context = args.get(2).copied().unwrap_or(Value::UNDEFINED);
                let has_source = machine.get_named_property(context, "source")? != Value::UNDEFINED;
                let json = machine.intrinsics.global("JSON").expect("JSON exists");
                let log = machine.get_named_property(json, "edgeLog")?;
                let index = machine.array_elements(log)?.expect("log is an array").len();
                let entry =
                    allocate_string(machine, EcmaString::encode(&format!("{key}:{has_source}")))?;
                machine.set_data_property(log, &index.to_string(), entry)?;
                // Replace numbers with a fresh value; the wrapper copy must
                // lose its source because it no longer parse-created.
                let value = args.get(1).copied().unwrap_or(Value::UNDEFINED);
                let primitive = machine.unbox_primitive_or_self(value)?;
                if matches!(
                    primitive.decode(),
                    Some(Decoded::Int32(_) | Decoded::Number(_))
                ) {
                    return Ok(BuiltinOutcome::Value(Value::int32(99)));
                }
                Ok(BuiltinOutcome::Value(value))
            },
        );
        let source = text(&mut machine, "[7, 8]");
        let parse_function = method(&mut machine, json, "parse");
        machine
            .call_value(parse_function, json, &[source, recorder])
            .expect("revived parse succeeds");
        let log = machine
            .get_named_property(json, "edgeLog")
            .expect("log exists");
        let entries: Vec<String> = machine
            .array_elements(log)
            .expect("log read succeeds")
            .expect("log is an array")
            .into_iter()
            .map(|entry| {
                machine
                    .string_value(entry)
                    .expect("entry is a string")
                    .to_utf8_lossy()
            })
            .collect();
        assert_eq!(
            entries,
            vec!["0:true", "1:true", ":false"]
                .into_iter()
                .map(str::to_owned)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn parse_uses_syntax_error_for_grammar_failures() {
        test_machine!(program, host, machine);
        let source = text(&mut machine, "{]");
        let error = json_parse(&mut machine, &[source]).expect_err("malformed JSON throws");
        let EvalFailure::ThrowValue(value) = error else {
            panic!("malformed JSON must throw a SyntaxError");
        };
        let syntax_error = global(&mut machine, "SyntaxError");
        let prototype = method(&mut machine, syntax_error, "prototype");
        assert!(
            machine
                .inherits_from_prototype(value, prototype)
                .expect("error has a valid prototype chain")
        );
    }

    #[test]
    fn raw_json_validates_empty_and_leading_continuations() {
        test_machine!(program, host, machine);
        let json = global(&mut machine, "JSON");
        let raw = method(&mut machine, json, "rawJSON");
        for input in ["", "   ", "\t\n ", ",", "] 1", "}0", "tru", "[1]", "{}"] {
            let argument = text(&mut machine, input);
            let error = machine
                .call_value(raw, json, &[argument])
                .expect_err("invalid raw text throws");
            assert!(
                matches!(error, EvalFailure::ThrowValue(_)),
                "{input:?} must surface as an abrupt throw"
            );
        }
        for input in ["0", "null", "\"s\"", "true"] {
            let argument = text(&mut machine, input);
            let object = machine
                .call_value(raw, json, &[argument])
                .expect("raw text outside the rejection set is accepted");
            assert_eq!(
                machine
                    .get_named_property(object, "rawJSON")
                    .and_then(|value| {
                        machine
                            .string_value(value)
                            .ok_or_else(|| type_error("rawJSON text must be a string"))
                    })
                    .expect("rawJSON carries its text"),
                EcmaString::encode(input)
            );
        }
    }

    #[test]
    fn stringify_rejects_primitive_bigint_and_serializes_wrappers() {
        test_machine!(program, host, machine);
        let bigint = machine
            .allocate(HeapEntry::BigInt("10".to_owned()))
            .expect("bigint allocation succeeds");
        let error =
            json_stringify(&mut machine, &[bigint]).expect_err("primitive BigInt cannot serialize");
        assert!(
            matches!(error, EvalFailure::Throw(ThrowOrigin::TypeError { .. })),
            "BigInt rejection is a TypeError"
        );
        let wrapped = machine
            .box_primitive(bigint)
            .expect("bigint wrapper boxing succeeds");
        let error =
            json_stringify(&mut machine, &[wrapped]).expect_err("boxed BigInt must also throw");
        assert!(
            matches!(error, EvalFailure::Throw(ThrowOrigin::TypeError { .. })),
            "boxed BigInt unboxes before rejection"
        );
        let holder = ordinary_object(&mut machine);
        define_own(&mut machine, holder, "v", bigint);
        assert!(
            json_stringify(&mut machine, &[holder]).is_err(),
            "nested primitive BigInt also throws"
        );
        let to_json = native(&mut machine, "toJSON", 1, bigint_to_json);
        let prototype = machine.intrinsics.builtins.bigint_prototype();
        machine
            .set_data_property(prototype, "toJSON", to_json)
            .expect("BigInt.prototype.toJSON installs");
        let output = json_stringify(&mut machine, &[bigint])
            .expect("toJSON overrides primitive BigInt rejection");
        assert!(
            machine
                .string_value(output)
                .expect("stringify returns text")
                .eq_ascii("\"x\""),
            "toJSON must run before primitive BigInt rejection"
        );
    }

    #[test]
    fn raw_json_requires_a_complete_primitive_json_text() {
        test_machine!(program, host, machine);
        let json = global(&mut machine, "JSON");
        let raw = method(&mut machine, json, "rawJSON");
        for input in [
            "", "   ", "\t\n ", ",", "] 1", "}0", "tru", "0 1", "null x", "[1]", "{}", " 0",
            "\ttrue ", " 123", "123 ",
        ] {
            let argument = text(&mut machine, input);
            let error = machine
                .call_value(raw, json, &[argument])
                .expect_err("invalid, trailing, or structured raw JSON throws");
            assert!(
                matches!(error, EvalFailure::ThrowValue(_)),
                "{input:?} must surface as a SyntaxError object"
            );
        }
        for input in ["0", "null", "\"s\"", "true"] {
            let argument = text(&mut machine, input);
            let object = machine
                .call_value(raw, json, &[argument])
                .expect("a complete primitive JSON text is accepted");
            assert_eq!(
                machine
                    .get_named_property(object, "rawJSON")
                    .and_then(|value| {
                        machine
                            .string_value(value)
                            .ok_or_else(|| type_error("rawJSON text must be a string"))
                    })
                    .expect("rawJSON carries its text"),
                EcmaString::encode(input)
            );
        }
    }

    #[test]
    fn is_raw_json_relies_on_the_internal_brand() {
        test_machine!(program, host, machine);
        let json = global(&mut machine, "JSON");
        let raw = method(&mut machine, json, "rawJSON");
        let is_raw = method(&mut machine, json, "isRawJSON");
        let argument = text(&mut machine, "1");
        let genuine = machine
            .call_value(raw, json, &[argument])
            .expect("raw JSON creation succeeds");
        assert_eq!(
            machine
                .call_value(is_raw, json, &[genuine])
                .expect("brand check succeeds"),
            Value::TRUE
        );
        // A structurally similar forgery without the private brand is rejected.
        let text_property = text(&mut machine, "1");
        let raw_json_key = PropertyKey::Named(machine.intern_str("rawJSON"));
        let forgery = machine
            .allocate(HeapEntry::Object {
                properties: {
                    let mut properties = PropertyMap::default();
                    properties.insert(
                        raw_json_key,
                        Property::Data {
                            value: text_property,
                            writable: false,
                            enumerable: true,
                            configurable: false,
                        },
                    );
                    properties
                },
                prototype: None,
                extensible: false,
                boxed_primitive: None,
            })
            .expect("forgery allocation succeeds");
        assert_eq!(
            machine
                .call_value(is_raw, json, &[forgery])
                .expect("brand check succeeds"),
            Value::FALSE
        );
        for probe in [Value::NULL, Value::UNDEFINED, Value::TRUE, Value::int32(1)] {
            assert_eq!(
                machine
                    .call_value(is_raw, json, &[probe])
                    .expect("brand check succeeds"),
                Value::FALSE
            );
        }
        assert_eq!(
            machine
                .call_value(is_raw, json, &[])
                .expect("missing argument is not an error"),
            Value::FALSE
        );
    }

    #[test]
    fn raw_json_object_is_frozen_and_null_prototyped() {
        test_machine!(program, host, machine);
        let json = global(&mut machine, "JSON");
        let raw = method(&mut machine, json, "rawJSON");
        let argument = text(&mut machine, "1");
        let object = machine
            .call_value(raw, json, &[argument])
            .expect("raw JSON creation succeeds");
        let index = super::super::heap_index(object);
        let HeapEntry::Object {
            properties,
            prototype,
            extensible,
            ..
        } = &machine.heap[index]
        else {
            panic!("raw JSON is an ordinary object");
        };
        assert!(prototype.is_none(), "raw JSON has a null prototype");
        assert!(!extensible, "raw JSON is frozen");
        let Some(Property::Data {
            writable: false,
            enumerable: true,
            configurable: false,
            ..
        }) = properties.get_ascii(&machine.atoms, "rawJSON")
        else {
            panic!("rawJSON property must be frozen but enumerable");
        };
    }

    #[test]
    fn stringify_injects_raw_json_verbatim() {
        test_machine!(program, host, machine);
        let json = global(&mut machine, "JSON");
        let raw = method(&mut machine, json, "rawJSON");
        let argument = text(&mut machine, "1e2");
        let raw_value = machine
            .call_value(raw, json, &[argument])
            .expect("raw JSON creation succeeds");
        let output = json_stringify(&mut machine, &[raw_value]).expect("raw value stringifies");
        assert_eq!(
            machine.string_value(output).expect("string result"),
            EcmaString::encode("1e2")
        );
        let holder = ordinary_object(&mut machine);
        define_own(&mut machine, holder, "v", raw_value);
        let output = json_stringify(&mut machine, &[holder]).expect("nested raw value stringifies");
        assert_eq!(
            machine.string_value(output).expect("string result"),
            EcmaString::encode("{\"v\":1e2}")
        );
    }

    #[test]
    fn stringify_rejects_primitive_and_boxed_bigint_after_to_json() {
        test_machine!(program, host, machine);
        let bigint = machine
            .allocate(HeapEntry::BigInt("10".to_owned()))
            .expect("bigint allocation succeeds");
        let error =
            json_stringify(&mut machine, &[bigint]).expect_err("primitive BigInt cannot serialize");
        assert!(
            matches!(error, EvalFailure::Throw(ThrowOrigin::TypeError { .. })),
            "BigInt rejection is a TypeError"
        );
        let wrapped = machine
            .box_primitive(bigint)
            .expect("bigint wrapper boxing succeeds");
        let error =
            json_stringify(&mut machine, &[wrapped]).expect_err("boxed BigInt must also throw");
        assert!(
            matches!(error, EvalFailure::Throw(ThrowOrigin::TypeError { .. })),
            "boxed BigInt unboxes before rejection"
        );
        let holder = ordinary_object(&mut machine);
        define_own(&mut machine, holder, "v", bigint);
        assert!(
            json_stringify(&mut machine, &[holder]).is_err(),
            "nested primitive BigInt also throws"
        );
        let to_json = native(&mut machine, "toJSON", 1, bigint_to_json);
        machine
            .set_data_property(wrapped, "toJSON", to_json)
            .expect("wrapper toJSON installs");
        let output =
            json_stringify(&mut machine, &[wrapped]).expect("toJSON runs before wrapper unboxing");
        assert!(
            machine
                .string_value(output)
                .expect("stringify returns text")
                .eq_ascii("\"x\""),
            "toJSON must run before primitive BigInt rejection"
        );
    }

    #[test]
    fn stringify_rejects_cycles_but_allows_shared_leaves() {
        test_machine!(program, host, machine);
        let first = ordinary_object(&mut machine);
        let second = ordinary_object(&mut machine);
        define_own(&mut machine, first, "peer", second);
        define_own(&mut machine, second, "peer", first);
        let error =
            json_stringify(&mut machine, &[first]).expect_err("cyclic structures cannot serialize");
        assert!(matches!(
            error,
            EvalFailure::Throw(ThrowOrigin::TypeError { .. })
        ));
        // A shared leaf visited twice is not a cycle.
        let leaf = ordinary_object(&mut machine);
        define_own(&mut machine, leaf, "n", Value::int32(7));
        let array_prototype = machine.intrinsics.array_prototype;
        let shared = machine
            .allocate(HeapEntry::Array {
                elements: vec![leaf, leaf],
                properties: PropertyMap::default(),
                prototype: Some(array_prototype),
                extensible: true,
                length_writable: true,
            })
            .expect("array allocation succeeds");
        let output = json_stringify(&mut machine, &[shared]).expect("diamond references serialize");
        assert_eq!(
            machine.string_value(output).expect("string result"),
            EcmaString::encode("[{\"n\":7},{\"n\":7}]")
        );
    }

    #[test]
    fn stringify_maps_holes_undefined_and_functions_to_null_in_arrays() {
        test_machine!(program, host, machine);
        let json = global(&mut machine, "JSON");
        let stringify = method(&mut machine, json, "stringify");
        let function = native(
            &mut machine,
            "holeFn",
            0,
            |_: &mut Machine<'_, TestHost>, _: Value, _: &[Value], _: bool| {
                Ok(BuiltinOutcome::Value(Value::UNDEFINED))
            },
        );
        let array_prototype = machine.intrinsics.array_prototype;
        let sparse = machine
            .allocate(HeapEntry::Array {
                elements: vec![Value::HOLE, Value::UNDEFINED, function, Value::int32(5)],
                properties: PropertyMap::default(),
                prototype: Some(array_prototype),
                extensible: true,
                length_writable: true,
            })
            .expect("sparse array allocation succeeds");
        let output = machine
            .call_value(stringify, json, &[sparse])
            .expect("sparse array stringifies");
        assert_eq!(
            machine.string_value(output).expect("string result"),
            EcmaString::encode("[null,null,null,5]")
        );
        let undefined_value = Value::UNDEFINED;
        let holder = ordinary_object(&mut machine);
        define_own(&mut machine, holder, "a", undefined_value);
        define_own(&mut machine, holder, "b", Value::int32(1));
        let output = machine
            .call_value(stringify, json, &[holder])
            .expect("undefined members are omitted");
        assert_eq!(
            machine.string_value(output).expect("string result"),
            EcmaString::encode("{\"b\":1}")
        );
    }

    #[test]
    fn stringify_gap_coercion_and_truncation() {
        test_machine!(program, host, machine);
        let json = global(&mut machine, "JSON");
        let holder = ordinary_object(&mut machine);
        define_own(&mut machine, holder, "a", Value::int32(1));

        let output = json_stringify(&mut machine, &[holder, Value::UNDEFINED, Value::int32(3)])
            .expect("numeric gap stringifies");
        assert_eq!(
            machine.string_value(output).expect("string result"),
            EcmaString::encode("{\n   \"a\": 1\n}")
        );
        let output = json_stringify(&mut machine, &[holder, Value::UNDEFINED, Value::int32(12)])
            .expect("numeric gap is clamped to ten");
        assert_eq!(
            machine.string_value(output).expect("string result"),
            EcmaString::encode("{\n          \"a\": 1\n}")
        );
        let gap = text(&mut machine, "abcdefghiJKL");
        let output = json_stringify(&mut machine, &[holder, Value::UNDEFINED, gap])
            .expect("string gap truncates at ten units");
        assert_eq!(
            machine.string_value(output).expect("string result"),
            EcmaString::encode("{\nabcdefghiJ\"a\": 1\n}")
        );
        // Number wrappers run observable ToNumber before the clamp.
        let boxed = machine
            .box_primitive(Value::int32(2))
            .expect("number boxing succeeds");
        let value_of = native(&mut machine, "valueOf", 0, number_space_value_of);
        machine
            .set_data_property(boxed, "valueOf", value_of)
            .expect("number wrapper valueOf installs");
        let output = json_stringify(&mut machine, &[holder, Value::UNDEFINED, boxed])
            .expect("boxed number gap uses observable ToNumber");
        assert_eq!(
            machine.string_value(output).expect("string result"),
            EcmaString::encode("{\n    \"a\": 1\n}")
        );
        assert_eq!(
            machine
                .get_named_property(json, "numberSpaceCoerced")
                .unwrap(),
            Value::TRUE
        );
        let string_primitive = text(&mut machine, "ignored");
        let boxed_string = machine
            .box_primitive(string_primitive)
            .expect("string boxing succeeds");
        let to_string = native(&mut machine, "toString", 0, string_space_to_string);
        machine
            .set_data_property(boxed_string, "toString", to_string)
            .expect("string wrapper toString installs");
        let output = json_stringify(&mut machine, &[holder, Value::UNDEFINED, boxed_string])
            .expect("boxed string gap uses observable ToString");
        assert_eq!(
            machine.string_value(output).expect("string result"),
            EcmaString::encode("{\n**\"a\": 1\n}")
        );
        assert_eq!(
            machine
                .get_named_property(json, "stringSpaceCoerced")
                .unwrap(),
            Value::TRUE
        );
        let throwing_number = machine
            .box_primitive(Value::int32(1))
            .expect("number boxing succeeds");
        let throwing_value_of = native(&mut machine, "valueOf", 0, failing_setter);
        machine
            .set_data_property(throwing_number, "valueOf", throwing_value_of)
            .expect("throwing valueOf installs");
        assert!(
            json_stringify(&mut machine, &[holder, Value::UNDEFINED, throwing_number]).is_err(),
            "abrupt ToNumber completion propagates"
        );
        let throwing_string_primitive = text(&mut machine, "ignored");
        let throwing_string = machine
            .box_primitive(throwing_string_primitive)
            .expect("string boxing succeeds");
        let throwing_to_string = native(&mut machine, "toString", 0, failing_setter);
        machine
            .set_data_property(throwing_string, "toString", throwing_to_string)
            .expect("throwing toString installs");
        assert!(
            json_stringify(&mut machine, &[holder, Value::UNDEFINED, throwing_string]).is_err(),
            "abrupt ToString completion propagates"
        );
        // A plain object never observes a coercion at all.
        let invasive = ordinary_object(&mut machine);
        let output = json_stringify(&mut machine, &[holder, Value::UNDEFINED, invasive])
            .expect("plain object space leaves a compact gap");
        assert_eq!(
            machine.string_value(output).expect("string result"),
            EcmaString::encode("{\"a\":1}")
        );
    }

    #[test]
    fn stringify_escapes_lone_surrogates_and_controls() {
        test_machine!(program, host, machine);
        let json = global(&mut machine, "JSON");
        let stringify = method(&mut machine, json, "stringify");
        let lone = allocate_string(&mut machine, EcmaString::from_units(&[0xD800]))
            .expect("string allocation succeeds");
        let output = machine
            .call_value(stringify, json, &[lone])
            .expect("lone surrogate stringifies");
        assert_eq!(
            machine.string_value(output).expect("string result"),
            EcmaString::encode("\"\\ud800\"")
        );
        let pair = allocate_string(&mut machine, EcmaString::from_units(&[0xD83D, 0xDE03]))
            .expect("string allocation succeeds");
        let output = machine
            .call_value(stringify, json, &[pair])
            .expect("well-formed pair stringifies");
        assert_eq!(
            machine
                .string_value(output)
                .expect("string result")
                .as_units(),
            &[0x0022, 0xD83D, 0xDE03, 0x0022]
        );
        let control = allocate_string(&mut machine, EcmaString::from_units(&[0x61, 0x0001, 0x62]))
            .expect("string allocation succeeds");
        let output = machine
            .call_value(stringify, json, &[control])
            .expect("control characters stringify");
        assert_eq!(
            machine.string_value(output).expect("string result"),
            EcmaString::encode("\"a\\u0001b\"")
        );
    }

    #[test]
    fn replacer_array_enumerates_before_any_space_observation() {
        test_machine!(program, host, machine);
        let holder = ordinary_object(&mut machine);
        // Keys defined in reverse insertion order; the property list must win.
        define_own(&mut machine, holder, "gamma", Value::int32(3));
        define_own(&mut machine, holder, "alpha", Value::int32(1));
        define_own(&mut machine, holder, "beta", Value::int32(2));
        let json = global(&mut machine, "JSON");
        let alpha = machine
            .box_primitive(Value::int32(1))
            .expect("number wrapper allocates");
        let alpha_to_string = native(&mut machine, "toString", 0, replacer_alpha_to_string);
        machine
            .set_data_property(alpha, "toString", alpha_to_string)
            .expect("number wrapper toString installs");
        let beta_primitive = text(&mut machine, "ignored");
        let beta = machine
            .box_primitive(beta_primitive)
            .expect("string wrapper allocates");
        let beta_to_string = native(&mut machine, "toString", 0, replacer_beta_to_string);
        machine
            .set_data_property(beta, "toString", beta_to_string)
            .expect("string wrapper toString installs");
        let duplicate = text(&mut machine, "alpha");
        let array_prototype = machine.intrinsics.array_prototype;
        let list = machine
            .allocate(HeapEntry::Array {
                elements: vec![alpha, beta, duplicate],
                properties: PropertyMap::default(),
                prototype: Some(array_prototype),
                extensible: true,
                length_writable: true,
            })
            .expect("replacer array allocation succeeds");
        let stringify = method(&mut machine, json, "stringify");
        let output = machine
            .call_value(stringify, json, &[holder, list])
            .expect("property list drives key order and dedupes");
        assert_eq!(
            machine.string_value(output).expect("string result"),
            EcmaString::encode("{\"alpha\":1,\"beta\":2}")
        );
        assert_eq!(
            machine
                .get_named_property(json, "numberReplacerCoerced")
                .unwrap(),
            Value::TRUE
        );
        assert_eq!(
            machine
                .get_named_property(json, "stringReplacerCoerced")
                .unwrap(),
            Value::TRUE
        );
    }

    #[test]
    fn evaluate_json_module_source_parses_and_rejects() {
        test_machine!(program, host, machine);
        let value = evaluate_json_module_source(&mut machine, &EcmaString::encode("[1,2]"))
            .expect("valid module source parses");
        let elements = machine
            .array_elements(value)
            .expect("array read succeeds")
            .expect("module tree is an array");
        assert_eq!(elements, vec![Value::int32(1), Value::int32(2)]);
        let error = evaluate_json_module_source(&mut machine, &EcmaString::encode("{]"))
            .expect_err("invalid module source throws");
        let EvalFailure::ThrowValue(thrown) = error else {
            panic!("module grammar failures must throw a SyntaxError");
        };
        let syntax_error = global(&mut machine, "SyntaxError");
        let prototype = method(&mut machine, syntax_error, "prototype");
        assert!(
            machine
                .inherits_from_prototype(thrown, prototype)
                .expect("error has a valid prototype chain")
        );
    }

    fn nested_text(depth: usize) -> String {
        format!("{}0{}", "[".repeat(depth), "]".repeat(depth))
    }

    fn nested_array(machine: &mut Machine<'_, TestHost>, depth: usize) -> Value {
        let mut value = Value::int32(0);
        for _ in 0..depth {
            value = allocate_array(machine, vec![value]).expect("array allocation succeeds");
        }
        value
    }

    fn is_stack_overflow(result: &Result<Value, EvalFailure>) -> bool {
        matches!(result, Err(EvalFailure::Throw(origin)) if *origin == crate::STACK_OVERFLOW)
    }

    fn identity_reviver(machine: &mut Machine<'_, TestHost>) -> Value {
        native(
            machine,
            "identityReviver",
            2,
            |_: &mut Machine<'_, TestHost>, _: Value, args: &[Value], _: bool| {
                Ok(BuiltinOutcome::Value(
                    args.get(1).copied().unwrap_or(Value::UNDEFINED),
                ))
            },
        )
    }

    #[test]
    fn a_recursive_walk_without_a_measured_stack_throws_range_error() {
        test_machine!(program, host, machine);
        let reviver = identity_reviver(&mut machine);
        let fits = text(&mut machine, &nested_text(UNMEASURED_JSON_DEPTH - 1));
        assert!(json_parse(&mut machine, &[fits, reviver]).is_ok());
        let deep = text(&mut machine, &nested_text(UNMEASURED_JSON_DEPTH + 1));
        assert!(is_stack_overflow(&json_parse(
            &mut machine,
            &[deep, reviver]
        )));
        let fits = nested_array(&mut machine, UNMEASURED_JSON_DEPTH - 1);
        assert!(json_stringify(&mut machine, &[fits]).is_ok());
        let deep = nested_array(&mut machine, UNMEASURED_JSON_DEPTH + 1);
        assert!(is_stack_overflow(&json_stringify(&mut machine, &[deep])));
    }

    #[test]
    fn text_of_any_depth_parses_on_a_small_stack() {
        with_measured_stack(1 << 20, |machine| {
            let depth = 1 << 18;
            let mut source = "[{\"a\":".repeat(depth);
            source.push('0');
            source.push_str(&"}]".repeat(depth));
            let deep = text(machine, &source);
            let mut value =
                json_parse(machine, &[deep]).unwrap_or_else(|error| panic!("{error:?}"));
            for _ in 0..depth {
                let object = machine
                    .get_named_property(value, "0")
                    .expect("element exists");
                value = machine
                    .get_named_property(object, "a")
                    .expect("member exists");
            }
            assert_eq!(value, Value::int32(0));
        });
        test_machine!(program, host, machine);
        let deep = text(&mut machine, &nested_text(UNMEASURED_JSON_DEPTH + 1));
        assert!(json_parse(&mut machine, &[deep]).is_ok());
    }

    /// Runs `body` with a machine that measures its native stack, on a thread whose
    /// stack holds `max_stack_bytes` and the slack past it.
    fn with_measured_stack(max_stack_bytes: usize, body: fn(&mut Machine<'_, TestHost>)) {
        std::thread::Builder::new()
            .stack_size(max_stack_bytes + (8 << 20))
            .spawn(move || {
                let program = blank_program("<json-edge>");
                let mut host = TestHost;
                let limits = Limits {
                    max_stack_bytes,
                    ..Limits::default()
                };
                let mut machine = Machine::new(&program, &mut host, limits);
                install(
                    &mut machine.heap,
                    &mut machine.atoms,
                    &mut machine.intrinsics.globals,
                    &mut machine.intrinsics.builtins,
                );
                body(&mut machine);
            })
            .expect("the thread starts")
            .join()
            .expect("the body does not panic");
    }

    #[test]
    fn a_measured_stack_holds_json_as_deep_as_it_fits() {
        with_measured_stack(64 << 20, |machine| {
            let deep = text(machine, &nested_text(4_000));
            assert!(json_parse(machine, &[deep]).is_ok());
            let deep = nested_array(machine, 4_000);
            let Ok(output) = json_stringify(machine, &[deep]) else {
                panic!("a nesting of 4,000 arrays fits the stack");
            };
            let output = machine
                .string_value(output)
                .expect("stringify gives a string");
            assert_eq!(output.to_utf8_lossy(), nested_text(4_000));
        });
    }

    #[test]
    fn a_recursive_walk_past_a_measured_stack_throws_range_error() {
        with_measured_stack(1 << 20, |machine| {
            let reviver = identity_reviver(machine);
            let deep = text(machine, &nested_text(1 << 16));
            assert!(is_stack_overflow(&json_parse(machine, &[deep, reviver])));
            let deep = nested_array(machine, 1 << 16);
            assert!(is_stack_overflow(&json_stringify(machine, &[deep])));
        });
    }

    #[test]
    fn an_indented_value_is_written_as_before() {
        test_machine!(program, host, machine);
        let script = r#"{"a":[1,[],{},[{"b":null}],"x"],"c":{},"d":{"e":[true]}}"#;
        let source = text(&mut machine, script);
        let Ok(value) = json_parse(&mut machine, &[source]) else {
            panic!("the text parses");
        };
        let gap = text(&mut machine, "--");
        let Ok(output) = json_stringify(&mut machine, &[value, Value::UNDEFINED, gap]) else {
            panic!("the value serializes");
        };
        let output = machine
            .string_value(output)
            .expect("stringify gives a string");
        assert_eq!(
            output.to_utf8_lossy(),
            "{\n--\"a\": [\n----1,\n----[],\n----{},\n----[\n------{\n--------\"b\": null\n------}\n----],\n----\"x\"\n--],\n--\"c\": {},\n--\"d\": {\n----\"e\": [\n------true\n----]\n--}\n}"
        );
    }
}
