//! DataView over the canonical ArrayBuffer and SharedArrayBuffer backings.

use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::Value;

use super::arraybuffer::to_index;
use super::typedarray_all::{
    ElementKind, LengthSlot, ViewBuffer, storage_from_value, value_from_storage,
};
use super::{
    builtin_property, define_data, heap_index, install_constructor_function, install_function,
    range_error, type_error,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct DataViewBounds {
    pub(crate) byte_length: usize,
    pub(crate) detached: bool,
    pub(crate) out_of_bounds: bool,
}

#[derive(Clone, Copy)]
struct ViewFields {
    buffer: Value,
    byte_offset: usize,
    byte_length: LengthSlot,
}

fn fields<H: Host>(machine: &Machine<'_, H>, view: Value) -> Result<ViewFields, EvalFailure> {
    let Some(index) = machine.runtime_slot(view).map_err(EvalFailure::Runtime)? else {
        return Err(type_error(
            "DataView method called on incompatible receiver",
        ));
    };
    let HeapEntry::DataView {
        buffer,
        byte_offset,
        byte_length,
        ..
    } = &machine.heap[index]
    else {
        return Err(type_error(
            "DataView method called on incompatible receiver",
        ));
    };
    Ok(ViewFields {
        buffer: *buffer,
        byte_offset: *byte_offset,
        byte_length: *byte_length,
    })
}

pub(crate) fn dataview_bounds<H: Host>(
    machine: &Machine<'_, H>,
    view: Value,
) -> Result<DataViewBounds, EvalFailure> {
    bounds_for(machine, fields(machine, view)?)
}

fn bounds_for<H: Host>(
    machine: &Machine<'_, H>,
    fields: ViewFields,
) -> Result<DataViewBounds, EvalFailure> {
    let buffer = ViewBuffer::from_value(machine, fields.buffer)?;
    if buffer.is_detached(machine) {
        return Ok(DataViewBounds {
            byte_length: 0,
            detached: true,
            out_of_bounds: true,
        });
    }
    let buffer_length = buffer.byte_length(machine)?;
    if fields.byte_offset > buffer_length {
        return Ok(DataViewBounds {
            byte_length: 0,
            detached: false,
            out_of_bounds: true,
        });
    }
    let remaining = buffer_length - fields.byte_offset;
    let byte_length = match fields.byte_length {
        LengthSlot::Auto => remaining,
        LengthSlot::Fixed(length) if length <= remaining => length,
        LengthSlot::Fixed(_) => {
            return Ok(DataViewBounds {
                byte_length: 0,
                detached: false,
                out_of_bounds: true,
            });
        }
    };
    Ok(DataViewBounds {
        byte_length,
        detached: false,
        out_of_bounds: false,
    })
}

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = super::super::ordinary_prototype(heap, builtins.object_prototype());
    let constructor = install_constructor_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "DataView",
            length: 1,
            handler: constructor::<H>,
        },
    );
    builtins.set_constructor_prototype(heap, atoms, shapes, constructor, prototype);
    builtins.set_dataview_prototype(prototype);
    define_data(heap, atoms, shapes, prototype, "constructor", constructor);

    for (name, length, handler) in [
        ("getInt8", 1, get_int8::<H> as BuiltinHandler<H>),
        ("getUint8", 1, get_uint8::<H>),
        ("getInt16", 1, get_int16::<H>),
        ("getUint16", 1, get_uint16::<H>),
        ("getInt32", 1, get_int32::<H>),
        ("getUint32", 1, get_uint32::<H>),
        ("getFloat16", 1, get_float16::<H>),
        ("getFloat32", 1, get_float32::<H>),
        ("getFloat64", 1, get_float64::<H>),
        ("getBigInt64", 1, get_big_int64::<H>),
        ("getBigUint64", 1, get_big_uint64::<H>),
        ("setInt8", 2, set_int8::<H>),
        ("setUint8", 2, set_uint8::<H>),
        ("setInt16", 2, set_int16::<H>),
        ("setUint16", 2, set_uint16::<H>),
        ("setInt32", 2, set_int32::<H>),
        ("setUint32", 2, set_uint32::<H>),
        ("setFloat16", 2, set_float16::<H>),
        ("setFloat32", 2, set_float32::<H>),
        ("setFloat64", 2, set_float64::<H>),
        ("setBigInt64", 2, set_big_int64::<H>),
        ("setBigUint64", 2, set_big_uint64::<H>),
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
        define_data(heap, atoms, shapes, prototype, name, function);
    }

    for (property_name, function_name, handler) in [
        ("buffer", "get buffer", get_buffer::<H> as BuiltinHandler<H>),
        ("byteLength", "get byteLength", get_byte_length::<H>),
        ("byteOffset", "get byteOffset", get_byte_offset::<H>),
    ] {
        let getter = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name: function_name,
                length: 0,
                handler,
            },
        );
        let HeapEntry::Object { properties, .. } = &mut heap[heap_index(prototype)] else {
            unreachable!("DataView.prototype is ordinary")
        };
        properties.insert(
            shapes,
            PropertyKey::Named(atoms.intern_str(property_name)),
            Property::Accessor {
                getter: Some(getter),
                setter: None,
                enumerable: false,
                configurable: true,
            },
        );
    }
    let tag = super::super::push(heap, HeapEntry::String(EcmaString::encode("DataView")));
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(prototype)] else {
        unreachable!("DataView.prototype is ordinary")
    };
    properties.insert(
        shapes,
        PropertyKey::Symbol(heap_index(builtins.symbol_to_string_tag()) as u32),
        builtin_property(tag),
    );
    globals.insert(EcmaString::encode("DataView"), constructor);
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _callee: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !constructing {
        return Err(type_error("DataView constructor requires 'new'"));
    }
    let buffer_value = args.first().copied().unwrap_or(Value::UNDEFINED);
    let buffer = ViewBuffer::from_value(machine, buffer_value)?;
    let byte_offset = to_index(machine, args.get(1).copied().unwrap_or(Value::UNDEFINED))?;
    if buffer.is_detached(machine) {
        return Err(type_error(
            "Cannot construct a DataView over a detached buffer",
        ));
    }
    let buffer_length = buffer.byte_length(machine)?;
    if byte_offset > buffer_length {
        return Err(range_error("DataView byteOffset is outside the buffer"));
    }
    let byte_length = match args.get(2).copied() {
        None | Some(Value::UNDEFINED) if buffer.is_resizable(machine)? => LengthSlot::Auto,
        None | Some(Value::UNDEFINED) => LengthSlot::Fixed(buffer_length - byte_offset),
        Some(value) => {
            let length = to_index(machine, value)?;
            if byte_offset
                .checked_add(length)
                .is_none_or(|end| end > buffer_length)
            {
                return Err(range_error("DataView exceeds its buffer"));
            }
            LengthSlot::Fixed(length)
        }
    };
    let intrinsic = machine.intrinsics.builtins.dataview_prototype();
    let new_target = machine.current_new_target();
    let prototype = if new_target == Value::UNDEFINED {
        intrinsic
    } else {
        let candidate = machine.get_named_property(new_target, "prototype")?;
        if machine.is_object(candidate) {
            candidate
        } else {
            intrinsic
        }
    };
    if buffer.is_detached(machine) {
        return Err(type_error(
            "Cannot construct a DataView over a detached buffer",
        ));
    }
    let depth = machine.native_roots.len();
    machine.push_native_roots(depth, &[prototype, buffer_value]);
    let outcome = (|| -> Result<BuiltinOutcome, EvalFailure> {
        let current_buffer_length = buffer.byte_length(machine)?;
        if byte_offset > current_buffer_length {
            return Err(range_error("DataView byteOffset is outside the buffer"));
        }
        if let LengthSlot::Fixed(length) = byte_length
            && byte_offset
                .checked_add(length)
                .is_none_or(|end| end > current_buffer_length)
        {
            return Err(range_error("DataView exceeds its buffer"));
        }
        let view = machine
            .allocate(HeapEntry::DataView {
                buffer: buffer_value,
                byte_offset,
                byte_length,
                properties: PropertyMap::default(),
                prototype: Some(prototype),
                extensible: true,
            })
            .map_err(EvalFailure::Runtime)?;
        Ok(BuiltinOutcome::Value(view))
    })();
    machine.pop_native_roots(depth);
    outcome
}

fn read<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    kind: ElementKind,
) -> Result<BuiltinOutcome, EvalFailure> {
    let fields = fields(machine, this)?;
    let offset = to_index(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let little_endian = kind.element_size() == 1
        || machine.to_boolean(args.get(1).copied().unwrap_or(Value::UNDEFINED));
    let buffer = ViewBuffer::from_value(machine, fields.buffer)?;
    let bounds = bounds_for(machine, fields)?;
    if bounds.detached {
        return Err(type_error("Cannot read a detached DataView"));
    }
    if bounds.out_of_bounds {
        return Err(type_error("Cannot read an out-of-bounds DataView"));
    }
    if offset
        .checked_add(kind.element_size())
        .is_none_or(|end| end > bounds.byte_length)
    {
        return Err(range_error("DataView read is outside the view"));
    }
    let start = fields.byte_offset + offset;
    let mut storage = [0_u8; 8];
    buffer.with_bytes(machine, |bytes| {
        storage[..kind.element_size()].copy_from_slice(&bytes[start..start + kind.element_size()]);
    })?;
    if !little_endian {
        storage[..kind.element_size()].reverse();
    }
    Ok(BuiltinOutcome::Value(value_from_storage(
        machine, kind, storage,
    )?))
}

fn write<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    kind: ElementKind,
) -> Result<BuiltinOutcome, EvalFailure> {
    let fields = fields(machine, this)?;
    let offset = to_index(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let mut storage = storage_from_value(
        machine,
        kind,
        args.get(1).copied().unwrap_or(Value::UNDEFINED),
    )?;
    let little_endian = kind.element_size() == 1
        || machine.to_boolean(args.get(2).copied().unwrap_or(Value::UNDEFINED));
    if !little_endian {
        storage[..kind.element_size()].reverse();
    }
    let buffer = ViewBuffer::from_value(machine, fields.buffer)?;
    let bounds = bounds_for(machine, fields)?;
    if bounds.detached {
        return Err(type_error("Cannot write a detached DataView"));
    }
    if bounds.out_of_bounds {
        return Err(type_error("Cannot write an out-of-bounds DataView"));
    }
    if offset
        .checked_add(kind.element_size())
        .is_none_or(|end| end > bounds.byte_length)
    {
        return Err(range_error("DataView write is outside the view"));
    }
    let start = fields.byte_offset + offset;
    buffer.with_bytes_mut(machine, |bytes| {
        bytes[start..start + kind.element_size()].copy_from_slice(&storage[..kind.element_size()]);
    })?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

macro_rules! data_view_getters {
    ($(($name:ident, $kind:expr)),* $(,)?) => {$ (
        fn $name<H: Host>(
            machine: &mut Machine<'_, H>, this: Value, args: &[Value], _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> { read(machine, this, args, $kind) }
    )* };
}

macro_rules! data_view_setters {
    ($(($name:ident, $kind:expr)),* $(,)?) => {$ (
        fn $name<H: Host>(
            machine: &mut Machine<'_, H>, this: Value, args: &[Value], _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> { write(machine, this, args, $kind) }
    )* };
}

data_view_getters!(
    (get_int8, ElementKind::Int8),
    (get_uint8, ElementKind::Uint8),
    (get_int16, ElementKind::Int16),
    (get_uint16, ElementKind::Uint16),
    (get_int32, ElementKind::Int32),
    (get_uint32, ElementKind::Uint32),
    (get_float16, ElementKind::Float16),
    (get_float32, ElementKind::Float32),
    (get_float64, ElementKind::Float64),
    (get_big_int64, ElementKind::BigInt64),
    (get_big_uint64, ElementKind::BigUint64),
);

data_view_setters!(
    (set_int8, ElementKind::Int8),
    (set_uint8, ElementKind::Uint8),
    (set_int16, ElementKind::Int16),
    (set_uint16, ElementKind::Uint16),
    (set_int32, ElementKind::Int32),
    (set_uint32, ElementKind::Uint32),
    (set_float16, ElementKind::Float16),
    (set_float32, ElementKind::Float32),
    (set_float64, ElementKind::Float64),
    (set_big_int64, ElementKind::BigInt64),
    (set_big_uint64, ElementKind::BigUint64),
);

fn get_buffer<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(fields(machine, this)?.buffer))
}

fn get_byte_length<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let bounds = dataview_bounds(machine, this)?;
    if bounds.detached {
        return Err(type_error("Cannot read a detached DataView"));
    }
    if bounds.out_of_bounds {
        return Err(type_error("Cannot read an out-of-bounds DataView"));
    }
    Ok(BuiltinOutcome::Value(crate::number_value(
        bounds.byte_length as f64,
    )))
}

fn get_byte_offset<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let fields = fields(machine, this)?;
    let bounds = bounds_for(machine, fields)?;
    if bounds.detached {
        return Err(type_error("Cannot read a detached DataView"));
    }
    if bounds.out_of_bounds {
        return Err(type_error("Cannot read an out-of-bounds DataView"));
    }
    Ok(BuiltinOutcome::Value(crate::number_value(
        fields.byte_offset as f64,
    )))
}

#[cfg(test)]
mod tests {
    use std::sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    };

    use super::super::{
        arraybuffer::{ArrayBufferHandle, SharedBlock},
        test_support::{TestHost, blank_program},
    };
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, ThrowOrigin};

    fn value(outcome: BuiltinOutcome) -> Value {
        let BuiltinOutcome::Value(value) = outcome else {
            panic!("DataView builtin returns a value");
        };
        value
    }

    static REENTRANT_BUFFER: AtomicU64 = AtomicU64::new(Value::UNDEFINED.to_bits());

    fn detach_during_prototype_lookup(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let buffer = Value::from_bits(REENTRANT_BUFFER.load(Ordering::SeqCst));
        ArrayBufferHandle::from_value(machine, buffer)?.detach(machine, Value::UNDEFINED)?;
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    static SUBCLASS_PROTOTYPE: AtomicU64 = AtomicU64::new(Value::UNDEFINED.to_bits());

    fn fresh_subclass_prototype(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let prototype = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.builtins.dataview_prototype()),
                extensible: true,
                boxed_primitive: None,
            })
            .map_err(EvalFailure::Runtime)?;
        let depth = machine.native_roots.len();
        machine.push_native_roots(depth, &[prototype]);
        SUBCLASS_PROTOTYPE.store(prototype.to_bits(), Ordering::SeqCst);
        machine.collect_garbage();
        machine.pop_native_roots(depth);
        Ok(BuiltinOutcome::Value(prototype))
    }

    fn with_machine(test: impl FnOnce(&mut Machine<'_, TestHost>)) {
        let program = blank_program("DataView contracts");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        test(&mut machine);
    }

    fn call_method(
        machine: &mut Machine<'_, TestHost>,
        receiver: Value,
        name: &str,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let prototype = machine.intrinsics.builtins.dataview_prototype();
        let method = machine.get_named_property(prototype, name)?;
        machine.call_value(method, receiver, args)
    }

    fn dispatch_from_view(
        machine: &mut Machine<'_, TestHost>,
        receiver: Value,
        name: &str,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let method = machine.get_named_property(receiver, name)?;
        machine.call_value(method, receiver, args)
    }

    fn make_view(
        machine: &mut Machine<'_, TestHost>,
        buffer: ArrayBufferHandle,
        byte_offset: usize,
        byte_length: Option<usize>,
    ) -> Value {
        let constructor = machine.intrinsics.global("DataView").unwrap();
        let mut args = vec![buffer.value(), crate::number_value(byte_offset as f64)];
        if let Some(length) = byte_length {
            args.push(crate::number_value(length as f64));
        }
        machine.construct_value(constructor, &args).unwrap()
    }

    fn bigint(machine: &mut Machine<'_, TestHost>, text: &str) -> Value {
        machine
            .allocate(HeapEntry::BigInt(text.to_owned()))
            .unwrap()
    }

    fn bigint_text(machine: &Machine<'_, TestHost>, value: Value) -> String {
        let index = machine.runtime_slot(value).unwrap().unwrap();
        let HeapEntry::BigInt(text) = &machine.heap[index] else {
            panic!("expected a BigInt value");
        };
        text.clone()
    }

    fn assert_type_error(result: Result<Value, EvalFailure>) {
        assert!(matches!(
            result,
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    fn assert_range_error(result: Result<Value, EvalFailure>) {
        assert!(matches!(
            result,
            Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
        ));
    }

    #[test]
    fn reads_and_writes_big_and_little_endian_values() {
        let program = blank_program("DataView endian");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let buffer_constructor = machine.intrinsics.global("ArrayBuffer").unwrap();
        let buffer = machine
            .construct_value(buffer_constructor, &[Value::int32(4)])
            .unwrap();
        let view_constructor = machine.intrinsics.global("DataView").unwrap();
        let view = machine
            .construct_value(view_constructor, &[buffer])
            .unwrap();

        write(
            &mut machine,
            view,
            &[Value::int32(0), Value::int32(0x1234)],
            ElementKind::Uint16,
        )
        .unwrap();
        assert_eq!(
            value(read(&mut machine, view, &[Value::int32(0)], ElementKind::Uint16).unwrap()),
            Value::int32(0x1234)
        );
        assert_eq!(
            value(
                read(
                    &mut machine,
                    view,
                    &[Value::int32(0), Value::TRUE],
                    ElementKind::Uint16
                )
                .unwrap()
            ),
            Value::int32(0x3412)
        );
        assert_eq!(
            value(read(&mut machine, view, &[Value::int32(0)], ElementKind::Uint8).unwrap()),
            Value::int32(0x12)
        );
        assert!(matches!(
            read(&mut machine, view, &[Value::int32(3)], ElementKind::Uint16),
            Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
        ));
    }

    #[test]
    fn accepts_shared_array_buffer_backing() {
        let program = blank_program("DataView shared backing");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let buffer = machine
            .allocate(HeapEntry::SharedArrayBuffer {
                data: Arc::new(SharedBlock::new(vec![0; 8], None)),
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
            })
            .unwrap();
        let view_constructor = machine.intrinsics.global("DataView").unwrap();
        let view = machine
            .construct_value(
                view_constructor,
                &[buffer, Value::int32(2), Value::int32(4)],
            )
            .unwrap();
        write(
            &mut machine,
            view,
            &[Value::int32(0), Value::int32(0x1020), Value::TRUE],
            ElementKind::Uint16,
        )
        .unwrap();
        assert_eq!(
            value(
                read(
                    &mut machine,
                    view,
                    &[Value::int32(0), Value::TRUE],
                    ElementKind::Uint16
                )
                .unwrap()
            ),
            Value::int32(0x1020)
        );
        assert_eq!(dataview_bounds(&machine, view).unwrap().byte_length, 4);
    }

    #[test]
    fn all_numeric_kinds_round_trip_at_last_valid_offset() {
        with_machine(|machine| {
            let buffer = ArrayBufferHandle::allocate(machine, 8, None).unwrap();
            let view = make_view(machine, buffer, 0, Some(8));
            let cases = [
                (
                    "setInt8",
                    "getInt8",
                    1,
                    Value::int32(255),
                    Value::int32(u32::MAX),
                ),
                (
                    "setUint8",
                    "getUint8",
                    1,
                    Value::int32(511),
                    Value::int32(255),
                ),
                (
                    "setInt16",
                    "getInt16",
                    2,
                    Value::int32(65_535),
                    Value::int32(u32::MAX),
                ),
                (
                    "setUint16",
                    "getUint16",
                    2,
                    Value::int32(65_537),
                    Value::int32(1),
                ),
                (
                    "setInt32",
                    "getInt32",
                    4,
                    Value::number(4_294_967_295.0),
                    Value::int32(u32::MAX),
                ),
                (
                    "setUint32",
                    "getUint32",
                    4,
                    Value::int32(u32::MAX),
                    Value::number(4_294_967_295.0),
                ),
                (
                    "setFloat32",
                    "getFloat32",
                    4,
                    Value::number(1.5),
                    Value::number(1.5),
                ),
                (
                    "setFloat64",
                    "getFloat64",
                    8,
                    Value::number(-1234.5),
                    Value::number(-1234.5),
                ),
            ];

            for (setter, getter, size, input, expected) in cases {
                let last = crate::number_value((8 - size) as f64);
                assert_eq!(
                    call_method(machine, view, setter, &[last, input]).unwrap(),
                    Value::UNDEFINED
                );
                assert_eq!(
                    call_method(machine, view, getter, &[last]).unwrap(),
                    expected,
                    "{getter} must preserve its numeric element semantics"
                );

                let first_invalid = crate::number_value((9 - size) as f64);
                assert_range_error(call_method(machine, view, getter, &[first_invalid]));
                assert_range_error(call_method(machine, view, setter, &[first_invalid, input]));
            }

            let negative_one = bigint(machine, "-1");
            assert_eq!(
                call_method(
                    machine,
                    view,
                    "setBigInt64",
                    &[Value::int32(0), negative_one],
                )
                .unwrap(),
                Value::UNDEFINED
            );
            let signed = call_method(machine, view, "getBigInt64", &[Value::int32(0)]).unwrap();
            assert_eq!(bigint_text(machine, signed), "-1");

            let maximum = bigint(machine, "18446744073709551615");
            call_method(machine, view, "setBigUint64", &[Value::int32(0), maximum]).unwrap();
            let unsigned = call_method(machine, view, "getBigUint64", &[Value::int32(0)]).unwrap();
            assert_eq!(bigint_text(machine, unsigned), "18446744073709551615");
            assert_range_error(call_method(
                machine,
                view,
                "getBigUint64",
                &[Value::int32(1)],
            ));
            assert_range_error(call_method(
                machine,
                view,
                "setBigUint64",
                &[Value::int32(1), maximum],
            ));
        });
    }

    #[test]
    fn default_big_endian_and_explicit_little_endian_cover_wide_kinds() {
        with_machine(|machine| {
            let buffer = ArrayBufferHandle::allocate(machine, 8, None).unwrap();
            let view = make_view(machine, buffer, 0, Some(8));
            let wide_bigint = bigint(machine, "72623859790382856");
            let cases = [
                (
                    "setUint16",
                    "getUint16",
                    Value::int32(0x0102),
                    &[0x01, 0x02][..],
                    &[0x02, 0x01][..],
                    false,
                ),
                (
                    "setUint32",
                    "getUint32",
                    Value::int32(0x0102_0304),
                    &[0x01, 0x02, 0x03, 0x04][..],
                    &[0x04, 0x03, 0x02, 0x01][..],
                    false,
                ),
                (
                    "setFloat32",
                    "getFloat32",
                    Value::number(1.0),
                    &[0x3f, 0x80, 0x00, 0x00][..],
                    &[0x00, 0x00, 0x80, 0x3f][..],
                    false,
                ),
                (
                    "setFloat64",
                    "getFloat64",
                    Value::number(1.0),
                    &[0x3f, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..],
                    &[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf0, 0x3f][..],
                    false,
                ),
                (
                    "setBigUint64",
                    "getBigUint64",
                    wide_bigint,
                    &[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08][..],
                    &[0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01][..],
                    true,
                ),
            ];

            for (setter, getter, input, big_endian, little_endian, is_bigint) in cases {
                buffer
                    .with_bytes_mut(machine, |bytes| bytes.fill(0))
                    .unwrap();
                call_method(machine, view, setter, &[Value::int32(0), input]).unwrap();
                buffer
                    .with_bytes(machine, |bytes| {
                        assert_eq!(&bytes[..big_endian.len()], big_endian)
                    })
                    .unwrap();
                let default_result =
                    call_method(machine, view, getter, &[Value::int32(0)]).unwrap();
                if is_bigint {
                    assert_eq!(
                        bigint_text(machine, default_result),
                        bigint_text(machine, input)
                    );
                } else {
                    assert_eq!(default_result, input);
                }

                buffer
                    .with_bytes_mut(machine, |bytes| bytes.fill(0))
                    .unwrap();
                call_method(
                    machine,
                    view,
                    setter,
                    &[Value::int32(0), input, Value::TRUE],
                )
                .unwrap();
                buffer
                    .with_bytes(machine, |bytes| {
                        assert_eq!(&bytes[..little_endian.len()], little_endian)
                    })
                    .unwrap();
                let little_result =
                    call_method(machine, view, getter, &[Value::int32(0), Value::TRUE]).unwrap();
                if is_bigint {
                    assert_eq!(
                        bigint_text(machine, little_result),
                        bigint_text(machine, input)
                    );
                } else {
                    assert_eq!(little_result, input);
                }
            }
        });
    }

    #[test]
    fn bigint_getters_expose_the_same_twos_complement_bits() {
        with_machine(|machine| {
            let buffer = ArrayBufferHandle::allocate(machine, 8, None).unwrap();
            let view = make_view(machine, buffer, 0, Some(8));
            let negative_one = bigint(machine, "-1");
            let maximum = bigint(machine, "18446744073709551615");

            call_method(
                machine,
                view,
                "setBigInt64",
                &[Value::int32(0), negative_one],
            )
            .unwrap();
            let unsigned = call_method(machine, view, "getBigUint64", &[Value::int32(0)]).unwrap();
            assert_eq!(bigint_text(machine, unsigned), "18446744073709551615");

            call_method(
                machine,
                view,
                "setBigUint64",
                &[Value::int32(0), maximum, Value::TRUE],
            )
            .unwrap();
            let signed = call_method(
                machine,
                view,
                "getBigInt64",
                &[Value::int32(0), Value::TRUE],
            )
            .unwrap();
            assert_eq!(bigint_text(machine, signed), "-1");
        });
    }

    #[test]
    fn receiver_index_and_value_validation_follow_spec_order() {
        with_machine(|machine| {
            let infinity = Value::number(f64::INFINITY);
            let wrong_numeric_value = bigint(machine, "1");
            let constructor = machine.intrinsics.global("DataView").unwrap();
            assert_type_error(machine.call_value(constructor, Value::UNDEFINED, &[]));
            assert_type_error(machine.construct_value(constructor, &[Value::NULL, infinity]));

            assert_type_error(call_method(machine, Value::NULL, "getInt8", &[infinity]));
            assert_type_error(call_method(
                machine,
                Value::NULL,
                "setInt8",
                &[infinity, wrong_numeric_value],
            ));

            let buffer = ArrayBufferHandle::allocate(machine, 1, None).unwrap();
            let empty_view = make_view(machine, buffer, 0, Some(0));
            assert_type_error(call_method(
                machine,
                empty_view,
                "setInt8",
                &[Value::int32(0), wrong_numeric_value],
            ));
            assert_type_error(call_method(
                machine,
                empty_view,
                "setBigInt64",
                &[Value::int32(0), Value::int32(1)],
            ));
            assert_range_error(call_method(
                machine,
                empty_view,
                "setInt8",
                &[infinity, wrong_numeric_value],
            ));
        });
    }

    #[test]
    fn detached_views_preserve_buffer_but_reject_other_access() {
        with_machine(|machine| {
            let buffer = ArrayBufferHandle::allocate(machine, 2, None).unwrap();
            let view = make_view(machine, buffer, 0, None);
            buffer.detach(machine, Value::UNDEFINED).unwrap();

            assert_eq!(
                machine.get_named_property(view, "buffer").unwrap(),
                buffer.value()
            );
            assert_type_error(machine.get_named_property(view, "byteLength"));
            assert_type_error(machine.get_named_property(view, "byteOffset"));
            assert_type_error(call_method(machine, view, "getUint8", &[Value::int32(0)]));
            assert_type_error(call_method(
                machine,
                view,
                "setUint8",
                &[Value::int32(0), Value::int32(1)],
            ));
            assert_range_error(call_method(
                machine,
                view,
                "getUint8",
                &[Value::number(f64::INFINITY)],
            ));
        });
    }

    #[test]
    fn fixed_view_resize_out_of_bounds_is_type_error_and_recovers() {
        with_machine(|machine| {
            let buffer = ArrayBufferHandle::allocate(machine, 8, Some(16)).unwrap();
            let view = make_view(machine, buffer, 2, Some(4));
            buffer.resize(machine, 5).unwrap();

            let bounds = dataview_bounds(machine, view).unwrap();
            assert!(bounds.out_of_bounds);
            assert!(!bounds.detached);
            assert_type_error(machine.get_named_property(view, "byteLength"));
            assert_type_error(machine.get_named_property(view, "byteOffset"));
            assert_type_error(call_method(machine, view, "getUint8", &[Value::int32(0)]));
            assert_type_error(call_method(
                machine,
                view,
                "setUint8",
                &[Value::int32(0), Value::int32(1)],
            ));

            buffer.resize(machine, 8).unwrap();
            assert_eq!(
                machine.get_named_property(view, "byteLength").unwrap(),
                Value::int32(4)
            );
            assert_eq!(
                machine.get_named_property(view, "byteOffset").unwrap(),
                Value::int32(2)
            );
            call_method(
                machine,
                view,
                "setUint8",
                &[Value::int32(3), Value::int32(7)],
            )
            .unwrap();
            assert_eq!(
                call_method(machine, view, "getUint8", &[Value::int32(3)]).unwrap(),
                Value::int32(7)
            );
        });
    }

    #[test]
    fn length_tracking_view_handles_zero_length_and_resize_recovery() {
        with_machine(|machine| {
            let buffer = ArrayBufferHandle::allocate(machine, 8, Some(16)).unwrap();
            let view = make_view(machine, buffer, 2, None);
            assert_eq!(
                machine.get_named_property(view, "byteLength").unwrap(),
                Value::int32(6)
            );

            buffer.resize(machine, 2).unwrap();
            let bounds = dataview_bounds(machine, view).unwrap();
            assert!(!bounds.out_of_bounds);
            assert_eq!(bounds.byte_length, 0);
            assert_eq!(
                machine.get_named_property(view, "byteLength").unwrap(),
                Value::int32(0)
            );
            assert_eq!(
                machine.get_named_property(view, "byteOffset").unwrap(),
                Value::int32(2)
            );
            assert_range_error(call_method(machine, view, "getUint8", &[Value::int32(0)]));

            buffer.resize(machine, 1).unwrap();
            assert_type_error(machine.get_named_property(view, "byteLength"));
            assert_type_error(machine.get_named_property(view, "byteOffset"));

            buffer.resize(machine, 6).unwrap();
            assert_eq!(
                machine.get_named_property(view, "byteLength").unwrap(),
                Value::int32(4)
            );
            assert_eq!(
                machine.get_named_property(view, "byteOffset").unwrap(),
                Value::int32(2)
            );
        });
    }

    #[test]
    fn constructor_revalidates_after_new_target_prototype_lookup() {
        with_machine(|machine| {
            let buffer = ArrayBufferHandle::allocate(machine, 4, None).unwrap();
            REENTRANT_BUFFER.store(buffer.value().to_bits(), Ordering::SeqCst);
            let id = machine.intrinsics.builtins.register(BuiltinDef {
                name: "DetachDuringPrototypeLookup",
                length: 0,
                handler: detach_during_prototype_lookup,
            });
            let new_target = native_function(
                &mut machine.heap,
                &mut machine.atoms,
                &mut machine.shapes,
                id,
                "DetachDuringPrototypeLookup",
                0,
            );
            let proto_key = PropertyKey::Named(machine.atoms.intern_str("prototype"));
            let index = machine.runtime_slot(new_target).unwrap().unwrap();
            let HeapEntry::NativeFunction { properties, .. } = &mut machine.heap[index] else {
                panic!("native new.target must be callable");
            };
            properties.insert(
                &mut machine.shapes,
                proto_key,
                Property::Accessor {
                    getter: Some(new_target),
                    setter: None,
                    enumerable: false,
                    configurable: true,
                },
            );
            machine.current_new_target = new_target;

            assert!(matches!(
                constructor(machine, Value::UNDEFINED, &[buffer.value()], true),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert!(buffer.is_detached(machine));
            machine.current_new_target = Value::UNDEFINED;
        });
    }

    #[test]
    fn production_global_reaches_methods_accessors_and_tag() {
        with_machine(|machine| {
            let global = machine.intrinsics.global("globalThis").unwrap();
            let constructor = machine.get_named_property(global, "DataView").unwrap();
            let buffer_ctor = machine.intrinsics.global("ArrayBuffer").unwrap();
            let buffer = machine
                .construct_value(buffer_ctor, &[Value::int32(8)])
                .unwrap();
            let view = machine
                .construct_value(constructor, &[buffer, Value::int32(0), Value::int32(8)])
                .unwrap();

            for name in [
                "getInt8",
                "getUint8",
                "getInt16",
                "getUint16",
                "getInt32",
                "getUint32",
                "getFloat16",
                "getFloat32",
                "getFloat64",
                "getBigInt64",
                "getBigUint64",
                "setInt8",
                "setUint8",
                "setInt16",
                "setUint16",
                "setInt32",
                "setUint32",
                "setFloat16",
                "setFloat32",
                "setFloat64",
                "setBigInt64",
                "setBigUint64",
            ] {
                assert!(
                    machine.get_named_property(view, name).is_ok(),
                    "{name} must be reachable from an installed DataView"
                );
            }
            for name in ["buffer", "byteLength", "byteOffset"] {
                assert!(
                    machine.get_named_property(view, name).is_ok(),
                    "{name} accessor must be reachable"
                );
            }
            let prototype = machine.intrinsics.builtins.dataview_prototype();
            let tag_key = PropertyKey::Symbol(
                machine
                    .runtime_slot(machine.intrinsics.builtins.symbol_to_string_tag())
                    .unwrap()
                    .unwrap() as u32,
            );
            let tag = machine.get_property_key(prototype, &tag_key).unwrap();
            assert_eq!(machine.to_string(tag).unwrap().to_utf8_lossy(), "DataView");

            dispatch_from_view(
                machine,
                view,
                "setUint8",
                &[Value::int32(0), Value::int32(0xAB)],
            )
            .unwrap();
            assert_eq!(
                dispatch_from_view(machine, view, "getUint8", &[Value::int32(0)]).unwrap(),
                Value::int32(0xAB)
            );
        });
    }

    #[test]
    fn ordinary_properties_and_zero_key_stay_non_exotic() {
        with_machine(|machine| {
            let buffer = ArrayBufferHandle::allocate(machine, 4, None).unwrap();
            let view = make_view(machine, buffer, 0, Some(4));
            machine
                .set_data_property(view, "marker", Value::int32(7))
                .unwrap();
            machine
                .set_data_property(view, "0", Value::int32(99))
                .unwrap();
            assert_eq!(
                machine.get_named_property(view, "marker").unwrap(),
                Value::int32(7)
            );
            assert_eq!(
                machine.get_named_property(view, "0").unwrap(),
                Value::int32(99)
            );
            assert_eq!(
                dispatch_from_view(machine, view, "getUint8", &[Value::int32(0)]).unwrap(),
                Value::int32(0),
                "numeric-looking own property must not shadow buffer reads"
            );
            let marker = PropertyKey::Named(machine.intern_str("marker"));
            assert!(machine.internal_delete(view, &marker).unwrap());
            assert_eq!(
                machine.get_named_property(view, "marker").unwrap(),
                Value::UNDEFINED
            );
            let keys = machine.own_property_keys(view).unwrap();
            assert!(
                keys.iter().any(
                    |key| matches!(key, PropertyKey::Named(name) if machine.atoms.resolve(*name).to_utf8_lossy() == "0")
                )
            );
        });
    }

    #[test]
    fn subclass_prototype_survives_forced_gc_and_backing_io() {
        with_machine(|machine| {
            let buffer = ArrayBufferHandle::allocate(machine, 2, None).unwrap();
            let id = machine.intrinsics.builtins.register(BuiltinDef {
                name: "FreshSubclassPrototype",
                length: 0,
                handler: fresh_subclass_prototype,
            });
            let new_target = native_function(
                &mut machine.heap,
                &mut machine.atoms,
                &mut machine.shapes,
                id,
                "FreshSubclassPrototype",
                0,
            );
            let proto_key = PropertyKey::Named(machine.atoms.intern_str("prototype"));
            let index = machine.runtime_slot(new_target).unwrap().unwrap();
            let HeapEntry::NativeFunction { properties, .. } = &mut machine.heap[index] else {
                panic!("native new.target must be callable");
            };
            properties.insert(
                &mut machine.shapes,
                proto_key,
                Property::Accessor {
                    getter: Some(new_target),
                    setter: None,
                    enumerable: false,
                    configurable: true,
                },
            );
            let buffer_value = buffer.value();
            let depth = machine.native_roots.len();
            machine.push_native_roots(depth, &[buffer_value, new_target]);
            let dataview_id = machine.intrinsics.builtins.id_named("DataView").unwrap();
            let BuiltinOutcome::Value(view) = machine
                .call_builtin_with_new_target(
                    dataview_id,
                    Value::UNDEFINED,
                    &[buffer_value],
                    true,
                    new_target,
                )
                .unwrap()
            else {
                panic!("DataView constructor returns a value");
            };
            machine.pop_native_roots(depth);

            let expected = Value::from_bits(SUBCLASS_PROTOTYPE.load(Ordering::SeqCst));
            let view_index = machine.runtime_slot(view).unwrap().unwrap();
            let HeapEntry::DataView { prototype, .. } = &machine.heap[view_index] else {
                panic!("constructed value must be a DataView");
            };
            assert_eq!(*prototype, Some(expected));
            dispatch_from_view(
                machine,
                view,
                "setUint8",
                &[Value::int32(0), Value::int32(0xCD)],
            )
            .unwrap();
            assert_eq!(
                dispatch_from_view(machine, view, "getUint8", &[Value::int32(0)]).unwrap(),
                Value::int32(0xCD)
            );
        });
    }

    #[test]
    fn float16_endian_bytes_are_exact() {
        with_machine(|machine| {
            let buffer = ArrayBufferHandle::allocate(machine, 4, None).unwrap();
            let view = make_view(machine, buffer, 0, Some(4));
            dispatch_from_view(
                machine,
                view,
                "setFloat16",
                &[Value::int32(0), Value::number(1.5)],
            )
            .unwrap();
            assert_eq!(
                dispatch_from_view(machine, view, "getFloat16", &[Value::int32(0)],).unwrap(),
                Value::number(1.5)
            );
            assert_eq!(
                dispatch_from_view(machine, view, "getUint8", &[Value::int32(0)]).unwrap(),
                Value::int32(0x3E)
            );
            assert_eq!(
                dispatch_from_view(machine, view, "getUint8", &[Value::int32(1)]).unwrap(),
                Value::int32(0x00)
            );
            dispatch_from_view(
                machine,
                view,
                "setFloat16",
                &[Value::int32(2), Value::number(2.0), Value::TRUE],
            )
            .unwrap();
            assert_eq!(
                dispatch_from_view(machine, view, "getFloat16", &[Value::int32(2), Value::TRUE],)
                    .unwrap(),
                Value::number(2.0)
            );
            assert_eq!(
                dispatch_from_view(machine, view, "getUint8", &[Value::int32(2)]).unwrap(),
                Value::int32(0x00)
            );
            assert_eq!(
                dispatch_from_view(machine, view, "getUint8", &[Value::int32(3)]).unwrap(),
                Value::int32(0x40)
            );
        });
    }

    #[test]
    fn constructor_to_index_and_resize_bounds_are_observable() {
        with_machine(|machine| {
            let resizable = ArrayBufferHandle::allocate(machine, 5, Some(8)).unwrap();
            let view = machine
                .construct_value(
                    machine.intrinsics.global("DataView").unwrap(),
                    &[resizable.value(), Value::number(1.9), Value::number(4.1)],
                )
                .unwrap();
            resizable.resize(machine, 3).unwrap();
            assert_type_error(machine.get_named_property(view, "byteLength"));
            resizable.resize(machine, 8).unwrap();
            assert_eq!(
                machine.get_named_property(view, "byteLength").unwrap(),
                Value::int32(4)
            );

            let tracking = ArrayBufferHandle::allocate(machine, 2, Some(16)).unwrap();
            let auto_view = make_view(machine, tracking, 1, None);
            assert_eq!(
                machine.get_named_property(auto_view, "byteLength").unwrap(),
                Value::int32(1)
            );
            tracking.resize(machine, 0).unwrap();
            assert_type_error(machine.get_named_property(auto_view, "byteLength"));
        });
    }
}
