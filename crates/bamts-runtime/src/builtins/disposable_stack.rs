use std::collections::BTreeMap;

use bamts_bytecode::{DisposeHint, EcmaString};
use bamts_native::Value;

use super::{
    builtin_property, define_data, define_to_string_tag, heap_index, install_constructor_function,
    install_function,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::vm::explicit_resource::{
    ASYNC_DISPOSABLE_STACK_CONSTRUCTOR, ASYNC_DISPOSABLE_STACK_INSTALLS,
    ASYNC_DISPOSABLE_STACK_METHODS, DISPOSABLE_STACK_CONSTRUCTOR, DISPOSABLE_STACK_INSTALLS,
    DISPOSABLE_STACK_METHODS, StackInstall, StackMethodKind,
    async_disposable_stack_disposed_getter, async_disposable_stack_method_handler,
    disposable_stack_disposed_getter, disposable_stack_method_handler, stack_constructor_handler,
};
use crate::{
    EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap, ThrowOrigin,
};

fn disposed_stack<H: Host>(
    machine: &Machine<'_, H>,
    this: Value,
    expected_hint: DisposeHint,
) -> Result<bool, EvalFailure> {
    let index = machine
        .runtime_slot(this)
        .map_err(EvalFailure::Runtime)?
        .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "DisposableStack method called on incompatible receiver",
        }))?;
    match &machine.heap[index] {
        HeapEntry::DisposableStack { state, hint, .. } if *hint == expected_hint => {
            Ok(state.is_disposed())
        }
        _ => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "DisposableStack method called on incompatible receiver",
        })),
    }
}

fn disposable_stack_public_method<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let dispose = machine
        .current_builtin_id()
        .is_some_and(|id| machine.intrinsics.builtins.get(id).name == "dispose");
    if dispose && disposed_stack(machine, this, DisposeHint::Sync)? {
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    }
    disposable_stack_method_handler(machine, this, args, constructing)
}

fn async_disposable_stack_public_method<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let dispose = machine
        .current_builtin_id()
        .is_some_and(|id| machine.intrinsics.builtins.get(id).name == "disposeAsync");
    if dispose {
        // Create the promise capability before receiver validation: an
        // incompatible receiver rejects the promise with a TypeError rather
        // than throwing synchronously (the sync `dispose` path keeps its
        // synchronous TypeError).
        let promise = machine.create_promise()?;
        match disposed_stack(machine, this, DisposeHint::Async) {
            Ok(true) => {
                machine
                    .fulfill_promise(promise, Value::UNDEFINED)
                    .map_err(EvalFailure::Runtime)?;
                Ok(BuiltinOutcome::Value(promise))
            }
            Ok(false) => {
                machine.continue_async_disposal(this, None, None, promise)?;
                Ok(BuiltinOutcome::Value(promise))
            }
            Err(EvalFailure::Throw(origin @ ThrowOrigin::TypeError { .. })) => {
                machine
                    .reject_promise(promise, Value::UNDEFINED, origin)
                    .map_err(EvalFailure::Runtime)?;
                Ok(BuiltinOutcome::Value(promise))
            }
            Err(failure) => Err(failure),
        }
    } else {
        async_disposable_stack_method_handler(machine, this, args, constructing)
    }
}

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    for descriptor in [
        DISPOSABLE_STACK_CONSTRUCTOR,
        ASYNC_DISPOSABLE_STACK_CONSTRUCTOR,
    ] {
        let prototype = ordinary(heap, Some(builtins.object_prototype()));
        let (methods, installs, method_handler, disposed_getter) = match descriptor.hint {
            DisposeHint::Sync => {
                builtins.set_disposable_stack_prototype(prototype);
                (
                    DISPOSABLE_STACK_METHODS.as_slice(),
                    DISPOSABLE_STACK_INSTALLS.as_slice(),
                    disposable_stack_public_method::<H> as BuiltinHandler<H>,
                    disposable_stack_disposed_getter::<H> as BuiltinHandler<H>,
                )
            }
            DisposeHint::Async => {
                builtins.set_async_disposable_stack_prototype(prototype);
                (
                    ASYNC_DISPOSABLE_STACK_METHODS.as_slice(),
                    ASYNC_DISPOSABLE_STACK_INSTALLS.as_slice(),
                    async_disposable_stack_public_method::<H> as BuiltinHandler<H>,
                    async_disposable_stack_disposed_getter::<H> as BuiltinHandler<H>,
                )
            }
        };
        let constructor = install_constructor_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: descriptor.name, length: descriptor.length, handler: stack_constructor_handler::<H> });
        builtins.set_constructor_prototype(heap, atoms, shapes, constructor, prototype);

        let mut disposal_method = None;
        for method in methods {
            let function = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: method.name, length: method.length, handler: method_handler });
            if matches!(
                method.kind,
                StackMethodKind::Dispose | StackMethodKind::DisposeAsync
            ) {
                disposal_method = Some(function);
            }
            define_data(heap, atoms, shapes, prototype, method.name, function);
        }
        let disposal_method = disposal_method.expect("stack method table includes disposal");
        for install in installs {
            match *install {
                StackInstall::DisposedAccessor => {
                    let getter =
                        install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "get disposed", length: 0, handler: disposed_getter });
                    define_getter(heap, atoms, shapes, prototype, "disposed", getter);
                }
                StackInstall::DisposeAlias => {
                    define_symbol(heap, shapes, prototype, builtins.symbol_dispose(), disposal_method)
                }
                StackInstall::AsyncDisposeAlias => define_symbol(
                    heap,
                    shapes,
                    prototype,
                    builtins.symbol_async_dispose(),
                    disposal_method,
                ),
                StackInstall::ToStringTag(tag) => {
                    define_to_string_tag(heap, shapes, prototype, builtins.symbol_to_string_tag(), tag)
                }
            }
        }
        globals.insert(EcmaString::encode(descriptor.name), constructor);
    }
}

fn ordinary(heap: &mut Vec<HeapEntry>, prototype: Option<Value>) -> Value {
    super::super::push(
        heap,
        HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype,
            boxed_primitive: None,
            extensible: true,
        },
    )
}

fn define_getter(
    heap: &mut [HeapEntry],
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    object: Value,
    name: &str,
    getter: Value,
) {
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(object)] else {
        unreachable!("DisposableStack prototype is an ordinary object")
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

fn define_symbol(heap: &mut [HeapEntry], shapes: &mut crate::ShapeTable, object: Value, symbol: Value, value: Value) {
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(object)] else {
        unreachable!("DisposableStack prototype is an ordinary object")
    };
    properties.insert(
        shapes,
        PropertyKey::Symbol(heap_index(symbol) as u32),
        builtin_property(value),
    );
}
