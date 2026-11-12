//! Explicit-resource stack state and transition policy.
//!
//! Runtime wiring owns property lookup, calls, promises, and `SuppressedError`
//! allocation. This leaf owns the total stack transitions those adapters use.

use bamts_bytecode::DisposeHint;
use bamts_native::{Decoded, Value};

const CAPTURE_METHOD: u8 = 1;
const CAPTURE_ASYNC_SYNC_FALLBACK: u8 = 2;
const ADOPT_CALLBACK: u8 = 3;
const DEFER_CALLBACK: u8 = 4;

/// A captured disposer together with the invocation policy needed by the driver.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct DisposableResource {
    pub(crate) value: Value,
    pub(crate) method: Value,
    pub(crate) kind: u8,
    pub(crate) hint: DisposeHint,
}

impl DisposableResource {
    pub(crate) fn awaits_result(self) -> bool {
        self.hint == DisposeHint::Async && self.kind != CAPTURE_ASYNC_SYNC_FALLBACK
    }

    pub(crate) const fn passes_value_argument(self) -> bool {
        self.kind == ADOPT_CALLBACK
    }

    pub(crate) const fn is_deferred_callback(self) -> bool {
        self.kind == DEFER_CALLBACK
    }
}

/// The internal state shared by `DisposableStack` and `AsyncDisposableStack`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct DisposalStackState {
    resources: Vec<DisposableResource>,
    disposed: bool,
}

impl DisposalStackState {
    pub(crate) const fn new() -> Self {
        Self {
            resources: Vec::new(),
            disposed: false,
        }
    }

    pub(crate) const fn is_disposed(&self) -> bool {
        self.disposed
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.resources.len()
    }

    /// Visits both operands retained by every resource record.
    pub(crate) fn visit_roots(&self, mut visit: impl FnMut(Value)) {
        for resource in &self.resources {
            visit(resource.value);
            visit(resource.method);
        }
    }
}

/// User-observable failure class selected by a stack transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum StackError {
    /// A mutating method was applied after disposal or move.
    Disposed,
    /// A non-nullish primitive cannot be registered as a resource.
    NotDisposable,
    /// An adopt/defer callback is not callable.
    NotCallable,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum StackErrorKind {
    ReferenceError,
    TypeError,
}

impl StackError {
    pub(crate) const fn kind(self) -> StackErrorKind {
        match self {
            Self::Disposed => StackErrorKind::ReferenceError,
            Self::NotDisposable | Self::NotCallable => StackErrorKind::TypeError,
        }
    }
}

/// Registers a resource captured by the existing `DisposeCapture` machinery.
pub(crate) fn stack_use(
    state: &mut DisposalStackState,
    captured: (Value, u8),
    value: Value,
    hint: DisposeHint,
) -> Result<(), StackError> {
    ensure_active(state)?;
    if is_nullish(value) {
        return Ok(());
    }
    if !matches!(value.decode(), Some(Decoded::HeapRef(_))) {
        return Err(StackError::NotDisposable);
    }

    let (method, kind) = captured;
    if !matches!(kind, CAPTURE_METHOD | CAPTURE_ASYNC_SYNC_FALLBACK)
        || (kind == CAPTURE_ASYNC_SYNC_FALLBACK && hint != DisposeHint::Async)
    {
        return Err(StackError::NotDisposable);
    }
    state.resources.push(DisposableResource {
        value,
        method,
        kind,
        hint,
    });
    Ok(())
}

/// Registers a callable that will receive `value` when the stack is disposed.
pub(crate) fn stack_adopt(
    state: &mut DisposalStackState,
    value: Value,
    on_dispose: Value,
    hint: DisposeHint,
    callable: bool,
) -> Result<(), StackError> {
    ensure_active(state)?;
    if !callable {
        return Err(StackError::NotCallable);
    }
    state.resources.push(DisposableResource {
        value,
        method: on_dispose,
        kind: ADOPT_CALLBACK,
        hint,
    });
    Ok(())
}

/// Registers a callable that will be invoked without arguments on disposal.
pub(crate) fn stack_defer(
    state: &mut DisposalStackState,
    on_dispose: Value,
    hint: DisposeHint,
    callable: bool,
) -> Result<(), StackError> {
    ensure_active(state)?;
    if !callable {
        return Err(StackError::NotCallable);
    }
    state.resources.push(DisposableResource {
        value: Value::UNDEFINED,
        method: on_dispose,
        kind: DEFER_CALLBACK,
        hint,
    });
    Ok(())
}

/// Transfers all resources without running them and permanently disposes the source.
pub(crate) fn stack_move(state: &mut DisposalStackState) -> Result<DisposalStackState, StackError> {
    ensure_active(state)?;
    state.disposed = true;
    Ok(DisposalStackState {
        resources: core::mem::take(&mut state.resources),
        disposed: false,
    })
}

/// Begins disposal if necessary and removes the next resource in strict LIFO order.
/// Repeated calls after the stack empties are idempotent.
pub(crate) fn pop_lifo(state: &mut DisposalStackState) -> Option<DisposableResource> {
    state.disposed = true;
    state.resources.pop()
}

fn ensure_active(state: &DisposalStackState) -> Result<(), StackError> {
    if state.disposed {
        Err(StackError::Disposed)
    } else {
        Ok(())
    }
}

const fn is_nullish(value: Value) -> bool {
    matches!(value.decode(), Some(Decoded::Undefined | Decoded::Null))
}

/// Allocation action for a newly-thrown disposal error.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ChainStep {
    Throw(Value),
    Suppress { error: Value, suppressed: Value },
}

/// Selects `SuppressedError { error: new_error, suppressed: pending }` direction.
pub(crate) const fn chain_disposal_error(pending: Option<Value>, new_error: Value) -> ChainStep {
    match pending {
        Some(suppressed) => ChainStep::Suppress {
            error: new_error,
            suppressed,
        },
        None => ChainStep::Throw(new_error),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct StackConstructor {
    pub(crate) name: &'static str,
    pub(crate) length: u32,
    pub(crate) hint: DisposeHint,
}

pub(crate) const DISPOSABLE_STACK_CONSTRUCTOR: StackConstructor = StackConstructor {
    name: "DisposableStack",
    length: 0,
    hint: DisposeHint::Sync,
};

pub(crate) const ASYNC_DISPOSABLE_STACK_CONSTRUCTOR: StackConstructor = StackConstructor {
    name: "AsyncDisposableStack",
    length: 0,
    hint: DisposeHint::Async,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct NewRequired;

/// Shared constructor adapter. The installing builtin selects the descriptor.
pub(crate) const fn construct_stack(constructing: bool) -> Result<DisposalStackState, NewRequired> {
    if constructing {
        Ok(DisposalStackState::new())
    } else {
        Err(NewRequired)
    }
}

/// The runtime action represented by a prototype method table entry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum StackMethodKind {
    Use,
    Adopt,
    Defer,
    Move,
    Dispose,
    DisposeAsync,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct StackMethod {
    pub(crate) name: &'static str,
    pub(crate) length: u32,
    pub(crate) kind: StackMethodKind,
}

pub(crate) const DISPOSABLE_STACK_METHODS: [StackMethod; 5] = [
    StackMethod {
        name: "use",
        length: 1,
        kind: StackMethodKind::Use,
    },
    StackMethod {
        name: "adopt",
        length: 2,
        kind: StackMethodKind::Adopt,
    },
    StackMethod {
        name: "defer",
        length: 1,
        kind: StackMethodKind::Defer,
    },
    StackMethod {
        name: "move",
        length: 0,
        kind: StackMethodKind::Move,
    },
    StackMethod {
        name: "dispose",
        length: 0,
        kind: StackMethodKind::Dispose,
    },
];

pub(crate) const ASYNC_DISPOSABLE_STACK_METHODS: [StackMethod; 5] = [
    StackMethod {
        name: "use",
        length: 1,
        kind: StackMethodKind::Use,
    },
    StackMethod {
        name: "adopt",
        length: 2,
        kind: StackMethodKind::Adopt,
    },
    StackMethod {
        name: "defer",
        length: 1,
        kind: StackMethodKind::Defer,
    },
    StackMethod {
        name: "move",
        length: 0,
        kind: StackMethodKind::Move,
    },
    StackMethod {
        name: "disposeAsync",
        length: 0,
        kind: StackMethodKind::DisposeAsync,
    },
];

/// Properties installed in addition to the named method tables.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum StackInstall {
    DisposedAccessor,
    DisposeAlias,
    AsyncDisposeAlias,
    ToStringTag(&'static str),
}

pub(crate) const DISPOSABLE_STACK_INSTALLS: [StackInstall; 3] = [
    StackInstall::DisposedAccessor,
    StackInstall::DisposeAlias,
    StackInstall::ToStringTag("DisposableStack"),
];

pub(crate) const ASYNC_DISPOSABLE_STACK_INSTALLS: [StackInstall; 3] = [
    StackInstall::DisposedAccessor,
    StackInstall::AsyncDisposeAlias,
    StackInstall::ToStringTag("AsyncDisposableStack"),
];

/// Sync-stack adapter for `use`.
pub(crate) fn disposable_stack_use(
    state: &mut DisposalStackState,
    captured: (Value, u8),
    value: Value,
) -> Result<Value, StackError> {
    stack_use(state, captured, value, DisposeHint::Sync)?;
    Ok(value)
}

/// Async-stack adapter for `use`.
pub(crate) fn async_disposable_stack_use(
    state: &mut DisposalStackState,
    captured: (Value, u8),
    value: Value,
) -> Result<Value, StackError> {
    stack_use(state, captured, value, DisposeHint::Async)?;
    Ok(value)
}

pub(crate) fn disposable_stack_adopt(
    state: &mut DisposalStackState,
    value: Value,
    on_dispose: Value,
    callable: bool,
) -> Result<Value, StackError> {
    stack_adopt(state, value, on_dispose, DisposeHint::Sync, callable)?;
    Ok(value)
}

pub(crate) fn async_disposable_stack_adopt(
    state: &mut DisposalStackState,
    value: Value,
    on_dispose: Value,
    callable: bool,
) -> Result<Value, StackError> {
    stack_adopt(state, value, on_dispose, DisposeHint::Async, callable)?;
    Ok(value)
}

pub(crate) fn disposable_stack_defer(
    state: &mut DisposalStackState,
    on_dispose: Value,
    callable: bool,
) -> Result<(), StackError> {
    stack_defer(state, on_dispose, DisposeHint::Sync, callable)
}

pub(crate) fn async_disposable_stack_defer(
    state: &mut DisposalStackState,
    on_dispose: Value,
    callable: bool,
) -> Result<(), StackError> {
    stack_defer(state, on_dispose, DisposeHint::Async, callable)
}

fn stack_failure(error: StackError) -> crate::EvalFailure {
    let operation = match error {
        StackError::Disposed => "DisposableStack is already disposed",
        StackError::NotDisposable => "value is not disposable",
        StackError::NotCallable => "disposal callback is not callable",
    };
    match error.kind() {
        StackErrorKind::ReferenceError => {
            crate::EvalFailure::Throw(crate::ThrowOrigin::ReferenceError { operation })
        }
        StackErrorKind::TypeError => {
            crate::EvalFailure::Throw(crate::ThrowOrigin::TypeError { operation })
        }
    }
}

fn expected_stack_index<H: crate::Host>(
    machine: &crate::Machine<'_, H>,
    value: Value,
    expected_hint: DisposeHint,
) -> Result<usize, crate::EvalFailure> {
    let index = machine
        .runtime_slot(value)
        .map_err(crate::EvalFailure::Runtime)?
        .ok_or(crate::EvalFailure::Throw(crate::ThrowOrigin::TypeError {
            operation: "DisposableStack method called on incompatible receiver",
        }))?;
    match &machine.heap[index] {
        crate::HeapEntry::DisposableStack { hint, .. } if *hint == expected_hint => Ok(index),
        _ => Err(crate::EvalFailure::Throw(crate::ThrowOrigin::TypeError {
            operation: "DisposableStack method called on incompatible receiver",
        })),
    }
}

fn stack_prototype<H: crate::Host>(
    machine: &mut crate::Machine<'_, H>,
    hint: DisposeHint,
) -> Result<Value, crate::EvalFailure> {
    let default = match hint {
        DisposeHint::Sync => machine.intrinsics.builtins.disposable_stack_prototype(),
        DisposeHint::Async => machine
            .intrinsics
            .builtins
            .async_disposable_stack_prototype(),
    };
    let new_target = machine.current_new_target();
    if new_target == Value::UNDEFINED {
        return Ok(default);
    }
    let candidate = machine.get_named_property(new_target, "prototype")?;
    Ok(if machine.is_object(candidate) {
        candidate
    } else {
        default
    })
}

pub(crate) fn stack_constructor_handler<H: crate::Host>(
    machine: &mut crate::Machine<'_, H>,
    _this: Value,
    _args: &[Value],
    constructing: bool,
) -> Result<crate::intrinsics::BuiltinOutcome, crate::EvalFailure> {
    let name = machine
        .current_builtin_id()
        .map(|id| machine.intrinsics.builtins.get(id).name)
        .ok_or(crate::EvalFailure::Throw(crate::ThrowOrigin::TypeError {
            operation: "invalid DisposableStack constructor",
        }))?;
    let hint = if name == ASYNC_DISPOSABLE_STACK_CONSTRUCTOR.name {
        DisposeHint::Async
    } else {
        DisposeHint::Sync
    };
    let state = construct_stack(constructing).map_err(|_| {
        crate::EvalFailure::Throw(crate::ThrowOrigin::TypeError {
            operation: "DisposableStack constructor requires new",
        })
    })?;
    let prototype = stack_prototype(machine, hint)?;
    let value = machine
        .allocate(crate::HeapEntry::DisposableStack {
            state,
            hint,
            properties: crate::PropertyMap::default(),
            prototype: Some(prototype),
            extensible: true,
        })
        .map_err(crate::EvalFailure::Runtime)?;
    Ok(crate::intrinsics::BuiltinOutcome::Value(value))
}

fn call_resource<H: crate::Host>(
    machine: &mut crate::Machine<'_, H>,
    resource: DisposableResource,
) -> Result<Value, crate::EvalFailure> {
    let this_value = if resource.is_deferred_callback() || resource.passes_value_argument() {
        Value::UNDEFINED
    } else {
        resource.value
    };
    if resource.passes_value_argument() {
        machine.call_value(resource.method, this_value, &[resource.value])
    } else {
        machine.call_value(resource.method, this_value, &[])
    }
}

fn method_name<H: crate::Host>(
    machine: &crate::Machine<'_, H>,
) -> Result<&'static str, crate::EvalFailure> {
    machine
        .current_builtin_id()
        .map(|id| machine.intrinsics.builtins.get(id).name)
        .ok_or(crate::EvalFailure::Throw(crate::ThrowOrigin::TypeError {
            operation: "invalid DisposableStack method",
        }))
}

fn stack_method<H: crate::Host>(
    machine: &mut crate::Machine<'_, H>,
    this: Value,
    args: &[Value],
    hint: DisposeHint,
) -> Result<crate::intrinsics::BuiltinOutcome, crate::EvalFailure> {
    let name = method_name(machine)?;
    let index = expected_stack_index(machine, this, hint)?;
    if matches!(name, "use" | "adopt" | "defer" | "move") {
        let crate::HeapEntry::DisposableStack { state, .. } = &machine.heap[index] else {
            unreachable!("receiver was checked above");
        };
        ensure_active(state).map_err(stack_failure)?;
    }
    match name {
        "use" => {
            let value = args.first().copied().unwrap_or(Value::UNDEFINED);
            let (method, kind) = machine.dispose_capture_raw(value, hint)?;
            let crate::HeapEntry::DisposableStack { state, .. } = &mut machine.heap[index] else {
                unreachable!("receiver was checked above");
            };
            let value = match hint {
                DisposeHint::Sync => disposable_stack_use(state, (method, kind as u8), value),
                DisposeHint::Async => {
                    async_disposable_stack_use(state, (method, kind as u8), value)
                }
            }
            .map_err(stack_failure)?;
            Ok(crate::intrinsics::BuiltinOutcome::Value(value))
        }
        "adopt" => {
            let value = args.first().copied().unwrap_or(Value::UNDEFINED);
            let callback = args.get(1).copied().unwrap_or(Value::UNDEFINED);
            let callable = machine.is_callable(callback)?;
            let crate::HeapEntry::DisposableStack { state, .. } = &mut machine.heap[index] else {
                unreachable!("receiver was checked above");
            };
            let value = match hint {
                DisposeHint::Sync => disposable_stack_adopt(state, value, callback, callable),
                DisposeHint::Async => {
                    async_disposable_stack_adopt(state, value, callback, callable)
                }
            }
            .map_err(stack_failure)?;
            Ok(crate::intrinsics::BuiltinOutcome::Value(value))
        }
        "defer" => {
            let callback = args.first().copied().unwrap_or(Value::UNDEFINED);
            let callable = machine.is_callable(callback)?;
            let crate::HeapEntry::DisposableStack { state, .. } = &mut machine.heap[index] else {
                unreachable!("receiver was checked above");
            };
            match hint {
                DisposeHint::Sync => disposable_stack_defer(state, callback, callable),
                DisposeHint::Async => async_disposable_stack_defer(state, callback, callable),
            }
            .map_err(stack_failure)?;
            Ok(crate::intrinsics::BuiltinOutcome::Value(Value::UNDEFINED))
        }
        "move" => {
            let crate::HeapEntry::DisposableStack { state, .. } = &mut machine.heap[index] else {
                unreachable!("receiver was checked above");
            };
            let state = stack_move(state).map_err(stack_failure)?;
            let prototype = match hint {
                DisposeHint::Sync => machine.intrinsics.builtins.disposable_stack_prototype(),
                DisposeHint::Async => machine
                    .intrinsics
                    .builtins
                    .async_disposable_stack_prototype(),
            };
            let moved = machine
                .allocate(crate::HeapEntry::DisposableStack {
                    state,
                    hint,
                    properties: crate::PropertyMap::default(),
                    prototype: Some(prototype),
                    extensible: true,
                })
                .map_err(crate::EvalFailure::Runtime)?;
            Ok(crate::intrinsics::BuiltinOutcome::Value(moved))
        }
        "dispose" => {
            let mut pending: Option<(Value, crate::ThrowOrigin)> = None;
            loop {
                let resource = {
                    let crate::HeapEntry::DisposableStack { state, .. } = &mut machine.heap[index]
                    else {
                        unreachable!("receiver was checked above");
                    };
                    pop_lifo(state)
                };
                let Some(resource) = resource else {
                    break;
                };
                if let Err(failure) = call_resource(machine, resource) {
                    let (new_error, origin) = machine.promise_rejection_value(failure)?;
                    pending = Some(
                        match chain_disposal_error(pending.map(|(value, _)| value), new_error) {
                            ChainStep::Throw(value) => (value, origin),
                            ChainStep::Suppress { error, suppressed } => (
                                machine.make_suppressed_error(error, suppressed)?,
                                crate::ThrowOrigin::Bytecode,
                            ),
                        },
                    );
                }
            }
            if let Some((value, origin)) = pending {
                Err(crate::EvalFailure::ThrowValueOrigin { value, origin })
            } else {
                Ok(crate::intrinsics::BuiltinOutcome::Value(Value::UNDEFINED))
            }
        }
        "disposeAsync" => {
            let capability = machine.create_promise()?;
            machine.continue_async_disposal(this, None, None, capability)?;
            Ok(crate::intrinsics::BuiltinOutcome::Value(capability))
        }
        _ => Err(crate::EvalFailure::Throw(crate::ThrowOrigin::TypeError {
            operation: "unknown DisposableStack method",
        })),
    }
}

pub(crate) fn disposable_stack_method_handler<H: crate::Host>(
    machine: &mut crate::Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<crate::intrinsics::BuiltinOutcome, crate::EvalFailure> {
    stack_method(machine, this, args, DisposeHint::Sync)
}

pub(crate) fn async_disposable_stack_method_handler<H: crate::Host>(
    machine: &mut crate::Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<crate::intrinsics::BuiltinOutcome, crate::EvalFailure> {
    stack_method(machine, this, args, DisposeHint::Async)
}

fn disposed_getter<H: crate::Host>(
    machine: &mut crate::Machine<'_, H>,
    this: Value,
    hint: DisposeHint,
) -> Result<crate::intrinsics::BuiltinOutcome, crate::EvalFailure> {
    let index = expected_stack_index(machine, this, hint)?;
    let crate::HeapEntry::DisposableStack { state, .. } = &machine.heap[index] else {
        unreachable!("receiver was checked above");
    };
    Ok(crate::intrinsics::BuiltinOutcome::Value(Value::boolean(
        state.is_disposed(),
    )))
}

pub(crate) fn disposable_stack_disposed_getter<H: crate::Host>(
    machine: &mut crate::Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<crate::intrinsics::BuiltinOutcome, crate::EvalFailure> {
    disposed_getter(machine, this, DisposeHint::Sync)
}

pub(crate) fn async_disposable_stack_disposed_getter<H: crate::Host>(
    machine: &mut crate::Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<crate::intrinsics::BuiltinOutcome, crate::EvalFailure> {
    disposed_getter(machine, this, DisposeHint::Async)
}

impl<'a, H: crate::Host> crate::Machine<'a, H> {
    fn chain_async_disposal_error(
        &mut self,
        pending: Option<Value>,
        new_error: Value,
    ) -> Result<Value, crate::EvalFailure> {
        match chain_disposal_error(pending, new_error) {
            ChainStep::Throw(value) => Ok(value),
            ChainStep::Suppress { error, suppressed } => {
                self.make_suppressed_error(error, suppressed)
            }
        }
    }

    fn arm_async_disposal_reaction(
        &mut self,
        promise: Value,
        stack: Value,
        pending_error: Option<Value>,
        capability: Value,
    ) -> Result<(), crate::EvalFailure> {
        let index = self
            .runtime_slot(promise)
            .map_err(crate::EvalFailure::Runtime)?
            .ok_or(crate::EvalFailure::Throw(crate::ThrowOrigin::TypeError {
                operation: "async disposer did not produce a Promise",
            }))?;
        let state = match &self.heap[index] {
            crate::HeapEntry::Promise { state, .. } => state.clone(),
            _ => {
                return Err(crate::EvalFailure::Throw(crate::ThrowOrigin::TypeError {
                    operation: "async disposer did not produce a Promise",
                }));
            }
        };
        let context = self.context_global;
        match state {
            crate::PromiseState::Pending { .. } => {
                self.charge_promise_reactions(index, 2)?;
                let crate::HeapEntry::Promise {
                    state:
                        crate::PromiseState::Pending {
                            fulfill_reactions,
                            reject_reactions,
                            ..
                        },
                    ..
                } = &mut self.heap[index]
                else {
                    unreachable!("promise state was checked before reaction registration");
                };
                fulfill_reactions.push(crate::PromiseReaction::AsyncDisposeStep {
                    stack,
                    pending_error,
                    capability,
                    rejected: false,
                    context,
                });
                reject_reactions.push(crate::PromiseReaction::AsyncDisposeStep {
                    stack,
                    pending_error,
                    capability,
                    rejected: true,
                    context,
                });
            }
            crate::PromiseState::Fulfilled { value } => {
                self.ensure_microtask_capacity(1)
                    .map_err(crate::EvalFailure::Runtime)?;
                self.microtasks.push_back(crate::QueuedMicrotask::uncharged(
                    crate::MicrotaskJob::Reaction {
                        reaction: crate::PromiseReaction::AsyncDisposeStep {
                            stack,
                            pending_error,
                            capability,
                            rejected: false,
                            context,
                        },
                        value,
                        origin: crate::ThrowOrigin::Bytecode,
                    },
                ));
            }
            crate::PromiseState::Rejected { reason, origin } => {
                self.ensure_microtask_capacity(1)
                    .map_err(crate::EvalFailure::Runtime)?;
                self.microtasks.push_back(crate::QueuedMicrotask::uncharged(
                    crate::MicrotaskJob::Reaction {
                        reaction: crate::PromiseReaction::AsyncDisposeStep {
                            stack,
                            pending_error,
                            capability,
                            rejected: true,
                            context,
                        },
                        value: reason,
                        origin,
                    },
                ));
            }
        }
        Ok(())
    }

    pub(crate) fn continue_async_disposal(
        &mut self,
        stack: Value,
        mut pending_error: Option<Value>,
        settled_error: Option<Value>,
        capability: Value,
    ) -> Result<(), crate::EvalFailure> {
        if let Some(error) = settled_error {
            pending_error = Some(self.chain_async_disposal_error(pending_error, error)?);
        }
        let index = self
            .runtime_slot(stack)
            .map_err(crate::EvalFailure::Runtime)?
            .ok_or(crate::EvalFailure::Throw(crate::ThrowOrigin::TypeError {
                operation: "AsyncDisposableStack driver lost its stack",
            }))?;
        loop {
            let resource = {
                let crate::HeapEntry::DisposableStack { state, .. } = &mut self.heap[index] else {
                    return Err(crate::EvalFailure::Throw(crate::ThrowOrigin::TypeError {
                        operation: "AsyncDisposableStack driver lost its stack",
                    }));
                };
                pop_lifo(state)
            };
            let Some(resource) = resource else {
                if let Some(error) = pending_error {
                    return self
                        .reject_promise(capability, error, crate::ThrowOrigin::Bytecode)
                        .map_err(crate::EvalFailure::Runtime);
                }
                return self
                    .fulfill_promise(capability, Value::UNDEFINED)
                    .map_err(crate::EvalFailure::Runtime);
            };
            let result = match call_resource(self, resource) {
                Ok(value) => value,
                Err(failure) => {
                    let (error, _) = self.promise_rejection_value(failure)?;
                    pending_error = Some(self.chain_async_disposal_error(pending_error, error)?);
                    continue;
                }
            };
            if !resource.awaits_result() {
                continue;
            }
            let promise = match self.promise_resolve(result) {
                Ok(promise) => promise,
                Err(failure) => {
                    let (error, _) = self.promise_rejection_value(failure)?;
                    pending_error = Some(self.chain_async_disposal_error(pending_error, error)?);
                    continue;
                }
            };
            return self.arm_async_disposal_reaction(promise, stack, pending_error, capability);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intrinsics::{BuiltinDef, BuiltinHandler, BuiltinOutcome, native_function};
    use crate::{
        EvalFailure, HeapEntry, Host, Limits, MicrotaskJob, PromiseState, PropertyKey, PropertyMap,
        QueuedMicrotask, ThrowOrigin,
    };
    use bamts_bytecode::{
        Constant, ConstantId, EcmaString, Function, FunctionFlags, FunctionId, Instruction, Module,
        ModuleId, Program, ProgramModule, Verified,
    };
    use bamts_native::{Decoded, SlotId};
    use core::num::{NonZeroU16, NonZeroU32};

    fn heap(slot: u32) -> Value {
        Value::heap_ref(SlotId::new(
            NonZeroU16::new(1).expect("nonzero segment"),
            NonZeroU32::new(slot).expect("nonzero slot"),
        ))
    }

    #[derive(Default)]
    struct TestHost;

    impl Host for TestHost {}

    fn blank_program(name: &str) -> Program<Verified> {
        let code = Module::new(
            vec![Constant::String(EcmaString::encode(name))],
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

    fn with_machine(test: impl FnOnce(&mut crate::Machine<'_, TestHost>)) {
        let program = blank_program("<explicit-resource-test>");
        let mut host = TestHost;
        let mut machine = crate::Machine::new(&program, &mut host, Limits::default());
        test(&mut machine);
    }

    fn object(machine: &mut crate::Machine<'_, TestHost>) -> Value {
        machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .expect("object allocation succeeds")
    }

    fn global(machine: &crate::Machine<'_, TestHost>, name: &str) -> Value {
        machine.intrinsics.global(name).expect("builtin exists")
    }

    fn callback(
        machine: &mut crate::Machine<'_, TestHost>,
        name: &'static str,
        handler: BuiltinHandler<TestHost>,
    ) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name,
            length: 0,
            handler,
        });
        native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            name,
            0,
        )
    }

    fn named_global(machine: &crate::Machine<'_, TestHost>, name: &str) -> Value {
        *machine
            .intrinsics
            .globals
            .get(&EcmaString::encode(name))
            .expect("test global exists")
    }

    fn set_named_global(machine: &mut crate::Machine<'_, TestHost>, name: &str, value: Value) {
        machine
            .intrinsics
            .globals
            .insert(EcmaString::encode(name), value);
    }

    fn increment_counter(
        machine: &mut crate::Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let current = named_global(machine, "counter");
        let next = match current.decode() {
            Some(Decoded::Int32(value)) => value + 1,
            _ => 1,
        };
        set_named_global(machine, "counter", Value::int32(next));
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    fn record_one(
        machine: &mut crate::Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let current = named_global(machine, "order");
        let current = match current.decode() {
            Some(Decoded::Int32(value)) => value,
            _ => 0,
        };
        set_named_global(machine, "order", Value::int32(current * 10 + 1));
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    fn record_two(
        machine: &mut crate::Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let current = named_global(machine, "order");
        let current = match current.decode() {
            Some(Decoded::Int32(value)) => value,
            _ => 0,
        };
        set_named_global(machine, "order", Value::int32(current * 10 + 2));
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    fn reenter_sync_dispose(
        machine: &mut crate::Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let current = named_global(machine, "order");
        let current = match current.decode() {
            Some(Decoded::Int32(value)) => value,
            _ => 0,
        };
        set_named_global(machine, "order", Value::int32(current * 10 + 2));

        let stack = named_global(machine, "reentrantStack");
        let dispose = named_global(machine, "reentrantDispose");
        let result = machine.call_value(dispose, stack, &[])?;
        set_named_global(machine, "reentrantResult", result);

        let current = named_global(machine, "order");
        let current = match current.decode() {
            Some(Decoded::Int32(value)) => value,
            _ => 0,
        };
        set_named_global(machine, "order", Value::int32(current * 10 + 3));
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    fn return_disposer_promise(
        machine: &mut crate::Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let current = named_global(machine, "counter");
        let next = match current.decode() {
            Some(Decoded::Int32(value)) => value + 1,
            _ => 1,
        };
        set_named_global(machine, "counter", Value::int32(next));
        Ok(BuiltinOutcome::Value(named_global(
            machine,
            "disposerPromise",
        )))
    }

    fn throw_first(
        machine: &mut crate::Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(EvalFailure::ThrowValueOrigin {
            value: named_global(machine, "firstError"),
            origin: ThrowOrigin::Bytecode,
        })
    }

    fn throw_second(
        machine: &mut crate::Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(EvalFailure::ThrowValueOrigin {
            value: named_global(machine, "secondError"),
            origin: ThrowOrigin::Bytecode,
        })
    }

    fn construct_named(machine: &mut crate::Machine<'_, TestHost>, name: &str) -> Value {
        let constructor = global(machine, name);
        machine
            .construct_value(constructor, &[])
            .expect("stack construction succeeds")
    }

    fn method(machine: &mut crate::Machine<'_, TestHost>, receiver: Value, name: &str) -> Value {
        machine
            .get_named_property(receiver, name)
            .expect("prototype method exists")
    }

    #[test]
    fn mixed_resources_pop_in_strict_lifo_order() {
        let mut state = DisposalStackState::new();
        disposable_stack_use(&mut state, (heap(11), CAPTURE_METHOD), heap(1)).unwrap();
        disposable_stack_adopt(&mut state, heap(2), heap(12), true).unwrap();
        disposable_stack_defer(&mut state, heap(13), true).unwrap();

        let kinds = [
            pop_lifo(&mut state).unwrap().kind,
            pop_lifo(&mut state).unwrap().kind,
            pop_lifo(&mut state).unwrap().kind,
        ];
        assert_eq!(kinds, [DEFER_CALLBACK, ADOPT_CALLBACK, CAPTURE_METHOD]);
        assert!(pop_lifo(&mut state).is_none());
        assert!(state.is_disposed());
    }

    #[test]
    fn move_transfers_without_disposal_and_disposes_source() {
        let mut source = DisposalStackState::new();
        disposable_stack_defer(&mut source, heap(1), true).unwrap();
        let mut target = stack_move(&mut source).unwrap();

        assert!(source.is_disposed());
        assert_eq!(source.len(), 0);
        assert_eq!(target.len(), 1);
        assert!(!target.is_disposed());
        assert!(pop_lifo(&mut source).is_none());
        assert_eq!(pop_lifo(&mut target).unwrap().method, heap(1));
        assert_eq!(stack_move(&mut source), Err(StackError::Disposed));
    }

    #[test]
    fn every_registration_rejects_a_disposed_stack_as_reference_error() {
        let mut state = DisposalStackState::new();
        assert!(pop_lifo(&mut state).is_none());
        for error in [
            disposable_stack_use(&mut state, (heap(2), CAPTURE_METHOD), heap(1)).unwrap_err(),
            disposable_stack_adopt(&mut state, heap(1), heap(2), true).unwrap_err(),
            disposable_stack_defer(&mut state, heap(2), true).unwrap_err(),
        ] {
            assert_eq!(error, StackError::Disposed);
            assert_eq!(error.kind(), StackErrorKind::ReferenceError);
        }
    }

    #[test]
    fn use_accepts_nullish_without_recording_and_rejects_primitives() {
        for nullish in [Value::UNDEFINED, Value::NULL] {
            let mut state = DisposalStackState::new();
            assert_eq!(
                disposable_stack_use(&mut state, (Value::UNDEFINED, 0), nullish),
                Ok(nullish)
            );
            assert_eq!(state.len(), 0);
        }

        for primitive in [Value::int32(1), Value::TRUE, Value::number(2.5)] {
            let mut state = DisposalStackState::new();
            let error =
                disposable_stack_use(&mut state, (Value::UNDEFINED, 0), primitive).unwrap_err();
            assert_eq!(error, StackError::NotDisposable);
            assert_eq!(error.kind(), StackErrorKind::TypeError);
        }
    }

    #[test]
    fn adopt_and_defer_enforce_callable_boundary_before_recording() {
        let mut state = DisposalStackState::new();
        assert_eq!(
            disposable_stack_adopt(&mut state, heap(1), Value::int32(2), false),
            Err(StackError::NotCallable)
        );
        assert_eq!(
            async_disposable_stack_defer(&mut state, Value::NULL, false),
            Err(StackError::NotCallable)
        );
        assert_eq!(state.len(), 0);
        assert_eq!(StackError::NotCallable.kind(), StackErrorKind::TypeError);
    }

    #[test]
    fn sync_and_async_adapters_preserve_disposal_hints_and_fallback_policy() {
        let mut sync = DisposalStackState::new();
        disposable_stack_use(&mut sync, (heap(2), CAPTURE_METHOD), heap(1)).unwrap();
        let sync_resource = pop_lifo(&mut sync).unwrap();
        assert_eq!(sync_resource.hint, DisposeHint::Sync);
        assert!(!sync_resource.awaits_result());

        let mut asynchronous = DisposalStackState::new();
        async_disposable_stack_use(&mut asynchronous, (heap(4), CAPTURE_METHOD), heap(3)).unwrap();
        async_disposable_stack_use(
            &mut asynchronous,
            (heap(6), CAPTURE_ASYNC_SYNC_FALLBACK),
            heap(5),
        )
        .unwrap();
        let fallback = pop_lifo(&mut asynchronous).unwrap();
        let direct = pop_lifo(&mut asynchronous).unwrap();
        assert_eq!(direct.hint, DisposeHint::Async);
        assert!(direct.awaits_result());
        assert!(!fallback.awaits_result());

        let mut invalid = DisposalStackState::new();
        assert_eq!(
            disposable_stack_use(
                &mut invalid,
                (heap(2), CAPTURE_ASYNC_SYNC_FALLBACK),
                heap(1),
            ),
            Err(StackError::NotDisposable)
        );
    }

    #[test]
    fn callback_records_expose_their_invocation_shapes() {
        let mut state = DisposalStackState::new();
        async_disposable_stack_adopt(&mut state, heap(1), heap(2), true).unwrap();
        async_disposable_stack_defer(&mut state, heap(3), true).unwrap();
        let deferred = pop_lifo(&mut state).unwrap();
        let adopted = pop_lifo(&mut state).unwrap();
        assert!(deferred.is_deferred_callback());
        assert!(!deferred.passes_value_argument());
        assert!(adopted.passes_value_argument());
        assert!(adopted.awaits_result());
    }

    #[test]
    fn suppression_places_new_disposal_error_over_pending_error() {
        let body_error = heap(1);
        let later_disposal_error = heap(2);
        assert_eq!(
            chain_disposal_error(None, body_error),
            ChainStep::Throw(body_error)
        );
        assert_eq!(
            chain_disposal_error(Some(body_error), later_disposal_error),
            ChainStep::Suppress {
                error: later_disposal_error,
                suppressed: body_error,
            }
        );

        let first_wrapper = heap(3);
        let earlier_disposer_error = heap(4);
        assert_eq!(
            chain_disposal_error(Some(first_wrapper), earlier_disposer_error),
            ChainStep::Suppress {
                error: earlier_disposer_error,
                suppressed: first_wrapper,
            }
        );
    }

    #[test]
    fn root_visitor_observes_every_retained_value_and_method() {
        let mut state = DisposalStackState::new();
        disposable_stack_use(&mut state, (heap(2), CAPTURE_METHOD), heap(1)).unwrap();
        disposable_stack_adopt(&mut state, heap(3), heap(4), true).unwrap();
        let mut roots = Vec::new();
        state.visit_roots(|value| roots.push(value));
        assert_eq!(roots, [heap(1), heap(2), heap(3), heap(4)]);
    }

    #[test]
    fn method_and_install_tables_cover_both_stack_surfaces() {
        assert_eq!(
            DISPOSABLE_STACK_CONSTRUCTOR,
            StackConstructor {
                name: "DisposableStack",
                length: 0,
                hint: DisposeHint::Sync,
            }
        );
        assert_eq!(
            ASYNC_DISPOSABLE_STACK_CONSTRUCTOR,
            StackConstructor {
                name: "AsyncDisposableStack",
                length: 0,
                hint: DisposeHint::Async,
            }
        );
        assert_eq!(construct_stack(false), Err(NewRequired));
        assert_eq!(construct_stack(true), Ok(DisposalStackState::new()));
        assert_eq!(
            DISPOSABLE_STACK_METHODS.map(|method| (method.name, method.length)),
            [
                ("use", 1),
                ("adopt", 2),
                ("defer", 1),
                ("move", 0),
                ("dispose", 0)
            ]
        );
        assert_eq!(
            ASYNC_DISPOSABLE_STACK_METHODS.map(|method| (method.name, method.length)),
            [
                ("use", 1),
                ("adopt", 2),
                ("defer", 1),
                ("move", 0),
                ("disposeAsync", 0)
            ]
        );
        assert_eq!(
            DISPOSABLE_STACK_INSTALLS,
            [
                StackInstall::DisposedAccessor,
                StackInstall::DisposeAlias,
                StackInstall::ToStringTag("DisposableStack"),
            ]
        );
        assert_eq!(
            ASYNC_DISPOSABLE_STACK_INSTALLS,
            [
                StackInstall::DisposedAccessor,
                StackInstall::AsyncDisposeAlias,
                StackInstall::ToStringTag("AsyncDisposableStack"),
            ]
        );
    }

    #[test]
    fn prototype_chain_resolution_and_constructor_contract() {
        with_machine(|machine| {
            let sync_constructor = global(machine, "DisposableStack");
            assert!(matches!(
                machine.call_value(sync_constructor, Value::UNDEFINED, &[]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));

            for (name, hint, expected_prototype) in [
                (
                    "DisposableStack",
                    DisposeHint::Sync,
                    machine.intrinsics.builtins.disposable_stack_prototype(),
                ),
                (
                    "AsyncDisposableStack",
                    DisposeHint::Async,
                    machine
                        .intrinsics
                        .builtins
                        .async_disposable_stack_prototype(),
                ),
            ] {
                let stack = construct_named(machine, name);
                let index = machine.runtime_slot(stack).unwrap().unwrap();
                let HeapEntry::DisposableStack {
                    hint: actual_hint,
                    prototype,
                    ..
                } = &machine.heap[index]
                else {
                    panic!("constructor allocated the stack representation")
                };
                assert_eq!(*actual_hint, hint);
                assert_eq!(*prototype, Some(expected_prototype));
                let use_method = method(machine, stack, "use");
                assert!(machine.is_callable(use_method).unwrap());
                assert_eq!(
                    machine.get_named_property(stack, "disposed").unwrap(),
                    Value::FALSE
                );
            }

            let custom_prototype = object(machine);
            let custom_new_target = object(machine);
            machine
                .set_data_property(custom_new_target, "prototype", custom_prototype)
                .unwrap();
            let constructor_id = machine
                .intrinsics
                .builtins
                .id_named("DisposableStack")
                .unwrap();
            let BuiltinOutcome::Value(overridden) = machine
                .call_builtin_with_new_target(
                    constructor_id,
                    Value::UNDEFINED,
                    &[],
                    true,
                    custom_new_target,
                )
                .unwrap()
            else {
                panic!("constructor returns a value")
            };
            let overridden_index = machine.runtime_slot(overridden).unwrap().unwrap();
            let HeapEntry::DisposableStack { prototype, .. } = &machine.heap[overridden_index]
            else {
                panic!("constructor allocated a stack")
            };
            assert_eq!(*prototype, Some(custom_prototype));

            machine
                .set_data_property(custom_new_target, "prototype", Value::int32(7))
                .unwrap();
            let BuiltinOutcome::Value(fallback) = machine
                .call_builtin_with_new_target(
                    constructor_id,
                    Value::UNDEFINED,
                    &[],
                    true,
                    custom_new_target,
                )
                .unwrap()
            else {
                panic!("constructor returns a value")
            };
            let fallback_index = machine.runtime_slot(fallback).unwrap().unwrap();
            let HeapEntry::DisposableStack { prototype, .. } = &machine.heap[fallback_index] else {
                panic!("constructor allocated a stack")
            };
            assert_eq!(
                *prototype,
                Some(machine.intrinsics.builtins.disposable_stack_prototype())
            );

            let sync_prototype = machine.intrinsics.builtins.disposable_stack_prototype();
            let dispose = method(machine, sync_prototype, "dispose");
            let dispose_symbol = machine.intrinsics.builtins.symbol_dispose();
            let dispose_key = machine.property_key_from_value(dispose_symbol).unwrap();
            assert_eq!(
                machine
                    .get_property_key(sync_prototype, &dispose_key)
                    .unwrap(),
                dispose
            );
        });
    }

    #[test]
    fn sync_dispose_lifo_marking_and_idempotence() {
        with_machine(|machine| {
            set_named_global(machine, "order", Value::int32(0));
            let one = callback(machine, "record one", record_one);
            let two = callback(machine, "record two", record_two);
            let stack = construct_named(machine, "DisposableStack");
            let defer = method(machine, stack, "defer");
            machine.call_value(defer, stack, &[one]).unwrap();
            machine.call_value(defer, stack, &[two]).unwrap();
            assert_eq!(
                machine.get_named_property(stack, "disposed").unwrap(),
                Value::FALSE
            );

            let dispose = method(machine, stack, "dispose");
            assert_eq!(
                machine.call_value(dispose, stack, &[]).unwrap(),
                Value::UNDEFINED
            );
            assert_eq!(named_global(machine, "order"), Value::int32(21));
            assert_eq!(
                machine.get_named_property(stack, "disposed").unwrap(),
                Value::TRUE
            );
            assert_eq!(
                machine.call_value(dispose, stack, &[]).unwrap(),
                Value::UNDEFINED
            );
            let use_method = method(machine, stack, "use");
            assert!(matches!(
                machine.call_value(use_method, stack, &[Value::UNDEFINED]),
                Err(EvalFailure::Throw(ThrowOrigin::ReferenceError { .. }))
            ));
        });
    }

    #[test]
    fn sync_dispose_callback_reentry_does_not_drain_outer_stack() {
        with_machine(|machine| {
            set_named_global(machine, "order", Value::int32(0));
            let remaining = callback(machine, "record remaining", record_one);
            let reentrant = callback(machine, "reenter dispose", reenter_sync_dispose);
            let stack = construct_named(machine, "DisposableStack");
            let defer = method(machine, stack, "defer");
            machine.call_value(defer, stack, &[remaining]).unwrap();
            machine.call_value(defer, stack, &[reentrant]).unwrap();
            let dispose = method(machine, stack, "dispose");
            set_named_global(machine, "reentrantStack", stack);
            set_named_global(machine, "reentrantDispose", dispose);

            assert_eq!(
                machine.call_value(dispose, stack, &[]).unwrap(),
                Value::UNDEFINED
            );
            assert_eq!(named_global(machine, "reentrantResult"), Value::UNDEFINED);
            assert_eq!(named_global(machine, "order"), Value::int32(231));
        });
    }

    #[test]
    fn move_transfers_and_severs_heap_ownership() {
        with_machine(|machine| {
            let callback = callback(machine, "retained callback", increment_counter);
            let source = construct_named(machine, "DisposableStack");
            let source_index = machine.runtime_slot(source).unwrap().unwrap();
            let HeapEntry::DisposableStack { state, .. } = &mut machine.heap[source_index] else {
                panic!("source is a stack")
            };
            disposable_stack_defer(state, callback, true).unwrap();

            let move_method = method(machine, source, "move");
            let moved = machine.call_value(move_method, source, &[]).unwrap();
            let moved_index = machine.runtime_slot(moved).unwrap().unwrap();
            let HeapEntry::DisposableStack {
                state: source_state,
                ..
            } = &machine.heap[source_index]
            else {
                panic!("source remains a stack")
            };
            assert!(source_state.is_disposed());
            assert_eq!(source_state.len(), 0);
            let HeapEntry::DisposableStack {
                state: moved_state,
                prototype,
                ..
            } = &machine.heap[moved_index]
            else {
                panic!("move returns a stack")
            };
            assert!(!moved_state.is_disposed());
            assert_eq!(moved_state.len(), 1);
            assert_eq!(
                *prototype,
                Some(machine.intrinsics.builtins.disposable_stack_prototype())
            );
            assert!(matches!(
                machine.call_value(move_method, source, &[]),
                Err(EvalFailure::Throw(ThrowOrigin::ReferenceError { .. }))
            ));
        });
    }

    #[test]
    fn sync_error_suppression_chain_preserves_lifo_failures() {
        with_machine(|machine| {
            let first_error = object(machine);
            let second_error = object(machine);
            set_named_global(machine, "firstError", first_error);
            set_named_global(machine, "secondError", second_error);
            let first = callback(machine, "throw first", throw_first);
            let second = callback(machine, "throw second", throw_second);
            let stack = construct_named(machine, "DisposableStack");
            let defer = method(machine, stack, "defer");
            machine.call_value(defer, stack, &[first]).unwrap();
            machine.call_value(defer, stack, &[second]).unwrap();
            let dispose = method(machine, stack, "dispose");
            let failure = machine.call_value(dispose, stack, &[]).unwrap_err();
            let EvalFailure::ThrowValueOrigin { value: chained, .. } = failure else {
                panic!("dispose throws the materialized suppression chain")
            };
            assert_eq!(
                machine.get_named_property(chained, "error").unwrap(),
                first_error
            );
            assert_eq!(
                machine.get_named_property(chained, "suppressed").unwrap(),
                second_error
            );
        });
    }

    #[test]
    fn async_dispose_full_lifecycle_and_at_most_once_resumption() {
        with_machine(|machine| {
            set_named_global(machine, "counter", Value::int32(0));
            let disposer_promise = machine.create_promise().unwrap();
            set_named_global(machine, "disposerPromise", disposer_promise);
            let disposer = callback(machine, "return promise", return_disposer_promise);
            let stack = construct_named(machine, "AsyncDisposableStack");
            let defer = method(machine, stack, "defer");
            machine.call_value(defer, stack, &[disposer]).unwrap();
            let dispose_async = method(machine, stack, "disposeAsync");
            let capability = machine.call_value(dispose_async, stack, &[]).unwrap();
            let capability_index = machine.runtime_slot(capability).unwrap().unwrap();
            assert!(matches!(
                &machine.heap[capability_index],
                HeapEntry::Promise {
                    state: PromiseState::Pending { .. },
                    ..
                }
            ));
            assert_eq!(named_global(machine, "counter"), Value::int32(1));

            machine
                .fulfill_promise(disposer_promise, Value::UNDEFINED)
                .unwrap();
            machine
                .fulfill_promise(disposer_promise, Value::int32(9))
                .unwrap();
            machine.drain_microtasks().unwrap();
            machine.drain_microtasks().unwrap();
            assert_eq!(named_global(machine, "counter"), Value::int32(1));
            assert!(matches!(
                &machine.heap[capability_index],
                HeapEntry::Promise {
                    state: PromiseState::Fulfilled {
                        value: Value::UNDEFINED
                    },
                    ..
                }
            ));

            let settled_stack = construct_named(machine, "AsyncDisposableStack");
            let settled_defer = method(machine, settled_stack, "defer");
            let increment = callback(machine, "increment", increment_counter);
            machine
                .call_value(settled_defer, settled_stack, &[increment])
                .unwrap();
            let settled_dispose = method(machine, settled_stack, "disposeAsync");
            let settled_capability = machine
                .call_value(settled_dispose, settled_stack, &[])
                .unwrap();
            machine.drain_microtasks().unwrap();
            let settled_index = machine.runtime_slot(settled_capability).unwrap().unwrap();
            assert!(matches!(
                &machine.heap[settled_index],
                HeapEntry::Promise {
                    state: PromiseState::Fulfilled {
                        value: Value::UNDEFINED
                    },
                    ..
                }
            ));
            assert_eq!(named_global(machine, "counter"), Value::int32(2));
        });
    }

    #[test]
    fn pending_double_dispose_async_returns_fresh_fulfilled_promise() {
        with_machine(|machine| {
            set_named_global(machine, "counter", Value::int32(0));
            let disposer_promise = machine.create_promise().unwrap();
            set_named_global(machine, "disposerPromise", disposer_promise);
            let remaining = callback(machine, "remaining", increment_counter);
            let pending = callback(machine, "pending disposer", return_disposer_promise);
            let stack = construct_named(machine, "AsyncDisposableStack");
            let defer = method(machine, stack, "defer");
            machine.call_value(defer, stack, &[remaining]).unwrap();
            machine.call_value(defer, stack, &[pending]).unwrap();
            let dispose_async = method(machine, stack, "disposeAsync");

            let original = machine.call_value(dispose_async, stack, &[]).unwrap();
            let reentry = machine.call_value(dispose_async, stack, &[]).unwrap();
            assert_ne!(reentry, original);
            let original_index = machine.runtime_slot(original).unwrap().unwrap();
            let reentry_index = machine.runtime_slot(reentry).unwrap().unwrap();
            assert!(matches!(
                &machine.heap[original_index],
                HeapEntry::Promise {
                    state: PromiseState::Pending { .. },
                    ..
                }
            ));
            assert!(matches!(
                &machine.heap[reentry_index],
                HeapEntry::Promise {
                    state: PromiseState::Fulfilled {
                        value: Value::UNDEFINED
                    },
                    ..
                }
            ));
            assert_eq!(named_global(machine, "counter"), Value::int32(1));

            machine
                .fulfill_promise(disposer_promise, Value::UNDEFINED)
                .unwrap();
            machine.drain_microtasks().unwrap();
            machine.drain_microtasks().unwrap();
            assert_eq!(named_global(machine, "counter"), Value::int32(2));
            assert!(matches!(
                &machine.heap[original_index],
                HeapEntry::Promise {
                    state: PromiseState::Fulfilled {
                        value: Value::UNDEFINED
                    },
                    ..
                }
            ));
        });
    }

    #[test]
    fn async_rejection_continues_and_sync_fallback_is_not_awaited() {
        with_machine(|machine| {
            set_named_global(machine, "counter", Value::int32(0));
            let disposer_promise = machine.create_promise().unwrap();
            set_named_global(machine, "disposerPromise", disposer_promise);
            let remaining = callback(machine, "remaining", increment_counter);
            let rejecting = callback(machine, "rejecting", return_disposer_promise);
            let stack = construct_named(machine, "AsyncDisposableStack");
            let defer = method(machine, stack, "defer");
            machine.call_value(defer, stack, &[remaining]).unwrap();
            machine.call_value(defer, stack, &[rejecting]).unwrap();
            let dispose_async = method(machine, stack, "disposeAsync");
            let capability = machine.call_value(dispose_async, stack, &[]).unwrap();
            let rejection = object(machine);
            machine
                .reject_promise(disposer_promise, rejection, ThrowOrigin::Bytecode)
                .unwrap();
            machine.drain_microtasks().unwrap();
            assert_eq!(named_global(machine, "counter"), Value::int32(2));
            let capability_index = machine.runtime_slot(capability).unwrap().unwrap();
            assert!(matches!(
                &machine.heap[capability_index],
                HeapEntry::Promise {
                    state: PromiseState::Rejected { reason, .. },
                    ..
                } if *reason == rejection
            ));

            let fallback_promise = machine.create_promise().unwrap();
            set_named_global(machine, "disposerPromise", fallback_promise);
            let fallback_stack = construct_named(machine, "AsyncDisposableStack");
            let fallback_index = machine.runtime_slot(fallback_stack).unwrap().unwrap();
            let fallback_resource = object(machine);
            let HeapEntry::DisposableStack { state, .. } = &mut machine.heap[fallback_index] else {
                panic!("fallback receiver is a stack")
            };
            async_disposable_stack_use(
                state,
                (rejecting, CAPTURE_ASYNC_SYNC_FALLBACK),
                fallback_resource,
            )
            .unwrap();
            let fallback_dispose = method(machine, fallback_stack, "disposeAsync");
            let fallback_capability = machine
                .call_value(fallback_dispose, fallback_stack, &[])
                .unwrap();
            let fallback_capability_index =
                machine.runtime_slot(fallback_capability).unwrap().unwrap();
            assert!(matches!(
                &machine.heap[fallback_capability_index],
                HeapEntry::Promise {
                    state: PromiseState::Fulfilled {
                        value: Value::UNDEFINED
                    },
                    ..
                }
            ));
            let fallback_promise_index = machine.runtime_slot(fallback_promise).unwrap().unwrap();
            assert!(matches!(
                &machine.heap[fallback_promise_index],
                HeapEntry::Promise {
                    state: PromiseState::Pending { .. },
                    ..
                }
            ));
        });
    }

    #[test]
    fn gc_roots_stack_resources_and_async_reaction_continuation() {
        with_machine(|machine| {
            let resource = object(machine);
            let resource_index = machine.runtime_slot(resource).unwrap().unwrap();
            let disposer = callback(machine, "rooted disposer", increment_counter);
            let disposer_index = machine.runtime_slot(disposer).unwrap().unwrap();
            let mut state = DisposalStackState::new();
            disposable_stack_use(&mut state, (disposer, CAPTURE_METHOD), resource).unwrap();
            let stack = machine
                .allocate(HeapEntry::DisposableStack {
                    state,
                    hint: DisposeHint::Sync,
                    properties: PropertyMap::default(),
                    prototype: Some(machine.intrinsics.builtins.disposable_stack_prototype()),
                    extensible: true,
                })
                .unwrap();
            set_named_global(machine, "rootedStack", stack);
            machine.collect_garbage();
            assert!(!matches!(machine.heap[resource_index], HeapEntry::Vacant));
            assert!(!matches!(machine.heap[disposer_index], HeapEntry::Vacant));

            let reaction_stack = construct_named(machine, "AsyncDisposableStack");
            let reaction_stack_index = machine.runtime_slot(reaction_stack).unwrap().unwrap();
            let capability = machine.create_promise().unwrap();
            let capability_index = machine.runtime_slot(capability).unwrap().unwrap();
            let pending_error = object(machine);
            let pending_error_index = machine.runtime_slot(pending_error).unwrap().unwrap();
            let context = object(machine);
            let context_index = machine.runtime_slot(context).unwrap().unwrap();
            machine
                .microtasks
                .push_back(QueuedMicrotask::uncharged(MicrotaskJob::Reaction {
                    reaction: crate::PromiseReaction::AsyncDisposeStep {
                        stack: reaction_stack,
                        pending_error: Some(pending_error),
                        capability,
                        rejected: false,
                        context: Some(context),
                    },
                    value: Value::UNDEFINED,
                    origin: ThrowOrigin::Bytecode,
                }));
            machine.collect_garbage();
            for index in [
                reaction_stack_index,
                capability_index,
                pending_error_index,
                context_index,
            ] {
                assert!(!matches!(machine.heap[index], HeapEntry::Vacant));
            }
        });
    }

    #[test]
    fn object_header_arms_preserve_ordinary_object_behavior() {
        with_machine(|machine| {
            let stack = construct_named(machine, "DisposableStack");
            machine
                .set_data_property(stack, "owned", Value::int32(3))
                .unwrap();
            assert_eq!(
                machine.get_named_property(stack, "owned").unwrap(),
                Value::int32(3)
            );
            let owned = PropertyKey::Named(machine.intern_str("owned"));
            assert!(machine.has_own_property_key(stack, &owned).unwrap());
            assert!(machine.internal_delete(stack, &owned).unwrap());
            assert!(!machine.has_own_property_key(stack, &owned).unwrap());

            let custom_prototype = object(machine);
            machine.set_prototype(stack, custom_prototype).unwrap();
            let stack_index = machine.runtime_slot(stack).unwrap().unwrap();
            assert_eq!(
                machine.prototype_index(stack_index).unwrap(),
                machine.runtime_slot(custom_prototype).unwrap()
            );
            assert_eq!(machine.type_of(stack), "object");
            assert!(machine.truthy(stack));
            assert!(matches!(
                machine.to_number(stack).unwrap().decode(),
                Some(Decoded::Number(number)) if number.is_nan()
            ));
            assert!(
                machine
                    .value_to_string(stack, 0)
                    .unwrap()
                    .eq_ascii("[object Object]")
            );
            assert_eq!(machine.own_property_keys(stack).unwrap(), Vec::new());

            let object_constructor = global(machine, "Object");
            let is_extensible = method(machine, object_constructor, "isExtensible");
            assert_eq!(
                machine
                    .call_value(is_extensible, object_constructor, &[stack])
                    .unwrap(),
                Value::TRUE
            );
            let prevent_extensions = method(machine, object_constructor, "preventExtensions");
            machine
                .call_value(prevent_extensions, object_constructor, &[stack])
                .unwrap();
            assert_eq!(
                machine
                    .call_value(is_extensible, object_constructor, &[stack])
                    .unwrap(),
                Value::FALSE
            );
        });
    }

    #[test]
    fn wrong_hint_and_foreign_receivers_are_rejected_before_state_access() {
        with_machine(|machine| {
            let sync_prototype = machine.intrinsics.builtins.disposable_stack_prototype();
            let dispose = method(machine, sync_prototype, "dispose");
            let async_stack = construct_named(machine, "AsyncDisposableStack");
            assert!(matches!(
                machine.call_value(dispose, async_stack, &[]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            let foreign = object(machine);
            assert!(matches!(
                machine.call_value(dispose, foreign, &[]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        });
    }

    #[test]
    fn structured_clone_rejects_and_weak_map_accepts_stack() {
        with_machine(|machine| {
            let stack = construct_named(machine, "DisposableStack");
            let structured_clone = global(machine, "structuredClone");
            assert!(
                machine
                    .call_value(structured_clone, Value::UNDEFINED, &[stack])
                    .is_err()
            );

            let weak_map = construct_named(machine, "WeakMap");
            let set = method(machine, weak_map, "set");
            assert_eq!(
                machine
                    .call_value(set, weak_map, &[stack, Value::int32(7)])
                    .unwrap(),
                weak_map
            );
            let get = method(machine, weak_map, "get");
            assert_eq!(
                machine.call_value(get, weak_map, &[stack]).unwrap(),
                Value::int32(7)
            );
        });
    }
}
