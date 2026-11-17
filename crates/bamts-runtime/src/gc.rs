use super::*;

#[cfg(test)]
thread_local! {
    static STRESS_SUSPENDED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Engine-parity tests compare raw slot numbers, which follow collection
/// timing; they run with the environment stress schedule suspended.
#[cfg(test)]
pub(crate) struct StressSuspended(());

#[cfg(test)]
impl StressSuspended {
    pub(crate) fn begin() -> Self {
        STRESS_SUSPENDED.set(true);
        Self(())
    }
}

#[cfg(test)]
impl Drop for StressSuspended {
    fn drop(&mut self) {
        STRESS_SUSPENDED.set(false);
    }
}

#[derive(Default)]
pub(super) struct GcState {
    marks: Vec<bool>,
    /// Runtime slots the last collection found live, plus every slot
    /// refilled since. A collection only walks this set and the unswept
    /// tail, so it never pays for every allocation the program ever made.
    pub(super) survivors: Vec<usize>,
    /// Heap indices the last sweep vacated; allocation hands them out again
    /// before it grows the heap.
    pub(super) free_slots: Vec<usize>,
    /// Vacated slots refilled since the last sweep. They sit below
    /// `swept_len`, so the unswept range alone would miss them.
    pub(super) young_reused: Vec<usize>,
    /// The heap length at the last sweep; every later slot is unswept.
    pub(super) swept_len: usize,
    work: Vec<usize>,
    weak_collections: Vec<usize>,
    /// Marked `WeakRef`s and `FinalizationRegistry`s, found while marking so
    /// that clearing them need not search the heap.
    weak_holders: Vec<usize>,
    pending: bool,
    /// Every allocation requests a collection, which runs at the next safe
    /// point: the only places a collection is sound in production too.
    every_allocation: bool,
    #[cfg(test)]
    schedule_pinned: bool,
    byte_watermark: usize,
    slot_watermark: usize,
}

impl<'a, H: Host> Machine<'a, H> {
    pub(crate) fn collect_garbage(&mut self) {
        let mut gc = std::mem::take(&mut self.gc);
        gc.collect(self);
        self.gc = gc;
    }

    pub(crate) fn collect_if_pending(&mut self) {
        if self.gc.pending {
            self.collect_garbage();
        }
    }

    pub(crate) fn gc_pending(&self) -> bool {
        self.gc.pending
    }

    #[cfg(test)]
    pub(super) fn set_gc_watermarks_for_test(&mut self, bytes: usize, slots: usize) {
        self.gc.set_watermarks(bytes, slots);
        self.request_garbage_collection();
    }

    #[cfg(test)]
    pub(super) fn gc_watermarks_for_test(&self) -> (usize, usize) {
        (self.gc.byte_watermark, self.gc.slot_watermark)
    }

    pub(crate) fn push_native_roots(&mut self, depth: usize, roots: &[Value]) {
        assert_eq!(depth, self.native_roots.len(), "native root depth mismatch");
        self.native_roots.push(roots.to_vec());
    }

    /// Keeps `roots` alive while `body` runs code that can reach a safe point.
    pub(crate) fn with_native_roots<T>(
        &mut self,
        roots: &[Value],
        body: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let depth = self.native_roots.len();
        self.push_native_roots(depth, roots);
        let result = body(self);
        self.pop_native_roots(depth);
        result
    }

    pub(crate) fn refresh_native_roots(&mut self, depth: usize, roots: &[Value]) {
        assert_eq!(
            depth + 1,
            self.native_roots.len(),
            "native root depth mismatch"
        );
        let frame = self
            .native_roots
            .last_mut()
            .expect("a matching native root frame exists");
        frame.clear();
        frame.extend_from_slice(roots);
    }

    pub(crate) fn pop_native_roots(&mut self, depth: usize) {
        assert_eq!(
            depth + 1,
            self.native_roots.len(),
            "native root depth mismatch"
        );
        self.native_roots.pop();
    }
}

/// The heap that starts the first collection, however large the limit is. Half of a
/// large limit would let garbage fill gigabytes before anything collects it.
const FIRST_COLLECTION_BYTES: usize = 32 << 20;
const FIRST_COLLECTION_SLOTS: usize = 1 << 19;

impl GcState {
    pub(super) fn new(limits: &Limits) -> Self {
        Self {
            byte_watermark: (limits.max_heap_bytes / 2).min(FIRST_COLLECTION_BYTES),
            slot_watermark: (limits.max_heap_slots / 2).min(FIRST_COLLECTION_SLOTS),
            every_allocation: limits.collect_every_allocation,
            ..Self::default()
        }
    }

    pub(super) fn request_collection(&mut self, heap_bytes: usize, live_slots: usize) {
        self.pending |= self.every_allocation
            || heap_bytes >= self.byte_watermark
            || live_slots >= self.slot_watermark;
    }

    #[cfg(test)]
    pub(super) fn stress_from_environment(&mut self) {
        if !self.schedule_pinned
            && !STRESS_SUSPENDED.get()
            && std::env::var_os("BAMTS_TEST_COLLECT_EVERY_ALLOCATION").is_some()
        {
            self.every_allocation = true;
        }
    }

    #[cfg(test)]
    fn set_watermarks(&mut self, bytes: usize, slots: usize) {
        self.byte_watermark = bytes;
        self.slot_watermark = slots;
        self.every_allocation = false;
        self.schedule_pinned = true;
    }

    fn recompute_watermarks<H: Host>(&mut self, machine: &Machine<'_, H>) {
        self.byte_watermark = machine
            .heap_bytes
            .saturating_mul(2)
            .min(machine.limits.max_heap_bytes);
        self.slot_watermark = machine
            .live_runtime_slots()
            .saturating_mul(2)
            .min(machine.limits.max_heap_slots);
    }

    fn collect<H: Host>(&mut self, machine: &mut Machine<'_, H>) {
        self.reset_marks(machine);
        self.work.clear();
        self.weak_collections.clear();
        self.weak_holders.clear();

        self.trace_roots(machine);
        self.drain(&machine.heap, &machine.shapes);
        self.ephemeron_fixed_point(&machine.heap, &machine.shapes);
        self.weak_holders.sort_unstable();
        machine.process_weak_targets_after_marking(&self.marks, &self.weak_holders);
        self.purge_weak_entries(machine);
        self.sweep(machine);
        self.pending = false;
        self.recompute_watermarks(machine);

        debug_assert_eq!(machine.slot_bytes.len(), machine.heap.len());
        debug_assert_eq!(
            machine.heap_bytes,
            machine.machine_bytes + machine.slot_bytes.iter().sum::<usize>()
        );
    }

    /// Clears the last collection's marks, which are all on intrinsics or
    /// survivors, and accounts for a rolled-back clone shortening the heap.
    fn reset_marks<H: Host>(&mut self, machine: &Machine<'_, H>) {
        for &index in &self.survivors {
            self.marks[index] = false;
        }
        let intrinsics = self.marks.len().min(machine.intrinsic_slots);
        self.marks[..intrinsics].fill(false);
        let heap_len = machine.heap.len();
        self.marks.resize(heap_len, false);
        self.survivors.retain(|&index| index < heap_len);
        self.free_slots.retain(|&index| index < heap_len);
        self.young_reused.retain(|&index| index < heap_len);
        self.swept_len = self.swept_len.min(heap_len);
    }

    fn trace_roots<H: Host>(&mut self, machine: &Machine<'_, H>) {
        for index in 0..machine.intrinsic_slots {
            mark_index(&machine.heap, &mut self.marks, &mut self.work, index);
        }

        for frame in &machine.frames {
            self.mark_values(&machine.heap, &frame.registers);
            self.mark_value(&machine.heap, frame.this_value);
            self.mark_value(&machine.heap, frame.new_target);
            self.mark_values(&machine.heap, &frame.args);
            if let Some(value) = frame.context {
                self.mark_value(&machine.heap, value);
            }
            if let Some(value) = frame.outer_context {
                self.mark_value(&machine.heap, value);
            }
            if let Some(value) = frame.arguments_object {
                self.mark_value(&machine.heap, value);
            }
            if let Some(value) = frame.return_to.and_then(|return_to| return_to.constructed) {
                self.mark_value(&machine.heap, value);
            }
        }
        self.mark_value(&machine.heap, machine.global_object);
        if let Some(value) = machine.context_global {
            self.mark_value(&machine.heap, value);
        }
        if let Some(value) = machine.last_completion {
            self.mark_value(&machine.heap, value);
        }
        self.mark_value(&machine.heap, machine.current_new_target);
        self.mark_values(&machine.heap, &machine.kept_alive);
        self.mark_values(&machine.heap, &machine.builtin_temporaries);
        self.mark_values(&machine.heap, &machine.array_join_stack);
        self.mark_values(&machine.heap, &machine.callback_results);
        if let Some(resume) = &machine.pending_generator_resume {
            trace_generator_resume(resume, &machine.heap, &mut self.marks, &mut self.work);
        }
        if let Some((awaited, activation)) = &machine.pending_async_suspend {
            mark_value(&machine.heap, &mut self.marks, &mut self.work, *awaited);
            trace_activation(activation, &machine.heap, &mut self.marks, &mut self.work);
        }
        for job in &machine.microtasks {
            trace_microtask(&job.job, &machine.heap, &mut self.marks, &mut self.work);
        }
        for job in &machine.running_jobs {
            trace_microtask(job, &machine.heap, &mut self.marks, &mut self.work);
        }
        for &registry in &machine.finalization_cleanup_queue {
            self.mark_value(&machine.heap, registry);
        }
        for waiter in machine.async_waiters.values() {
            self.mark_value(&machine.heap, waiter.promise);
        }
        for timer in machine.timers.values() {
            self.mark_value(&machine.heap, timer.callback);
            self.mark_values(&machine.heap, &timer.arguments);
            self.mark_value(&machine.heap, timer.handle);
            if let Some(context) = timer.context {
                self.mark_value(&machine.heap, context);
            }
        }
        machine.intrinsics.for_each_value(|value| {
            mark_value(&machine.heap, &mut self.marks, &mut self.work, value);
        });
        for module in &machine.registry.modules {
            if let Some(value) = module.namespace {
                self.mark_value(&machine.heap, value);
            }
            if let Some(value) = module.import_meta {
                self.mark_value(&machine.heap, value);
            }
            match &module.state {
                ModuleState::Unevaluated | ModuleState::Evaluating => {}
                ModuleState::EvaluatingAsync {
                    record, promise, ..
                } => {
                    self.mark_value(&machine.heap, *record);
                    self.mark_value(&machine.heap, *promise);
                }
                ModuleState::Evaluated(Ok(())) => {}
                ModuleState::Evaluated(Err(error)) => {
                    trace_runtime_error(error, &machine.heap, &mut self.marks, &mut self.work);
                }
            }
        }
        for cell in &machine.registry.cells {
            self.mark_value(&machine.heap, cell.value);
        }
        for external in machine.registry.external.values() {
            self.mark_value(&machine.heap, external.namespace);
            for export in external.exports.values() {
                self.mark_value(&machine.heap, export.value);
            }
            for value in external.internals.values().copied() {
                self.mark_value(&machine.heap, value);
            }
        }
        for roots in &machine.native_roots {
            self.mark_values(&machine.heap, roots);
        }
        for key in machine.shapes.live_keys() {
            match key {
                PropertyKey::Symbol(index) | PropertyKey::Private(index) => {
                    mark_index(
                        &machine.heap,
                        &mut self.marks,
                        &mut self.work,
                        *index as usize,
                    );
                }
                PropertyKey::Named(_) => {}
            }
        }
    }

    fn mark_value(&mut self, heap: &[HeapEntry], value: Value) {
        mark_value(heap, &mut self.marks, &mut self.work, value);
    }

    fn mark_values(&mut self, heap: &[HeapEntry], values: &[Value]) {
        for value in values {
            self.mark_value(heap, *value);
        }
    }

    fn drain(&mut self, heap: &[HeapEntry], shapes: &ShapeTable) {
        while let Some(index) = self.work.pop() {
            if matches!(
                heap[index],
                HeapEntry::WeakRef { .. } | HeapEntry::FinalizationRegistry { .. }
            ) {
                self.weak_holders.push(index);
            }
            trace_entry(
                &heap[index],
                index,
                shapes,
                heap,
                &mut self.marks,
                &mut self.work,
                &mut self.weak_collections,
            );
        }
    }

    fn ephemeron_fixed_point(&mut self, heap: &[HeapEntry], shapes: &ShapeTable) {
        loop {
            let weak_count = self.weak_collections.len();
            for list_index in 0..weak_count {
                let slot = self.weak_collections[list_index];
                let HeapEntry::Collection {
                    kind: CollectionKind::WeakMap,
                    entries,
                    ..
                } = &heap[slot]
                else {
                    continue;
                };
                for entry in entries.iter().filter(|entry| entry.live) {
                    if is_marked_value(&self.marks, entry.key) {
                        mark_value(heap, &mut self.marks, &mut self.work, entry.value);
                    }
                }
            }
            if self.work.is_empty() {
                break;
            }
            self.drain(heap, shapes);
        }
    }

    fn purge_weak_entries<H: Host>(&self, machine: &mut Machine<'_, H>) {
        for &index in &self.weak_collections {
            if !self.marks[index] {
                continue;
            }
            let retained = match &machine.heap[index] {
                HeapEntry::Collection {
                    kind: CollectionKind::WeakMap | CollectionKind::WeakSet,
                    entries,
                    size,
                    ..
                } => Some((
                    entries
                        .iter()
                        .copied()
                        .filter(|entry| entry.live && is_marked_value(&self.marks, entry.key))
                        .collect::<Vec<_>>(),
                    *size,
                )),
                _ => None,
            };
            let (replacement, removed) = match retained {
                Some((retained_entries, size)) => {
                    let mut rebuilt = crate::CollectionIndex::default();
                    for (entry_index, entry) in retained_entries.iter().enumerate() {
                        rebuilt.insert(crate::collection_key_hash(machine, entry.key), entry_index);
                    }
                    let removed = size - retained_entries.len();
                    (Some((retained_entries, rebuilt)), removed)
                }
                None => (None, 0),
            };
            if let Some((retained_entries, rebuilt)) = replacement {
                let HeapEntry::Collection {
                    entries,
                    index: stored_index,
                    size,
                    ..
                } = &mut machine.heap[index]
                else {
                    unreachable!("weak collection was checked")
                };
                *entries = retained_entries;
                *stored_index = rebuilt;
                *size -= removed;
            }
            machine.refund_slot(
                index,
                removed * (CollectionEntry::BYTES + crate::CollectionIndex::ENTRY_BYTES),
            );
        }
    }

    /// Reclaims every unmarked slot in `survivors` plus every slot in the
    /// unswept tail `swept_len..heap.len()`; a slot refilled since the last
    /// sweep sits in `young_reused` and joins the sweep through `survivors`,
    /// which `allocate` extends when it reuses a free slot. A vacated slot
    /// joins `free_slots`, so the next `allocate` hands it out again.
    ///
    /// Precondition: after marking, no root, frame register, shadow frame,
    /// weak table entry or finalization cell references a swept (Vacant)
    /// runtime slot. `trace_roots` walks the same root set the debug
    /// assertion at the end of this method re-walks.
    fn sweep<H: Host>(&mut self, machine: &mut Machine<'_, H>) {
        self.survivors.append(&mut self.young_reused);
        let tail = self.swept_len.max(machine.intrinsic_slots)..machine.heap.len();
        let mut retained = Vec::with_capacity(self.survivors.len() + tail.len());
        for index in self.survivors.drain(..).chain(tail) {
            if self.marks[index] && !matches!(machine.heap[index], HeapEntry::Vacant) {
                retained.push(index);
                continue;
            }
            if !matches!(machine.heap[index], HeapEntry::Vacant) {
                machine.heap[index] = HeapEntry::Vacant;
                let charge = std::mem::take(&mut machine.slot_bytes[index]);
                machine.heap_bytes -= charge;
                machine.vacant_count += 1;
            }
            self.free_slots.push(index);
        }
        self.survivors = retained;
        self.swept_len = machine.heap.len();
        machine.has_instance_symbol = None;
        self.assert_no_rooted_vacant(machine);
    }
    /// The sweep precondition: after marking, nothing the root walk visits
    /// names a slot that is now `Vacant`. The check re-derives every rooted
    /// `Value` the same way `trace_roots` did, then asserts each decoded
    /// index still holds a live entry.
    #[cfg(debug_assertions)]
    fn assert_no_rooted_vacant<H: Host>(&self, machine: &Machine<'_, H>) {
        let heap = &machine.heap;
        for frame in &machine.frames {
            check_values(&frame.registers, heap);
            check_value(frame.this_value, heap);
            check_value(frame.new_target, heap);
            check_values(&frame.args, heap);
            if let Some(value) = frame.context {
                check_value(value, heap);
            }
            if let Some(value) = frame.outer_context {
                check_value(value, heap);
            }
            if let Some(value) = frame.arguments_object {
                check_value(value, heap);
            }
            if let Some(value) = frame.return_to.and_then(|return_to| return_to.constructed) {
                check_value(value, heap);
            }
        }
        check_value(machine.global_object, heap);
        if let Some(value) = machine.context_global {
            check_value(value, heap);
        }
        if let Some(value) = machine.last_completion {
            check_value(value, heap);
        }
        check_value(machine.current_new_target, heap);
        check_values(&machine.kept_alive, heap);
        check_values(&machine.builtin_temporaries, heap);
        check_values(&machine.array_join_stack, heap);
        check_values(&machine.callback_results, heap);
        if let Some(resume) = &machine.pending_generator_resume {
            check_generator_resume(resume, heap);
        }
        if let Some((awaited, activation)) = &machine.pending_async_suspend {
            check_value(*awaited, heap);
            check_activation(activation, heap);
        }
        for job in &machine.microtasks {
            check_microtask(&job.job, heap);
        }
        for job in &machine.running_jobs {
            check_microtask(job, heap);
        }
        for &registry in &machine.finalization_cleanup_queue {
            check_value(registry, heap);
        }
        for waiter in machine.async_waiters.values() {
            check_value(waiter.promise, heap);
        }
        for timer in machine.timers.values() {
            check_value(timer.callback, heap);
            check_values(&timer.arguments, heap);
            check_value(timer.handle, heap);
            if let Some(context) = timer.context {
                check_value(context, heap);
            }
        }
        machine
            .intrinsics
            .for_each_value(|value| check_value(value, heap));
        for module in &machine.registry.modules {
            if let Some(value) = module.namespace {
                check_value(value, heap);
            }
            if let Some(value) = module.import_meta {
                check_value(value, heap);
            }
            match &module.state {
                ModuleState::EvaluatingAsync {
                    record, promise, ..
                } => {
                    check_value(*record, heap);
                    check_value(*promise, heap);
                }
                ModuleState::Evaluated(Err(error)) => check_runtime_error(error, heap),
                _ => {}
            }
        }
        for cell in &machine.registry.cells {
            check_value(cell.value, heap);
        }
        for external in machine.registry.external.values() {
            check_value(external.namespace, heap);
            for export in external.exports.values() {
                check_value(export.value, heap);
            }
            for value in external.internals.values().copied() {
                check_value(value, heap);
            }
        }
        for roots in &machine.native_roots {
            check_values(roots, heap);
        }
    }

    #[cfg(not(debug_assertions))]
    fn assert_no_rooted_vacant<H: Host>(&self, _machine: &Machine<'_, H>) {}
}

#[cfg(debug_assertions)]
fn check_value(value: Value, heap: &[HeapEntry]) {
    if let Some(index) = runtime_index(value)
        && index < heap.len()
        && matches!(heap[index], HeapEntry::Vacant)
    {
        panic!("rooted value names swept slot {index}");
    }
}

#[cfg(debug_assertions)]
fn check_values(values: &[Value], heap: &[HeapEntry]) {
    for &value in values {
        check_value(value, heap);
    }
}

#[cfg(debug_assertions)]
fn check_activation(activation: &SuspendedActivation, heap: &[HeapEntry]) {
    check_values(&activation.registers, heap);
    check_value(activation.this_value, heap);
    check_value(activation.new_target, heap);
    check_values(&activation.args, heap);
    if let Some(value) = activation.arguments_object {
        check_value(value, heap);
    }
    if let Some(value) = activation.context {
        check_value(value, heap);
    }
}

#[cfg(debug_assertions)]
fn check_generator_resume(resume: &GeneratorResume, heap: &[HeapEntry]) {
    match resume {
        GeneratorResume::Yield { value, activation } => {
            check_value(*value, heap);
            check_activation(activation, heap);
        }
        GeneratorResume::Return(value) | GeneratorResume::Throw { value, .. } => {
            check_value(*value, heap);
        }
    }
}

#[cfg(debug_assertions)]
fn check_microtask(job: &MicrotaskJob, heap: &[HeapEntry]) {
    match job {
        MicrotaskJob::Reaction {
            reaction, value, ..
        } => {
            check_promise_reaction(reaction, heap);
            check_value(*value, heap);
        }
        MicrotaskJob::Thenable {
            promise,
            thenable,
            then,
            context,
        } => {
            check_value(*promise, heap);
            check_value(*thenable, heap);
            check_value(*then, heap);
            if let Some(context) = context {
                check_value(*context, heap);
            }
        }
        MicrotaskJob::Callback { callback, context } => {
            check_value(*callback, heap);
            if let Some(context) = context {
                check_value(*context, heap);
            }
        }
        MicrotaskJob::FinalizationCleanup { registry, context } => {
            check_value(*registry, heap);
            if let Some(context) = context {
                check_value(*context, heap);
            }
        }
    }
}

#[cfg(debug_assertions)]
fn check_promise_reaction(reaction: &PromiseReaction, heap: &[HeapEntry]) {
    match reaction {
        PromiseReaction::Fulfilled {
            handler, derived, ..
        }
        | PromiseReaction::Rejected {
            handler, derived, ..
        } => {
            check_value(*handler, heap);
            check_value(*derived, heap);
        }
        PromiseReaction::AsyncFulfill { activation, .. }
        | PromiseReaction::AsyncReject { activation, .. } => {
            check_value(*activation, heap);
        }
        PromiseReaction::AsyncGeneratorFulfill { generator, .. }
        | PromiseReaction::AsyncGeneratorReject { generator, .. } => {
            check_value(*generator, heap);
        }
        PromiseReaction::ModuleDepFulfill { .. } | PromiseReaction::ModuleDepReject { .. } => {}
        PromiseReaction::AsyncFromSyncFulfill { derived, .. } => {
            check_value(*derived, heap);
        }
        PromiseReaction::AsyncFromSyncReject {
            derived,
            sync_iterator,
            ..
        } => {
            check_value(*derived, heap);
            check_value(*sync_iterator, heap);
        }
        PromiseReaction::AsyncDisposeStep {
            stack,
            pending_error,
            capability,
            ..
        } => {
            check_value(*stack, heap);
            if let Some(error) = pending_error {
                check_value(*error, heap);
            }
            check_value(*capability, heap);
        }
        PromiseReaction::DynamicImportFulfill { promise, .. }
        | PromiseReaction::DynamicImportReject { promise, .. } => {
            check_value(*promise, heap);
        }
    }
    if let Some(context) = reaction.context() {
        check_value(context, heap);
    }
}

#[cfg(debug_assertions)]
fn check_runtime_error(error: &RuntimeError, heap: &[HeapEntry]) {
    match &error.kind {
        RuntimeErrorKind::UncaughtThrow { value, .. }
        | RuntimeErrorKind::InvalidValue { value } => check_value(*value, heap),
        _ => {}
    }
}

fn runtime_index(value: Value) -> Option<usize> {
    let Decoded::HeapRef(id) = value.decode()? else {
        return None;
    };
    if id.segment() != RUNTIME_HEAP_SEGMENT {
        return None;
    }
    // SlotId stores a NonZeroU32 slot (from_parts rejects zero), so every
    // decoded HeapRef has slot() >= 1; the subtraction cannot underflow.
    debug_assert!(id.slot() > 0, "SlotId slot is NonZeroU32");
    (id.slot() as usize).checked_sub(1)
}

fn is_marked_value(marks: &[bool], value: Value) -> bool {
    runtime_index(value).is_some_and(|index| marks.get(index).copied().unwrap_or(false))
}

fn mark_value(heap: &[HeapEntry], marks: &mut [bool], work: &mut Vec<usize>, value: Value) {
    let Some(index) = runtime_index(value) else {
        return;
    };
    mark_index(heap, marks, work, index);
}

fn mark_index(heap: &[HeapEntry], marks: &mut [bool], work: &mut Vec<usize>, index: usize) {
    if index >= heap.len() || marks[index] || matches!(heap[index], HeapEntry::Vacant) {
        return;
    }
    marks[index] = true;
    work.push(index);
}

fn trace_property_map(
    properties: &PropertyMap,
    shapes: &ShapeTable,
    heap: &[HeapEntry],
    marks: &mut [bool],
    work: &mut Vec<usize>,
) {
    for (key, property) in properties.iter(shapes) {
        match key {
            PropertyKey::Named(_) => {}
            PropertyKey::Symbol(index) | PropertyKey::Private(index) => {
                mark_index(heap, marks, work, *index as usize);
            }
        }
        match property {
            Property::Data { value, .. } => mark_value(heap, marks, work, *value),
            Property::Accessor { getter, setter, .. } => {
                if let Some(value) = getter {
                    mark_value(heap, marks, work, *value);
                }
                if let Some(value) = setter {
                    mark_value(heap, marks, work, *value);
                }
            }
        }
    }
}

fn trace_properties_and_prototype(
    properties: &PropertyMap,
    shapes: &ShapeTable,
    prototype: Option<Value>,
    heap: &[HeapEntry],
    marks: &mut [bool],
    work: &mut Vec<usize>,
) {
    trace_property_map(properties, shapes, heap, marks, work);
    if let Some(value) = prototype {
        mark_value(heap, marks, work, value);
    }
}

fn trace_values(heap: &[HeapEntry], marks: &mut [bool], work: &mut Vec<usize>, values: &[Value]) {
    for value in values {
        mark_value(heap, marks, work, *value);
    }
}

fn trace_activation(
    activation: &SuspendedActivation,
    heap: &[HeapEntry],
    marks: &mut [bool],
    work: &mut Vec<usize>,
) {
    trace_values(heap, marks, work, &activation.registers);
    mark_value(heap, marks, work, activation.this_value);
    mark_value(heap, marks, work, activation.new_target);
    trace_values(heap, marks, work, &activation.args);
    if let Some(value) = activation.arguments_object {
        mark_value(heap, marks, work, value);
    }
    if let Some(value) = activation.context {
        mark_value(heap, marks, work, value);
    }
}

fn trace_generator_start(
    start: &GeneratorStart,
    heap: &[HeapEntry],
    marks: &mut [bool],
    work: &mut Vec<usize>,
) {
    trace_values(heap, marks, work, &start.captures);
    mark_value(heap, marks, work, start.this_value);
    mark_value(heap, marks, work, start.new_target);
    trace_values(heap, marks, work, &start.args);
    if let Some(value) = start.context {
        mark_value(heap, marks, work, value);
    }
}

fn trace_generator_state(
    state: &GeneratorState,
    heap: &[HeapEntry],
    marks: &mut [bool],
    work: &mut Vec<usize>,
) {
    match state {
        GeneratorState::SuspendedStart(start) => trace_generator_start(start, heap, marks, work),
        GeneratorState::Suspended(activation) => trace_activation(activation, heap, marks, work),
        GeneratorState::Executing | GeneratorState::Completed => {}
    }
}

fn trace_async_generator_state(
    state: &AsyncGeneratorState,
    heap: &[HeapEntry],
    marks: &mut [bool],
    work: &mut Vec<usize>,
) {
    match state {
        AsyncGeneratorState::SuspendedStart(start) => {
            trace_generator_start(start, heap, marks, work)
        }
        AsyncGeneratorState::SuspendedYield(activation)
        | AsyncGeneratorState::AwaitingOperand(activation)
        | AsyncGeneratorState::AwaitingYield(activation)
        | AsyncGeneratorState::AwaitingResumption(activation) => {
            trace_activation(activation, heap, marks, work);
        }
        AsyncGeneratorState::Executing
        | AsyncGeneratorState::AwaitingReturn
        | AsyncGeneratorState::Completed => {}
    }
}

fn trace_generator_resume(
    resume: &GeneratorResume,
    heap: &[HeapEntry],
    marks: &mut [bool],
    work: &mut Vec<usize>,
) {
    match resume {
        GeneratorResume::Yield { value, activation } => {
            mark_value(heap, marks, work, *value);
            trace_activation(activation, heap, marks, work);
        }
        GeneratorResume::Return(value) | GeneratorResume::Throw { value, .. } => {
            mark_value(heap, marks, work, *value);
        }
    }
}

fn trace_promise_reaction(
    reaction: &PromiseReaction,
    heap: &[HeapEntry],
    marks: &mut [bool],
    work: &mut Vec<usize>,
) {
    match reaction {
        PromiseReaction::Fulfilled {
            handler, derived, ..
        }
        | PromiseReaction::Rejected {
            handler, derived, ..
        } => {
            mark_value(heap, marks, work, *handler);
            mark_value(heap, marks, work, *derived);
        }
        PromiseReaction::AsyncFulfill { activation, .. }
        | PromiseReaction::AsyncReject { activation, .. } => {
            mark_value(heap, marks, work, *activation);
        }
        PromiseReaction::AsyncGeneratorFulfill { generator, .. }
        | PromiseReaction::AsyncGeneratorReject { generator, .. } => {
            mark_value(heap, marks, work, *generator);
        }
        PromiseReaction::ModuleDepFulfill { .. } | PromiseReaction::ModuleDepReject { .. } => {}
        PromiseReaction::AsyncFromSyncFulfill { derived, .. } => {
            mark_value(heap, marks, work, *derived);
        }
        PromiseReaction::AsyncFromSyncReject {
            derived,
            sync_iterator,
            ..
        } => {
            mark_value(heap, marks, work, *derived);
            mark_value(heap, marks, work, *sync_iterator);
        }
        PromiseReaction::AsyncDisposeStep {
            stack,
            pending_error,
            capability,
            ..
        } => {
            mark_value(heap, marks, work, *stack);
            if let Some(error) = pending_error {
                mark_value(heap, marks, work, *error);
            }
            mark_value(heap, marks, work, *capability);
        }
        PromiseReaction::DynamicImportFulfill { promise, .. }
        | PromiseReaction::DynamicImportReject { promise, .. } => {
            mark_value(heap, marks, work, *promise);
        }
    }
    if let Some(context) = reaction.context() {
        mark_value(heap, marks, work, context);
    }
}

fn trace_promise_state(
    state: &PromiseState,
    heap: &[HeapEntry],
    marks: &mut [bool],
    work: &mut Vec<usize>,
) {
    match state {
        PromiseState::Pending {
            fulfill_reactions,
            reject_reactions,
        } => {
            for reaction in fulfill_reactions.iter().chain(reject_reactions) {
                trace_promise_reaction(reaction, heap, marks, work);
            }
        }
        PromiseState::Fulfilled { value } => mark_value(heap, marks, work, *value),
        PromiseState::Rejected { reason, .. } => mark_value(heap, marks, work, *reason),
    }
}

fn trace_microtask(
    job: &MicrotaskJob,
    heap: &[HeapEntry],
    marks: &mut [bool],
    work: &mut Vec<usize>,
) {
    match job {
        MicrotaskJob::Reaction {
            reaction, value, ..
        } => {
            trace_promise_reaction(reaction, heap, marks, work);
            mark_value(heap, marks, work, *value);
        }
        MicrotaskJob::Thenable {
            promise,
            thenable,
            then,
            context,
        } => {
            mark_value(heap, marks, work, *promise);
            mark_value(heap, marks, work, *thenable);
            mark_value(heap, marks, work, *then);
            if let Some(context) = context {
                mark_value(heap, marks, work, *context);
            }
        }
        MicrotaskJob::Callback { callback, context } => {
            mark_value(heap, marks, work, *callback);
            if let Some(context) = context {
                mark_value(heap, marks, work, *context);
            }
        }
        MicrotaskJob::FinalizationCleanup { registry, context } => {
            mark_value(heap, marks, work, *registry);
            if let Some(context) = context {
                mark_value(heap, marks, work, *context);
            }
        }
    }
}

fn trace_execution(
    execution: &Execution,
    heap: &[HeapEntry],
    marks: &mut [bool],
    work: &mut Vec<usize>,
) {
    mark_value(heap, marks, work, execution.value);
    mark_value(heap, marks, work, execution.link);
    trace_values(heap, marks, work, &execution.entry_registers);
}

fn trace_runtime_error(
    error: &RuntimeError,
    heap: &[HeapEntry],
    marks: &mut [bool],
    work: &mut Vec<usize>,
) {
    match &error.kind {
        RuntimeErrorKind::UncaughtThrow { value, .. }
        | RuntimeErrorKind::InvalidValue { value } => {
            mark_value(heap, marks, work, *value);
        }
        RuntimeErrorKind::FuelExhausted { .. }
        | RuntimeErrorKind::CallDepthExceeded { .. }
        | RuntimeErrorKind::RegisterLimitExceeded { .. }
        | RuntimeErrorKind::ArgumentLimitExceeded { .. }
        | RuntimeErrorKind::HeapSlotLimitExceeded { .. }
        | RuntimeErrorKind::HeapByteLimitExceeded { .. }
        | RuntimeErrorKind::ModuleCellLimitExceeded { .. }
        | RuntimeErrorKind::DynamicModuleLimitExceeded { .. }
        | RuntimeErrorKind::MicrotaskQueueLimitExceeded { .. }
        | RuntimeErrorKind::MicrotaskDrainReentry
        | RuntimeErrorKind::TimerProviderFailure { .. }
        | RuntimeErrorKind::TimerCapacityExceeded { .. }
        | RuntimeErrorKind::TimerCheckpointReentry
        | RuntimeErrorKind::InvalidDynamicScript { .. }
        | RuntimeErrorKind::TemporalDeadZone { .. }
        | RuntimeErrorKind::ExternalModuleUnavailable { .. }
        | RuntimeErrorKind::DynamicImportEdgeMissing { .. }
        | RuntimeErrorKind::InvalidVerifiedProgram { .. }
        | RuntimeErrorKind::InvalidRuntimeHeapReference { .. }
        | RuntimeErrorKind::ModuleEvaluationStalled { .. }
        | RuntimeErrorKind::RegexpStepBudgetExceeded { .. }
        | RuntimeErrorKind::Cancelled => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn trace_entry(
    entry: &HeapEntry,
    index: usize,
    shapes: &ShapeTable,
    heap: &[HeapEntry],
    marks: &mut [bool],
    work: &mut Vec<usize>,
    weak_collections: &mut Vec<usize>,
) {
    match entry {
        HeapEntry::Rope { left, right, .. } => {
            mark_value(heap, marks, work, *left);
            mark_value(heap, marks, work, *right);
        }
        HeapEntry::Vacant
        | HeapEntry::String(_)
        | HeapEntry::BigInt(_)
        | HeapEntry::ModuleNamespace { .. }
        | HeapEntry::ExternalModuleNamespace { .. }
        | HeapEntry::Symbol { .. }
        | HeapEntry::PrivateName { .. } => {}
        HeapEntry::Proxy { record } => {
            record.for_each_value(|value| mark_value(heap, marks, work, value));
        }
        HeapEntry::ProxyRevoker {
            record, properties, ..
        } => {
            record.for_each_value(|value| mark_value(heap, marks, work, value));
            trace_properties_and_prototype(properties, shapes, None, heap, marks, work);
        }
        HeapEntry::WeakRef { .. } | HeapEntry::FinalizationRegistry { .. } => {
            crate::intrinsics::builtins::weakref_finalization::trace_strong_edges(entry, |value| {
                mark_value(heap, marks, work, value);
            });
        }
        HeapEntry::Object {
            properties,
            prototype,
            boxed_primitive,
            ..
        } => {
            trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work);
            if let Some(value) = boxed_primitive {
                mark_value(heap, marks, work, *value);
            }
        }
        HeapEntry::Array {
            elements,
            properties,
            prototype,
            ..
        } => {
            trace_values(heap, marks, work, elements);
            trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work);
        }
        HeapEntry::Function {
            captures,
            context,
            properties,
            prototype,
            ..
        } => {
            trace_values(heap, marks, work, captures);
            if let Some(value) = context {
                mark_value(heap, marks, work, *value);
            }
            trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work);
        }
        HeapEntry::Script {
            entry,
            properties,
            prototype,
            ..
        } => {
            mark_value(heap, marks, work, *entry);
            trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work);
        }
        HeapEntry::HashState { update, digest, .. } => {
            mark_value(heap, marks, work, *update);
            mark_value(heap, marks, work, *digest);
        }
        HeapEntry::RegExp {
            properties,
            prototype,
            ..
        }
        | HeapEntry::Date {
            properties,
            prototype,
            ..
        }
        | HeapEntry::Temporal {
            properties,
            prototype,
            ..
        }
        | HeapEntry::Timeout {
            properties,
            prototype,
            ..
        }
        | HeapEntry::SharedArrayBuffer {
            properties,
            prototype,
            ..
        } => trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work),
        HeapEntry::Intl {
            bound,
            properties,
            prototype,
            ..
        } => {
            if let Some(bound) = bound {
                mark_value(heap, marks, work, *bound);
            }
            trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work);
        }
        HeapEntry::TypedArray {
            buffer,
            properties,
            prototype,
            ..
        } => {
            mark_value(heap, marks, work, *buffer);
            trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work);
        }
        HeapEntry::DataView {
            buffer,
            properties,
            prototype,
            ..
        } => {
            mark_value(heap, marks, work, *buffer);
            trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work);
        }
        HeapEntry::ArrayBuffer {
            data,
            properties,
            prototype,
            ..
        } => {
            mark_value(heap, marks, work, data.detach_key());
            trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work);
        }
        HeapEntry::Collection {
            kind,
            entries,
            properties,
            prototype,
            ..
        } => {
            trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work);
            match kind {
                CollectionKind::Map | CollectionKind::Set => {
                    for entry in entries.iter().filter(|entry| entry.live) {
                        mark_value(heap, marks, work, entry.key);
                        mark_value(heap, marks, work, entry.value);
                    }
                }
                CollectionKind::WeakMap | CollectionKind::WeakSet => {
                    weak_collections.push(index);
                }
            }
        }
        HeapEntry::BuiltinIterator {
            source,
            properties,
            prototype,
            ..
        } => {
            mark_value(heap, marks, work, *source);
            trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work);
        }
        HeapEntry::Iterator { state } => match state {
            IteratorState::Keys(for_in) => {
                if let Some(current) = for_in.current {
                    mark_value(heap, marks, work, current);
                }
            }
            IteratorState::Protocol { iterator, next } => {
                mark_value(heap, marks, work, *iterator);
                mark_value(heap, marks, work, *next);
            }
        },
        HeapEntry::AsyncFromSync {
            iterator,
            next,
            properties,
            prototype,
            ..
        } => {
            mark_value(heap, marks, work, *iterator);
            mark_value(heap, marks, work, *next);
            trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work);
        }
        HeapEntry::Generator {
            state,
            properties,
            prototype,
            ..
        } => {
            trace_generator_state(state, heap, marks, work);
            trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work);
        }
        HeapEntry::AsyncGenerator {
            state,
            queue,
            properties,
            prototype,
            ..
        } => {
            trace_async_generator_state(state, heap, marks, work);
            for request in queue {
                request
                    .completion
                    .visit_roots(|value| mark_value(heap, marks, work, value));
                mark_value(heap, marks, work, request.capability);
            }
            trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work);
        }
        HeapEntry::DisposableStack {
            state,
            properties,
            prototype,
            ..
        } => {
            state.visit_roots(|value| mark_value(heap, marks, work, value));
            trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work);
        }
        HeapEntry::ProcessEnv { prototype, .. } => {
            if let Some(value) = prototype {
                mark_value(heap, marks, work, *value);
            }
        }
        HeapEntry::Promise {
            state,
            properties,
            prototype,
            ..
        } => {
            trace_promise_state(state, heap, marks, work);
            trace_properties_and_prototype(properties, shapes, *prototype, heap, marks, work);
        }
        HeapEntry::PromiseResolver { promise, .. } => {
            mark_value(heap, marks, work, *promise);
        }
        HeapEntry::PromiseAll {
            resolve,
            reject,
            values,
            ..
        } => {
            mark_value(heap, marks, work, *resolve);
            mark_value(heap, marks, work, *reject);
            trace_values(heap, marks, work, values);
        }
        HeapEntry::PromiseAllElement { aggregate, .. } => {
            mark_value(heap, marks, work, *aggregate);
        }
        HeapEntry::AsyncActivation {
            activation,
            promise,
            completion,
            ..
        } => {
            if let Some(activation) = activation {
                trace_activation(activation, heap, marks, work);
            }
            mark_value(heap, marks, work, *promise);
            if let Some(completion) = completion {
                match completion {
                    Ok(execution) => trace_execution(execution, heap, marks, work),
                    Err(error) => trace_runtime_error(error, heap, marks, work),
                }
            }
        }
        HeapEntry::NativeFunction {
            callable,
            properties,
            prototype,
            ..
        } => {
            match callable {
                NativeCallable::Builtin(_) => {}
                NativeCallable::Bound(bound) => {
                    mark_value(heap, marks, work, bound.target);
                    mark_value(heap, marks, work, bound.this_value);
                    trace_values(heap, marks, work, &bound.arguments);
                }
            }
            trace_property_map(properties, shapes, heap, marks, work);
            if let Some(prototype) = prototype {
                mark_value(heap, marks, work, *prototype);
            }
        }
    }
}
#[cfg(test)]
mod stress_hardening;
