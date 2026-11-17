use std::ops::{Index, IndexMut};

use crate::HeapEntry;

/// Every heap entry of one machine, with the bookkeeping a generational
/// collector needs.
///
/// A slot is old once a collection has kept it. Reads go through [`Index`];
/// every write goes through [`IndexMut`], which records an old slot as
/// remembered the first time it is borrowed mutably after a collection. A
/// minor collection then traces the young slots and the remembered old
/// slots, and nothing else. A mutable borrow that stores nothing still
/// records the slot, which only costs the collector an extra visit.
#[derive(Default)]
pub(crate) struct Heap {
    entries: Vec<HeapEntry>,
    old: Vec<bool>,
    dirty: Vec<bool>,
    remembered: Vec<usize>,
    young_only_trace: bool,
}

impl Heap {
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn push(&mut self, entry: HeapEntry) {
        self.entries.push(entry);
        self.old.push(false);
        self.dirty.push(false);
    }

    pub(crate) fn get(&self, index: usize) -> Option<&HeapEntry> {
        self.entries.get(index)
    }

    /// Drops every slot at or above `len`, as a rolled-back structured clone does.
    pub(crate) fn truncate(&mut self, len: usize) {
        self.entries.truncate(len);
        self.old.truncate(len);
        self.dirty.truncate(len);
        self.remembered.retain(|&index| index < len);
    }

    /// Puts a new entry into a slot a collection vacated. The slot is young.
    pub(crate) fn fill_vacant(&mut self, index: usize, entry: HeapEntry) {
        debug_assert!(matches!(self.entries[index], HeapEntry::Vacant));
        debug_assert!(!self.old[index] && !self.dirty[index]);
        self.entries[index] = entry;
    }

    /// Empties a slot and makes it young again, so the next entry in it is
    /// traced like any other new entry.
    pub(crate) fn vacate(&mut self, index: usize) {
        self.entries[index] = HeapEntry::Vacant;
        self.old[index] = false;
        self.dirty[index] = false;
    }

    pub(crate) fn mark_old(&mut self, index: usize) {
        self.old[index] = true;
    }

    pub(crate) fn mark_old_prefix(&mut self, len: usize) {
        self.old[..len].fill(true);
    }

    #[cfg(test)]
    pub(crate) fn is_old(&self, index: usize) -> bool {
        self.old[index]
    }

    /// Hands the remembered old slots to the collector and starts a new list.
    pub(crate) fn take_remembered(&mut self) -> Vec<usize> {
        let remembered = std::mem::take(&mut self.remembered);
        for &index in &remembered {
            if let Some(dirty) = self.dirty.get_mut(index) {
                *dirty = false;
            }
        }
        remembered
    }

    /// After a major collection every live slot is old and none holds a young
    /// reference, so nothing needs remembering.
    pub(crate) fn forget_remembered(&mut self) {
        self.take_remembered();
    }

    #[cfg(test)]
    pub(crate) fn is_remembered(&self, index: usize) -> bool {
        self.dirty[index]
    }

    /// While set, marking leaves old slots alone: a minor collection trusts
    /// that every old slot holding a young reference is remembered.
    pub(crate) fn set_young_only_trace(&mut self, young_only: bool) {
        self.young_only_trace = young_only;
    }

    pub(crate) fn skips_marking(&self, index: usize) -> bool {
        self.young_only_trace && self.old[index]
    }
}

impl Index<usize> for Heap {
    type Output = HeapEntry;

    fn index(&self, index: usize) -> &HeapEntry {
        &self.entries[index]
    }
}

impl IndexMut<usize> for Heap {
    fn index_mut(&mut self, index: usize) -> &mut HeapEntry {
        if self.old[index] && !self.dirty[index] {
            self.dirty[index] = true;
            self.remembered.push(index);
        }
        &mut self.entries[index]
    }
}

#[cfg(test)]
mod tests {
    use bamts_bytecode::EcmaString;

    use super::*;

    fn text(value: &str) -> HeapEntry {
        HeapEntry::String(EcmaString::encode(value))
    }

    fn heap_of(len: usize) -> Heap {
        let mut heap = Heap::default();
        for _ in 0..len {
            heap.push(text("x"));
        }
        heap
    }

    #[test]
    fn a_write_to_an_old_slot_is_remembered_once() {
        let mut heap = heap_of(3);
        heap.mark_old(1);
        heap[1] = text("y");
        heap[1] = text("z");
        assert_eq!(heap.take_remembered(), vec![1]);
    }

    #[test]
    fn reads_and_writes_to_young_slots_are_not_remembered() {
        let mut heap = heap_of(3);
        heap.mark_old(0);
        assert!(matches!(heap[0], HeapEntry::String(_)));
        heap[2] = text("y");
        assert!(heap.take_remembered().is_empty());
    }

    #[test]
    fn a_slot_is_remembered_again_after_the_collector_takes_the_list() {
        let mut heap = heap_of(2);
        heap.mark_old(0);
        heap[0] = text("y");
        assert_eq!(heap.take_remembered(), vec![0]);
        assert!(!heap.is_remembered(0));
        heap[0] = text("z");
        assert_eq!(heap.take_remembered(), vec![0]);
    }

    #[test]
    fn a_vacated_slot_is_young_again() {
        let mut heap = heap_of(2);
        heap.mark_old(1);
        heap[1] = text("y");
        heap.vacate(1);
        assert!(!heap.is_old(1));
        assert!(!heap.is_remembered(1));
        heap.take_remembered();
        heap.fill_vacant(1, text("fresh"));
        heap[1] = text("again");
        assert!(heap.take_remembered().is_empty());
    }

    #[test]
    fn truncating_forgets_the_slots_it_drops() {
        let mut heap = heap_of(3);
        heap.mark_old(1);
        heap.mark_old(2);
        heap[1] = text("y");
        heap[2] = text("z");
        heap.truncate(2);
        assert_eq!(heap.len(), 2);
        assert_eq!(heap.take_remembered(), vec![1]);
    }

    #[test]
    fn marking_skips_old_slots_only_while_tracing_young() {
        let mut heap = heap_of(2);
        heap.mark_old(0);
        assert!(!heap.skips_marking(0));
        heap.set_young_only_trace(true);
        assert!(heap.skips_marking(0));
        assert!(!heap.skips_marking(1));
    }
}
