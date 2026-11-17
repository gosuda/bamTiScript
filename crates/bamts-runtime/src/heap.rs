use std::ops::{Index, IndexMut};

use crate::HeapEntry;

/// Every heap entry of one machine.
///
/// Reads go through [`Index`]; every write goes through [`IndexMut`], so one
/// type is the single gate a collector can watch.
#[derive(Default)]
pub(crate) struct Heap {
    entries: Vec<HeapEntry>,
}

impl Heap {
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn push(&mut self, entry: HeapEntry) {
        self.entries.push(entry);
    }

    pub(crate) fn get(&self, index: usize) -> Option<&HeapEntry> {
        self.entries.get(index)
    }

    pub(crate) fn truncate(&mut self, len: usize) {
        self.entries.truncate(len);
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
        &mut self.entries[index]
    }
}
