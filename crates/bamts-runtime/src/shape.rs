use std::cell::OnceCell;
use std::collections::HashMap;

use bamts_bytecode::Instruction;

use crate::PropertyKey;

pub(crate) const SHAPED_CAPACITY: usize = 64;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ShapeId(u32);

impl ShapeId {
    pub(crate) const ROOT: ShapeId = ShapeId(0);

    fn index(self) -> usize {
        self.0 as usize
    }
}

pub(crate) struct Shape {
    parent: Option<ShapeId>,
    key: PropertyKey,
    slot: u32,
    transitions: Vec<(PropertyKey, ShapeId)>,
    table: OnceCell<HashMap<PropertyKey, u32>>,
}

pub(crate) struct ShapeTable(Vec<Shape>);

impl ShapeTable {
    pub(crate) fn new() -> Self {
        Self(vec![Shape {
            parent: None,
            key: PropertyKey::Private(u32::MAX),
            slot: 0,
            transitions: Vec::new(),
            table: OnceCell::new(),
        }])
    }

    pub(crate) fn slot_count(&self, id: ShapeId) -> u32 {
        if id == ShapeId::ROOT {
            0
        } else {
            self.0[id.index()].slot + 1
        }
    }

    pub(crate) fn transition(&mut self, from: ShapeId, key: &PropertyKey) -> ShapeId {
        if let Some((_, id)) = self.0[from.index()]
            .transitions
            .iter()
            .find(|(candidate, _)| candidate == key)
        {
            return *id;
        }
        let slot = if from == ShapeId::ROOT {
            0
        } else {
            self.0[from.index()].slot + 1
        };
        let id = ShapeId(u32::try_from(self.0.len()).expect("shape count fits u32"));
        self.0[from.index()].transitions.push((key.clone(), id));
        self.0.push(Shape {
            parent: Some(from),
            key: key.clone(),
            slot,
            transitions: Vec::new(),
            table: OnceCell::new(),
        });
        id
    }

    pub(crate) fn slot_of(&self, id: ShapeId, key: &PropertyKey) -> Option<u32> {
        self.0[id.index()]
            .table
            .get_or_init(|| self.build_table(id))
            .get(key)
            .copied()
    }

    pub(crate) fn ordered_keys(&self, id: ShapeId) -> Vec<&PropertyKey> {
        let mut keys = Vec::new();
        let mut current = Some(id);
        while let Some(shape_id) = current {
            let shape = &self.0[shape_id.index()];
            if shape.parent.is_some() {
                keys.push(&shape.key);
            }
            current = shape.parent;
        }
        keys.reverse();
        keys
    }

    pub(crate) fn live_keys(&self) -> impl Iterator<Item = &PropertyKey> {
        self.0
            .iter()
            .filter(|shape| shape.parent.is_some())
            .map(|shape| &shape.key)
    }

    fn build_table(&self, id: ShapeId) -> HashMap<PropertyKey, u32> {
        let mut table = HashMap::new();
        let mut current = Some(id);
        while let Some(shape_id) = current {
            let shape = &self.0[shape_id.index()];
            if shape.parent.is_some() {
                table.insert(shape.key.clone(), shape.slot);
            }
            current = shape.parent;
        }
        table
    }
}
/// Which cache table a site index addresses.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Which {
    Get,
    Set,
}
/// One inline cache site for named property get or set.
#[derive(Clone, Debug)]
pub(crate) struct PropertySite {
    pub(crate) entries: [(ShapeId, PropertyKey); 4],
    pub(crate) len: u8,
}
impl PropertySite {
    const fn new() -> Self {
        Self {
            entries: [
                (ShapeId::ROOT, PropertyKey::Private(u32::MAX)),
                (ShapeId::ROOT, PropertyKey::Private(u32::MAX)),
                (ShapeId::ROOT, PropertyKey::Private(u32::MAX)),
                (ShapeId::ROOT, PropertyKey::Private(u32::MAX)),
            ],
            len: 0,
        }
    }
    pub(crate) fn matches(&self, shape: ShapeId, key: &PropertyKey) -> bool {
        self.entries[..usize::from(self.len)]
            .iter()
            .any(|(cached_shape, cached_key)| *cached_shape == shape && cached_key == key)
    }
    pub(crate) fn record(&mut self, shape: ShapeId, key: PropertyKey) {
        if usize::from(self.len) < self.entries.len() {
            self.entries[usize::from(self.len)] = (shape, key);
            self.len += 1;
        } else {
            self.len = u8::MAX;
        }
    }
    pub(crate) fn usable(&self) -> bool {
        self.len != u8::MAX
    }
}
/// Per-function inline cache sites: one entry per get or set instruction.
#[derive(Debug, Default)]
pub(crate) struct FunctionSites {
    pub(crate) gets: Vec<PropertySite>,
    pub(crate) sets: Vec<PropertySite>,
}
impl FunctionSites {
    pub(crate) fn build(code: &[Instruction]) -> Self {
        Self {
            gets: (0..code.len())
                .map(|pc| match code[pc] {
                    Instruction::GetProperty { .. } => PropertySite::new(),
                    _ => PropertySite {
                        len: u8::MAX,
                        ..PropertySite::new()
                    },
                })
                .collect(),
            sets: (0..code.len())
                .map(|pc| match code[pc] {
                    Instruction::SetProperty { .. } => PropertySite::new(),
                    _ => PropertySite {
                        len: u8::MAX,
                        ..PropertySite::new()
                    },
                })
                .collect(),
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn slot_count_tracks_shape_depth() {
        let mut shapes = ShapeTable::new();
        assert_eq!(shapes.slot_count(ShapeId::ROOT), 0);
        let child = shapes.transition(ShapeId::ROOT, &PropertyKey::Private(0));
        assert_eq!(shapes.slot_count(child), 1);
        let grandchild = shapes.transition(child, &PropertyKey::Private(1));
        assert_eq!(shapes.slot_count(grandchild), 2);
    }
}
