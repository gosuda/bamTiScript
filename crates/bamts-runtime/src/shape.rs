use std::cell::OnceCell;
use std::collections::HashMap;

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
        self.0[id.index()].slot + 1
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
