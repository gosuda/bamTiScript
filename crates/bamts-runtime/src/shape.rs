use std::cell::OnceCell;
use std::collections::HashMap;
use std::num::NonZeroU32;

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

    pub(crate) fn unordered_entries(
        &self,
        id: ShapeId,
    ) -> impl Iterator<Item = (&PropertyKey, u32)> {
        let mut current = id;
        std::iter::from_fn(move || {
            let shape = &self.0[current.index()];
            current = shape.parent?;
            Some((&shape.key, shape.slot))
        })
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
/// The property operation that owns a cache site.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Which {
    Get,
    Set,
}
/// One inline cache site for named property get or set.
#[derive(Clone, Debug)]
pub(crate) struct PropertySite {
    which: Which,
    entries: [(ShapeId, PropertyKey, u32); 4],
    pub(crate) len: u8,
}
impl PropertySite {
    const fn new(which: Which) -> Self {
        Self {
            which,
            entries: [
                (ShapeId::ROOT, PropertyKey::Private(u32::MAX), 0),
                (ShapeId::ROOT, PropertyKey::Private(u32::MAX), 0),
                (ShapeId::ROOT, PropertyKey::Private(u32::MAX), 0),
                (ShapeId::ROOT, PropertyKey::Private(u32::MAX), 0),
            ],
            len: 0,
        }
    }
    pub(crate) fn slot(&self, shape: ShapeId, key: &PropertyKey) -> Option<u32> {
        self.entries[..usize::from(self.len)]
            .iter()
            .find_map(|(cached_shape, cached_key, slot)| {
                (*cached_shape == shape && cached_key == key).then_some(*slot)
            })
    }
    pub(crate) fn record(&mut self, shape: ShapeId, key: PropertyKey, slot: u32) {
        if usize::from(self.len) < self.entries.len() {
            self.entries[usize::from(self.len)] = (shape, key, slot);
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
    by_pc: Box<[Option<NonZeroU32>]>,
    pub(crate) sites: Box<[PropertySite]>,
}
impl FunctionSites {
    pub(crate) fn build(code: &[Instruction]) -> Self {
        let mut by_pc = vec![None; code.len()];
        let mut sites = Vec::new();
        for (pc, instruction) in code.iter().enumerate() {
            let which = match instruction {
                Instruction::GetProperty { .. } => Which::Get,
                Instruction::SetProperty { .. } => Which::Set,
                _ => continue,
            };
            let index = NonZeroU32::new(
                u32::try_from(sites.len() + 1).expect("property site count fits u32"),
            )
            .expect("one-based site index is nonzero");
            by_pc[pc] = Some(index);
            sites.push(PropertySite::new(which));
        }
        Self {
            by_pc: by_pc.into_boxed_slice(),
            sites: sites.into_boxed_slice(),
        }
    }

    pub(crate) fn site_index(&self, pc: usize, which: Which) -> Option<usize> {
        let index = self.by_pc.get(pc).copied().flatten()?.get() as usize - 1;
        let site = &self.sites[index];
        (site.which == which && site.usable()).then_some(index)
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

    #[test]
    fn compact_sites_preserve_instruction_pcs_and_kinds() {
        let register = bamts_bytecode::Register::new(0);
        let code = [
            Instruction::Halt,
            Instruction::GetProperty {
                dst: register,
                object: register,
                key: register,
            },
            Instruction::Halt,
            Instruction::SetProperty {
                object: register,
                key: register,
                value: register,
            },
            Instruction::Halt,
        ];
        let mut sites = FunctionSites::build(&code);
        assert_eq!(sites.sites.len(), 2);
        assert_eq!(sites.site_index(0, Which::Get), None);
        assert_eq!(sites.site_index(1, Which::Get), Some(0));
        assert_eq!(sites.site_index(1, Which::Set), None);
        assert_eq!(sites.site_index(2, Which::Set), None);
        assert_eq!(sites.site_index(3, Which::Set), Some(1));
        assert_eq!(sites.site_index(3, Which::Get), None);
        assert_eq!(sites.site_index(4, Which::Get), None);
        assert_eq!(sites.site_index(5, Which::Get), None);
        sites.sites[0].len = u8::MAX;
        assert_eq!(sites.site_index(1, Which::Get), None);
        assert_eq!(sites.site_index(3, Which::Set), Some(1));
    }
}
