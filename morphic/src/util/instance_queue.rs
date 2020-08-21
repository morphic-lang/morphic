// TODO: Should this be changed to HashSet?
use std::collections::BTreeMap;
use std::collections::VecDeque;

use crate::util::id_type::Id;

#[derive(Clone, Debug)]
pub struct InstanceQueue<Inst, MonoId> {
    ids: BTreeMap<Inst, MonoId>,
    pending: VecDeque<(MonoId, Inst)>,
}

impl<Inst: Ord + Clone, MonoId: Id> InstanceQueue<Inst, MonoId> {
    pub fn new() -> Self {
        InstanceQueue {
            ids: BTreeMap::new(),
            pending: VecDeque::new(),
        }
    }

    pub fn resolve(&mut self, inst: Inst) -> MonoId {
        let new_id_if_needed = MonoId::from_index(self.ids.len());
        let pending = &mut self.pending; // Appease the borrow checker
        self.ids
            .entry(inst.clone())
            .or_insert_with(|| {
                pending.push_back((new_id_if_needed.clone(), inst));
                new_id_if_needed
            })
            .clone()
    }

    pub fn pop_pending(&mut self) -> Option<(MonoId, Inst)> {
        self.pending.pop_front()
    }
}
