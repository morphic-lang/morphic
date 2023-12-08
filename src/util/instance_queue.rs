use crate::util::id_gen::IdGen;
use id_collections::Id;
use std::collections::BTreeMap; // TODO: Should this be changed to HashSet?
use std::collections::VecDeque;

#[derive(Clone, Debug)]
pub struct InstanceQueue<Inst, MonoId: Id> {
    id_gen: IdGen<MonoId>,
    ids: BTreeMap<Inst, MonoId>,
    pending: VecDeque<(MonoId, Inst)>,
}

impl<Inst: Ord + Clone, MonoId: Id> InstanceQueue<Inst, MonoId> {
    pub fn new() -> Self {
        InstanceQueue {
            id_gen: IdGen::new(),
            ids: BTreeMap::new(),
            pending: VecDeque::new(),
        }
    }

    pub fn resolve(&mut self, inst: Inst) -> MonoId {
        let pending = &mut self.pending; // Appease the borrow checker
        self.ids
            .entry(inst.clone())
            .or_insert_with(|| {
                let new_id = self.id_gen.fresh();
                pending.push_back((new_id, inst));
                new_id
            })
            .clone()
    }

    pub fn pop_pending(&mut self) -> Option<(MonoId, Inst)> {
        self.pending.pop_front()
    }
}
