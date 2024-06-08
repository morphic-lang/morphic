use id_collections::{Count, Id};
use num_traits::ToPrimitive;
use std::collections::BTreeMap;
use std::rc::Rc;

/// A context that can be cheaply cloned.
#[derive(Debug)]
pub struct ImmutContext<I: Id, V> {
    count: Count<I>,
    stack: im_rc::Vector<Rc<V>>,
}

impl<I: Id, V> Clone for ImmutContext<I, V> {
    fn clone(&self) -> Self {
        Self {
            count: self.count.clone(),
            stack: self.stack.clone(),
        }
    }
}

impl<I: Id, V> ImmutContext<I, V> {
    pub fn new() -> Self {
        Self {
            count: Count::new(),
            stack: im_rc::Vector::new(),
        }
    }

    pub fn local_binding(&self, local: I) -> &Rc<V> {
        let idx = local.to_index().to_usize().unwrap();
        &self.stack[idx]
    }

    pub fn add_local(&mut self, binding: Rc<V>) -> I {
        let id = self.count.inc();
        self.stack.push_back(binding);
        id
    }

    pub fn update_local(&mut self, local: I, binding: Rc<V>) {
        let idx = local.to_index().to_usize().unwrap();
        self.stack[idx] = binding;
    }

    pub fn truncate(&mut self, count: Count<I>) {
        if count < self.count {
            self.count = count;
            let len = count.to_value().to_usize().unwrap();
            self.stack.truncate(len);
        }
    }
}

#[derive(Clone, Debug)]
pub struct LocalUpdates<I: Id, V> {
    inner: BTreeMap<I, Rc<V>>,
}

impl<I: Id, V> LocalUpdates<I, V> {
    pub fn new() -> Self {
        Self {
            inner: BTreeMap::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn local_binding(&self, local: I) -> Option<&Rc<V>> {
        self.inner.get(&local)
    }

    pub fn record(&mut self, id: I, binding: Rc<V>) {
        self.inner.insert(id, binding);
    }

    pub fn truncate(&mut self, count: Count<I>) {
        // TODO: in practice we only remove the most recently added element; we could optimize this.
        self.inner.retain(|id, _| id.to_index() < count.to_value());
    }

    pub fn merge_with(&mut self, other: &Self, f: impl Fn(&V, &V) -> V) {
        use std::collections::btree_map::Entry;
        for (id, val) in &other.inner {
            match self.inner.entry(*id) {
                Entry::Vacant(entry) => {
                    entry.insert(val.clone());
                }
                Entry::Occupied(mut entry) => {
                    let curr = entry.get_mut();
                    *curr = Rc::new(f(curr, val));
                }
            }
        }
    }
}

/// An context that tracks all updates so that they can be replayed onto another context.
#[derive(Clone, Debug)]
pub struct TrackedContext<I: Id, V> {
    ctx: ImmutContext<I, V>,
    updates: LocalUpdates<I, V>,
}

impl<I: Id, V> TrackedContext<I, V> {
    pub fn new(ctx: &ImmutContext<I, V>) -> Self {
        Self {
            ctx: ctx.clone(),
            updates: LocalUpdates::new(),
        }
    }

    pub fn local_binding(&self, local: I) -> &Rc<V> {
        self.ctx.local_binding(local)
    }

    pub fn add_local(&mut self, binding: Rc<V>) -> I {
        let local = self.ctx.add_local(binding.clone());
        self.updates.record(local, binding);
        local
    }

    pub fn update_local(&mut self, local: I, binding: Rc<V>) {
        self.ctx.update_local(local, binding.clone());
        self.updates.record(local, binding);
    }

    pub fn update_all(&mut self, updates: &LocalUpdates<I, V>) {
        for (id, binding) in &updates.inner {
            self.update_local(*id, binding.clone());
        }
    }

    pub fn truncate(&mut self, count: Count<I>) {
        self.ctx.truncate(count);
        self.updates.truncate(count);
    }

    pub fn as_untracked(&self) -> &ImmutContext<I, V> {
        &self.ctx
    }

    pub fn into_updates(self) -> LocalUpdates<I, V> {
        self.updates
    }
}
