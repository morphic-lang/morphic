use hashbrown::hash_map::RawEntryMut;
use hashbrown::HashMap;
use rustc_hash::FxHasher;
use std::cell::RefCell;
use std::fmt;
use std::hash::{BuildHasher, BuildHasherDefault, Hash, Hasher};
use std::ops::Deref;
use std::rc::Rc;

pub trait Internable: Hash + Eq {}
impl<T: Hash + Eq> Internable for T {}

#[derive(Clone, PartialOrd, Ord)]
pub struct Interned<T> {
    data: Rc<T>,
    // Often, we build deep, recursive data structures out of interned objects, in which case it's
    // nice to avoid rehashing substructures.
    hash: u64,
}

impl<T> Deref for Interned<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &*self.data
    }
}

impl<T> Hash for Interned<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash.hash(state);
    }
}

impl<T: PartialEq> PartialEq for Interned<T> {
    fn eq(&self, other: &Self) -> bool {
        // Note that `Rc::eq` tries `Rc::ptr_eq` before performing a deep comparison.
        self.data == other.data
    }
}

impl<T: Eq> Eq for Interned<T> {}

impl<T: fmt::Debug> fmt::Debug for Interned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.data.fmt(f)
    }
}

pub struct Interner<T> {
    store: RefCell<HashMap<Rc<T>, (), BuildHasherDefault<FxHasher>>>,
}

impl<T: Internable> Interner<T> {
    pub fn empty() -> Self {
        Interner {
            store: RefCell::new(HashMap::default()),
        }
    }

    pub fn gc(&self) {
        self.store
            .borrow_mut()
            .retain(|rc, _| Rc::strong_count(rc) > 1);
    }

    pub fn new(&self, obj: T) -> Interned<T> {
        let mut store = self.store.borrow_mut();
        let hash = {
            let mut hasher = BuildHasher::build_hasher(store.hasher());
            obj.hash(&mut hasher);
            hasher.finish()
        };
        match store.raw_entry_mut().from_key_hashed_nocheck(hash, &obj) {
            RawEntryMut::Occupied(occ) => Interned {
                data: occ.key().clone(),
                hash,
            },
            RawEntryMut::Vacant(vac) => Interned {
                data: vac.insert_hashed_nocheck(hash, Rc::new(obj), ()).0.clone(),
                hash,
            },
        }
    }
}
