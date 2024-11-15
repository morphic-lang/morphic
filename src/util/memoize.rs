use std::cell::RefCell;
use std::collections::BTreeMap;

#[derive(Clone, Debug)]
struct Memo<T, U> {
    cache: RefCell<BTreeMap<T, U>>,
}

impl<T: Ord, U: Clone> Memo<T, U> {
    fn new() -> Self {
        Memo {
            cache: RefCell::new(BTreeMap::new()),
        }
    }

    /// Panics if `f` modifies the cache held by `self`.
    fn for_each(&self, mut f: impl FnMut(&T, &U)) {
        for (key, value) in self.cache.borrow().iter() {
            f(key, value);
        }
    }

    fn memoize(&self, key: T, f: impl Fn(&T) -> U) -> U {
        if let Some(value) = self.cache.borrow().get(&key) {
            return value.clone();
        }

        let value = f(&key);
        self.cache.borrow_mut().insert(key, value.clone());
        value
    }
}
