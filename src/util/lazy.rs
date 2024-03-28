// `once_cell::unsync::Lazy` is invariant in its function parameter:
// https://github.com/matklad/once_cell/issues/167
//
// This implementation of `Lazy` (due to "danielhenrymantilla", see the issue linked above) is
// covariant in its function parameter at the cost of having a custom drop. That is, `'a` is not
// allowed to dangle where `Lazy<&'a T>` is dropped.

use std::cell::{Cell, OnceCell};
use std::mem::ManuallyDrop;
use std::panic::RefUnwindSafe;
use std::rc::Rc;
use std::{fmt, ops};

struct CovariantCellOption<F> {
    /// Invariant: if this is `true` then `value` must contain a non-dropped `F`
    is_some: Cell<bool>,
    value: ManuallyDrop<F>,
}

impl<F> CovariantCellOption<F> {
    const fn some(value: F) -> Self {
        Self {
            is_some: Cell::new(true),
            value: ManuallyDrop::new(value),
        }
    }

    fn into_inner(self) -> Option<F> {
        // Small optimization: disable drop glue so as not to have to overwrite `is_some`.
        let mut this = ManuallyDrop::new(self);
        let is_some = this.is_some.get_mut();
        is_some.then(|| unsafe {
            // SAFETY: as per the invariant, we can use `value`. We can also
            // *consume* it by doing `*is_some = false`, but we actually don't
            // even need to do it since we don't use `this` anymore.
            ManuallyDrop::take(&mut this.value)
        })
    }

    fn take(&self) -> Option<F> {
        self.is_some.get().then(|| unsafe {
            // SAFETY: as per the invariant, we can use `value`. Clearing the `is_some` flag also
            // lets us *consume* it.
            self.is_some.set(false);
            // `ManuallyDrop::take_by_ref`, morally.
            <*const F>::read(&*self.value)
        })
    }
}

impl<F> Drop for CovariantCellOption<F> {
    fn drop(&mut self) {
        if *self.is_some.get_mut() {
            unsafe {
                // SAFETY: as per the invariant, we can use `value`.
                ManuallyDrop::drop(&mut self.value)
            }
        }
    }
}

pub struct Lazy<T, F = fn() -> T> {
    cell: OnceCell<T>,
    init: CovariantCellOption<F>,
}

impl<T, F: RefUnwindSafe> RefUnwindSafe for Lazy<T, F> where OnceCell<T>: RefUnwindSafe {}

impl<T: fmt::Debug, F> fmt::Debug for Lazy<T, F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Lazy")
            .field("cell", &self.cell)
            .field("init", &"..")
            .finish()
    }
}

impl<T, F> Lazy<T, F> {
    pub const fn new(init: F) -> Lazy<T, F> {
        Lazy {
            cell: OnceCell::new(),
            init: CovariantCellOption::some(init),
        }
    }

    pub fn into_value(this: Lazy<T, F>) -> Result<T, F> {
        let cell = this.cell;
        let init = this.init;
        cell.into_inner().ok_or_else(|| {
            init.take()
                .unwrap_or_else(|| panic!("Lazy instance has previously been poisoned"))
        })
    }
}

impl<T, F: FnOnce() -> T> Lazy<T, F> {
    pub fn force(this: &Lazy<T, F>) -> &T {
        this.cell.get_or_init(|| match this.init.take() {
            Some(f) => f(),
            None => panic!("Lazy instance has previously been poisoned"),
        })
    }

    pub fn force_mut(this: &mut Lazy<T, F>) -> &mut T {
        Self::force(this);
        Self::get_mut(this).unwrap_or_else(|| unreachable!())
    }

    pub fn get(this: &Lazy<T, F>) -> Option<&T> {
        this.cell.get()
    }

    pub fn get_mut(this: &mut Lazy<T, F>) -> Option<&mut T> {
        this.cell.get_mut()
    }
}

impl<T, F: FnOnce() -> T> ops::Deref for Lazy<T, F> {
    type Target = T;
    fn deref(&self) -> &T {
        Lazy::force(self)
    }
}

impl<T, F: FnOnce() -> T> ops::DerefMut for Lazy<T, F> {
    fn deref_mut(&mut self) -> &mut T {
        Lazy::force(self);
        self.cell.get_mut().unwrap_or_else(|| unreachable!())
    }
}

impl<T: Default> Default for Lazy<T> {
    fn default() -> Lazy<T> {
        Lazy::new(T::default)
    }
}

pub type DynLazy<'a, T> = Rc<Lazy<T, Box<dyn FnOnce() -> T + 'a>>>;

pub fn lazy<'a, T>(f: impl FnOnce() -> T + 'a) -> DynLazy<'a, T> {
    Rc::new(Lazy::new(Box::new(f)))
}
