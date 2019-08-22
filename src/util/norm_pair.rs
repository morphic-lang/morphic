/// A normalized unordered pair, where the first component is always <= the second
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct NormPair<T>(T, T);

impl<T: Ord> NormPair<T> {
    fn new(fst: T, snd: T) -> Self {
        if fst <= snd {
            NormPair(fst, snd)
        } else {
            NormPair(snd, fst)
        }
    }

    fn fst(&self) -> &T {
        &self.0
    }

    fn snd(&self) -> &T {
        &self.1
    }

    fn into_fst(self) -> T {
        self.0
    }

    fn into_snd(self) -> T {
        self.1
    }

    fn into_tuple(self) -> (T, T) {
        (self.0, self.1)
    }
}
