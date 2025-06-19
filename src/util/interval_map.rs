use std::cmp::Ordering;

pub struct IntervalMap<K, V> {
    intervals: Vec<(K, K, V)>,
}

impl<K: Ord, V> IntervalMap<K, V> {
    /// For all I, J either I must be disjoint from J or one must be contained in the other.
    pub fn new(mut intervals: Vec<(K, K, V)>) -> Option<Self> {
        intervals.sort_by(|(lo1, hi1, _), (lo2, hi2, _)| lo1.cmp(lo2).then(hi1.cmp(hi2)));

        for i in 1..intervals.len() {
            let (prev_lo, prev_hi, _) = &intervals[i - 1];
            let (curr_lo, curr_hi, _) = &intervals[i];

            let disjoint = prev_hi.cmp(curr_lo).is_le();
            let curr_contains_prev = curr_lo.cmp(prev_lo).is_le() && curr_hi.cmp(prev_hi).is_ge();

            if !(disjoint || curr_contains_prev) {
                return None;
            }
        }

        Some(Self { intervals })
    }

    pub fn lookup(&self, key: &K) -> Option<&V> {
        let idx = self
            .intervals
            .binary_search_by(|(lo, hi, _)| match lo.cmp(key) {
                Ordering::Greater => Ordering::Greater,
                _ => match hi.cmp(key) {
                    Ordering::Less => Ordering::Less,
                    _ => Ordering::Equal,
                },
            });

        let Ok(mut idx) = idx else {
            return None;
        };

        while idx < self.intervals.len() && self.intervals[idx].0.cmp(key).is_le() {
            idx += 1;
        }

        Some(&self.intervals[idx - 1].2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_invalid_input() {
        let map = IntervalMap::new(vec![(0, 100, "a"), (50, 150, "b")]);
        assert!(map.is_none());

        let map = IntervalMap::new(vec![(0, 100, "a"), (0, 200, "b"), (50, 150, "c")]);
        assert!(map.is_none());
    }

    #[test]
    fn test_lookup() {
        let _ = IntervalMap::<u32, &str>::new(vec![]).unwrap();

        let map = IntervalMap::new(vec![
            (100, 200, "a"),
            (100, 125, "b"),
            (100, 150, "c"),
            (100, 110, "d"),
            (200, 300, "e"),
            (150, 200, "f"),
        ])
        .unwrap();
        assert_eq!(map.lookup(&100), Some(&"d"));
        assert_eq!(map.lookup(&115), Some(&"b"));
        assert_eq!(map.lookup(&125), Some(&"c"));
        assert_eq!(map.lookup(&155), Some(&"f"));
        assert_eq!(map.lookup(&205), Some(&"e"));
        assert_eq!(map.lookup(&305), None);

        let map = IntervalMap::new(vec![(0, 100, "a"), (200, 300, "b")]).unwrap();
        assert_eq!(map.lookup(&150), None);
    }
}
