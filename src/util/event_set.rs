use im_rc::OrdMap;
use std::cmp::Ordering;

use crate::util::id_gen::IdGen;
use crate::util::id_vec::IdVec;

// Event ids are *reverse-chronological*, in the sense that events with *higher* id values occur
// earlier, and *per-block*, in the sense that ids are unique and sequentially assigned within a
// block, but will in general overlap between blocks.
id_type!(RevEventId);

// Block ids are global per event set
id_type!(pub BlockId);

#[derive(Clone, Debug)]
struct Block {
    event_gen: IdGen<RevEventId>,
    /// `parent` identifies the parent block, and this block's event id *in the parent block*.
    parent: Option<(BlockId, RevEventId)>,
}

#[derive(Clone, Debug)]
enum HorizonInBlock {
    Event(RevEventId),
    Branched(RevEventId, OrdMap<BlockId, HorizonInBlock>),
}

/// A "horizon" is a set of zero or more events, all of which are incomparable.  That is, there must
/// be no two events `a`, `b` in the horizon such that `a` can occur before `b`.  This means that if
/// a horizon contains more than one event, those events must occur along mutually exclusive branch
/// arms.  In mathematics, a subset of a partial order satisfying this property is sometimes called
/// an "antichain".
///
/// Horizons can be used to represent the lifetimes of variables within a control flow graph, where
/// each variable's lifetime ends at exactly one point along each execution path.  They can also be
/// used to represent upper bounds on the "time of last access" of a value in a control flow graph.
/// You can use these together to implement lifetime analysis.
#[derive(Clone, Debug)]
pub struct Horizon(Option<HorizonInBlock>);

#[derive(Clone, Debug)]
pub struct EventSet {
    blocks: IdVec<BlockId, Block>,
}

impl EventSet {
    pub fn new() -> (Self, BlockId) {
        let mut blocks = IdVec::new();
        let root_id = blocks.push(Block {
            event_gen: IdGen::new(),
            parent: None,
        });
        (EventSet { blocks }, root_id)
    }

    pub fn prepend_event(&mut self, block: BlockId) -> Horizon {
        let event_id_in_block = self.blocks[block].event_gen.fresh();

        let mut horizon = HorizonInBlock::Event(event_id_in_block);
        let mut curr_block = block;
        while let Some((parent_block, curr_block_id_in_parent)) = self.blocks[curr_block].parent {
            horizon = HorizonInBlock::Branched(
                curr_block_id_in_parent,
                OrdMap::unit(curr_block, horizon),
            );
            curr_block = parent_block;
        }

        Horizon(Some(horizon))
    }

    pub fn prepend_branch(&mut self, block: BlockId, num_arms: usize) -> Vec<BlockId> {
        let branch_id_in_block = self.blocks[block].event_gen.fresh();
        (0..num_arms)
            .map(|_| {
                self.blocks.push(Block {
                    event_gen: IdGen::new(),
                    parent: Some((block, branch_id_in_block)),
                })
            })
            .collect()
    }
}

impl HorizonInBlock {
    fn event_id(&self) -> RevEventId {
        match self {
            HorizonInBlock::Event(event_id) => *event_id,
            HorizonInBlock::Branched(event_id, _) => *event_id,
        }
    }

    fn disjoint_union(&mut self, other: &HorizonInBlock) {
        match (self, other) {
            (HorizonInBlock::Event(_), HorizonInBlock::Event(_)) => {
                panic!(
                    "Cannot take the disjoint union of two horizons with events in the same block."
                );
            }
            (HorizonInBlock::Branched(event1, arms1), HorizonInBlock::Branched(event2, arms2)) => {
                if event1 != event2 {
                    panic!(
                        "Cannot take the disjoint union of two horizons in distinct sequential \
                         branches (that is, two branches for which one always occurs after the \
                         other)",
                    );
                }
                for (block2, sub_horizon) in arms2 {
                    arms1
                        .entry(*block2)
                        .and_modify(|entry| entry.merge_latest(sub_horizon))
                        .or_insert_with(|| sub_horizon.clone());
                }
            }
            _ => panic!("Cannot take the disjoint union of two sequentially ordered horizons"),
        }
    }

    fn merge_latest(&mut self, other: &HorizonInBlock) {
        // Careful!  The ordering of event ids is *reverse* chronological order!
        match self.event_id().cmp(&other.event_id()) {
            Ordering::Less => {
                // `self` occurs after `other`; do nothing
            }
            Ordering::Greater => {
                // `self` occurs before `other`
                *self = other.clone();
            }
            Ordering::Equal => match (self, other) {
                (HorizonInBlock::Event(_), HorizonInBlock::Event(_)) => {}
                (HorizonInBlock::Branched(_, arms1), HorizonInBlock::Branched(_, arms2)) => {
                    for (block2, sub_horizon) in arms2 {
                        arms1
                            .entry(*block2)
                            .and_modify(|entry| entry.merge_latest(sub_horizon))
                            .or_insert_with(|| sub_horizon.clone());
                    }
                }
                _ => unreachable!(),
            },
        }
    }

    fn can_occur_before(&self, other: &HorizonInBlock) -> bool {
        // Careful!  The ordering of event ids is *reverse* chronological order!
        match self.event_id().cmp(&other.event_id()) {
            Ordering::Less => {
                // `self` occurs strictly after `other`
                false
            }
            Ordering::Greater => {
                // `self` occurs strictly before `other`
                true
            }
            Ordering::Equal => match (self, other) {
                // The "occurs before" relation is reflexive
                (HorizonInBlock::Event(_), HorizonInBlock::Event(_)) => true,
                (HorizonInBlock::Branched(_, arms1), HorizonInBlock::Branched(_, arms2)) => {
                    arms1.iter().any(|(block1, sub_horizon1)| {
                        arms2
                            .get(block1)
                            .map(|sub_horizon2| sub_horizon1.can_occur_before(sub_horizon2))
                            .unwrap_or(false)
                    })
                }
                _ => unreachable!(),
            },
        }
    }
}

impl Horizon {
    pub fn new() -> Self {
        Horizon(None)
    }

    /// Merge two disjoint horizons.
    ///
    /// This function will panic if there exist events `a` in `self` and `b` in `other` such that
    /// `a` and `b` are comparable.
    pub fn disjoint_union(&mut self, other: &Horizon) {
        // TODO: Should we consolidate this option merging logic somewhere?  It's repeated in
        // `merge_latest`, among other places.
        match (&mut *self, other) {
            (Horizon(Some(horizon1)), Horizon(Some(horizon2))) => {
                horizon1.disjoint_union(horizon2);
            }
            (_, Horizon(None)) => {}
            (Horizon(None), _) => {
                *self = other.clone();
            }
        }
    }

    /// Merge two horizons two produce their least upper bound -- in other words, the earliest and
    /// smallest horizon that occurs after (or at the same time as) every event in each horizon.
    ///
    /// This function should never fail.
    pub fn merge_latest(&mut self, other: &Horizon) {
        match (&mut *self, other) {
            (Horizon(Some(horizon1)), Horizon(Some(horizon2))) => {
                horizon1.merge_latest(horizon2);
            }
            (_, Horizon(None)) => {}
            (Horizon(None), _) => {
                *self = other.clone();
            }
        }
    }

    /// Determine if any event in `self` can occur before any event in `other`.
    ///
    /// The "occurs before" relation on events is reflexive.
    pub fn can_occur_before(&self, other: &Horizon) -> bool {
        match (self, other) {
            (Horizon(Some(horizon1)), Horizon(Some(horizon2))) => {
                horizon1.can_occur_before(horizon2)
            }
            _ => false,
        }
    }
}
