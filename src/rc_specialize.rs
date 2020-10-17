use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::rc::Rc;

use crate::data::alias_specialized_ast as spec;
use crate::data::fate_annot_ast as fate;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mode_annot_ast as mode;
use crate::data::rc_specialized_ast as rc;
use crate::util::id_gen::IdGen;
use crate::util::id_vec::IdVec;
use crate::util::inequality_graph as ineq;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ReleasePaths {
    release_paths: BTreeSet<mode::StackPath>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RetainPaths {
    retain_paths: BTreeSet<mode::StackPath>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ConcreteRcOps {
    release_prologues: IdVec<fate::ExprId, Vec<(flat::LocalId, ReleasePaths)>>,
    occur_retains: IdVec<fate::OccurId, RetainPaths>,
    let_release_epilogues: IdVec<fate::LetBlockId, Vec<(flat::LocalId, ReleasePaths)>>,
    branch_release_epilogues: IdVec<fate::BranchBlockId, Vec<(flat::LocalId, ReleasePaths)>>,
    arg_release_epilogue: ReleasePaths,
}

fn get_mode(
    modes: &IdVec<ineq::ExternalVarId, mode::Mode>,
    bound: &ineq::UpperBound<mode::Mode>,
) -> mode::Mode {
    // TODO: Should we make this short-circuiting?
    bound
        .lte_vars
        .iter()
        .map(|var| modes[var])
        .min()
        .unwrap_or(bound.lte_const)
}

fn concretize_drop_modes(
    modes: &IdVec<ineq::ExternalVarId, mode::Mode>,
    drops: &mode::DropModes,
) -> ReleasePaths {
    ReleasePaths {
        release_paths: drops
            .dropped_paths
            .iter()
            .filter_map(|(path, bound)| match get_mode(modes, bound) {
                mode::Mode::Owned => Some(path.clone()),
                mode::Mode::Borrowed => None,
            })
            .collect(),
    }
}

fn concretize_drops(
    modes: &IdVec<ineq::ExternalVarId, mode::Mode>,
    drops: &Vec<(flat::LocalId, mode::DropModes)>,
) -> Vec<(flat::LocalId, ReleasePaths)> {
    drops
        .iter()
        .map(|(local, dropped_paths)| (*local, concretize_drop_modes(modes, dropped_paths)))
        .collect()
}

fn concretize_occurs(
    modes: &IdVec<ineq::ExternalVarId, mode::Mode>,
    occur: &mode::OccurModes,
) -> RetainPaths {
    RetainPaths {
        retain_paths: occur
            .path_modes
            .iter()
            .filter_map(|(path, path_mode)| match path_mode {
                mode::PathOccurMode::Intermediate {
                    src: src_bound,
                    dest: dest_bound,
                } => {
                    let src = get_mode(modes, src_bound);
                    let dest = get_mode(modes, dest_bound);
                    debug_assert!(src <= dest);
                    match dest {
                        mode::Mode::Owned => Some(path.clone()),
                        mode::Mode::Borrowed => None,
                    }
                }
                mode::PathOccurMode::Final => None,
                mode::PathOccurMode::Unused => {
                    // TODO: Add an assert that this path has mode `Borrowed` (this will require
                    // tracking the mode bound in the annotations)
                    None
                }
            })
            .collect(),
    }
}

fn concretize_ops(
    modes: &IdVec<ineq::ExternalVarId, mode::Mode>,
    mode_annots: &mode::ModeAnnots,
) -> ConcreteRcOps {
    let release_prologues = mode_annots
        .drop_prologues
        .map(|_, drops| concretize_drops(modes, drops));

    let occur_retains = mode_annots
        .occur_modes
        .map(|_, occur_modes| concretize_occurs(modes, occur_modes));

    let let_release_epilogues = mode_annots
        .let_drop_epilogues
        .map(|_, drops| concretize_drops(modes, drops));

    let branch_release_epilogues = mode_annots
        .branch_drop_epilogues
        .map(|_, drops| concretize_drops(modes, drops));

    let arg_release_epilogue = concretize_drop_modes(modes, &mode_annots.arg_drop_epilogue);

    ConcreteRcOps {
        release_prologues,
        occur_retains,
        let_release_epilogues,
        branch_release_epilogues,
        arg_release_epilogue,
    }
}

#[derive(Clone, Debug)]
struct FuncInstances {
    by_modes: BTreeMap<IdVec<ineq::ExternalVarId, mode::Mode>, rc::CustomFuncId>,
    // We use an `Rc` here because these values tend to be large, and appear in both this instance
    // cache and the pending instance queue.
    //
    // TODO: This should *really* be a hashmap -- we just need to make sure we never depend on
    // iteration order.
    by_ops: BTreeMap<Rc<ConcreteRcOps>, rc::CustomFuncId>,
}

// We can't use `util::InstanceQueue` here because we have two layers of caching.  The uncached
// monomorphization process consists of a three-step transformation 'concrete modes -> concrete ops
// -> monomorphized function'.  We maintain caches for both 'concrete modes -> monomorphized
// function' and 'concrete ops -> monomorphized function'.
//
// The reason we have two layers of caching is that two distinct assignments of concrete mode
// parameters may result in the same set of concrete RC operations in the function body, and we want
// to deduplicate functions based on this fact.
#[derive(Clone, Debug)]
struct InstanceQueue<'a> {
    // We maintain a reference to `orig_funcs` only to access the mode annotations of each function
    // for the purpose of the 'concrete modes -> concrete ops' transformation.
    orig_funcs: &'a IdVec<first_ord::CustomFuncId, mode::FuncDef>,

    func_id_gen: IdGen<rc::CustomFuncId>,
    instances: IdVec<first_ord::CustomFuncId, IdVec<spec::FuncVersionId, FuncInstances>>,

    pending: VecDeque<(
        (first_ord::CustomFuncId, spec::FuncVersionId),
        rc::CustomFuncId,
        IdVec<ineq::ExternalVarId, mode::Mode>,
        Rc<ConcreteRcOps>,
    )>,
}

impl<'a> InstanceQueue<'a> {
    fn new(orig_funcs: &'a IdVec<first_ord::CustomFuncId, mode::FuncDef>) -> Self {
        InstanceQueue {
            orig_funcs,

            func_id_gen: IdGen::new(),
            instances: orig_funcs.map(|_, func_def| {
                func_def.versions.map(|_, _| FuncInstances {
                    by_modes: BTreeMap::new(),
                    by_ops: BTreeMap::new(),
                })
            }),

            pending: VecDeque::new(),
        }
    }

    fn resolve(
        &mut self,
        func: first_ord::CustomFuncId,
        version: spec::FuncVersionId,
        modes: IdVec<ineq::ExternalVarId, mode::Mode>,
    ) -> rc::CustomFuncId {
        let func_instances = &mut self.instances[func][version];

        if let Some(inst) = func_instances.by_modes.get(&modes) {
            return *inst;
        }

        let concrete_ops = Rc::new(concretize_ops(
            &modes,
            &self.orig_funcs[func].modes[version],
        ));

        if let Some(inst) = func_instances.by_ops.get(&concrete_ops) {
            return *inst;
        }

        let new_id = self.func_id_gen.fresh();

        func_instances.by_modes.insert(modes.clone(), new_id);
        func_instances.by_ops.insert(concrete_ops.clone(), new_id);

        self.pending
            .push_back(((func, version), new_id, modes, concrete_ops));

        new_id
    }
}

pub fn rc_specialize(_program: mode::Program) -> rc::Program {
    todo!()
}
