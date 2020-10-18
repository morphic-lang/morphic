use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::rc::Rc;

use crate::data::alias_specialized_ast as spec;
use crate::data::anon_sum_ast as anon;
use crate::data::fate_annot_ast as fate;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mode_annot_ast as mode;
use crate::data::rc_specialized_ast as rc;
use crate::util::id_gen::IdGen;
use crate::util::id_vec::IdVec;
use crate::util::inequality_graph as ineq;
use crate::util::local_context::LocalContext;

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

// TODO: Can we unify this with the `LetManyBuilder` in `flatten`, or the `LowAstBuilder` in
// `lower_structures`?
#[derive(Clone, Debug)]
struct LetManyBuilder {
    free_locals: usize,
    bindings: Vec<(anon::Type, rc::Expr)>,
}

impl LetManyBuilder {
    fn new(free_locals: usize) -> Self {
        LetManyBuilder {
            free_locals,
            bindings: Vec::new(),
        }
    }

    fn add_binding(&mut self, type_: anon::Type, rhs: rc::Expr) -> rc::LocalId {
        let binding_id = rc::LocalId(self.free_locals + self.bindings.len());
        self.bindings.push((type_, rhs));
        binding_id
    }

    fn to_expr(self, ret: rc::LocalId) -> rc::Expr {
        debug_assert!(ret.0 < self.free_locals + self.bindings.len());
        rc::Expr::LetMany(self.bindings, ret)
    }

    fn child(&self) -> LetManyBuilder {
        LetManyBuilder::new(self.free_locals + self.bindings.len())
    }
}

#[derive(Clone, Debug)]
struct LocalInfo<'a> {
    type_: &'a anon::Type,
    new_id: rc::LocalId,
}

#[derive(Clone, Debug)]
enum RcOpPlan {
    NoOp,
    LeafOp,
    OnTupleFields(BTreeMap<usize, RcOpPlan>),
    OnVariantCases(BTreeMap<first_ord::VariantId, RcOpPlan>),
    OnCustom(first_ord::CustomTypeId, Box<RcOpPlan>),
}

impl RcOpPlan {
    fn add_leaf_path(&mut self, path: &mode::StackPath) {
        let mut curr = self;
        for field in path.iter() {
            if matches!(&curr, RcOpPlan::NoOp) {
                *curr = match field {
                    mode::StackField::Field(_) => RcOpPlan::OnTupleFields(BTreeMap::new()),
                    mode::StackField::Variant(_) => RcOpPlan::OnVariantCases(BTreeMap::new()),
                    mode::StackField::Custom(custom_id) => {
                        RcOpPlan::OnCustom(*custom_id, Box::new(RcOpPlan::NoOp))
                    }
                };
            }

            curr = match (curr, field) {
                (RcOpPlan::OnTupleFields(sub_plans), mode::StackField::Field(idx)) => {
                    sub_plans.entry(*idx).or_insert(RcOpPlan::NoOp)
                }
                (RcOpPlan::OnVariantCases(sub_plans), mode::StackField::Variant(variant_id)) => {
                    sub_plans.entry(*variant_id).or_insert(RcOpPlan::NoOp)
                }
                (
                    RcOpPlan::OnCustom(custom_id, sub_plan),
                    mode::StackField::Custom(field_custom_id),
                ) => {
                    debug_assert_eq!(custom_id, field_custom_id);
                    &mut **sub_plan
                }
                _ => unreachable!(),
            };
        }
        debug_assert!(matches!(&curr, RcOpPlan::NoOp));
        *curr = RcOpPlan::LeafOp;
    }
}

fn build_plan(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    rc_op: rc::RcOp,
    root: rc::LocalId,
    root_type: &anon::Type,
    plan: &RcOpPlan,
    builder: &mut LetManyBuilder,
) {
    match plan {
        RcOpPlan::NoOp => {}

        RcOpPlan::LeafOp => {
            let (container_type, item_type) = match root_type {
                anon::Type::Array(item_type) => (rc::ContainerType::Array, item_type),
                anon::Type::HoleArray(item_type) => (rc::ContainerType::HoleArray, item_type),
                anon::Type::Boxed(item_type) => (rc::ContainerType::Boxed, item_type),
                _ => unreachable!(),
            };

            builder.add_binding(
                anon::Type::Tuple(vec![]),
                rc::Expr::RcOp(rc_op, container_type, (**item_type).clone(), root),
            );
        }

        RcOpPlan::OnTupleFields(sub_plans) => {
            let field_types = if let anon::Type::Tuple(field_types) = root_type {
                field_types
            } else {
                unreachable!()
            };

            for (idx, sub_plan) in sub_plans {
                let field_type = &field_types[*idx];
                let field_local =
                    builder.add_binding(field_type.clone(), rc::Expr::TupleField(root, *idx));
                Some(build_plan(
                    typedefs,
                    rc_op,
                    field_local,
                    field_type,
                    sub_plan,
                    builder,
                ));
            }
        }

        RcOpPlan::OnVariantCases(sub_plans) => {
            let variant_types = if let anon::Type::Variants(variant_types) = root_type {
                variant_types
            } else {
                unreachable!()
            };

            let mut cases = Vec::new();
            for (variant_id, sub_plan) in sub_plans {
                let variant_type = &variant_types[variant_id];
                let cond = flat::Condition::Variant(*variant_id, Box::new(flat::Condition::Any));

                let mut case_builder = builder.child();
                let content_id = case_builder.add_binding(
                    variant_type.clone(),
                    rc::Expr::UnwrapVariant(*variant_id, root),
                );
                build_plan(
                    typedefs,
                    rc_op,
                    content_id,
                    variant_type,
                    sub_plan,
                    &mut case_builder,
                );

                // We need to return *something* from this branch arm, so we return a `()` value.
                //
                // TODO: Should we reuse the result of the generated RC op to make the generated
                // code for this case slightly easier to read?
                let unit_id =
                    case_builder.add_binding(anon::Type::Tuple(vec![]), rc::Expr::Tuple(vec![]));

                cases.push((cond, case_builder.to_expr(unit_id)))
            }
            cases.push((flat::Condition::Any, rc::Expr::Tuple(vec![])));

            builder.add_binding(
                anon::Type::Tuple(vec![]),
                rc::Expr::Branch(root, cases, anon::Type::Tuple(vec![])),
            );
        }

        RcOpPlan::OnCustom(custom_id, sub_plan) => {
            debug_assert_eq!(root_type, &anon::Type::Custom(*custom_id));

            let content_type = &typedefs[custom_id];

            let content_id = builder.add_binding(
                content_type.clone(),
                rc::Expr::UnwrapCustom(*custom_id, root),
            );
            build_plan(typedefs, rc_op, content_id, content_type, sub_plan, builder);
        }
    }
}

fn build_rc_ops(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    rc_op: rc::RcOp,
    local: rc::LocalId,
    local_type: &anon::Type,
    paths: &BTreeSet<mode::StackPath>,
    builder: &mut LetManyBuilder,
) {
    let mut plan = RcOpPlan::NoOp;
    for path in paths {
        plan.add_leaf_path(path);
    }
    build_plan(typedefs, rc_op, local, local_type, &plan, builder);
}

fn build_releases(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    locals: &LocalContext<flat::LocalId, LocalInfo>,
    releases: &Vec<(flat::LocalId, ReleasePaths)>,
    builder: &mut LetManyBuilder,
) {
    for (flat_local, release_paths) in releases {
        let local_info = locals.local_binding(*flat_local);
        build_rc_ops(
            typedefs,
            rc::RcOp::Release,
            local_info.new_id,
            local_info.type_,
            &release_paths.release_paths,
            builder,
        );
    }
}

fn resolve_expr<'a>(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    _insts: &mut InstanceQueue,
    _modes: &IdVec<ineq::ExternalVarId, mode::Mode>,
    ops: &ConcreteRcOps,
    locals: &mut LocalContext<flat::LocalId, LocalInfo<'a>>,
    expr: &'a fate::Expr,
    _result_type: anon::Type,
    builder: &mut LetManyBuilder,
) -> rc::LocalId {
    build_releases(typedefs, locals, &ops.release_prologues[expr.id], builder);

    todo!()
}

pub fn rc_specialize(_program: mode::Program) -> rc::Program {
    todo!()
}
