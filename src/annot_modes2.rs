use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast::{CustomFuncId, CustomTypeId, NumType};
use crate::data::flat_ast::{self as flat, LocalId};
use crate::data::mode_annot_ast2::{
    self as annot, Lt, LtParam, ModeConstr, ModeParam, ModeTerm, OldOverlay,
};
use crate::fixed_point::{self, Signature, SignatureAssumptions};
use crate::util::graph as old_graph; // TODO: switch completely to `id_graph_sccs`
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{id_type, Count, Id, IdMap, IdVec};
use id_graph_sccs::{find_components, Scc, SccKind, Sccs};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

fn count_stack_params(counts: &IdMap<CustomTypeId, usize>, ty: &anon::Type) -> usize {
    match ty {
        anon::Type::Bool => 0,
        anon::Type::Num(_) => 0,
        anon::Type::Tuple(tys) => tys.iter().map(|ty| count_stack_params(counts, ty)).sum(),
        anon::Type::Variants(tys) => tys
            .iter()
            .map(|(_, ty)| count_stack_params(counts, ty))
            .sum(),
        anon::Type::Custom(id) => match counts.get(id) {
            Some(count) => *count,
            // This is a typedef in the same SCC; the reference to it here contributes no additional
            // parameters to the entire SCC.
            None => 0,
        },
        anon::Type::Array(_) => 1,
        anon::Type::HoleArray(_) => 1,
        anon::Type::Boxed(_) => 1,
    }
}

fn count_heap_params(counts: &IdMap<CustomTypeId, usize>, ty: &anon::Type) -> usize {
    match ty {
        anon::Type::Bool => 0,
        anon::Type::Num(_) => 0,
        anon::Type::Tuple(tys) => tys.iter().map(|ty| count_heap_params(counts, ty)).sum(),
        anon::Type::Variants(tys) => tys
            .iter()
            .map(|(_, ty)| count_heap_params(counts, ty))
            .sum(),
        anon::Type::Custom(id) => match counts.get(id) {
            Some(count) => *count,
            // This is a typedef in the same SCC; the reference to it here contributes no additional
            // parameters to the entire SCC.
            None => 0,
        },
        anon::Type::Array(ty) => count_heap_params(counts, ty) + 1,
        anon::Type::HoleArray(ty) => count_heap_params(counts, ty) + 1,
        anon::Type::Boxed(ty) => count_heap_params(counts, ty) + 1,
    }
}

fn fresh_params<I: Id, J: Id>(n: Count<I>, fresh: &mut Count<J>) -> IdVec<I, J> {
    IdVec::from_count_with(n, |_| fresh.inc())
}

fn fresh_overlay(
    scc_overlay_mode_count: Count<ModeParam>,
    fresh_mode: &mut Count<ModeParam>,
    ty: &anon::Type,
) -> OldOverlay<ModeParam> {
    match ty {
        anon::Type::Bool => OldOverlay::Bool,
        anon::Type::Num(num_ty) => OldOverlay::Num(*num_ty),
        anon::Type::Tuple(tys) => OldOverlay::Tuple(
            tys.iter()
                .map(|ty| fresh_overlay(scc_overlay_mode_count, fresh_mode, ty))
                .collect(),
        ),
        anon::Type::Variants(tys) => OldOverlay::Variants(
            tys.map_refs(|_, ty| fresh_overlay(scc_overlay_mode_count, fresh_mode, ty)),
        ),
        anon::Type::Custom(id) => OldOverlay::Custom(*id),
        anon::Type::Array(_) => OldOverlay::Array(fresh_mode.inc()),
        anon::Type::HoleArray(_) => OldOverlay::HoleArray(fresh_mode.inc()),
        anon::Type::Boxed(_) => OldOverlay::Boxed(fresh_mode.inc()),
    }
}

fn parameterize(
    parameterized: &IdMap<CustomTypeId, annot::CustomTypeDef>,
    scc_mode_count: Count<ModeParam>,
    scc_overlay_mode_count: Count<ModeParam>,
    scc_lt_count: Count<LtParam>,
    fresh_mode: &mut Count<ModeParam>,
    fresh_lt: &mut Count<LtParam>,
    ty: &anon::Type,
) -> annot::OldType<ModeParam, LtParam> {
    match ty {
        anon::Type::Bool => annot::OldType::Bool,
        anon::Type::Num(num_ty) => annot::OldType::Num(*num_ty),
        anon::Type::Tuple(tys) => annot::OldType::Tuple(
            tys.iter()
                .map(|ty| {
                    parameterize(
                        parameterized,
                        scc_mode_count,
                        scc_overlay_mode_count,
                        scc_lt_count,
                        fresh_mode,
                        fresh_lt,
                        ty,
                    )
                })
                .collect(),
        ),
        anon::Type::Variants(tys) => annot::OldType::Variants(tys.map_refs(|_, ty| {
            parameterize(
                parameterized,
                scc_mode_count,
                scc_overlay_mode_count,
                scc_lt_count,
                fresh_mode,
                fresh_lt,
                ty,
            )
        })),
        anon::Type::Custom(id) => match parameterized.get(id) {
            Some(typedef) => annot::OldType::Custom(
                *id,
                fresh_params(typedef.num_mode_params, fresh_mode),
                fresh_params(typedef.num_lt_params, fresh_lt),
            ),
            // This is a typedef in the same SCC; we need to parameterize it by all the SCC
            // parameters
            None => annot::OldType::Custom(
                *id,
                fresh_params(scc_mode_count, fresh_mode),
                fresh_params(scc_lt_count, fresh_lt),
            ),
        },
        anon::Type::Array(ty) => {
            let content = parameterize(
                parameterized,
                scc_mode_count,
                scc_overlay_mode_count,
                scc_lt_count,
                fresh_mode,
                fresh_lt,
                ty,
            );
            annot::OldType::Array(
                fresh_mode.inc(),
                fresh_lt.inc(),
                Box::new(content),
                fresh_overlay(scc_overlay_mode_count, fresh_mode, ty),
            )
        }
        anon::Type::HoleArray(ty) => {
            let content = parameterize(
                parameterized,
                scc_mode_count,
                scc_overlay_mode_count,
                scc_lt_count,
                fresh_mode,
                fresh_lt,
                ty,
            );
            annot::OldType::HoleArray(
                fresh_mode.inc(),
                fresh_lt.inc(),
                Box::new(content),
                fresh_overlay(scc_overlay_mode_count, fresh_mode, ty),
            )
        }
        anon::Type::Boxed(ty) => {
            let content = parameterize(
                parameterized,
                scc_mode_count,
                scc_overlay_mode_count,
                scc_lt_count,
                fresh_mode,
                fresh_lt,
                ty,
            );
            annot::OldType::Boxed(
                fresh_mode.inc(),
                fresh_lt.inc(),
                Box::new(content),
                fresh_overlay(scc_overlay_mode_count, fresh_mode, ty),
            )
        }
    }
}

fn parameterize_custom_scc(
    customs: &IdVec<CustomTypeId, flat::CustomTypeDef>,
    parameterized: &IdMap<CustomTypeId, annot::CustomTypeDef>,
    stack_param_counts: &IdMap<CustomTypeId, usize>,
    heap_param_counts: &IdMap<CustomTypeId, usize>,
    scc: &old_graph::Scc<CustomTypeId>,
) -> BTreeMap<CustomTypeId, annot::CustomTypeDef> {
    let num_stack_params: usize = scc
        .iter()
        .map(|id| count_stack_params(stack_param_counts, &customs[*id].content))
        .sum();
    let num_heap_params: usize = scc
        .iter()
        .map(|id| count_heap_params(heap_param_counts, &customs[*id].content))
        .sum();

    let num_mode_params = Count::from_value(num_heap_params);
    let num_overlay_mode_params = Count::from_value(num_stack_params);
    let num_lt_params = Count::from_value(num_heap_params);

    let mut fresh_mode = Count::new();
    let mut fresh_lt = Count::new();

    let to_populate = scc
        .iter()
        .map(|id| {
            (
                *id,
                annot::CustomTypeDef {
                    num_mode_params,
                    num_overlay_mode_params,
                    num_lt_params,
                    content: parameterize(
                        parameterized,
                        num_mode_params,
                        num_overlay_mode_params,
                        num_lt_params,
                        &mut fresh_mode,
                        &mut fresh_lt,
                        &customs[*id].content,
                    ),
                    overlay: fresh_overlay(num_mode_params, &mut fresh_mode, &customs[*id].content),
                },
            )
        })
        .collect();

    debug_assert_eq!(num_mode_params, fresh_mode);
    debug_assert_eq!(num_lt_params, fresh_lt);
    to_populate
}

fn parameterize_customs(customs: &flat::CustomTypes) -> IdVec<CustomTypeId, annot::CustomTypeDef> {
    let mut parameterized = IdMap::new();
    let mut stack_param_counts = IdMap::new();
    let mut heap_param_counts = IdMap::new();

    for scc in customs.sccs.values() {
        let to_populate = parameterize_custom_scc(
            &customs.types,
            &parameterized,
            &mut stack_param_counts,
            &mut heap_param_counts,
            scc,
        );

        debug_assert_eq!(
            to_populate.keys().collect::<BTreeSet<_>>(),
            scc.iter().collect::<BTreeSet<_>>()
        );

        for (id, typedef) in to_populate {
            parameterized.insert(id, typedef);
        }
    }
    parameterized.to_id_vec(customs.types.count())
}

#[id_type]
struct ModeVar(usize);

type SolverType = annot::OldType<ModeVar, Lt>;
type SolverOccur = annot::Occur<ModeVar, Lt>;
type SolverOverlay = annot::OldOverlay<ModeVar>;
type SolverCondition = annot::Condition<ModeVar, Lt>;
type SolverExpr = annot::Expr<ModeVar, Lt>;

struct ConstrGraph {
    // a -> b means a <= b, i.e. if a is owned then b is owned
    edges_out: IdVec<ModeVar, Vec<ModeVar>>,
    owned: BTreeSet<ModeVar>,
}

impl ConstrGraph {
    fn new() -> Self {
        Self {
            edges_out: IdVec::new(),
            owned: BTreeSet::new(),
        }
    }

    fn fresh_var(&mut self) -> ModeVar {
        self.edges_out.push(Vec::new())
    }

    fn add_constrs(&mut self, constrs: &[ModeConstr<ModeVar>]) {
        for constr in constrs {
            match constr {
                ModeConstr::Lte(a, b) => {
                    self.enforce_lte(*a, *b);
                }
                ModeConstr::Owned(a) => {
                    self.enforce_owned(*a);
                }
            }
        }
    }

    fn enforce_lte(&mut self, a: ModeVar, b: ModeVar) {
        self.edges_out[a].push(b);
    }

    fn enforce_eq(&mut self, a: ModeVar, b: ModeVar) {
        self.enforce_lte(a, b);
        self.enforce_lte(b, a);
    }

    fn enforce_owned(&mut self, a: ModeVar) {
        self.owned.insert(a);
    }

    fn solve(&self) -> IdVec<ModeVar, ModeTerm<ModeVar>> {
        todo!()
    }
}

fn mode_bind_overlays(constrs: &mut ConstrGraph, o1: &SolverOverlay, o2: &SolverOverlay) {
    match (o1, o2) {
        (OldOverlay::Bool, OldOverlay::Bool) => {}
        (OldOverlay::Num(_), OldOverlay::Num(_)) => {}
        (OldOverlay::Tuple(os1), OldOverlay::Tuple(os2)) => {
            for (o1, o2) in os1.iter().zip(os2.iter()) {
                mode_bind_overlays(constrs, o1, o2);
            }
        }
        (OldOverlay::Variants(os1), OldOverlay::Variants(os2)) => {
            for ((_, o1), (_, o2)) in os1.iter().zip(os2.iter()) {
                mode_bind_overlays(constrs, o1, o2);
            }
        }
        (OldOverlay::Array(m1), OldOverlay::Array(m2)) => {
            constrs.enforce_eq(*m1, *m2);
        }
        (OldOverlay::HoleArray(m1), OldOverlay::HoleArray(m2)) => {
            constrs.enforce_eq(*m1, *m2);
        }
        (OldOverlay::Boxed(m1), OldOverlay::Boxed(m2)) => {
            constrs.enforce_eq(*m1, *m2);
        }
        _ => panic!("incompatible overlays"),
    }
}

fn mode_bind(constrs: &mut ConstrGraph, ty1: &SolverType, ty2: &SolverType) {
    match (ty1, ty2) {
        (annot::OldType::Bool, annot::OldType::Bool) => {}
        (annot::OldType::Num(_), annot::OldType::Num(_)) => {}
        (annot::OldType::Tuple(tys1), annot::OldType::Tuple(tys2)) => {
            for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
                mode_bind(constrs, ty1, ty2);
            }
        }
        (annot::OldType::Variants(tys1), annot::OldType::Variants(tys2)) => {
            for ((_, ty1), (_, ty2)) in tys1.iter().zip(tys2.iter()) {
                mode_bind(constrs, ty1, ty2);
            }
        }
        (annot::OldType::Array(m1, _lt1, ty1, o1), annot::OldType::Array(m2, _lt2, ty2, o2)) => {
            constrs.enforce_eq(*m1, *m2);
        }
        _ => panic!("incompatible types"),
    }
}

fn emit_occur_constr(
    constrs: &mut ConstrGraph,
    path: &annot::Path,
    binding_lt: &Lt,
    use_lt: &Lt,
    binding_mode: ModeVar,
    use_mode: ModeVar,
) {
    if use_lt.does_not_exceed(path) {
        if *binding_lt == Lt::Empty && *use_lt != Lt::Empty {
            // Case: this is a non-escaping, final ("opportunistic") occurrence.
            constrs.enforce_lte(use_mode, binding_mode);
        }
    } else {
        // Case: this is an escaping ("move" or "dup") occurrence.
        constrs.enforce_lte(binding_mode, use_mode);
    }
}

fn emit_occur_constrs_overlay(
    constrs: &mut ConstrGraph,
    path: &annot::Path,
    binding_overlay: &SolverOverlay,
    use_overlay: &SolverOverlay,
) {
    todo!()
}

fn emit_occur_constrs_heap(
    constrs: &mut ConstrGraph,
    path: &annot::Path,
    binding_ty: &SolverType,
    fut_ty: &SolverType,
) {
    todo!()
}

fn emit_occur_constrs(
    constrs: &mut ConstrGraph,
    path: &annot::Path,
    binding_ty: &SolverType,
    fut_ty: &SolverType,
) {
    match (binding_ty, fut_ty) {
        (annot::OldType::Bool, annot::OldType::Bool) => {}
        (annot::OldType::Num(_), annot::OldType::Num(_)) => {}
        (annot::OldType::Tuple(tys1), annot::OldType::Tuple(tys2)) => {
            for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
                emit_occur_constrs(constrs, path, ty1, ty2);
            }
        }
        (annot::OldType::Variants(tys1), annot::OldType::Variants(tys2)) => {
            for ((_, ty1), (_, ty2)) in tys1.iter().zip(tys2.iter()) {
                emit_occur_constrs(constrs, path, ty1, ty2);
            }
        }
        (annot::OldType::Array(m1, lt1, ty1, o1), annot::OldType::Array(m2, lt2, ty2, o2)) => {
            emit_occur_constr(constrs, path, lt1, lt2, *m1, *m2);
            emit_occur_constrs_heap(constrs, path, ty1, ty2);
            emit_occur_constrs_overlay(constrs, path, o1, o2);
        }
        _ => panic!("incompatible types"),
    }
}

#[derive(Clone, Debug)]
struct ImmutContext {
    count: Count<LocalId>,
    stack: im_rc::Vector<Rc<SolverType>>, // TODO: `Vector` is slow
}

impl ImmutContext {
    fn new() -> Self {
        Self {
            count: Count::new(),
            stack: im_rc::Vector::new(),
        }
    }

    fn add_local(&mut self, binding: Rc<SolverType>) -> LocalId {
        let id = self.count.inc();
        self.stack.push_back(binding);
        id
    }

    fn set_local(&mut self, local: LocalId, binding: Rc<SolverType>) {
        self.stack[local.0] = binding;
    }

    fn local_binding(&self, local: LocalId) -> &Rc<SolverType> {
        &self.stack[local.0]
    }
}

#[derive(Clone, Debug)]
struct LocalUpdates(BTreeMap<LocalId, Rc<SolverType>>);

impl LocalUpdates {
    fn new() -> Self {
        LocalUpdates(BTreeMap::new())
    }

    fn record(&mut self, id: LocalId, binding: Rc<SolverType>) {
        self.0.insert(id, binding);
    }

    fn merge(&mut self, other: &Self) {
        use std::collections::btree_map::Entry;
        for (id, ty) in &other.0 {
            match self.0.entry(*id) {
                Entry::Vacant(entry) => {
                    entry.insert(ty.clone());
                }
                Entry::Occupied(mut entry) => {
                    let old = entry.get_mut();
                    *old = Rc::new(old.left_meet(&ty));
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
struct TrackedContext {
    ctx: ImmutContext,
    updates: LocalUpdates,
}

impl TrackedContext {
    fn new(ctx: &ImmutContext) -> Self {
        Self {
            ctx: ctx.clone(),
            updates: LocalUpdates::new(),
        }
    }

    fn add_local(&mut self, binding: Rc<SolverType>) -> LocalId {
        let local = self.ctx.add_local(binding.clone());
        self.updates.record(local, binding);
        local
    }

    fn set_local(&mut self, local: LocalId, binding: Rc<SolverType>) {
        self.ctx.set_local(local, binding.clone());
        self.updates.record(local, binding);
    }

    fn set_locals(&mut self, updates: &LocalUpdates) {
        for (id, binding) in &updates.0 {
            self.ctx.set_local(*id, binding.clone());
        }
    }

    fn local_binding(&self, local: LocalId) -> &Rc<SolverType> {
        self.ctx.local_binding(local)
    }

    fn as_untracked(&self) -> &ImmutContext {
        &self.ctx
    }

    fn into_updates(self) -> LocalUpdates {
        self.updates
    }
}

fn same_shape(ty1: &anon::Type, ty2: &SolverType) -> bool {
    match (ty1, ty2) {
        (anon::Type::Bool, annot::OldType::Bool) => true,
        (anon::Type::Num(num_ty1), annot::OldType::Num(num_ty2)) => num_ty1 == num_ty2,
        (anon::Type::Tuple(tys1), annot::OldType::Tuple(tys2)) => {
            tys1.len() == tys2.len()
                && tys1
                    .iter()
                    .zip(tys2.iter())
                    .all(|(ty1, ty2)| same_shape(ty1, ty2))
        }
        (anon::Type::Variants(tys1), annot::OldType::Variants(tys2)) => {
            tys1.len() == tys2.len()
                && tys1
                    .iter()
                    .zip(tys2.iter())
                    .all(|((id1, ty1), (id2, ty2))| id1 == id2 && same_shape(ty1, ty2))
        }
        (anon::Type::Custom(id1), annot::OldType::Custom(id2, _, _)) => id1 == id2,
        (anon::Type::Array(ty1), annot::OldType::Array(_, _, ty2, _)) => same_shape(ty1, ty2),
        (anon::Type::HoleArray(ty1), annot::OldType::HoleArray(_, _, ty2, _)) => {
            same_shape(ty1, ty2)
        }
        (anon::Type::Boxed(ty1), annot::OldType::Boxed(_, _, ty2, _)) => same_shape(ty1, ty2),
        _ => false,
    }
}

fn apply_overlay(ty: &SolverType, overlay: &SolverOverlay) -> SolverType {
    match (ty, overlay) {
        (annot::OldType::Bool, annot::OldOverlay::Bool) => annot::OldType::Bool,
        (annot::OldType::Num(num_ty1), annot::OldOverlay::Num(num_ty2)) => {
            assert_eq!(num_ty1, num_ty2);
            annot::OldType::Num(*num_ty1)
        }
        (annot::OldType::Tuple(tys), annot::OldOverlay::Tuple(os)) => {
            assert_eq!(tys.len(), os.len());
            let tys = tys
                .iter()
                .zip(os.iter())
                .map(|(ty, o)| apply_overlay(ty, o))
                .collect();
            annot::OldType::Tuple(tys)
        }
        (annot::OldType::Variants(tys), annot::OldOverlay::Variants(os)) => {
            assert_eq!(tys.len(), os.len());
            let tys = tys
                .values()
                .zip(os.values())
                .map(|(ty, o)| apply_overlay(ty, o))
                .collect();
            annot::OldType::Variants(IdVec::from_vec(tys))
        }
        (annot::OldType::Custom(id1, modes, lts), annot::OldOverlay::Custom(id2)) => {
            assert_eq!(id1, id2);
            annot::OldType::Custom(*id1, modes.clone(), lts.clone())
        }
        (annot::OldType::Array(_, lt, ty, o), annot::OldOverlay::Array(m)) => {
            annot::OldType::Array(*m, lt.clone(), ty.clone(), o.clone())
        }
        (annot::OldType::HoleArray(_, lt, ty, o), annot::OldOverlay::HoleArray(m)) => {
            annot::OldType::HoleArray(*m, lt.clone(), ty.clone(), o.clone())
        }
        (annot::OldType::Boxed(_, lt, ty, o), annot::OldOverlay::Boxed(m)) => {
            annot::OldType::Boxed(*m, lt.clone(), ty.clone(), o.clone())
        }
        _ => panic!("type and overlay are incompatible"),
    }
}

fn instantiate_occur(
    ctx: &mut TrackedContext,
    constrs: &mut ConstrGraph,
    path: &annot::Path,
    id: LocalId,
    fut_ty: &SolverType,
) -> SolverOccur {
    let old_ty = ctx.local_binding(id);
    emit_occur_constrs(constrs, path, old_ty, fut_ty);

    let new_ty = Rc::new(old_ty.left_meet(fut_ty));
    ctx.set_local(id, new_ty);

    annot::Occur {
        local: id,
        ty: fut_ty.clone(),
    }
}

fn instantiate_condition(
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    constrs: &mut ConstrGraph,
    cond: &flat::Condition,
) -> SolverCondition {
    match cond {
        flat::Condition::Any => annot::Condition::Any,
        flat::Condition::Tuple(conds) => annot::Condition::Tuple(
            conds
                .iter()
                .map(|cond| instantiate_condition(customs, constrs, cond))
                .collect(),
        ),
        flat::Condition::Variant(id, cond) => {
            annot::Condition::Variant(*id, Box::new(instantiate_condition(customs, constrs, cond)))
        }
        flat::Condition::Boxed(cond, ty) => annot::Condition::Boxed(
            Box::new(instantiate_condition(customs, constrs, cond)),
            instantiate_type(customs, constrs, ty),
        ),
        flat::Condition::Custom(id, cond) => {
            annot::Condition::Custom(*id, Box::new(instantiate_condition(customs, constrs, cond)))
        }
        flat::Condition::BoolConst(v) => annot::Condition::BoolConst(*v),
        flat::Condition::ByteConst(v) => annot::Condition::ByteConst(*v),
        flat::Condition::IntConst(v) => annot::Condition::IntConst(*v),
        flat::Condition::FloatConst(v) => annot::Condition::FloatConst(*v),
    }
}

impl Signature for annot::FuncDef {
    type Sig = annot::Sig;

    fn signature(&self) -> &Self::Sig {
        &self.sig
    }
}

fn instantiate_occur_int(ctx: &TrackedContext, id: LocalId) -> SolverOccur {
    assert!(matches!(
        **ctx.local_binding(id),
        annot::OldType::Num(NumType::Int)
    ));
    annot::Occur {
        local: id,
        ty: annot::OldType::Num(NumType::Int),
    }
}

fn instantiate_occur_array(
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    ctx: &mut TrackedContext,
    updates: &mut LocalUpdates,
    constrs: &mut ConstrGraph,
    path: &annot::Path,
    item_ty: &anon::Type,
    id: LocalId,
) -> SolverOccur {
    let occur_ty = annot::OldType::Array(
        constrs.fresh_var(),
        path.as_lt(),
        Box::new(instantiate_type(customs, constrs, item_ty)),
        instantiate_overlay(customs, constrs, item_ty),
    );
    instantiate_occur(ctx, constrs, path, id, &occur_ty)
}

fn instantiate_occur_hole(
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    ctx: &mut TrackedContext,
    constrs: &mut ConstrGraph,
    path: &annot::Path,
    item_ty: &anon::Type,
    id: LocalId,
) -> SolverOccur {
    let occur_ty = annot::OldType::Array(
        constrs.fresh_var(),
        path.as_lt(),
        Box::new(instantiate_type(customs, constrs, item_ty)),
        instantiate_overlay(customs, constrs, item_ty),
    );
    instantiate_occur(ctx, constrs, path, id, &occur_ty)
}

fn freshen_type(
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    constrs: &mut ConstrGraph,
    ty: &annot::OldType<ModeParam, LtParam>,
) -> SolverType {
    match ty {
        annot::OldType::Bool => annot::OldType::Bool,
        annot::OldType::Num(num_ty) => annot::OldType::Num(*num_ty),
        annot::OldType::Tuple(tys) => {
            let tys = tys
                .iter()
                .map(|ty| freshen_type(customs, constrs, ty))
                .collect();
            annot::OldType::Tuple(tys)
        }
        annot::OldType::Variants(tys) => {
            let tys = tys.map_refs(|_, ty| freshen_type(customs, constrs, ty));
            annot::OldType::Variants(tys)
        }
        annot::OldType::Custom(id, modes, lts) => {
            let typedef = &customs[*id];
            let modes = IdVec::from_count_with(typedef.num_mode_params, |_| constrs.fresh_var());
            let lts = IdVec::from_count_with(typedef.num_lt_params, |_| Lt::Empty);
            annot::OldType::Custom(*id, modes, lts)
        }
        annot::OldType::Array(m, lt, ty, o) => {
            // let m = constrs.fresh_var();
            // let ty = Box::new(freshen_type(customs, constrs, ty));
            // let o = instantiate_overlay(customs, constrs, ty);
            // annot::Type::Array(m, Lt::Empty, ty, o)
            todo!()
        }
        annot::OldType::HoleArray(m, lt, ty, o) => {
            // let m = constrs.fresh_var();
            // let ty = Box::new(freshen_type(customs, constrs, ty));
            // let o = instantiate_overlay(customs, constrs, ty);
            // annot::Type::HoleArray(m, Lt::Empty, ty, o)
            todo!()
        }
        annot::OldType::Boxed(m, lt, ty, o) => {
            // let m = constrs.fresh_var();
            // let ty = Box::new(freshen_type(customs, constrs, ty));
            // let o = instantiate_overlay(customs, constrs, ty);
            // annot::Type::Boxed(m, Lt::Empty, ty, o)
            todo!()
        }
    }
}

// This function is the core logic for this pass. It implements the judgement from the paper:
// Δ ; Γ ; S ; q ⊢ e : t ⇝ e ; Q ; Γ'
//
// Note that we must return a set of updates rather than mutating Γ because I-Match requires that we
// check all branches in the initial Γ.
fn instantiate_expr(
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    sigs: &SignatureAssumptions<CustomFuncId, annot::FuncDef>,
    constrs: &mut ConstrGraph,
    ctx: &ImmutContext,
    scopes: &mut LocalContext<LocalId, annot::Path>,
    path: annot::Path,
    fut_ty: &SolverType,
    expr: &flat::Expr,
) -> (SolverExpr, LocalUpdates) {
    let mut ctx = TrackedContext::new(ctx);

    let expr_annot = match expr {
        flat::Expr::Local(local) => {
            let occur = instantiate_occur(&mut ctx, constrs, &path, *local, fut_ty);
            annot::Expr::Local(occur)
        }

        flat::Expr::Call(_purity, func, arg) => {
            /*
            instantiate_occur(&mut ctx, &mut updates, constrs, &path, *arg, ty);
            match globals.funcs_annot.get(func) {
                Some(func_annot) => {
                    todo!()
                }
                None => {
                    // This is a function in the current SCC

                    let pending_sig = &globals.sigs_pending[func];
                    todo!()
                }
            }
            */
            todo!()
        }

        flat::Expr::Branch(discrim_id, cases, ret_ty) => {
            debug_assert!(same_shape(ret_ty, fut_ty));

            let mut updates = LocalUpdates::new();
            let mut cases_annot = Vec::new();
            for (i, (cond, body)) in cases.iter().enumerate() {
                let branch_path = path.par(i, cases.len());
                let cond_annot = instantiate_condition(customs, constrs, cond);
                let (body_annot, body_updates) = instantiate_expr(
                    customs,
                    sigs,
                    constrs,
                    ctx.as_untracked(),
                    scopes,
                    branch_path,
                    fut_ty,
                    body,
                );

                // Record the updates, but DO NOT apply them to the context. Every branch should be
                // checked in the original context.
                updates.merge(&body_updates);

                cases_annot.push((cond_annot, body_annot));
            }

            // Finally, apply the updates before instantiating the discriminant.
            ctx.set_locals(&updates);
            let discrim_occur =
                instantiate_occur(&mut ctx, constrs, &path.seq(0), *discrim_id, fut_ty);

            annot::Expr::Branch(discrim_occur, cases_annot, fut_ty.clone())
        }

        flat::Expr::LetMany(bindings, result_id) => scopes.with_scope(|scopes| {
            let end_of_scope = path.seq(bindings.len());

            let result_occur =
                instantiate_occur(&mut ctx, constrs, &end_of_scope, *result_id, fut_ty);

            let mut locals = Vec::new();
            for (binding_ty, _) in bindings {
                let id1 = scopes.add_local(end_of_scope.clone());
                let id2 = if id1 == *result_id {
                    ctx.add_local(Rc::new(instantiate_type(customs, constrs, binding_ty)))
                } else {
                    ctx.add_local(Rc::new(fut_ty.clone()))
                };
                assert_eq!(id1, id2);
                locals.push(id1);
            }

            let mut exprs_annot = Vec::new();
            for (i, (_, binding_expr)) in bindings.iter().enumerate().rev() {
                let (expr_annot, expr_updates) = instantiate_expr(
                    customs,
                    sigs,
                    constrs,
                    ctx.as_untracked(),
                    scopes,
                    path.seq(i),
                    fut_ty,
                    binding_expr,
                );

                // Record the updates and apply them to the context. It is important that the
                // enclosing loop is in reverse order so that each binding is checking in the
                // correct context.
                ctx.set_locals(&expr_updates);

                exprs_annot.push(expr_annot);
            }

            let new_bindings = locals
                .into_iter()
                .zip(exprs_annot.into_iter())
                .map(|(local, expr_annot)| ((**ctx.local_binding(local)).clone(), expr_annot))
                .collect();

            annot::Expr::LetMany(new_bindings, result_occur)
        }),

        flat::Expr::Tuple(item_ids) => {
            let annot::OldType::Tuple(fut_tys) = fut_ty else {
                unreachable!();
            };
            assert_eq!(item_ids.len(), fut_tys.len());
            let occurs = item_ids
                .iter()
                .zip(fut_tys.iter())
                .enumerate()
                .rev()
                .map(|(i, (item_id, item_fut_ty))| {
                    instantiate_occur(&mut ctx, constrs, &path.seq(i), *item_id, item_fut_ty)
                })
                .collect();
            annot::Expr::Tuple(occurs)
        }

        flat::Expr::TupleField(tuple_id, idx) => {
            let tuple_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *tuple_id, fut_ty);
            annot::Expr::TupleField(tuple_occur, *idx)
        }

        flat::Expr::WrapVariant(variant_tys, variant_id, content) => todo!(),

        flat::Expr::UnwrapVariant(variant_id, wrapped) => {
            let content_ty =
                if let annot::OldType::Variants(variant_tys) = &**ctx.local_binding(*wrapped) {
                    &variant_tys[variant_id]
                } else {
                    unreachable!();
                };

            let wrapped_occur =
                instantiate_occur(&mut ctx, constrs, &path.seq(0), *wrapped, fut_ty);

            // annot::Expr::UnwrapVariant(variant_id, content_occur)
            todo!()
        }

        flat::Expr::WrapBoxed(content, item_ty) => todo!(),

        flat::Expr::UnwrapBoxed(wrapped, item_ty) => todo!(),

        flat::Expr::WrapCustom(custom_id, content) => {
            let annot::OldType::Custom(fut_custom_id, modes, lts) = fut_ty else {
                unreachable!();
            };
            assert_eq!(custom_id, fut_custom_id);
            todo!()
        }

        flat::Expr::UnwrapCustom(custom_id, wrapped) => {
            // let wrapped_fresh = instantiate_type(customs, constrs, customs[custom_id].content);
            todo!()
        }

        flat::Expr::Intrinsic(intr, arg) => todo!(),

        flat::Expr::ArrayOp(flat::ArrayOp::Get(_, arr_id, idx_id)) => {
            let idx_occur = instantiate_occur_int(&ctx, *idx_id);

            let annot::OldType::Array(mode, lt, item_ty, overlay) = &**ctx.local_binding(*arr_id)
            else {
                unreachable!();
            };
            let ret_ty = apply_overlay(item_ty, overlay);
            mode_bind(constrs, &ret_ty, fut_ty);

            // let item_ty = instantiate_type(customs, constrs, item_ty);

            // annot::Expr::ArrayOp(annot::ArrayOp::Get(item_ty, arr_occur, idx_occur))
            todo!()
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Extract(item_ty, arr_id, idx_id)) => {
            // TODO: apply overlay
            let annot::OldType::HoleArray(mode, _, item_ty, _) = fut_ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, fut_ty);
            let idx_occur = instantiate_occur_int(&ctx, *idx_id);
            todo!()
            // let item_ty = instantiate_type(customs, constrs, item_ty);
            // annot::Expr::ArrayOp(annot::ArrayOp::Extract(item_ty, arr_occur, idx_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Len(item_ty, arr_id)) => {
            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, fut_ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Len(item_ty, arr_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Push(item_ty, arr_id, item_id)) => {
            let annot::OldType::Array(mode, _, _, _) = fut_ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, fut_ty);
            let item_occur = instantiate_occur(&mut ctx, constrs, &path.seq(1), *item_id, fut_ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Push(item_ty, arr_occur, item_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Pop(item_ty, arr_id)) => {
            let annot::OldType::Tuple(ret_items) = fut_ty else {
                unreachable!();
            };
            assert_eq!(ret_items.len(), 2);

            let annot::OldType::Array(mode, _, fut_item_ty, _) = &ret_items[0] else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, fut_ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Pop(item_ty, arr_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Replace(item_ty, hole_id, item_id)) => {
            let annot::OldType::Array(mode, _, _, _) = fut_ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let hole_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *hole_id, fut_ty);
            let item_occur = instantiate_occur(&mut ctx, constrs, &path.seq(1), *item_id, fut_ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Replace(item_ty, hole_occur, item_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Reserve(item_ty, arr_id, cap_id)) => {
            let annot::OldType::Array(mode, _, _, _) = fut_ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, fut_ty);
            let cap_occur = instantiate_occur_int(&ctx, *cap_id);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Reserve(item_ty, arr_occur, cap_occur))
        }

        flat::Expr::IoOp(flat::IoOp::Input) => {
            let annot::OldType::Array(mode, _, item_ty, _) = fut_ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);
            assert!(matches!(**item_ty, annot::OldType::Num(NumType::Byte)));
            annot::Expr::IoOp(annot::IoOp::Input)
        }

        flat::Expr::IoOp(flat::IoOp::Output(arr_id)) => {
            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, fut_ty);
            annot::Expr::IoOp(annot::IoOp::Output(arr_occur))
        }

        flat::Expr::Panic(ret_ty, msg_id) => {
            let msg_occur = instantiate_occur(&mut ctx, constrs, &path.seq(1), *msg_id, fut_ty);
            let ret_ty = instantiate_type(customs, constrs, ret_ty);
            annot::Expr::Panic(ret_ty, msg_occur)
        }

        flat::Expr::ArrayLit(item_ty, item_ids) => {
            let annot::OldType::Array(mode, _, _, _) = fut_ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let item_occurs = item_ids
                .iter()
                .enumerate()
                .map(|(i, item_id)| {
                    instantiate_occur(&mut ctx, constrs, &path.seq(i), *item_id, fut_ty)
                })
                .collect();

            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayLit(item_ty, item_occurs)
        }

        flat::Expr::BoolLit(val) => annot::Expr::BoolLit(*val),

        flat::Expr::ByteLit(val) => annot::Expr::ByteLit(*val),

        flat::Expr::IntLit(val) => annot::Expr::IntLit(*val),

        flat::Expr::FloatLit(val) => annot::Expr::FloatLit(*val),
    };

    (expr_annot, ctx.into_updates())
}

fn add_func_deps(deps: &mut BTreeSet<CustomFuncId>, expr: &flat::Expr) {
    match expr {
        flat::Expr::Call(_, other, _) => {
            deps.insert(*other);
        }
        flat::Expr::Branch(_, cases, _) => {
            for (_, body) in cases {
                add_func_deps(deps, body);
            }
        }
        flat::Expr::LetMany(bindings, _) => {
            for (_, rhs) in bindings {
                add_func_deps(deps, rhs);
            }
        }
        _ => {}
    }
}

struct SolverScc {
    func_sigs: BTreeMap<CustomFuncId, SolverType>,
    constrs: ConstrGraph,
}

fn instantiate_overlay(
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    constrs: &mut ConstrGraph,
    ty: &anon::Type,
) -> SolverOverlay {
    match ty {
        anon::Type::Bool => OldOverlay::Bool,
        anon::Type::Num(num_ty) => OldOverlay::Num(*num_ty),
        anon::Type::Tuple(tys) => OldOverlay::Tuple(
            tys.iter()
                .map(|ty| instantiate_overlay(customs, constrs, ty))
                .collect(),
        ),
        anon::Type::Variants(tys) => {
            OldOverlay::Variants(tys.map_refs(|_, ty| instantiate_overlay(customs, constrs, ty)))
        }
        anon::Type::Custom(id) => annot::OldOverlay::Custom(*id),
        anon::Type::Array(_) => OldOverlay::Array(constrs.fresh_var()),
        anon::Type::HoleArray(_) => OldOverlay::HoleArray(constrs.fresh_var()),
        anon::Type::Boxed(_) => OldOverlay::Boxed(constrs.fresh_var()),
    }
}

// Replaces parameters with fresh variables from the constraint graph.
fn instantiate_type(
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    constrs: &mut ConstrGraph,
    ty: &anon::Type,
) -> SolverType {
    match ty {
        anon::Type::Bool => annot::OldType::Bool,
        anon::Type::Num(num_ty) => annot::OldType::Num(*num_ty),
        anon::Type::Tuple(tys) => annot::OldType::Tuple(
            tys.iter()
                .map(|ty| instantiate_type(customs, constrs, ty))
                .collect(),
        ),
        anon::Type::Variants(tys) => {
            annot::OldType::Variants(tys.map_refs(|_, ty| instantiate_type(customs, constrs, ty)))
        }
        anon::Type::Custom(id) => annot::OldType::Custom(
            *id,
            IdVec::from_count_with(customs[*id].num_mode_params, |_| constrs.fresh_var()),
            IdVec::from_count_with(customs[*id].num_lt_params, |_| Lt::Empty),
        ),
        anon::Type::Array(content_ty) => annot::OldType::Array(
            constrs.fresh_var(),
            Lt::Empty,
            Box::new(instantiate_type(customs, constrs, content_ty)),
            instantiate_overlay(customs, constrs, content_ty),
        ),
        anon::Type::HoleArray(content_ty) => annot::OldType::HoleArray(
            constrs.fresh_var(),
            Lt::Empty,
            Box::new(instantiate_type(customs, constrs, content_ty)),
            instantiate_overlay(customs, constrs, content_ty),
        ),
        anon::Type::Boxed(content_ty) => annot::OldType::Boxed(
            constrs.fresh_var(),
            Lt::Empty,
            Box::new(instantiate_type(customs, constrs, content_ty)),
            instantiate_overlay(customs, constrs, content_ty),
        ),
    }
}

fn instantiate_scc(
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    funcs_annot: &mut IdMap<CustomTypeId, annot::FuncDef>,
    scc: Scc<CustomFuncId>,
) -> SolverScc {
    let mut constrs = ConstrGraph::new();

    match scc.kind {
        SccKind::Acyclic => {
            // Since the SCC is acyclic, we can skip lifetime fixed point iteration
            todo!()
        }
        SccKind::Cyclic => {
            for id in scc.nodes {
                // instantiate_expr(
                //     customs,
                //     globals,
                //     &mut constrs,
                //     &mut LocalContext::new(),
                //     annot::Path::final_(),
                //     ty,
                //     expr,
                // );
            }
        }
    }

    todo!()
}

fn solve_scc(
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    funcs_annot: &mut IdMap<CustomTypeId, annot::FuncDef>,
    scc: Scc<CustomFuncId>,
) {
    let instantiated = instantiate_scc(customs, funcs_annot, scc);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strategy {
    Aggressive,
    AlwaysOwned,        // similar to "Perceus"
    OnlyTrivialBorrows, // similar to "Immutable Beans"
}

pub fn annot_modes(
    program: &flat::Program,
    strat: Strategy,
    progress: impl ProgressLogger,
) -> annot::Program {
    #[id_type]
    struct FuncSccId(usize);

    let mut progress = progress.start_session(Some(program.funcs.len()));

    let customs = parameterize_customs(&program.custom_types);

    let sccs: Sccs<FuncSccId, _> = find_components(program.funcs.count(), |id| {
        let mut deps = BTreeSet::new();
        add_func_deps(&mut deps, &program.funcs[id].body);
        deps
    });

    let mut funcs_annot = IdMap::new();
    for (_, scc) in &sccs {
        solve_scc(&customs, &mut funcs_annot, scc);
        progress.update(scc.nodes.len());
    }

    progress.finish();

    todo!()
}
