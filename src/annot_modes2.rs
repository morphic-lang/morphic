#![allow(dead_code, unused_variables, unused_imports)]

use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast::{CustomFuncId, CustomTypeId, NumType};
use crate::data::flat_ast::{self as flat, LocalId};
use crate::data::mode_annot_ast2::{
    self as annot, DataKind, Lt, LtParam, ModeConstr, ModeParam, ModeTerm, Overlay,
};
use crate::fixed_point::{self, Signature, SignatureAssumptions};
use crate::util::graph as old_graph; // TODO: switch completely to `id_graph_sccs`
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{id, id_type, Count, Id, IdMap, IdVec};
use id_graph_sccs::{find_components, Scc, SccKind, Sccs};
use std::cell::{RefCell, RefMut};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

struct State<T>(Rc<RefCell<T>>);

impl<T> Clone for State<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

fn state<T>(inner: T) -> State<T> {
    State(Rc::new(RefCell::new(inner)))
}

impl<T> State<T> {
    fn get<'a>(&'a self) -> RefMut<'a, T> {
        self.0.borrow_mut()
    }

    fn take(self) -> Option<T> {
        Rc::into_inner(self.0).map(|cell| cell.into_inner())
    }
}

fn count_lt_params(customs: &IdMap<CustomTypeId, annot::TypeDef>, ty: &anon::Type) -> usize {
    ty.items()
        .map(
            |_, id, _| match customs.get(id) {
                Some(typedef) => typedef.num_lt_params.to_value(),
                // This is a typedef in the same SCC; the reference to it here contributes no additional
                // parameters to the entire SCC.
                None => 0,
            },
            |_, _| 1,
            |_, _, _| 0,
            |_, _| 0,
        )
        .fold(0, |a, b| a + b)
}

fn count_mode_params(
    customs: &IdMap<CustomTypeId, annot::TypeDef>,
    ty: &anon::Type,
) -> (usize, BTreeSet<ModeParam>) {
    let count = state(0);
    let overlay_params = state(BTreeSet::new());

    // It would be nicer to use `fold` like in `count_lt_params`, but we need to update
    // `scc_overlay_params`.
    ty.items().for_each(
        |_, id, _| {
            if let Some(typedef) = customs.get(id) {
                *count.get() += typedef.num_mode_params.to_value();
            }
            // Otherwise, this is a typedef in the same SCC
        },
        |_, _| (),
        |_, id, _| {
            if let Some(typedef) = customs.get(id) {
                overlay_params.get().insert(ModeParam(*count.get()));
                *count.get() += typedef.overlay_params.len();
            }
            // Otherwise, this is a typedef in the same SCC
        },
        |_, _| (),
    );

    let count = *count.get();
    (count, overlay_params.take().unwrap())
}

fn overlay_custom_params(
    parameterized: &IdMap<CustomTypeId, annot::TypeDef>,
    scc_overlay_params: &BTreeSet<ModeParam>,
    next_mode: State<&mut Count<ModeParam>>,
    id: CustomTypeId,
) -> BTreeMap<ModeParam, ModeParam> {
    match parameterized.get(id) {
        Some(typedef) => typedef
            .overlay_params
            .iter()
            .map(|id| (*id, next_mode.get().inc()))
            .collect::<BTreeMap<_, _>>(),
        // This is a typedef in the same SCC; we need to parameterize it by all the SCC
        // parameters
        None => scc_overlay_params.iter().map(|id| (*id, *id)).collect(),
    }
}

fn parameterize_overlay(
    parameterized: &IdMap<CustomTypeId, annot::TypeDef>,
    scc_overlay_params: &BTreeSet<ModeParam>,
    next_mode: &mut Count<ModeParam>,
    ty: &anon::Type,
) -> Overlay<ModeParam> {
    let next_mode = state(next_mode);
    ty.overlay_items()
        .map(
            |id, _| overlay_custom_params(parameterized, scc_overlay_params, next_mode.clone(), id),
            |_| next_mode.get().inc(),
        )
        .collect()
}

fn parameterize_type(
    parameterized: &IdMap<CustomTypeId, annot::TypeDef>,
    scc_mode_count: Count<ModeParam>,
    scc_lt_count: Count<LtParam>,
    scc_overlay_params: &BTreeSet<ModeParam>,
    next_mode: &mut Count<ModeParam>,
    next_lt: &mut Count<LtParam>,
    ty: &anon::Type,
) -> annot::Type<ModeParam, LtParam> {
    let next_mode = state(next_mode);
    let next_lt = state(next_lt);
    ty.items()
        .map(
            |_, id, _| {
                match parameterized.get(id) {
                    Some(typedef) => (
                        IdVec::from_count_with(typedef.num_mode_params, |_| next_mode.get().inc()),
                        IdVec::from_count_with(typedef.num_lt_params, |_| next_lt.get().inc()),
                    ),
                    // This is a typedef in the same SCC; we need to parameterize it by all the SCC
                    // parameters
                    None => (
                        IdVec::from_count_with(scc_mode_count, |id| id),
                        IdVec::from_count_with(scc_lt_count, |id| id),
                    ),
                }
            },
            |_, _| (next_mode.get().inc(), next_lt.get().inc()),
            |_, id, _| {
                overlay_custom_params(parameterized, scc_overlay_params, next_mode.clone(), id)
            },
            |_, _| next_mode.get().inc(),
        )
        .collect()
}

fn parameterize_custom_scc(
    customs: &IdVec<CustomTypeId, flat::CustomTypeDef>,
    parameterized: &IdMap<CustomTypeId, annot::TypeDef>,
    stack_param_counts: &IdMap<CustomTypeId, usize>,
    heap_param_counts: &IdMap<CustomTypeId, usize>,
    scc: &old_graph::Scc<CustomTypeId>,
) -> BTreeMap<CustomTypeId, annot::TypeDef> {
    let (num_mode_params, overlay_params) = scc
        .iter()
        .map(|id| count_mode_params(parameterized, &customs[*id].content))
        .fold((0, BTreeSet::new()), |(a, b), (c, d)| {
            (a + c, b.union(&d).copied().collect())
        });
    let num_mode_params = Count::from_value(num_mode_params);

    let num_lt_params = Count::from_value(
        scc.iter()
            .map(|id| count_lt_params(parameterized, &customs[*id].content))
            .sum(),
    );

    let mut next_mode = Count::new();
    let mut next_lt = Count::new();

    let to_populate = scc
        .iter()
        .map(|id| {
            (
                *id,
                annot::TypeDef {
                    num_mode_params,
                    num_lt_params,
                    overlay_params: overlay_params.clone(),
                    content: parameterize_type(
                        parameterized,
                        num_mode_params,
                        num_lt_params,
                        &overlay_params,
                        &mut next_mode,
                        &mut next_lt,
                        &customs[*id].content,
                    ),
                    overlay: parameterize_overlay(
                        parameterized,
                        &overlay_params,
                        &mut next_mode,
                        &customs[*id].content,
                    ),
                },
            )
        })
        .collect();

    debug_assert_eq!(num_mode_params, next_mode);
    debug_assert_eq!(num_lt_params, next_lt);
    to_populate
}

fn parameterize_customs(customs: &flat::CustomTypes) -> IdVec<CustomTypeId, annot::TypeDef> {
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

type SolverType = annot::Type<ModeVar, Lt>;
type SolverOccur = annot::Occur<ModeVar, Lt>;
type SolverOverlay = annot::Overlay<ModeVar>;
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

fn mode_bind(constrs: &mut ConstrGraph, ty1: &SolverType, ty2: &SolverType) {
    let constrs = state(constrs);
    ty1.items().zip(ty2.items()).for_each(
        |_, _, ((ms1, _), (ms2, _))| {
            for ((_, m1), (_, m2)) in ms1.iter().zip(ms2.iter()) {
                constrs.get().enforce_eq(*m1, *m2);
            }
        },
        |_, ((m1, _), (m2, _))| {
            constrs.get().enforce_eq(*m1, *m2);
        },
        |_, _, (ms1, ms2)| {
            for ((_, m1), (_, m2)) in ms1.iter().zip(ms2.iter()) {
                constrs.get().enforce_eq(*m1, *m2);
            }
        },
        |_, (m1, m2)| {
            constrs.get().enforce_eq(*m1, *m2);
        },
    )
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

fn emit_occur_constrs(
    constrs: &mut ConstrGraph,
    path: &annot::Path,
    binding_ty: &SolverType,
    fut_ty: &SolverType,
) {
    let constrs = state(constrs);
    binding_ty.items().zip(fut_ty.items()).for_each(
        |kind, id, ((ms1, lts1), (ms2, lts2))| {},
        |kind, ((m1, lt1), (m2, lt2))| {},
        |kind, id, (ms1, ms2)| {},
        |kind, (m1, m2)| {},
    );
    // match (binding_ty, fut_ty) {
    //     (annot::Type::Bool, annot::Type::Bool) => {}
    //     (annot::Type::Num(_), annot::Type::Num(_)) => {}
    //     (annot::Type::Tuple(tys1), annot::Type::Tuple(tys2)) => {
    //         for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
    //             emit_occur_constrs(constrs, path, ty1, ty2);
    //         }
    //     }
    //     (annot::Type::Variants(tys1), annot::Type::Variants(tys2)) => {
    //         for ((_, ty1), (_, ty2)) in tys1.iter().zip(tys2.iter()) {
    //             emit_occur_constrs(constrs, path, ty1, ty2);
    //         }
    //     }
    //     (annot::Type::Array(m1, lt1, ty1, o1), annot::Type::Array(m2, lt2, ty2, o2)) => {
    //         emit_occur_constr(constrs, path, lt1, lt2, *m1, *m2);
    //         emit_occur_constrs_heap(constrs, path, ty1, ty2);
    //         emit_occur_constrs_overlay(constrs, path, o1, o2);
    //     }
    //     _ => panic!("incompatible types"),
    // }
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
        (anon::Type::Bool, annot::Type::Bool) => true,
        (anon::Type::Num(num_ty1), annot::Type::Num(num_ty2)) => num_ty1 == num_ty2,
        (anon::Type::Tuple(tys1), annot::Type::Tuple(tys2)) => {
            tys1.len() == tys2.len()
                && tys1
                    .iter()
                    .zip(tys2.iter())
                    .all(|(ty1, ty2)| same_shape(ty1, ty2))
        }
        (anon::Type::Variants(tys1), annot::Type::Variants(tys2)) => {
            tys1.len() == tys2.len()
                && tys1
                    .iter()
                    .zip(tys2.iter())
                    .all(|((_, ty1), (_, ty2))| same_shape(ty1, ty2))
        }
        (anon::Type::Custom(id1), annot::Type::Custom(id2, _, _)) => id1 == id2,
        (anon::Type::Array(ty1), annot::Type::Array(_, _, ty2, _)) => same_shape(ty1, ty2),
        (anon::Type::HoleArray(ty1), annot::Type::HoleArray(_, _, ty2, _)) => same_shape(ty1, ty2),
        (anon::Type::Boxed(ty1), annot::Type::Boxed(_, _, ty2, _)) => same_shape(ty1, ty2),
        _ => false,
    }
}

fn apply_overlay(ty: &SolverType, overlay: &SolverOverlay) -> SolverType {
    todo!()
    // match (ty, overlay) {
    //     (annot::Type::Bool, annot::Overlay::Bool) => annot::Type::Bool,
    //     (annot::Type::Num(num_ty1), annot::Overlay::Num(num_ty2)) => {
    //         assert_eq!(num_ty1, num_ty2);
    //         annot::Type::Num(*num_ty1)
    //     }
    //     (annot::Type::Tuple(tys), annot::Overlay::Tuple(os)) => {
    //         assert_eq!(tys.len(), os.len());
    //         let tys = tys
    //             .iter()
    //             .zip(os.iter())
    //             .map(|(ty, o)| apply_overlay(ty, o))
    //             .collect();
    //         annot::Type::Tuple(tys)
    //     }
    //     (annot::Type::Variants(tys), annot::Overlay::Variants(os)) => {
    //         assert_eq!(tys.len(), os.len());
    //         let tys = tys
    //             .values()
    //             .zip(os.values())
    //             .map(|(ty, o)| apply_overlay(ty, o))
    //             .collect();
    //         annot::Type::Variants(IdVec::from_vec(tys))
    //     }
    //     (annot::Type::Custom(id1, modes, lts), annot::Overlay::Custom(id2)) => {
    //         assert_eq!(id1, id2);
    //         annot::Type::Custom(*id1, modes.clone(), lts.clone())
    //     }
    //     (annot::Type::Array(_, lt, ty, o), annot::Overlay::Array(m)) => {
    //         annot::Type::Array(*m, lt.clone(), ty.clone(), o.clone())
    //     }
    //     (annot::Type::HoleArray(_, lt, ty, o), annot::Overlay::HoleArray(m)) => {
    //         annot::Type::HoleArray(*m, lt.clone(), ty.clone(), o.clone())
    //     }
    //     (annot::Type::Boxed(_, lt, ty, o), annot::Overlay::Boxed(m)) => {
    //         annot::Type::Boxed(*m, lt.clone(), ty.clone(), o.clone())
    //     }
    //     _ => panic!("type and overlay are incompatible"),
    // }
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
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
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
        annot::Type::Num(NumType::Int)
    ));
    annot::Occur {
        local: id,
        ty: annot::Type::Num(NumType::Int),
    }
}

fn instantiate_occur_array(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    ctx: &mut TrackedContext,
    updates: &mut LocalUpdates,
    constrs: &mut ConstrGraph,
    path: &annot::Path,
    item_ty: &anon::Type,
    id: LocalId,
) -> SolverOccur {
    let occur_ty = annot::Type::Array(
        constrs.fresh_var(),
        path.as_lt(),
        Box::new(instantiate_type(customs, constrs, item_ty)),
        instantiate_overlay(customs, constrs, item_ty),
    );
    instantiate_occur(ctx, constrs, path, id, &occur_ty)
}

fn instantiate_occur_hole(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    ctx: &mut TrackedContext,
    constrs: &mut ConstrGraph,
    path: &annot::Path,
    item_ty: &anon::Type,
    id: LocalId,
) -> SolverOccur {
    let occur_ty = annot::Type::Array(
        constrs.fresh_var(),
        path.as_lt(),
        Box::new(instantiate_type(customs, constrs, item_ty)),
        instantiate_overlay(customs, constrs, item_ty),
    );
    instantiate_occur(ctx, constrs, path, id, &occur_ty)
}

fn freshen_type(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    constrs: &mut ConstrGraph,
    ty: &annot::Type<ModeParam, LtParam>,
) -> SolverType {
    match ty {
        annot::Type::Bool => annot::Type::Bool,
        annot::Type::Num(num_ty) => annot::Type::Num(*num_ty),
        annot::Type::Tuple(tys) => {
            let tys = tys
                .iter()
                .map(|ty| freshen_type(customs, constrs, ty))
                .collect();
            annot::Type::Tuple(tys)
        }
        annot::Type::Variants(tys) => {
            let tys = tys.map_refs(|_, ty| freshen_type(customs, constrs, ty));
            annot::Type::Variants(tys)
        }
        annot::Type::Custom(id, modes, lts) => {
            let typedef = &customs[*id];
            let modes = IdVec::from_count_with(typedef.num_mode_params, |_| constrs.fresh_var());
            let lts = IdVec::from_count_with(typedef.num_lt_params, |_| Lt::Empty);
            annot::Type::Custom(*id, modes, lts)
        }
        annot::Type::Array(mode, lt, ty, o) => {
            // let m = constrs.fresh_var();
            // let ty = Box::new(freshen_type(customs, constrs, ty));
            // let o = instantiate_overlay(customs, constrs, ty);
            // annot::Type::Array(m, Lt::Empty, ty, o)
            todo!()
        }
        annot::Type::HoleArray(mode, lt, ty, o) => {
            // let m = constrs.fresh_var();
            // let ty = Box::new(freshen_type(customs, constrs, ty));
            // let o = instantiate_overlay(customs, constrs, ty);
            // annot::Type::HoleArray(m, Lt::Empty, ty, o)
            todo!()
        }
        annot::Type::Boxed(mode, lt, ty, o) => {
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
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
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
            let annot::Type::Tuple(fut_tys) = fut_ty else {
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
                if let annot::Type::Variants(variant_tys) = &**ctx.local_binding(*wrapped) {
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
            let annot::Type::Custom(fut_custom_id, modes, lts) = fut_ty else {
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

            let annot::Type::Array(mode, lt, item_ty, overlay) = &**ctx.local_binding(*arr_id)
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
            let annot::Type::HoleArray(mode, _, item_ty, _) = fut_ty else {
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
            let annot::Type::Array(mode, _, _, _) = fut_ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, fut_ty);
            let item_occur = instantiate_occur(&mut ctx, constrs, &path.seq(1), *item_id, fut_ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Push(item_ty, arr_occur, item_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Pop(item_ty, arr_id)) => {
            let annot::Type::Tuple(ret_items) = fut_ty else {
                unreachable!();
            };
            assert_eq!(ret_items.len(), 2);

            let annot::Type::Array(mode, _, fut_item_ty, _) = &ret_items[0] else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, fut_ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Pop(item_ty, arr_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Replace(item_ty, hole_id, item_id)) => {
            let annot::Type::Array(mode, _, _, _) = fut_ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let hole_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *hole_id, fut_ty);
            let item_occur = instantiate_occur(&mut ctx, constrs, &path.seq(1), *item_id, fut_ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Replace(item_ty, hole_occur, item_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Reserve(item_ty, arr_id, cap_id)) => {
            let annot::Type::Array(mode, _, _, _) = fut_ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, fut_ty);
            let cap_occur = instantiate_occur_int(&ctx, *cap_id);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Reserve(item_ty, arr_occur, cap_occur))
        }

        flat::Expr::IoOp(flat::IoOp::Input) => {
            let annot::Type::Array(mode, _, item_ty, _) = fut_ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);
            assert!(matches!(**item_ty, annot::Type::Num(NumType::Byte)));
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
            let annot::Type::Array(mode, _, _, _) = fut_ty else {
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
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    constrs: &mut ConstrGraph,
    ty: &anon::Type,
) -> SolverOverlay {
    todo!()
    // match ty {
    //     anon::Type::Bool => Overlay::Bool,
    //     anon::Type::Num(num_ty) => Overlay::Num(*num_ty),
    //     anon::Type::Tuple(tys) => Overlay::Tuple(
    //         tys.iter()
    //             .map(|ty| instantiate_overlay(customs, constrs, ty))
    //             .collect(),
    //     ),
    //     anon::Type::Variants(tys) => {
    //         Overlay::Variants(tys.map_refs(|_, ty| instantiate_overlay(customs, constrs, ty)))
    //     }
    //     anon::Type::Custom(id) => annot::Overlay::Custom(
    //         *id,
    //         IdVec::from_count_with(customs[*id].num_overlay_mode_params, |_| {
    //             constrs.fresh_var()
    //         }),
    //     ),
    //     anon::Type::Array(_) => Overlay::Array(constrs.fresh_var()),
    //     anon::Type::HoleArray(_) => Overlay::HoleArray(constrs.fresh_var()),
    //     anon::Type::Boxed(_) => Overlay::Boxed(constrs.fresh_var()),
    // }
}

// Replaces parameters with fresh variables from the constraint graph.
fn instantiate_type(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    constrs: &mut ConstrGraph,
    ty: &anon::Type,
) -> SolverType {
    match ty {
        anon::Type::Bool => annot::Type::Bool,
        anon::Type::Num(num_ty) => annot::Type::Num(*num_ty),
        anon::Type::Tuple(tys) => annot::Type::Tuple(
            tys.iter()
                .map(|ty| instantiate_type(customs, constrs, ty))
                .collect(),
        ),
        anon::Type::Variants(tys) => {
            annot::Type::Variants(tys.map_refs(|_, ty| instantiate_type(customs, constrs, ty)))
        }
        anon::Type::Custom(id) => annot::Type::Custom(
            *id,
            IdVec::from_count_with(customs[*id].num_mode_params, |_| constrs.fresh_var()),
            IdVec::from_count_with(customs[*id].num_lt_params, |_| Lt::Empty),
        ),
        anon::Type::Array(content_ty) => annot::Type::Array(
            constrs.fresh_var(),
            Lt::Empty,
            Box::new(instantiate_type(customs, constrs, content_ty)),
            instantiate_overlay(customs, constrs, content_ty),
        ),
        anon::Type::HoleArray(content_ty) => annot::Type::HoleArray(
            constrs.fresh_var(),
            Lt::Empty,
            Box::new(instantiate_type(customs, constrs, content_ty)),
            instantiate_overlay(customs, constrs, content_ty),
        ),
        anon::Type::Boxed(content_ty) => annot::Type::Boxed(
            constrs.fresh_var(),
            Lt::Empty,
            Box::new(instantiate_type(customs, constrs, content_ty)),
            instantiate_overlay(customs, constrs, content_ty),
        ),
    }
}

fn instantiate_scc(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    funcs_annot: &mut IdMap<CustomTypeId, annot::FuncDef>,
    scc: Scc<CustomFuncId>,
) -> SolverScc {
    let constrs = ConstrGraph::new();

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
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
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
