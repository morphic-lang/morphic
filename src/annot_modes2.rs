use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast::{CustomFuncId, CustomTypeId, NumType};
use crate::data::flat_ast::{self as flat, LocalId};
use crate::data::mode_annot_ast2::{
    self as annot, Lt, LtParam, ModeConstr, ModeParam, ModeTerm, Overlay,
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
) -> Overlay<ModeParam> {
    match ty {
        anon::Type::Bool => Overlay::Bool,
        anon::Type::Num(num_ty) => Overlay::Num(*num_ty),
        anon::Type::Tuple(tys) => Overlay::Tuple(
            tys.iter()
                .map(|ty| fresh_overlay(scc_overlay_mode_count, fresh_mode, ty))
                .collect(),
        ),
        anon::Type::Variants(tys) => Overlay::Variants(
            tys.map_refs(|_, ty| fresh_overlay(scc_overlay_mode_count, fresh_mode, ty)),
        ),
        anon::Type::Custom(id) => Overlay::Custom(*id),
        anon::Type::Array(_) => Overlay::Array(fresh_mode.inc()),
        anon::Type::HoleArray(_) => Overlay::HoleArray(fresh_mode.inc()),
        anon::Type::Boxed(_) => Overlay::Boxed(fresh_mode.inc()),
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
) -> annot::Type<ModeParam, LtParam> {
    match ty {
        anon::Type::Bool => annot::Type::Bool,
        anon::Type::Num(num_ty) => annot::Type::Num(*num_ty),
        anon::Type::Tuple(tys) => annot::Type::Tuple(
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
        anon::Type::Variants(tys) => annot::Type::Variants(tys.map_refs(|_, ty| {
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
            Some(typedef) => annot::Type::Custom(
                *id,
                fresh_params(typedef.num_mode_params, fresh_mode),
                fresh_params(typedef.num_lt_params, fresh_lt),
            ),
            // This is a typedef in the same SCC; we need to parameterize it by all the SCC
            // parameters
            None => annot::Type::Custom(
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
            annot::Type::Array(
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
            annot::Type::HoleArray(
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
            annot::Type::Boxed(
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

fn mode_bind_overlays(constrs: &mut ConstrGraph, o1: &SolverOverlay, o2: &SolverOverlay) {
    match (o1, o2) {
        (Overlay::Bool, Overlay::Bool) => {}
        (Overlay::Num(_), Overlay::Num(_)) => {}
        (Overlay::Tuple(os1), Overlay::Tuple(os2)) => {
            for (o1, o2) in os1.iter().zip(os2.iter()) {
                mode_bind_overlays(constrs, o1, o2);
            }
        }
        (Overlay::Variants(os1), Overlay::Variants(os2)) => {
            for ((_, o1), (_, o2)) in os1.iter().zip(os2.iter()) {
                mode_bind_overlays(constrs, o1, o2);
            }
        }
        (Overlay::Array(m1), Overlay::Array(m2)) => {
            constrs.enforce_eq(*m1, *m2);
        }
        (Overlay::HoleArray(m1), Overlay::HoleArray(m2)) => {
            constrs.enforce_eq(*m1, *m2);
        }
        (Overlay::Boxed(m1), Overlay::Boxed(m2)) => {
            constrs.enforce_eq(*m1, *m2);
        }
        _ => panic!("incompatible overlays"),
    }
}

fn mode_bind(constrs: &mut ConstrGraph, ty1: &SolverType, ty2: &SolverType) {
    match (ty1, ty2) {
        (annot::Type::Bool, annot::Type::Bool) => {}
        (annot::Type::Num(_), annot::Type::Num(_)) => {}
        (annot::Type::Tuple(tys1), annot::Type::Tuple(tys2)) => {
            for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
                mode_bind(constrs, ty1, ty2);
            }
        }
        (annot::Type::Variants(tys1), annot::Type::Variants(tys2)) => {
            for ((_, ty1), (_, ty2)) in tys1.iter().zip(tys2.iter()) {
                mode_bind(constrs, ty1, ty2);
            }
        }
        (annot::Type::Array(m1, _lt1, ty1, o1), annot::Type::Array(m2, _lt2, ty2, o2)) => {
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
    use_ty: &SolverType,
) {
    todo!()
}

fn emit_occur_constrs(
    constrs: &mut ConstrGraph,
    path: &annot::Path,
    binding_ty: &SolverType,
    use_ty: &SolverType,
) {
    match (binding_ty, use_ty) {
        (annot::Type::Bool, annot::Type::Bool) => {}
        (annot::Type::Num(_), annot::Type::Num(_)) => {}
        (annot::Type::Tuple(tys1), annot::Type::Tuple(tys2)) => {
            for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
                emit_occur_constrs(constrs, path, ty1, ty2);
            }
        }
        (annot::Type::Variants(tys1), annot::Type::Variants(tys2)) => {
            for ((_, ty1), (_, ty2)) in tys1.iter().zip(tys2.iter()) {
                emit_occur_constrs(constrs, path, ty1, ty2);
            }
        }
        (annot::Type::Array(m1, lt1, ty1, o1), annot::Type::Array(m2, lt2, ty2, o2)) => {
            emit_occur_constr(constrs, path, lt1, lt2, *m1, *m2);
            emit_occur_constrs_heap(constrs, path, ty1, ty2);
            emit_occur_constrs_overlay(constrs, path, o1, o2);
        }
        _ => panic!("incompatible types"),
    }
}

mod context {
    use id_collections::{Count, Id};
    use im_rc::OrdMap;
    use std::collections::{BTreeMap, BTreeSet};
    use std::rc::Rc;

    #[derive(Clone, Debug)]
    pub struct ImmutContext<Var: Id, T> {
        count: Count<Var>,
        stack: OrdMap<Var, Rc<T>>, // TODO: `OrdMap` is slow, use something else.
    }

    impl<Var: Id, T: Clone> ImmutContext<Var, T> {
        pub fn new() -> Self {
            ImmutContext {
                count: Count::new(),
                stack: OrdMap::new(),
            }
        }

        pub fn local_binding(&self, local: Var) -> &Rc<T> {
            &self.stack[&local]
        }

        pub fn add_local(&mut self, binding: T) -> Var {
            let id = self.count.inc();
            self.stack.insert(id, Rc::new(binding));
            id
        }

        fn update(&mut self, local: Var, binding: Rc<T>) {
            let old = self.stack.insert(local, binding);
            assert!(old.is_some());
        }
    }

    #[derive(Clone, Debug)]
    pub struct TrackedContext<Var: Id, T> {
        inner: ImmutContext<Var, T>,
        updates: BTreeSet<Var>,
    }

    impl<Var: Id, T: Clone> TrackedContext<Var, T> {
        pub fn new(ctx: &ImmutContext<Var, T>) -> Self {
            Self {
                inner: ctx.clone(),
                updates: BTreeSet::new(),
            }
        }

        pub fn as_untracked(&self) -> &ImmutContext<Var, T> {
            &self.inner
        }

        pub fn local_binding(&self, local: Var) -> &T {
            self.inner.local_binding(local)
        }

        pub fn add_local(&mut self, binding: T) -> Var {
            let id = self.inner.add_local(binding);
            self.updates.insert(id);
            id
        }

        pub fn update(&mut self, local: Var, binding: T) {
            self.inner.update(local, Rc::new(binding));
            self.updates.insert(local);
        }

        pub fn update_all(&mut self, updates: BTreeMap<Var, Rc<T>>) {
            for (id, binding) in updates {
                self.inner.update(id, binding);
            }
        }

        pub fn get_updates(&self) -> BTreeMap<Var, Rc<T>> {
            self.updates
                .iter()
                .map(|id| (*id, self.inner.local_binding(*id).clone()))
                .collect()
        }
    }
}

use context::{ImmutContext, TrackedContext};

fn merge_updates(
    lhs: &mut BTreeMap<LocalId, Rc<SolverType>>,
    rhs: &BTreeMap<LocalId, Rc<SolverType>>,
) {
    for (id, rhs_ty) in rhs {
        match lhs.get(id) {
            Some(lhs_ty) => {
                lhs.insert(*id, Rc::new(lhs_ty.left_meet(rhs_ty)));
            }
            None => {
                lhs.insert(*id, rhs_ty.clone());
            }
        }
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
                    .all(|((id1, ty1), (id2, ty2))| id1 == id2 && same_shape(ty1, ty2))
        }
        (anon::Type::Custom(id1), annot::Type::Custom(id2, _, _)) => id1 == id2,
        (anon::Type::Array(ty1), annot::Type::Array(_, _, ty2, _)) => same_shape(ty1, ty2),
        (anon::Type::HoleArray(ty1), annot::Type::HoleArray(_, _, ty2, _)) => same_shape(ty1, ty2),
        (anon::Type::Boxed(ty1), annot::Type::Boxed(_, _, ty2, _)) => same_shape(ty1, ty2),
        _ => false,
    }
}

fn apply_overlay(ty: &SolverType, overlay: &SolverOverlay) -> SolverType {
    match (ty, overlay) {
        (annot::Type::Bool, annot::Overlay::Bool) => annot::Type::Bool,
        (annot::Type::Num(num_ty1), annot::Overlay::Num(num_ty2)) => {
            assert_eq!(num_ty1, num_ty2);
            annot::Type::Num(*num_ty1)
        }
        (annot::Type::Tuple(tys), annot::Overlay::Tuple(os)) => {
            assert_eq!(tys.len(), os.len());
            let tys = tys
                .iter()
                .zip(os.iter())
                .map(|(ty, o)| apply_overlay(ty, o))
                .collect();
            annot::Type::Tuple(tys)
        }
        (annot::Type::Variants(tys), annot::Overlay::Variants(os)) => {
            assert_eq!(tys.len(), os.len());
            let tys = tys
                .values()
                .zip(os.values())
                .map(|(ty, o)| apply_overlay(ty, o))
                .collect();
            annot::Type::Variants(IdVec::from_vec(tys))
        }
        (annot::Type::Custom(id1, modes, lts), annot::Overlay::Custom(id2)) => {
            assert_eq!(id1, id2);
            annot::Type::Custom(*id1, modes.clone(), lts.clone())
        }
        (annot::Type::Array(_, lt, ty, o), annot::Overlay::Array(m)) => {
            annot::Type::Array(*m, lt.clone(), ty.clone(), o.clone())
        }
        (annot::Type::HoleArray(_, lt, ty, o), annot::Overlay::HoleArray(m)) => {
            annot::Type::HoleArray(*m, lt.clone(), ty.clone(), o.clone())
        }
        (annot::Type::Boxed(_, lt, ty, o), annot::Overlay::Boxed(m)) => {
            annot::Type::Boxed(*m, lt.clone(), ty.clone(), o.clone())
        }
        _ => panic!("type and overlay are incompatible"),
    }
}

fn instantiate_occur(
    ctx: &mut TrackedContext<LocalId, SolverType>,
    constrs: &mut ConstrGraph,
    path: &annot::Path,
    id: LocalId,
    use_ty: &SolverType,
) -> SolverOccur {
    emit_occur_constrs(constrs, path, ctx.local_binding(id), use_ty);
    let old_ty = ctx.local_binding(id).clone();
    ctx.update(id, old_ty.left_meet(use_ty));
    annot::Occur {
        local: id,
        ty: old_ty,
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

fn instantiate_expr(
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    sigs: &SignatureAssumptions<CustomFuncId, annot::FuncDef>,
    constrs: &mut ConstrGraph,
    ctx: &ImmutContext<LocalId, SolverType>,
    scopes: &mut LocalContext<LocalId, annot::Path>,
    path: annot::Path,
    ty: &SolverType,
    expr: &flat::Expr,
) -> (SolverExpr, BTreeMap<LocalId, Rc<SolverType>>) {
    let mut ctx = TrackedContext::new(ctx);

    let expr_annot = match expr {
        flat::Expr::Local(local) => {
            let occur = instantiate_occur(&mut ctx, constrs, &path, *local, ty);
            annot::Expr::Local(occur)
        }

        flat::Expr::Call(_purity, func, arg) => {
            /*/
            instantiate_occur(&mut ctx, constrs, &path, *arg, ty);
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

        flat::Expr::Branch(discrim, cases, ret_ty) => {
            /*
            let mut updates = BTreeMap::new();
            let mut cases_annot = Vec::new();
            for (i, (cond, body)) in cases.iter().enumerate() {
                let branch_path = path.par(i, cases.len());
                let cond_annot = instantiate_condition(customs, constrs, cond);
                let (body_annot, body_updates) = instantiate_expr(
                    customs,
                    globals,
                    constrs,
                    &ctx.as_untracked(),
                    scopes,
                    branch_path,
                    ty,
                    body,
                );
                merge_updates(&mut updates, &body_updates);
                cases_annot.push((cond_annot, body_annot));
            }

            debug_assert!(same_shape(ret_ty, ty));
            annot::Expr::Branch(*discrim, cases_annot, ty.clone())
            */
            todo!()
        }

        flat::Expr::LetMany(bindings, result) => scopes.with_scope(|scopes| {
            /*
            let end_of_scope = path.seq(bindings.len());

            let mut locals = Vec::new();
            for (binding_ty, _) in bindings {
                let id1 = scopes.add_local(end_of_scope.clone());
                let id2 = if id1 == *result {
                    ctx.add_local(instantiate_type(customs, constrs, binding_ty))
                } else {
                    ctx.add_local(ty.clone())
                };
                assert_eq!(id1, id2);
                locals.push(id1);
            }

            let mut exprs_annot = Vec::new();
            for (i, (_, binding_expr)) in bindings.iter().enumerate().rev() {
                let (expr_annot, updates) = instantiate_expr(
                    customs,
                    globals,
                    constrs,
                    &ctx.as_untracked(),
                    scopes,
                    path.seq(i),
                    ty,
                    binding_expr,
                );
                ctx.update_all(updates);
                exprs_annot.push(expr_annot);
            }

            let new_bindings = locals
                .into_iter()
                .zip(exprs_annot.into_iter())
                .map(|(local, expr_annot)| (ctx.local_binding(local).clone(), expr_annot))
                .collect();

            annot::Expr::LetMany(new_bindings, *result)
            */
            todo!()
        }),

        flat::Expr::Tuple(items) => {
            /*
            let annot::Type::Tuple(tys) = ty else {
                unreachable!();
            };
            debug_assert_eq!(items.len(), tys.len());
            for (i, (item, ty)) in items.iter().zip(tys.iter()).enumerate().rev() {
                instantiate_occur(&mut ctx, constrs, &path.seq(i), *item, ty);
            }
            annot::Expr::Tuple(items.clone())
            */
            todo!()
        }

        flat::Expr::TupleField(tuple_id, idx) => {
            let tuple_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *tuple_id, ty);
            annot::Expr::TupleField(tuple_occur, *idx)
        }

        flat::Expr::WrapVariant(variant_tys, variant_id, content) => todo!(),

        flat::Expr::UnwrapVariant(variant_id, wrapped) => todo!(),

        flat::Expr::WrapBoxed(content, item_ty) => todo!(),

        flat::Expr::UnwrapBoxed(wrapped, item_ty) => todo!(),

        flat::Expr::WrapCustom(custom_id, content) => todo!(),

        flat::Expr::UnwrapCustom(custom_id, wrapped) => todo!(),

        flat::Expr::Intrinsic(intr, arg) => todo!(),

        flat::Expr::ArrayOp(flat::ArrayOp::Get(item_ty, arr_id, idx_id)) => {
            // TODO: apply overlay
            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, ty);
            let idx_occur = instantiate_occur(&mut ctx, constrs, &path.seq(1), *idx_id, ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Get(item_ty, arr_occur, idx_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Extract(item_ty, arr_id, idx_id)) => {
            // TODO: apply overlay
            let annot::Type::HoleArray(mode, _, _, _) = ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, ty);
            let idx_occur = instantiate_occur(&mut ctx, constrs, &path.seq(1), *idx_id, ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Extract(item_ty, arr_occur, idx_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Len(item_ty, arr_id)) => {
            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Len(item_ty, arr_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Push(item_ty, arr_id, item_id)) => {
            let annot::Type::Array(mode, _, _, _) = ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, ty);
            let item_occur = instantiate_occur(&mut ctx, constrs, &path.seq(1), *item_id, ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Push(item_ty, arr_occur, item_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Pop(item_ty, arr_id)) => {
            // TODO: apply overlay
            let annot::Type::Tuple(ret_items) = ty else {
                unreachable!();
            };
            assert!(ret_items.len() == 2);
            let annot::Type::Array(mode, _, _, _) = &ret_items[0] else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Pop(item_ty, arr_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Replace(item_ty, hole_id, item_id)) => {
            let annot::Type::Array(mode, _, _, _) = ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let hole_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *hole_id, ty);
            let item_occur = instantiate_occur(&mut ctx, constrs, &path.seq(1), *item_id, ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Replace(item_ty, hole_occur, item_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Reserve(item_ty, arr_id, cap_id)) => {
            let annot::Type::Array(mode, _, _, _) = ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, ty);
            let cap_occur = instantiate_occur(&mut ctx, constrs, &path.seq(1), *cap_id, ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Reserve(item_ty, arr_occur, cap_occur))
        }

        flat::Expr::IoOp(flat::IoOp::Input) => {
            let annot::Type::Array(mode, _, item_ty, _) = ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);
            assert!(matches!(**item_ty, annot::Type::Num(NumType::Byte)));
            annot::Expr::IoOp(annot::IoOp::Input)
        }

        flat::Expr::IoOp(flat::IoOp::Output(arr_id)) => {
            let arr_occur = instantiate_occur(&mut ctx, constrs, &path.seq(0), *arr_id, ty);
            annot::Expr::IoOp(annot::IoOp::Output(arr_occur))
        }

        flat::Expr::Panic(ret_ty, msg_id) => {
            let msg_occur = instantiate_occur(&mut ctx, constrs, &path.seq(1), *msg_id, ty);
            let ret_ty = instantiate_type(customs, constrs, ret_ty);
            annot::Expr::Panic(ret_ty, msg_occur)
        }

        flat::Expr::ArrayLit(item_ty, item_ids) => {
            let annot::Type::Array(mode, _, _, _) = ty else {
                unreachable!();
            };
            constrs.enforce_owned(*mode);

            let item_occurs = item_ids
                .iter()
                .enumerate()
                .map(|(i, item_id)| {
                    instantiate_occur(&mut ctx, constrs, &path.seq(i), *item_id, ty)
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

    (expr_annot, ctx.get_updates())
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
        anon::Type::Bool => Overlay::Bool,
        anon::Type::Num(num_ty) => Overlay::Num(*num_ty),
        anon::Type::Tuple(tys) => Overlay::Tuple(
            tys.iter()
                .map(|ty| instantiate_overlay(customs, constrs, ty))
                .collect(),
        ),
        anon::Type::Variants(tys) => {
            Overlay::Variants(tys.map_refs(|_, ty| instantiate_overlay(customs, constrs, ty)))
        }
        anon::Type::Custom(id) => annot::Overlay::Custom(*id),
        anon::Type::Array(_) => Overlay::Array(constrs.fresh_var()),
        anon::Type::HoleArray(_) => Overlay::HoleArray(constrs.fresh_var()),
        anon::Type::Boxed(_) => Overlay::Boxed(constrs.fresh_var()),
    }
}

// Replaces parameters with fresh variables from the constraint graph.
fn instantiate_type(
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
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
