use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast::{CustomFuncId, CustomTypeId};
use crate::data::flat_ast::{self as flat, LocalId};
use crate::data::mode_annot_ast2::iter::{CollectOverlayExt, CollectTypeExt, IterExt, IterExt2};
use crate::data::mode_annot_ast2::{
    self as annot, Lt, LtParam, ModeConstr, ModeParam, ModeTerm, Overlay,
};
use crate::util::graph as old_graph; // TODO: switch completely to `id_graph_sccs`
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{id_type, Count, Id, IdMap, IdVec};
use id_graph_sccs::{find_components, Scc, SccKind, Sccs};
use im_rc::OrdMap;
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

    let num_mode_params = Count::from_value(num_stack_params + num_heap_params);
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
                    num_overlay_mode_params: num_mode_params,
                    num_lt_params,
                    content: parameterize(
                        parameterized,
                        num_mode_params,
                        num_mode_params,
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
type SolverOverlay = annot::Overlay<ModeVar>;
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

#[derive(Clone, Debug)]
struct PendingSig {
    arg: SolverType,
    ret: SolverType,
}

#[derive(Clone, Copy, Debug)]
struct GlobalContext<'a> {
    funcs_annot: &'a IdMap<CustomFuncId, annot::FuncDef>,
    sigs_pending: &'a BTreeMap<CustomFuncId, PendingSig>,
}

fn merge_updates(
    ctx: &mut LocalContext<LocalId, SolverType>,
    updates: BTreeMap<LocalId, SolverType>,
) {
    for (id, ty) in updates {
        *ctx.local_binding_mut(id) = ty;
    }
}

struct ContextScratch {
    ctx: OrdMap<LocalId, Rc<SolverType>>,
    updated: BTreeSet<LocalId>,
}

impl ContextScratch {
    fn new(ctx: &OrdMap<LocalId, Rc<SolverType>>) -> Self {
        Self {
            ctx: ctx.clone(),
            updated: BTreeSet::new(),
        }
    }

    fn get_updates(&self) -> BTreeMap<LocalId, Rc<SolverType>> {
        self.updated
            .iter()
            .map(|id| (*id, self.ctx[id].clone()))
            .collect()
    }

    fn insert_left_meet(&mut self, id: LocalId, ty: &SolverType) {
        self.ctx.insert(id, Rc::new(self.ctx[&id].left_meet(ty)));
        self.updated.insert(id);
    }
}

fn handle_occur(
    ty_ctx: &mut ContextScratch,
    constrs: &mut ConstrGraph,
    path: &annot::Path,
    id: LocalId,
    use_ty: &SolverType,
) {
    emit_occur_constrs(constrs, path, &ty_ctx.ctx[&id], use_ty);
    ty_ctx.insert_left_meet(id, use_ty);
}

fn instantiate_expr(
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    globals: GlobalContext,
    constrs: &mut ConstrGraph,
    ty_ctx: &OrdMap<LocalId, Rc<SolverType>>, // TODO: `OrdMap` is slow, use something else
    scope_ctx: &mut LocalContext<LocalId, annot::Path>,
    path: &annot::Path,
    ty: &SolverType,
    expr: &flat::Expr,
) -> (SolverExpr, BTreeMap<LocalId, Rc<SolverType>>) {
    let mut ty_ctx = ContextScratch::new(ty_ctx);

    let expr_annot = match expr {
        flat::Expr::Local(local) => {
            handle_occur(&mut ty_ctx, constrs, path, *local, ty);
            annot::Expr::Local(*local)
        }

        flat::Expr::Call(_purity, func, arg) => {
            handle_occur(&mut ty_ctx, constrs, path, *arg, ty);
            todo!()
        }

        flat::Expr::Branch(discrim, cases, ret_ty) => todo!(),

        flat::Expr::LetMany(bindings, result) => scope_ctx.with_scope(|scope_ctx| {
            let end_of_scope = path.seq(bindings.len());
            let locals = bindings
                .iter()
                .map(|_| scope_ctx.add_local(end_of_scope.clone()));

            todo!()
        }),

        flat::Expr::Tuple(items) => {
            let annot::Type::Tuple(tys) = ty else {
                unreachable!();
            };
            debug_assert_eq!(items.len(), tys.len());
            for (i, (item, ty)) in items.iter().zip(tys.iter()).enumerate().rev() {
                handle_occur(&mut ty_ctx, constrs, &path.seq(i), *item, ty);
            }
            annot::Expr::Tuple(items.clone())
        }

        flat::Expr::TupleField(tuple, idx) => {
            handle_occur(&mut ty_ctx, constrs, &path.seq(0), *tuple, ty);
            annot::Expr::TupleField(*tuple, *idx)
        }

        flat::Expr::WrapVariant(variant_tys, variant_id, content) => todo!(),

        flat::Expr::UnwrapVariant(variant_id, wrapped) => todo!(),

        flat::Expr::WrapBoxed(content, item_ty) => todo!(),

        flat::Expr::UnwrapBoxed(wrapped, item_ty) => todo!(),

        flat::Expr::WrapCustom(custom_id, content) => todo!(),

        flat::Expr::UnwrapCustom(custom_id, wrapped) => todo!(),

        flat::Expr::Intrinsic(intr, arg) => annot::Expr::Intrinsic(*intr, *arg),

        flat::Expr::ArrayOp(flat::ArrayOp::Get(item_ty, arr, idx)) => {
            handle_occur(&mut ty_ctx, constrs, &path.seq(0), *arr, ty);
            handle_occur(&mut ty_ctx, constrs, &path.seq(1), *idx, ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Get(item_ty, *arr, *idx))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Extract(item_ty, arr, idx)) => {
            handle_occur(&mut ty_ctx, constrs, &path.seq(0), *arr, ty);
            handle_occur(&mut ty_ctx, constrs, &path.seq(1), *idx, ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Extract(item_ty, *arr, *idx))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Len(item_ty, arr)) => {
            handle_occur(&mut ty_ctx, constrs, &path.seq(0), *arr, ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Len(item_ty, *arr))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Push(item_ty, arr, item)) => {
            handle_occur(&mut ty_ctx, constrs, &path.seq(0), *arr, ty);
            handle_occur(&mut ty_ctx, constrs, &path.seq(1), *item, ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Push(item_ty, *arr, *item))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Pop(item_ty, arr)) => {
            handle_occur(&mut ty_ctx, constrs, &path.seq(0), *arr, ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Pop(item_ty, *arr))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Replace(item_ty, hole_arr, item)) => {
            handle_occur(&mut ty_ctx, constrs, &path.seq(0), *hole_arr, ty);
            handle_occur(&mut ty_ctx, constrs, &path.seq(1), *item, ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Replace(item_ty, *hole_arr, *item))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Reserve(item_ty, arr, cap)) => {
            handle_occur(&mut ty_ctx, constrs, &path.seq(0), *arr, ty);
            handle_occur(&mut ty_ctx, constrs, &path.seq(1), *cap, ty);
            let item_ty = instantiate_type(customs, constrs, item_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Reserve(item_ty, *arr, *cap))
        }

        flat::Expr::IoOp(flat::IoOp::Input) => todo!(),

        flat::Expr::IoOp(flat::IoOp::Output(arr)) => todo!(),

        flat::Expr::Panic(ret_ty, byte_arr) => todo!(),

        flat::Expr::ArrayLit(item_ty, items) => todo!(),

        flat::Expr::BoolLit(val) => annot::Expr::BoolLit(*val),

        flat::Expr::ByteLit(val) => annot::Expr::ByteLit(*val),

        flat::Expr::IntLit(val) => annot::Expr::IntLit(*val),

        flat::Expr::FloatLit(val) => annot::Expr::FloatLit(*val),
    };

    (expr_annot, ty_ctx.get_updates())
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
