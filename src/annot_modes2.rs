//! This module implements the specializing variant of first compiler pass described in the borrow
//! inference paper. A signficant proportion of the machinery is dedicated to specialization. The
//! core logic for the pass is contained in `instantiate_expr`.

use crate::data::anon_sum_ast as anon;
use crate::data::borrow_spec as spec;
use crate::data::first_order_ast::{CustomFuncId, CustomTypeId, NumType, VariantId};
use crate::data::flat_ast::{self as flat, CustomTypeSccId, LocalId};
use crate::data::intrinsics as intr;
use crate::data::mode_annot_ast2::{
    self as annot, CollectLtData, CollectModeData, CollectOverlay, Lt, LtData, LtParam, Mode,
    ModeData, ModeParam, ModeSolution, ModeVar, Occur, Overlay, SlotId,
};
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::intrinsic_config::intrinsic_sig;
use crate::pretty_print::utils::{CustomTypeRenderer, FuncRenderer};
use crate::util::graph as old_graph; // TODO: switch completely to `id_graph_sccs`
use crate::util::immut_context as immut;
use crate::util::inequality_graph2 as in_eq;
use crate::util::iter::IterExt;
use crate::util::local_context::LocalContext;
use crate::util::map_ext::MapRef;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{id_type, Count, IdMap, IdVec};
use id_graph_sccs::{find_components, Scc, SccKind, Sccs};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

type ImmutContext = immut::ImmutContext<LocalId, annot::Type<ModeVar, Lt>>;
type LocalUpdates = immut::LocalUpdates<LocalId, annot::Type<ModeVar, Lt>>;
type TrackedContext = immut::TrackedContext<LocalId, annot::Type<ModeVar, Lt>>;

// It is crucial that RC specialization (the next pass) does not inhibit tail calls by inserting
// retains/releases after them. To that end, this pass must handle tail calls specially during
// constraint generation. The machinery here is duplicative of the machinery during the actual tail
// call elimination pass, but it is better to recompute later which calls are tail in case we
// accidently *do* inhibit such a call.

fn last_index<T>(slice: &[T]) -> Option<usize> {
    if slice.is_empty() {
        None
    } else {
        Some(slice.len() - 1)
    }
}

// This function should only be called on 'expr' when the expression occurs in tail position.
fn add_tail_call_deps(deps: &mut BTreeSet<CustomFuncId>, vars_in_scope: usize, expr: &flat::Expr) {
    match expr {
        flat::Expr::Call(_purity, id, _arg) => {
            deps.insert(*id);
        }

        flat::Expr::Branch(_discrim, cases, _result_type) => {
            for (_cond, body) in cases {
                add_tail_call_deps(deps, vars_in_scope, body);
            }
        }

        flat::Expr::LetMany(bindings, final_local) => {
            if let Some(last_i) = last_index(bindings) {
                if *final_local == flat::LocalId(vars_in_scope + last_i) {
                    add_tail_call_deps(deps, vars_in_scope + last_i, &bindings[last_i].1);
                }
            }
        }

        _ => {}
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Position {
    Tail,
    NotTail,
}

#[derive(Clone, Debug)]
struct TailFuncDef {
    pub purity: Purity,
    pub arg_type: anon::Type,
    pub ret_type: anon::Type,
    pub body: TailExpr,
    pub profile_point: Option<prof::ProfilePointId>,
}

/// A `flat::Expr` where all tail calls are marked.
#[derive(Clone, Debug)]
enum TailExpr {
    Local(LocalId),
    Call(Purity, Position, CustomFuncId, LocalId),
    Branch(LocalId, Vec<(flat::Condition, TailExpr)>, anon::Type),
    LetMany(Vec<(anon::Type, TailExpr)>, LocalId),

    Tuple(Vec<LocalId>),
    TupleField(LocalId, usize),
    WrapVariant(IdVec<VariantId, anon::Type>, VariantId, LocalId),
    UnwrapVariant(VariantId, LocalId),
    WrapBoxed(LocalId, anon::Type),
    UnwrapBoxed(LocalId, anon::Type),
    WrapCustom(CustomTypeId, LocalId),
    UnwrapCustom(CustomTypeId, LocalId),

    Intrinsic(intr::Intrinsic, LocalId),
    ArrayOp(flat::ArrayOp),
    IoOp(flat::IoOp),
    Panic(anon::Type, LocalId),

    ArrayLit(anon::Type, Vec<LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

fn mark_tail_calls(
    tail_candidates: &BTreeSet<CustomFuncId>,
    pos: Position,
    vars_in_scope: usize,
    expr: &flat::Expr,
) -> TailExpr {
    match expr {
        flat::Expr::Local(id) => TailExpr::Local(*id),

        flat::Expr::Call(purity, func, arg) => {
            let actual_pos = if pos == Position::Tail && tail_candidates.contains(func) {
                Position::Tail
            } else {
                Position::NotTail
            };
            TailExpr::Call(*purity, actual_pos, *func, *arg)
        }

        flat::Expr::Branch(discrim, cases, result_type) => TailExpr::Branch(
            *discrim,
            cases
                .iter()
                .map(|(cond, body)| {
                    (
                        cond.clone(),
                        mark_tail_calls(tail_candidates, pos, vars_in_scope, body),
                    )
                })
                .collect(),
            result_type.clone(),
        ),

        flat::Expr::LetMany(bindings, final_local) => TailExpr::LetMany(
            bindings
                .iter()
                .enumerate()
                .map(|(i, (ty, binding))| {
                    let is_final_binding =
                        i + 1 == bindings.len() && *final_local == flat::LocalId(vars_in_scope + i);

                    let sub_pos = if is_final_binding {
                        pos
                    } else {
                        Position::NotTail
                    };

                    (
                        ty.clone(),
                        mark_tail_calls(tail_candidates, sub_pos, vars_in_scope + i, binding),
                    )
                })
                .collect(),
            *final_local,
        ),

        flat::Expr::Tuple(items) => TailExpr::Tuple(items.clone()),
        flat::Expr::TupleField(tuple, idx) => TailExpr::TupleField(*tuple, *idx),
        flat::Expr::WrapVariant(variant_types, variant, content) => {
            TailExpr::WrapVariant(variant_types.clone(), *variant, *content)
        }
        flat::Expr::UnwrapVariant(variant, wrapped) => TailExpr::UnwrapVariant(*variant, *wrapped),
        flat::Expr::WrapBoxed(content, content_type) => {
            TailExpr::WrapBoxed(*content, content_type.clone())
        }
        flat::Expr::UnwrapBoxed(content, content_type) => {
            TailExpr::UnwrapBoxed(*content, content_type.clone())
        }
        flat::Expr::WrapCustom(custom, content) => TailExpr::WrapCustom(*custom, *content),
        flat::Expr::UnwrapCustom(custom, wrapped) => TailExpr::UnwrapCustom(*custom, *wrapped),
        flat::Expr::Intrinsic(intr, arg) => TailExpr::Intrinsic(*intr, *arg),
        flat::Expr::ArrayOp(op) => TailExpr::ArrayOp(op.clone()),
        flat::Expr::IoOp(op) => TailExpr::IoOp(*op),
        flat::Expr::Panic(ret_type, message) => TailExpr::Panic(ret_type.clone(), *message),
        flat::Expr::ArrayLit(item_type, items) => {
            TailExpr::ArrayLit(item_type.clone(), items.clone())
        }
        flat::Expr::BoolLit(val) => TailExpr::BoolLit(*val),
        flat::Expr::ByteLit(val) => TailExpr::ByteLit(*val),
        flat::Expr::IntLit(val) => TailExpr::IntLit(*val),
        flat::Expr::FloatLit(val) => TailExpr::FloatLit(*val),
    }
}

fn compute_tail_calls(
    funcs: &IdVec<CustomFuncId, flat::FuncDef>,
) -> IdVec<CustomFuncId, TailFuncDef> {
    #[id_type]
    struct TailSccId(usize);

    let sccs: Sccs<TailSccId, _> = find_components(funcs.count(), |func_id| {
        let mut deps = BTreeSet::new();
        // The argument always provides exactly one free variable in scope for the body of the
        // function.
        add_tail_call_deps(&mut deps, 1, &funcs[func_id].body);
        deps
    });

    let mut tail_funcs = IdMap::new();
    for (_, scc) in &sccs {
        let tail_candidates = scc.nodes.into_iter().copied().collect();
        for func_id in scc.nodes {
            let func = &funcs[func_id];
            let body = mark_tail_calls(&tail_candidates, Position::Tail, 1, &func.body);
            tail_funcs.insert(
                func_id,
                TailFuncDef {
                    purity: func.purity,
                    arg_type: func.arg_type.clone(),
                    ret_type: func.ret_type.clone(),
                    body,
                    profile_point: func.profile_point,
                },
            );
        }
    }

    tail_funcs.to_id_vec(funcs.count())
}

// ------------------------
// Step 1: Parameterization
// ------------------------
// We start by lifting the set of custom type definitions from the previous pass into the current
// pass by annotating them with fresh mode and lifetime parameters.

fn parameterize_mode_data<'a>(
    customs: impl MapRef<'a, CustomTypeId, annot::TypeDef>,
    sccs: Option<(CustomTypeSccId, &IdVec<CustomTypeId, CustomTypeSccId>)>,
    count: &mut Count<SlotId>,
    ty: &anon::Type,
) -> ModeData<SlotId> {
    match ty {
        anon::Type::Bool => ModeData::Bool,
        anon::Type::Num(n) => ModeData::Num(*n),
        anon::Type::Tuple(tys) => ModeData::Tuple(
            tys.iter()
                .map(|ty| parameterize_mode_data(customs, sccs, count, ty))
                .collect(),
        ),
        anon::Type::Variants(tys) => ModeData::Variants(
            tys.map_refs(|_, ty| parameterize_mode_data(customs, sccs, count, ty)),
        ),
        anon::Type::Custom(id) => {
            if sccs.map_or(false, |(scc_id, sccs)| sccs[id] == scc_id) {
                ModeData::SelfCustom(*id)
            } else {
                let custom = customs.get(id).unwrap();
                let osub = custom
                    .ov_slots
                    .iter()
                    .map(|key| (*key, count.inc()))
                    .collect();
                let tsub = IdVec::from_count_with(custom.slot_count, |_| count.inc());
                ModeData::Custom(*id, osub, tsub)
            }
        }
        anon::Type::Array(ty) => {
            let slot = count.inc();
            let ty = parameterize_mode_data(customs, sccs, count, ty);
            let ov = ty.unapply_overlay();
            ModeData::Array(slot, ov, Box::new(ty))
        }
        anon::Type::HoleArray(ty) => {
            let slot = count.inc();
            let ty = parameterize_mode_data(customs, sccs, count, ty);
            let ov = ty.unapply_overlay();
            ModeData::HoleArray(slot, ov, Box::new(ty))
        }
        anon::Type::Boxed(ty) => {
            let slot = count.inc();
            let ty = parameterize_mode_data(customs, sccs, count, ty);
            let ov = ty.unapply_overlay();
            ModeData::Boxed(slot, ov, Box::new(ty))
        }
    }
}

/// `sccs` determines whether `SelfCustom` nodes are generated. If parameterizing the body of a
/// custom type, `sccs` should be a tuple of the SCC ID of that custom type's SCC and the full list
/// of SCCs. Otherwise, `sccs` should be `None`.
fn parameterize_type<'a>(
    customs: impl MapRef<'a, CustomTypeId, annot::TypeDef>,
    sccs: Option<(CustomTypeSccId, &IdVec<CustomTypeId, CustomTypeSccId>)>,
    count: &mut Count<SlotId>,
    ty: &anon::Type,
) -> annot::Type<SlotId, SlotId> {
    let modes = parameterize_mode_data(customs, sccs, count, ty);
    let lts = modes.extract_lts(customs);
    // println!("----------------------------");
    // println!("modes: {:?}", modes);
    // println!("lts: {:?}", lts);
    annot::Type::new(lts, modes)
}

// TODO: We could remove this if we had a version of `instantiate_type` for `anon::Type`.
fn parameterize_type_simple(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    ty: &anon::Type,
) -> annot::Type<SlotId, SlotId> {
    let mut count = Count::new();
    parameterize_type(customs, None, &mut count, ty)
}

fn parameterize_custom_scc(
    old_customs: &IdVec<CustomTypeId, flat::CustomTypeDef>,
    parameterized: &IdMap<CustomTypeId, annot::TypeDef>,
    sccs: &IdVec<CustomTypeId, CustomTypeSccId>,
    scc_id: CustomTypeSccId,
    scc: &old_graph::Scc<CustomTypeId>,
) -> BTreeMap<CustomTypeId, annot::TypeDef> {
    let mut count = Count::new();
    let mut scc_ov_slots = BTreeSet::new();
    let mut scc_lt_slots = BTreeSet::new();
    let mut bodies = BTreeMap::new();

    for id in scc.iter() {
        let ty = parameterize_type(
            parameterized,
            Some((scc_id, sccs)),
            &mut count,
            &old_customs[*id].content,
        );

        let ov = ty.modes().unapply_overlay();
        scc_ov_slots.extend(ov.iter().copied());
        scc_lt_slots.extend(ty.lts().iter().copied());
        bodies.insert(*id, (ty, ov));
    }

    bodies
        .into_iter()
        .map(|(id, (ty, ov))| {
            (
                id,
                annot::TypeDef {
                    ty,
                    ov,
                    slot_count: count,
                    ov_slots: scc_ov_slots.clone(),
                    lt_slots: scc_lt_slots.clone(),
                },
            )
        })
        .collect()
}

fn parameterize_customs(
    customs: &flat::CustomTypes,
    custom_sccs: &IdVec<CustomTypeId, CustomTypeSccId>,
) -> IdVec<CustomTypeId, annot::TypeDef> {
    let mut parameterized = IdMap::new();

    for (scc_id, scc) in &customs.sccs {
        let to_populate =
            parameterize_custom_scc(&customs.types, &parameterized, custom_sccs, scc_id, scc);

        debug_assert_eq!(
            to_populate.keys().collect::<BTreeSet<_>>(),
            scc.iter().collect::<BTreeSet<_>>()
        );

        for (id, typedef) in to_populate {
            println!("{:?}: {:?}", id, typedef);
            parameterized.insert(id, typedef);
        }
    }
    parameterized.to_id_vec(customs.types.count())
}

// ---------------------
// Step 2: Instantiation
// ---------------------
// After we are done with parameterization, we are ready to solve for modes and lifetimes. For each
// SCC of functions, we create a graph of mode constraints and lift each function body from the
// previous pass into the current pass by annotating it with fresh mode variables (not to be
// confused with mode parameters) from the constraint graph, emitting the constraints incident on
// these variables as we go. If we encounter a custom type, we can take the "template" we produced
// during parameterization and replace the mode parameters with fresh mode variables.
//
// Once all the constraints have been generated, we can solve them for the set of signature
// variables of the functions in the SCC. Yes, every function in the SCC is parameterized by all the
// signature variables of all the functions in the SCC! It is always OK to over-parameterize a
// function and doing things this way will help us deduplicated specializations when we monomorphize
// in the next pass.
//
// Note that we have yet to discuss how we handle lifetimes. Since the constraints on lifetimes are
// much simpler than the constraints on modes, we take lifetime meets (i.e. greatest lower bounds)
// as needed as we go.

type ConstrGraph = in_eq::ConstrGraph<ModeVar, Mode>;

fn require_owned(constrs: &mut ConstrGraph, var: ModeVar) {
    constrs.require_lte_const(&Mode::Owned, var);
}

fn mode_bind(constrs: &mut ConstrGraph, ty1: &ModeData<ModeVar>, ty2: &ModeData<ModeVar>) {
    debug_assert_eq!(ty1.shape(), ty2.shape());
    for (m1, m2) in ty1.iter().zip_eq(ty2.iter()) {
        constrs.require_eq(*m1, *m2);
    }
}

fn emit_occur_constr(
    constrs: &mut ConstrGraph,
    scope: &annot::Path,
    binding_mode: ModeVar,
    use_mode: ModeVar,
    use_lt: &Lt,
) {
    if use_lt.does_not_exceed(scope) {
        // Case: this is a non-escaping, ("opportunistic" or "borrow") occurrence.
        constrs.require_lte(use_mode, binding_mode);
    } else {
        // Case: this is an escaping ("move" or "dup") occurrence.
        constrs.require_eq(binding_mode, use_mode);
    }
}

fn emit_occur_constrs_overlay(
    constrs: &mut ConstrGraph,
    scope: &annot::Path,
    binding_ov: &Overlay<ModeVar>,
    use_ov: &Overlay<ModeVar>,
    use_lts: &LtData<Lt>,
) {
    for ((binding_mode, use_mode), use_lt) in binding_ov
        .iter()
        .zip_eq(use_ov.iter())
        .zip_eq(use_lts.iter())
    {
        emit_occur_constr(constrs, scope, *binding_mode, *use_mode, use_lt);
    }
}

fn emit_occur_constrs_heap(
    strategy: Strategy,
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    constrs: &mut ConstrGraph,
    scope: &annot::Path,
    binding_modes: &ModeData<ModeVar>,
    use_modes: &ModeData<ModeVar>,
    use_lts: &LtData<Lt>,
) {
    use LtData as L;
    use ModeData as M;
    match (binding_modes, use_modes, use_lts) {
        (M::Bool, M::Bool, L::Bool) => {}
        (M::Num(n1), M::Num(n2), L::Num(_)) if n1 == n2 => {}
        (M::Tuple(ms1), M::Tuple(ms2), L::Tuple(lts)) => {
            for ((m1, m2), lt) in ms1.iter().zip_eq(ms2).zip_eq(lts) {
                emit_occur_constrs(strategy, customs, constrs, scope, m1, m2, lt);
            }
        }
        (M::Variants(ms1), M::Variants(ms2), L::Variants(lts)) => {
            for ((m1, m2), lt) in ms1.values().zip_eq(ms2.values()).zip_eq(lts.values()) {
                emit_occur_constrs(strategy, customs, constrs, scope, m1, m2, lt);
            }
        }
        (M::SelfCustom(id1), M::SelfCustom(id2), L::SelfCustom(_)) if id1 == id2 => {}
        (M::Custom(id1, osub1, tsub1), M::Custom(id2, osub2, tsub2), L::Custom(_, lsub))
            if id1 == id2 =>
        {
            for (m1, m2) in osub1.values().zip_eq(osub2.values()) {
                constrs.require_eq(*m1, *m2);
            }
            let custom = &customs[id1];
            emit_occur_constrs_heap(
                strategy,
                customs,
                constrs,
                scope,
                &custom.ty.modes().hydrate(tsub1),
                &custom.ty.modes().hydrate(tsub2),
                &custom.ty.lts().hydrate(lsub),
            );
        }
        (M::Array(m1, ov1, ms1), M::Array(m2, ov2, ms2), L::Array(_, lts))
        | (M::HoleArray(m1, ov1, ms1), M::HoleArray(m2, ov2, ms2), L::HoleArray(_, lts))
        | (M::Boxed(m1, ov1, ms1), M::Boxed(m2, ov2, ms2), L::Boxed(_, lts)) => {
            constrs.require_eq(*m1, *m2);
            emit_occur_constrs_heap(strategy, customs, constrs, scope, ms1, ms2, lts);
            emit_occur_constrs_overlay(constrs, scope, ov1, ov2, lts);
        }
        _ => panic!("incompatible types"),
    }
}

fn emit_occur_constrs(
    strategy: Strategy,
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    constrs: &mut ConstrGraph,
    scope: &annot::Path,
    binding_modes: &ModeData<ModeVar>,
    use_modes: &ModeData<ModeVar>,
    use_lts: &LtData<Lt>,
) {
    use LtData as L;
    use ModeData as M;
    match (binding_modes, use_modes, use_lts) {
        (M::Bool, M::Bool, L::Bool) => {}
        (M::Num(n1), M::Num(n2), L::Num(_)) if n1 == n2 => {}
        (M::Tuple(ms1), M::Tuple(ms2), L::Tuple(lts)) => {
            for ((m1, m2), lt) in ms1.iter().zip_eq(ms2).zip_eq(lts) {
                emit_occur_constrs(strategy, customs, constrs, scope, m1, m2, lt);
            }
        }
        (M::Variants(ms1), M::Variants(ms2), L::Variants(lts)) => {
            for ((m1, m2), lt) in ms1.values().zip_eq(ms2.values()).zip_eq(lts.values()) {
                emit_occur_constrs(strategy, customs, constrs, scope, m1, m2, lt);
            }
        }
        (M::SelfCustom(id1), M::SelfCustom(id2), L::SelfCustom(_)) if id1 == id2 => {}
        (M::Custom(id1, osub1, tsub1), M::Custom(id2, osub2, tsub2), L::Custom(_, lsub))
            if id1 == id2 =>
        {
            let custom = &customs[id1];
            let use_lts = custom.ty.lts().hydrate(lsub);
            emit_occur_constrs(
                strategy,
                customs,
                constrs,
                scope,
                &custom.ty.modes().hydrate(tsub1),
                &custom.ty.modes().hydrate(tsub2),
                &use_lts,
            );
            emit_occur_constrs_overlay(
                constrs,
                scope,
                &custom.ov.hydrate(osub1),
                &custom.ov.hydrate(osub2),
                &use_lts,
            )
        }
        (M::Array(m1, ov1, ms1), M::Array(m2, ov2, ms2), L::Array(lt, lts))
        | (M::HoleArray(m1, ov1, ms1), M::HoleArray(m2, ov2, ms2), L::HoleArray(lt, lts))
        | (M::Boxed(m1, ov1, ms1), M::Boxed(m2, ov2, ms2), L::Boxed(lt, lts)) => {
            if strategy == Strategy::OnlyTrivialBorrows {
                emit_occur_constr(constrs, scope, *m1, *m2, lt);
                for m in ms1
                    .iter()
                    .chain(ms2.iter())
                    .chain(ov1.iter())
                    .chain(ov2.iter())
                {
                    require_owned(constrs, *m);
                }
            } else {
                emit_occur_constr(constrs, scope, *m1, *m2, lt);
                emit_occur_constrs_heap(strategy, customs, constrs, scope, ms1, ms2, lts);
                emit_occur_constrs_overlay(constrs, scope, ov1, ov2, lts);
            }
        }
        _ => panic!("incompatible types"),
    }
}

fn same_shape(ty1: &anon::Type, ty2: &ModeData<ModeVar>) -> bool {
    match (ty1, ty2) {
        (anon::Type::Bool, ModeData::Bool) => true,
        (anon::Type::Num(n1), ModeData::Num(n2)) => n1 == n2,
        (anon::Type::Tuple(items1), ModeData::Tuple(items2)) => {
            items1.len() == items2.len()
                && items1
                    .iter()
                    .zip(items2.iter())
                    .all(|(ty1, ty2)| same_shape(ty1, ty2))
        }
        (anon::Type::Variants(variants1), ModeData::Variants(variants2)) => {
            variants1.len() == variants2.len()
                && variants1
                    .iter()
                    .zip(variants2.iter())
                    .all(|((_, ty1), (_, ty2))| same_shape(ty1, ty2))
        }
        (anon::Type::Custom(id1), ModeData::SelfCustom(id2)) => id1 == id2,
        (anon::Type::Custom(id1), ModeData::Custom(id2, _, _)) => id1 == id2,
        (anon::Type::Array(ty1), ModeData::Array(_, _, ty2)) => same_shape(ty1, ty2),
        (anon::Type::HoleArray(ty1), ModeData::HoleArray(_, _, ty2)) => same_shape(ty1, ty2),
        (anon::Type::Boxed(ty1), ModeData::Boxed(_, _, ty2)) => same_shape(ty1, ty2),
        _ => false,
    }
}

fn lt_bind(lts1: &LtData<LtParam>, lts2: &LtData<Lt>) -> BTreeMap<LtParam, Lt> {
    let mut result = BTreeMap::new();
    for (param, lt) in lts1.iter().zip_eq(lts2.iter()) {
        result
            .entry(*param)
            .and_modify(|old: &mut Lt| *old = old.join(&lt))
            .or_insert_with(|| lt.clone());
    }
    result
}

fn subst_lts(lts: &LtData<Lt>, subst: &BTreeMap<LtParam, Lt>) -> LtData<Lt> {
    lts.iter()
        .map(|lt| match lt {
            Lt::Empty => Lt::Empty,
            Lt::Local(lt) => Lt::Local(lt.clone()),
            Lt::Join(params) => params
                .iter()
                .map(|p| &subst[p])
                .fold(Lt::Empty, |lt1, lt2| Lt::join(&lt1, lt2)),
        })
        .collect_lt_data(lts)
}

fn join_everywhere(lts: &LtData<Lt>, new_lt: &Lt) -> LtData<Lt> {
    lts.iter()
        .map(|lt| Lt::join(lt, new_lt))
        .collect_lt_data(lts)
}

fn lt_equiv(lts1: &LtData<Lt>, lts2: &LtData<Lt>) -> bool {
    debug_assert_eq!(lts1.shape(), lts2.shape());
    lts1.iter().zip_eq(lts2.iter()).all(|(lt1, lt2)| lt1 == lt2)
}

/// Computes the nominal equivalent of `o'[a |-> mu a. o]` where `o'` is `overlay` and `o` is
/// `self_sub`.
fn unfold_overlay(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    self_sub: &BTreeMap<SlotId, ModeVar>,
    overlay: &Overlay<ModeVar>,
) -> Overlay<ModeVar> {
    match overlay {
        Overlay::Bool => Overlay::Bool,
        Overlay::Num(num_ty) => Overlay::Num(*num_ty),
        Overlay::Tuple(os) => Overlay::Tuple(
            os.iter()
                .map(|o| unfold_overlay(customs, self_sub, o))
                .collect(),
        ),
        Overlay::Variants(os) => {
            Overlay::Variants(os.map_refs(|_, o| unfold_overlay(customs, self_sub, o)))
        }
        Overlay::SelfCustom(id) => Overlay::Custom(*id, self_sub.clone()),
        Overlay::Custom(id, osub) => Overlay::Custom(*id, osub.clone()),
        Overlay::Array(m) => Overlay::Array(*m),
        Overlay::HoleArray(m) => Overlay::HoleArray(*m),
        Overlay::Boxed(m) => Overlay::Boxed(*m),
    }
}

fn unfold_lts<L: Clone>(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    self_sub: &BTreeMap<SlotId, L>,
    lts: &LtData<L>,
) -> LtData<L> {
    match lts {
        LtData::Bool => LtData::Bool,
        LtData::Num(num_ty) => LtData::Num(*num_ty),
        LtData::Tuple(lts) => LtData::Tuple(
            lts.iter()
                .map(|lt| unfold_lts(customs, self_sub, lt))
                .collect(),
        ),
        LtData::Variants(lts) => {
            LtData::Variants(lts.map_refs(|_, lt| unfold_lts(customs, self_sub, lt)))
        }
        LtData::SelfCustom(id) => LtData::Custom(*id, self_sub.clone()),
        LtData::Custom(id, sub) => LtData::Custom(*id, sub.clone()),
        LtData::Array(lt, item) => {
            LtData::Array(lt.clone(), Box::new(unfold_lts(customs, self_sub, item)))
        }
        LtData::HoleArray(lt, item) => {
            LtData::HoleArray(lt.clone(), Box::new(unfold_lts(customs, self_sub, item)))
        }
        LtData::Boxed(lt, item) => {
            LtData::Boxed(lt.clone(), Box::new(unfold_lts(customs, self_sub, item)))
        }
    }
}

fn unfold_modes(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    extracted: &BTreeMap<SlotId, ModeVar>,
    ty_orig: &IdVec<SlotId, ModeVar>,
    ov_orig: &BTreeMap<SlotId, ModeVar>,
    ty: &ModeData<ModeVar>,
) -> ModeData<ModeVar> {
    match ty {
        ModeData::Bool => ModeData::Bool,
        ModeData::Num(num_ty) => ModeData::Num(*num_ty),
        ModeData::Tuple(tys) => ModeData::Tuple(
            tys.iter()
                .map(|ty| unfold_modes(customs, extracted, ty_orig, ov_orig, ty))
                .collect(),
        ),
        ModeData::Variants(tys) => ModeData::Variants(
            tys.map_refs(|_, ty| unfold_modes(customs, extracted, ty_orig, ov_orig, ty)),
        ),
        ModeData::SelfCustom(id) => ModeData::Custom(*id, extracted.clone(), ty_orig.clone()),
        ModeData::Custom(id, osub, tsub) => ModeData::Custom(*id, osub.clone(), tsub.clone()),
        ModeData::Array(m, ov, ty) => ModeData::Array(
            *m,
            unfold_overlay(customs, ov_orig, ov),
            Box::new(unfold_modes(customs, extracted, ty_orig, ov_orig, ty)),
        ),
        ModeData::HoleArray(m, ov, ty) => ModeData::HoleArray(
            *m,
            unfold_overlay(customs, ov_orig, ov),
            Box::new(unfold_modes(customs, extracted, ty_orig, ov_orig, ty)),
        ),
        ModeData::Boxed(m, ov, ty) => ModeData::Boxed(
            *m,
            unfold_overlay(customs, ov_orig, ov),
            Box::new(unfold_modes(customs, extracted, ty_orig, ov_orig, ty)),
        ),
    }
}

fn unfold_custom<L: Clone>(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    msub: &IdVec<SlotId, ModeVar>,
    lsub: &BTreeMap<SlotId, L>,
    osub: &BTreeMap<SlotId, ModeVar>,
    id: CustomTypeId,
) -> annot::Type<ModeVar, L> {
    let custom = &customs[id];
    let folded = custom.ty.hydrate(lsub, msub);
    let extracted = custom
        .ov_slots
        .iter()
        .map(|&key| (key, msub[key]))
        .collect();
    let unfolded_lts = unfold_lts(customs, lsub, &folded.lts());
    let unfolded_ms = unfold_modes(customs, &extracted, msub, osub, &folded.modes());
    annot::Type::new(unfolded_lts, unfolded_ms)
}

fn instantiate_overlay<M>(constrs: &mut ConstrGraph, ov: &Overlay<M>) -> Overlay<ModeVar> {
    ov.iter().map(|_| constrs.fresh_var()).collect_overlay(ov)
}

fn instantiate_type<M, L1, L2>(
    constrs: &mut ConstrGraph,
    fresh_lt: &mut impl FnMut() -> L2,
    ty: &annot::Type<M, L1>,
) -> annot::Type<ModeVar, L2> {
    let lts = ty
        .lts()
        .iter()
        .map(|_| fresh_lt())
        .collect_lt_data(ty.lts());
    let modes = ty
        .modes()
        .iter()
        .map(|_| constrs.fresh_var())
        .collect_mode_data(ty.modes());
    annot::Type::new(lts, modes)
}

// Replaces parameters with fresh variables from the constraint graph.
fn instantiate_type_unused<M, L>(
    constrs: &mut ConstrGraph,
    ty: &annot::Type<M, L>,
) -> annot::Type<ModeVar, Lt> {
    instantiate_type(constrs, &mut || Lt::Empty, ty)
}

fn instantiate_condition(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    constrs: &mut ConstrGraph,
    cond: &flat::Condition,
) -> annot::Condition<ModeVar, Lt> {
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
            instantiate_type_unused(constrs, &parameterize_type_simple(customs, ty)),
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

fn instantiate_occur_in_position(
    pos: Position,
    strategy: Strategy,
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    ctx: &mut TrackedContext,
    scopes: &LocalContext<LocalId, annot::Path>,
    constrs: &mut ConstrGraph,
    id: LocalId,
    use_modes: &ModeData<ModeVar>,
    use_lts: &LtData<Lt>,
) -> Occur<ModeVar, Lt> {
    let binding_ty = ctx.local_binding(id);

    if pos == Position::Tail {
        mode_bind(constrs, &binding_ty.modes(), &use_modes);
    } else {
        emit_occur_constrs(
            strategy,
            customs,
            constrs,
            scopes.local_binding(id),
            binding_ty.modes(),
            use_modes,
            use_lts,
        );
    }

    let use_ty = annot::Type::new(use_lts.clone(), use_modes.clone());
    let new_ty = Rc::new(binding_ty.left_meet(&use_ty));
    ctx.update_local(id, new_ty);

    annot::Occur { id, ty: use_ty }
}

/// Generate occurrence constraints and merge `fut_ty` into the typing context. Corresponds to the
/// I-Occur rule.
fn instantiate_occur(
    strategy: Strategy,
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    ctx: &mut TrackedContext,
    scopes: &LocalContext<LocalId, annot::Path>,
    constrs: &mut ConstrGraph,
    id: LocalId,
    fut_modes: &ModeData<ModeVar>,
    fut_lts: &LtData<Lt>,
) -> Occur<ModeVar, Lt> {
    instantiate_occur_in_position(
        Position::NotTail,
        strategy,
        customs,
        ctx,
        scopes,
        constrs,
        id,
        fut_modes,
        fut_lts,
    )
}

fn instantiate_prim_modes<M>(ty: &intr::Type) -> ModeData<M> {
    match ty {
        intr::Type::Bool => ModeData::Bool,
        intr::Type::Num(n) => ModeData::Num(*n),
        intr::Type::Tuple(items) => {
            ModeData::Tuple(items.iter().map(|ty| instantiate_prim_modes(ty)).collect())
        }
    }
}

fn instantiate_prim_lts<L>(ty: &intr::Type) -> LtData<L> {
    match ty {
        intr::Type::Bool => LtData::Bool,
        intr::Type::Num(n) => LtData::Num(*n),
        intr::Type::Tuple(items) => {
            LtData::Tuple(items.iter().map(|ty| instantiate_prim_lts(ty)).collect())
        }
    }
}

fn instantiate_prim_type<M, L>(ty: &intr::Type) -> annot::Type<M, L> {
    annot::Type::new(instantiate_prim_lts(ty), instantiate_prim_modes(ty))
}

/// Used during lifetime fixed point iteration. `know_defs` contains the definitions of all
/// functions from previous SCCs. `pending_args` and `pending_rets` contain the signatures of types
/// from the current SCC as of the previous iteration.
#[derive(Clone, Copy, Debug)]
struct SignatureAssumptions<'a> {
    known_defs: &'a IdMap<CustomFuncId, annot::FuncDef>,
    pending_args: &'a BTreeMap<CustomFuncId, annot::Type<ModeVar, Lt>>,
    pending_rets: &'a BTreeMap<CustomFuncId, annot::Type<ModeVar, LtParam>>,
}

impl<'a> SignatureAssumptions<'a> {
    fn sig_of(
        &self,
        constrs: &mut ConstrGraph,
        id: CustomFuncId,
    ) -> (annot::Type<ModeVar, Lt>, annot::Type<ModeVar, LtParam>) {
        self.known_defs.get(id).map_or_else(
            || {
                (
                    self.pending_args[&id].clone(),
                    self.pending_rets[&id].clone(),
                )
            },
            |def| {
                let params_to_vars = constrs.instantiate_subgraph(&def.constrs.sig);
                let map = |param: &ModeParam| params_to_vars[*param];
                (def.arg_ty.map_modes(&map), def.ret_ty.map_modes(&map))
            },
        )
    }
}

mod model {
    use crate::data::borrow_spec::*;

    use super::{ConstrGraph, LocalContext, LocalId, Strategy, TrackedContext};
    use crate::data::first_order_ast::CustomTypeId;
    use crate::data::mode_annot_ast2::{self as annot, LtData, ModeData};
    use crate::util::iter::IterExt;
    use id_collections::{Id, IdMap, IdVec};
    use std::collections::BTreeSet;

    #[derive(Clone, Debug)]
    struct SigData {
        modes: IdMap<Mode, annot::ModeVar>,
        lts: IdMap<Lt, annot::Lt>,
        tys: IdMap<TypeVar, annot::Type<annot::ModeVar, annot::Lt>>,
        ovs: IdMap<TypeVar, annot::Overlay<annot::ModeVar>>, // only present for item types
    }

    fn extract_annot(
        result: &mut SigData,
        model: &Type,
        modes: &ModeData<annot::ModeVar>,
        lts: &LtData<annot::Lt>,
    ) {
        fn insert<I: Id, T>(map: &mut IdMap<I, T>, id: I, val: T) {
            debug_assert!(
                !map.contains_key(id),
                "duplicate variables are not supported in model return types"
            );
            map.insert(id, val);
        }

        use LtData as L;
        use ModeData as M;
        use Type as T;

        match (model, modes, lts) {
            (T::Var(v), modes, lts) => {
                insert(
                    &mut result.tys,
                    *v,
                    annot::Type::new(lts.clone(), modes.clone()),
                );
            }
            (T::Num(n1), M::Num(n2), L::Num(n3)) if n1 == n2 && n1 == n3 => {}
            (T::Tuple(items1), M::Tuple(items2), L::Tuple(items3)) => {
                for ((item1, item2), item3) in items1.iter().zip_eq(items2).zip_eq(items3) {
                    extract_annot(result, item1, item2, item3);
                }
            }
            (T::Array(m1, lt1, item1), M::Array(m2, ov, item2), L::Array(lt2, item3))
            | (
                T::HoleArray(m1, lt1, item1),
                M::HoleArray(m2, ov, item2),
                L::HoleArray(lt2, item3),
            ) => {
                insert(&mut result.modes, *m1, *m2);
                insert(&mut result.lts, *lt1, lt2.clone());
                match item1 {
                    ItemType::Num(_) => {}
                    ItemType::Var(v) => {
                        insert(&mut result.ovs, *v, ov.clone());
                        insert(
                            &mut result.tys,
                            *v,
                            annot::Type::new((**item3).clone(), (**item2).clone()),
                        );
                    }
                }
            }
            _ => panic!("type does not match model"),
        }
    }

    fn fill_vacant(
        data: &mut SigData,
        customs: &IdVec<CustomTypeId, annot::TypeDef>,
        constrs: &mut ConstrGraph,
        path: &annot::Path,
        accessed: &BTreeSet<Lt>,
        model: &Type,
        modes: &ModeData<annot::ModeVar>,
        lts: &LtData<annot::Lt>,
    ) {
        use LtData as L;
        use ModeData as M;
        use Type as T;

        match (model, modes, lts) {
            (T::Var(v), modes, lts) => {
                if !data.tys.contains_key(*v) {
                    data.tys.insert(
                        *v,
                        super::instantiate_type_unused(
                            constrs,
                            &annot::Type::new(lts.clone(), modes.clone()),
                        ),
                    );
                }
            }
            (T::Num(n1), M::Num(n2), L::Num(n3)) if n1 == n2 && n1 == n3 => {}
            (T::Tuple(items1), M::Tuple(items2), L::Tuple(items3)) => {
                for ((item1, item2), item3) in items1.iter().zip_eq(items2).zip_eq(items3) {
                    fill_vacant(data, customs, constrs, path, accessed, item1, item2, item3);
                }
            }
            (T::Array(m, lt, item1), M::Array(_, _, item2), L::Array(_, item3))
            | (T::HoleArray(m, lt, item1), M::HoleArray(_, _, item2), L::HoleArray(_, item3)) => {
                if !data.modes.contains_key(*m) {
                    data.modes.insert(*m, constrs.fresh_var());
                }
                if !data.lts.contains_key(*lt) {
                    data.lts.insert(
                        *lt,
                        if accessed.contains(lt) {
                            path.as_lt()
                        } else {
                            annot::Lt::Empty
                        },
                    );
                }
                match item1 {
                    ItemType::Num(_) => {}
                    ItemType::Var(v) => {
                        if !data.tys.contains_key(*v) {
                            assert!(!data.ovs.contains_key(*v));
                            data.ovs.insert(
                                *v,
                                super::instantiate_overlay(constrs, &item2.unapply_overlay()),
                            );
                            data.tys.insert(
                                *v,
                                super::instantiate_type_unused(
                                    constrs,
                                    &annot::Type::new((**item3).clone(), (**item2).clone()),
                                ),
                            );
                        }
                    }
                }
            }
            _ => panic!("type does not match model"),
        }
    }

    fn instantiate_model_modes(data: &SigData, model: &Type) -> ModeData<annot::ModeVar> {
        match model {
            Type::Var(v) => data.tys[v].modes().clone(),
            Type::Num(n) => ModeData::Num(*n),
            Type::Tuple(items) => ModeData::Tuple(
                items
                    .iter()
                    .map(|item| instantiate_model_modes(data, item))
                    .collect(),
            ),
            Type::Array(m, _, item) => {
                let (ov, item) = match item {
                    ItemType::Num(n) => (annot::Overlay::Num(*n), annot::ModeData::Num(*n)),
                    ItemType::Var(v) => (data.ovs[v].clone(), data.tys[v].modes().clone()),
                };
                ModeData::Array(data.modes[m], ov, Box::new(item))
            }
            Type::HoleArray(m, _, item) => {
                let (ov, item) = match item {
                    ItemType::Num(n) => (annot::Overlay::Num(*n), annot::ModeData::Num(*n)),
                    ItemType::Var(v) => (data.ovs[v].clone(), data.tys[v].modes().clone()),
                };
                ModeData::HoleArray(data.modes[m], ov, Box::new(item))
            }
        }
    }

    fn instantiate_model_lts(data: &SigData, model: &Type) -> LtData<annot::Lt> {
        match model {
            Type::Var(v) => data.tys[v].lts().clone(),
            Type::Num(n) => LtData::Num(*n),
            Type::Tuple(items) => LtData::Tuple(
                items
                    .iter()
                    .map(|item| instantiate_model_lts(data, item))
                    .collect(),
            ),
            Type::Array(_, lt, item) | Type::HoleArray(_, lt, item) => {
                let item = match item {
                    ItemType::Num(n) => annot::LtData::Num(*n),
                    ItemType::Var(v) => data.tys[v].lts().clone(),
                };
                LtData::Array(data.lts[lt].clone(), Box::new(item))
            }
        }
    }

    /// Signatures are interpreted as follows:
    /// - if a mode, lifetime, or type variable is present in the return, it is assigned its value
    ///   from the return everywhere
    /// - any modes not present in the return are assigned fresh variables
    /// - any modes in `sig.owned` are constrained to be owned
    /// - any lifetimes not present in the return are assigned the current path if they are present
    ///   in `sig.accessed` and the empty lifetime otherwise
    /// - any type variables not present in the return are assigned fresh, unconstrained, unused
    ///   types (and overlays) of the correct shape
    ///
    /// NOTE: we currently do not support duplicate modes, lifetimes, or type variables in the
    /// return, though such an extension would be straightforward.
    pub fn instantiate_model(
        sig: &BuiltinSig,
        strategy: Strategy,
        customs: &IdVec<CustomTypeId, annot::TypeDef>,
        constrs: &mut ConstrGraph,
        ctx: &mut TrackedContext,
        scopes: &mut LocalContext<LocalId, annot::Path>,
        path: &annot::Path,
        args: &[LocalId],
        ret_modes: &ModeData<annot::ModeVar>,
        ret_lts: &LtData<annot::Lt>,
    ) -> Vec<annot::Occur<annot::ModeVar, annot::Lt>> {
        let mut data = SigData {
            modes: IdMap::new(),
            lts: IdMap::new(),
            tys: IdMap::new(),
            ovs: IdMap::new(),
        };

        extract_annot(&mut data, &sig.ret, ret_modes, ret_lts);
        for (i, arg) in args.iter().enumerate() {
            let ty = ctx.local_binding(*arg);
            fill_vacant(
                &mut data,
                customs,
                constrs,
                path,
                &sig.accessed,
                &sig.args[i],
                ty.modes(),
                ty.lts(),
            );
        }

        for m in &sig.owned {
            super::require_owned(constrs, data.modes[m]);
        }

        // `.rev()` ensures the calls to `instantiate_occur` are in the correct order
        let mut occurs = Vec::new();
        debug_assert_eq!(args.len(), sig.args.len());
        for (arg_id, arg) in args.iter().zip(&sig.args).rev() {
            occurs.push(super::instantiate_occur(
                strategy,
                customs,
                ctx,
                scopes,
                constrs,
                *arg_id,
                &instantiate_model_modes(&data, arg),
                &instantiate_model_lts(&data, arg),
            ));
        }

        occurs.reverse();
        occurs
    }
}

// This function is the core logic for this pass. It implements the judgement from the paper:
// Δ ; Γ ; S ; q ⊢ e : t ⇝ e ; Q ; Γ'
//
// Note that we must return a set of updates rather than mutating Γ because I-Match requires that we
// check all branches in the initial Γ.
fn instantiate_expr(
    strategy: Strategy,
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    sigs: SignatureAssumptions,
    constrs: &mut ConstrGraph,
    lt_count: &mut Count<LtParam>,
    ctx: &ImmutContext,
    scopes: &mut LocalContext<LocalId, annot::Path>,
    path: annot::Path,
    fut_modes: &ModeData<ModeVar>,
    fut_lts: &LtData<Lt>,
    expr: &TailExpr,
    renderer: &CustomTypeRenderer<CustomTypeId>,
) -> (annot::Expr<ModeVar, Lt>, LocalUpdates) {
    use LtData as L;
    use ModeData as M;

    let mut ctx = TrackedContext::new(ctx);

    let expr_annot = match expr {
        TailExpr::Local(local) => {
            let occur = instantiate_occur(
                strategy, customs, &mut ctx, scopes, constrs, *local, fut_modes, fut_lts,
            );
            annot::Expr::Local(occur)
        }

        TailExpr::Call(purity, pos, func, arg) => {
            let (arg_ty, ret_ty) = sigs.sig_of(constrs, *func);

            mode_bind(constrs, ret_ty.modes(), fut_modes);
            let lt_subst = lt_bind(ret_ty.lts(), fut_lts);

            // This `join_everywhere` reflects the fact that we assume that functions access all of
            // their arguments. We could be more precise here.
            let arg_lts = join_everywhere(&subst_lts(&arg_ty.lts(), &lt_subst), &path.as_lt());
            let arg = instantiate_occur_in_position(
                *pos,
                strategy,
                customs,
                &mut ctx,
                scopes,
                constrs,
                *arg,
                arg_ty.modes(),
                &arg_lts,
            );

            annot::Expr::Call(*purity, *func, arg)
        }

        TailExpr::Branch(discrim_id, cases, ret_ty) => {
            debug_assert!(same_shape(ret_ty, fut_modes));

            let mut updates = LocalUpdates::new();
            let mut cases_annot = Vec::new();

            for (i, (cond, body)) in cases.iter().enumerate() {
                let cond_annot = instantiate_condition(customs, constrs, cond);
                let (body_annot, body_updates) = instantiate_expr(
                    strategy,
                    customs,
                    sigs,
                    constrs,
                    lt_count,
                    ctx.as_untracked(),
                    scopes,
                    path.alt(i, cases.len()),
                    fut_modes,
                    fut_lts,
                    body,
                    renderer,
                );

                // Record the updates, but DO NOT apply them to the context. Every branch should be
                // checked in the original context.
                updates.merge_with(&body_updates, |ty1, ty2| ty1.left_meet(&ty2));

                cases_annot.push((cond_annot, body_annot));
            }

            // Finally, apply the updates before instantiating the discriminant.
            ctx.update_all(&updates);

            let discrim_fut_ty = ctx.local_binding(*discrim_id).clone();
            let discrim_occur = instantiate_occur(
                strategy,
                customs,
                &mut ctx,
                scopes,
                constrs,
                *discrim_id,
                discrim_fut_ty.modes(),
                discrim_fut_ty.lts(),
            );

            annot::Expr::Branch(
                discrim_occur,
                cases_annot,
                annot::Type::new(fut_lts.clone(), fut_modes.clone()),
            )
        }

        // We're only using `with_scope` here for its debug assertion, and to signal intent; by the
        // time the passed closure returns, we've manually truncated away all the variables which it
        // would usually be `with_scope`'s responsibility to remove.
        TailExpr::LetMany(bindings, result_id) => scopes.with_scope(|scopes| {
            let locals_offset = scopes.len();
            let end_of_scope = path.seq(bindings.len());

            for (binding_ty, _) in bindings {
                let annot_ty = instantiate_type_unused(
                    constrs,
                    &parameterize_type_simple(customs, binding_ty),
                );
                let local_id1 = scopes.add_local(end_of_scope.clone());
                let local_id2 = ctx.add_local(Rc::new(annot_ty));
                debug_assert_eq!(local_id1, local_id2);
            }

            let result_occur = instantiate_occur(
                strategy, customs, &mut ctx, scopes, constrs, *result_id, fut_modes, fut_lts,
            );

            let mut bindings_annot_rev = Vec::new();
            for (i, (_, binding_expr)) in bindings.iter().enumerate().rev() {
                let local = LocalId(locals_offset + i);
                let fut_ty = (**ctx.local_binding(local)).clone();

                // Only retain the locals *strictly* before this binding.
                scopes.truncate(Count::from_value(local.0));
                ctx.truncate(Count::from_value(local.0));

                let (expr_annot, expr_updates) = instantiate_expr(
                    strategy,
                    customs,
                    sigs,
                    constrs,
                    lt_count,
                    ctx.as_untracked(),
                    scopes,
                    path.seq(i),
                    fut_ty.modes(),
                    fut_ty.lts(),
                    binding_expr,
                    renderer,
                );

                // Apply the updates to the context. It is important that the enclosing loop is in
                // reverse order to ensure that each binding is checked in the correct context.
                ctx.update_all(&expr_updates);

                bindings_annot_rev.push((fut_ty, expr_annot));
            }

            let bindings_annot = {
                bindings_annot_rev.reverse();
                bindings_annot_rev
            };

            annot::Expr::LetMany(bindings_annot, result_occur)
        }),

        TailExpr::Tuple(item_ids) => {
            let (M::Tuple(fut_item_modes), L::Tuple(fut_item_lts)) = (fut_modes, fut_lts) else {
                unreachable!();
            };

            debug_assert_eq!(item_ids.len(), fut_item_modes.len());
            debug_assert_eq!(item_ids.len(), fut_item_lts.len());

            let mut occurs_rev: Vec<_> = item_ids
                .iter()
                .zip(fut_item_modes.iter())
                .zip(fut_item_lts.iter())
                // We must process the items in reverse order to ensure `instantiate_occur` (which
                // updates the lifetimes in `ctx`) generates the correct constraints.
                .rev()
                .map(|((item_id, item_fut_modes), item_fut_lts)| {
                    instantiate_occur(
                        strategy,
                        customs,
                        &mut ctx,
                        scopes,
                        constrs,
                        *item_id,
                        item_fut_modes,
                        item_fut_lts,
                    )
                })
                .collect();
            let occurs = {
                occurs_rev.reverse();
                occurs_rev
            };
            annot::Expr::Tuple(occurs)
        }

        TailExpr::TupleField(tuple_id, idx) => {
            let mut tuple_ty = instantiate_type_unused(constrs, ctx.local_binding(*tuple_id));

            let M::Tuple(item_modes) = tuple_ty.modes_mut() else {
                unreachable!();
            };
            item_modes[*idx] = fut_modes.clone();

            let L::Tuple(item_lts) = tuple_ty.lts_mut() else {
                unreachable!();
            };
            item_lts[*idx] = fut_lts.clone();

            let tuple_occur = instantiate_occur(
                strategy,
                customs,
                &mut ctx,
                scopes,
                constrs,
                *tuple_id,
                tuple_ty.modes(),
                tuple_ty.lts(),
            );

            annot::Expr::TupleField(tuple_occur, *idx)
        }

        TailExpr::WrapVariant(_variant_tys, variant_id, content) => {
            let (M::Variants(fut_variant_modes), L::Variants(fut_variant_lts)) =
                (fut_modes, fut_lts)
            else {
                unreachable!();
            };

            let content_occur = instantiate_occur(
                strategy,
                customs,
                &mut ctx,
                scopes,
                constrs,
                *content,
                &fut_variant_modes[*variant_id],
                &fut_variant_lts[*variant_id],
            );

            let fut_variant_tys = IdVec::from_vec(
                fut_variant_modes
                    .values()
                    .zip_eq(fut_variant_lts.values())
                    .map(|(modes, lts)| annot::Type::new(lts.clone(), modes.clone()))
                    .collect(),
            );
            annot::Expr::WrapVariant(fut_variant_tys, *variant_id, content_occur)
        }

        TailExpr::UnwrapVariant(variant_id, wrapped) => {
            let mut wrapped_ty = instantiate_type_unused(constrs, ctx.local_binding(*wrapped));

            let M::Variants(variant_modes) = wrapped_ty.modes_mut() else {
                unreachable!();
            };
            variant_modes[*variant_id] = fut_modes.clone();

            let L::Variants(variant_lts) = wrapped_ty.lts_mut() else {
                unreachable!();
            };
            variant_lts[*variant_id] = fut_lts.clone();

            let wrapped_occur = instantiate_occur(
                strategy,
                customs,
                &mut ctx,
                scopes,
                constrs,
                *wrapped,
                wrapped_ty.modes(),
                wrapped_ty.lts(),
            );

            annot::Expr::UnwrapVariant(*variant_id, wrapped_occur)
        }

        // See I-Rc; this is the operation that constructs new boxes
        TailExpr::WrapBoxed(content, _item_ty) => {
            let (M::Boxed(fut_mode, fut_ov, fut_item_modes), L::Boxed(_, fut_item_lts)) =
                (fut_modes, fut_lts)
            else {
                unreachable!();
            };

            require_owned(constrs, *fut_mode);
            for (m1, m2) in fut_item_modes.iter_stack().zip_eq(fut_ov.iter()) {
                constrs.require_eq(*m1, *m2);
            }

            let content_occur = instantiate_occur(
                strategy,
                customs,
                &mut ctx,
                scopes,
                constrs,
                *content,
                fut_item_modes,
                fut_item_lts,
            );

            annot::Expr::WrapBoxed(
                content_occur,
                annot::Type::new((**fut_item_lts).clone(), (**fut_item_modes).clone()),
            )
        }

        // See I-Get
        TailExpr::UnwrapBoxed(wrapped, _item_ty) => {
            let item_modes = fut_modes
                .iter()
                .map(|_| constrs.fresh_var())
                .collect_mode_data(fut_modes);
            let item_lts = fut_lts.clone();
            let item_ov = fut_modes.unapply_overlay();

            let box_modes = M::Boxed(constrs.fresh_var(), item_ov, Box::new(item_modes.clone()));
            let box_lts = L::Boxed(path.as_lt(), Box::new(fut_lts.clone()));
            let box_occur = instantiate_occur(
                strategy, customs, &mut ctx, scopes, constrs, *wrapped, &box_modes, &box_lts,
            );

            annot::Expr::UnwrapBoxed(box_occur, annot::Type::new(item_lts, item_modes))
        }

        TailExpr::WrapCustom(custom_id, content) => {
            let (M::Custom(fut_id1, fut_osub, fut_msub), L::Custom(fut_id2, fut_lsub)) =
                (fut_modes, fut_lts)
            else {
                unreachable!();
            };

            debug_assert_eq!(*custom_id, *fut_id1);
            debug_assert_eq!(*custom_id, *fut_id2);

            let unfolded_ty = unfold_custom(customs, fut_msub, fut_lsub, fut_osub, *custom_id);
            let unfolded_ov = unfold_overlay(
                customs,
                &fut_osub,
                &customs[*custom_id].ov.hydrate(fut_osub),
            );

            let content_modes = unfolded_ty.modes().apply_overlay(&unfolded_ov);
            let content_lts = unfolded_ty.lts();
            let content_occur = instantiate_occur(
                strategy,
                customs,
                &mut ctx,
                scopes,
                constrs,
                *content,
                &content_modes,
                content_lts,
            );

            annot::Expr::WrapCustom(*custom_id, content_occur)
        }

        TailExpr::UnwrapCustom(custom_id, folded) => {
            let custom = &customs[custom_id];

            let folded_ov = custom
                .ov_slots
                .iter()
                .map(|_| constrs.fresh_var())
                .collect_overlay(&custom.ov);
            let folded_osub = custom
                .ov_slots
                .iter()
                .zip(folded_ov.iter())
                .map(|(slot, m)| (*slot, *m))
                .collect();

            let folded_modes = custom
                .slot_count
                .into_iter()
                .map(|_| constrs.fresh_var())
                .collect_mode_data(ctx.local_binding(*folded).modes());
            let folded_msub = IdVec::from_vec(folded_modes.iter().copied().collect());

            let folded_lsub = custom
                .lt_slots
                .iter()
                .map(|slot| (*slot, lt_count.inc()))
                .collect();

            let raw_unfolded_ty = unfold_custom(
                customs,
                &folded_msub,
                &folded_lsub,
                &folded_osub,
                *custom_id,
            );
            let unfolded_ov = unfold_overlay(customs, &folded_osub, &folded_ov);
            let unfolded_modes = raw_unfolded_ty.modes().apply_overlay(&unfolded_ov);
            let unfolded_lts = raw_unfolded_ty.lts();

            for (m1, m2) in unfolded_modes.iter().zip_eq(fut_modes.iter()) {
                constrs.require_eq(*m1, *m2);
            }

            let lt_subst = lt_bind(&unfolded_lts, fut_lts);
            let folded_lts = folded_lsub
                .iter()
                .map(|(_, lt)| lt_subst[lt].clone())
                .collect_lt_data(ctx.local_binding(*folded).lts());
            let folded_occur = instantiate_occur(
                strategy,
                customs,
                &mut ctx,
                scopes,
                constrs,
                *folded,
                &folded_modes,
                &folded_lts,
            );

            annot::Expr::UnwrapCustom(*custom_id, folded_occur)
        }

        // Right now, all intrinsics are trivial from a mode inference perspective because they
        // operate on arithmetic types. If this changes, we will have to update this.
        TailExpr::Intrinsic(intr, arg) => {
            let sig = intrinsic_sig(*intr);
            let ty = instantiate_prim_type(&sig.arg);
            let arg_occur = Occur { id: *arg, ty };
            annot::Expr::Intrinsic(*intr, arg_occur)
        }

        // See I-Get
        TailExpr::ArrayOp(flat::ArrayOp::Get(_, arr_id, idx_id)) => {
            let item_modes = fut_modes
                .iter()
                .map(|_| constrs.fresh_var())
                .collect_mode_data(fut_modes);
            let item_ov = fut_modes.unapply_overlay();

            let arr_modes = ModeData::Array(constrs.fresh_var(), item_ov, Box::new(item_modes));
            let arr_lts = LtData::Array(path.as_lt(), Box::new(fut_lts.clone()));

            let idx_occur = instantiate_occur(
                strategy,
                customs,
                &mut ctx,
                scopes,
                constrs,
                *idx_id,
                &M::Num(NumType::Int),
                &L::Num(NumType::Int),
            );
            let arr_occur = instantiate_occur(
                strategy, customs, &mut ctx, scopes, constrs, *arr_id, &arr_modes, &arr_lts,
            );

            annot::Expr::ArrayOp(annot::ArrayOp::Get(
                arr_occur,
                idx_occur,
                annot::Type::new(fut_lts.clone(), fut_modes.clone()),
            ))
        }

        TailExpr::ArrayOp(flat::ArrayOp::Extract(_item_ty, arr_id, idx_id)) => {
            let occurs = model::instantiate_model(
                &*spec::SIG_ARRAY_EXTRACT,
                strategy,
                customs,
                constrs,
                &mut ctx,
                scopes,
                &path,
                &[*arr_id, *idx_id],
                fut_modes,
                fut_lts,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::ArrayOp(annot::ArrayOp::Extract(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        TailExpr::ArrayOp(flat::ArrayOp::Len(_item_ty, arr_id)) => {
            let occurs = model::instantiate_model(
                &*spec::SIG_ARRAY_LEN,
                strategy,
                customs,
                constrs,
                &mut ctx,
                scopes,
                &path,
                &[*arr_id],
                fut_modes,
                fut_lts,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::ArrayOp(annot::ArrayOp::Len(occurs.next().unwrap()))
        }

        TailExpr::ArrayOp(flat::ArrayOp::Push(_item_ty, arr_id, item_id)) => {
            let occurs = model::instantiate_model(
                &*spec::SIG_ARRAY_PUSH,
                strategy,
                customs,
                constrs,
                &mut ctx,
                scopes,
                &path,
                &[*arr_id, *item_id],
                fut_modes,
                fut_lts,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::ArrayOp(annot::ArrayOp::Push(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        TailExpr::ArrayOp(flat::ArrayOp::Pop(_item_ty, arr_id)) => {
            let occurs = model::instantiate_model(
                &*spec::SIG_ARRAY_POP,
                strategy,
                customs,
                constrs,
                &mut ctx,
                scopes,
                &path,
                &[*arr_id],
                fut_modes,
                fut_lts,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::ArrayOp(annot::ArrayOp::Pop(occurs.next().unwrap()))
        }

        TailExpr::ArrayOp(flat::ArrayOp::Replace(_item_ty, hole_id, item_id)) => {
            let occurs = model::instantiate_model(
                &*spec::SIG_ARRAY_REPLACE,
                strategy,
                customs,
                constrs,
                &mut ctx,
                scopes,
                &path,
                &[*hole_id, *item_id],
                fut_modes,
                fut_lts,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::ArrayOp(annot::ArrayOp::Replace(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        TailExpr::ArrayOp(flat::ArrayOp::Reserve(_item_ty, arr_id, cap_id)) => {
            let occurs = model::instantiate_model(
                &*spec::SIG_ARRAY_RESERVE,
                strategy,
                customs,
                constrs,
                &mut ctx,
                scopes,
                &path,
                &[*arr_id, *cap_id],
                fut_modes,
                fut_lts,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::ArrayOp(annot::ArrayOp::Reserve(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        TailExpr::IoOp(flat::IoOp::Input) => {
            let _ = model::instantiate_model(
                &*spec::SIG_IO_INPUT,
                strategy,
                customs,
                constrs,
                &mut ctx,
                scopes,
                &path,
                &[],
                fut_modes,
                fut_lts,
            );
            annot::Expr::IoOp(annot::IoOp::Input)
        }

        TailExpr::IoOp(flat::IoOp::Output(arr_id)) => {
            let occurs = model::instantiate_model(
                &*spec::SIG_IO_OUTPUT,
                strategy,
                customs,
                constrs,
                &mut ctx,
                scopes,
                &path,
                &[*arr_id],
                fut_modes,
                fut_lts,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::IoOp(annot::IoOp::Output(occurs.next().unwrap()))
        }

        TailExpr::Panic(_ret_ty, msg_id) => {
            let occurs = model::instantiate_model(
                &*spec::SIG_PANIC,
                strategy,
                customs,
                constrs,
                &mut ctx,
                scopes,
                &path,
                &[*msg_id],
                fut_modes,
                fut_lts,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::Panic(
                annot::Type::new(fut_lts.clone(), fut_modes.clone()),
                occurs.next().unwrap(),
            )
        }

        // See I-Rc; this is the operation that constructs new arrays
        TailExpr::ArrayLit(_item_ty, item_ids) => {
            let (M::Array(fut_mode, _, fut_item_modes), L::Array(_, fut_item_lts)) =
                (fut_modes, fut_lts)
            else {
                unreachable!();
            };

            require_owned(constrs, *fut_mode);

            let mut item_occurs_rev: Vec<_> = item_ids
                .iter()
                // We must process the items in reverse order to ensure `instantiate_occur` (which
                // updates the lifetimes in `ctx`) generates the correct constraints.
                .rev()
                .map(|item_id| {
                    instantiate_occur(
                        strategy,
                        customs,
                        &mut ctx,
                        scopes,
                        constrs,
                        *item_id,
                        fut_item_modes,
                        fut_item_lts,
                    )
                })
                .collect();

            let item_occurs = {
                item_occurs_rev.reverse();
                item_occurs_rev
            };
            annot::Expr::ArrayLit(
                annot::Type::new((**fut_item_lts).clone(), (**fut_item_modes).clone()),
                item_occurs,
            )
        }

        TailExpr::BoolLit(val) => annot::Expr::BoolLit(*val),

        TailExpr::ByteLit(val) => annot::Expr::ByteLit(*val),

        TailExpr::IntLit(val) => annot::Expr::IntLit(*val),

        TailExpr::FloatLit(val) => annot::Expr::FloatLit(*val),
    };

    (expr_annot, ctx.into_updates())
}

#[derive(Clone, Debug)]
struct SolverScc {
    func_args: BTreeMap<CustomFuncId, annot::Type<ModeVar, Lt>>,
    func_rets: BTreeMap<CustomFuncId, annot::Type<ModeVar, LtParam>>,
    func_bodies: BTreeMap<CustomFuncId, annot::Expr<ModeVar, Lt>>,
    scc_constrs: ConstrGraph,
}

fn process_arg_ty(ty: &annot::Type<ModeVar, Lt>) -> annot::Type<ModeVar, Lt> {
    ty.map_lts(|lt| match lt {
        Lt::Empty => Lt::Empty,
        Lt::Local(_) => Lt::Empty,
        Lt::Join(vars) => Lt::Join(vars.clone()),
    })
}

fn instantiate_scc(
    strategy: Strategy,
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    funcs: &IdVec<CustomFuncId, TailFuncDef>,
    funcs_annot: &IdMap<CustomFuncId, annot::FuncDef>,
    scc: Scc<CustomFuncId>,
    renderer: &CustomTypeRenderer<CustomTypeId>,
) -> SolverScc {
    match scc.kind {
        SccKind::Acyclic | SccKind::Cyclic => {
            // TODO: if the SCC is acyclic, we can skip lifetime fixed point iteration

            let mut constrs = ConstrGraph::new();
            let mut next_lt = Count::new();

            let mut arg_tys = scc
                .nodes
                .iter()
                .map(|id| {
                    (
                        *id,
                        instantiate_type_unused(
                            &mut constrs,
                            &parameterize_type_simple(customs, &funcs[id].arg_type),
                        ),
                    )
                })
                .collect::<BTreeMap<_, _>>();

            let mut first_lt = next_lt;
            let ret_tys = scc
                .nodes
                .iter()
                .map(|id| {
                    (
                        *id,
                        instantiate_type(
                            &mut constrs,
                            &mut || next_lt.inc(),
                            &parameterize_type_simple(customs, &funcs[id].ret_type),
                        ),
                    )
                })
                .collect::<BTreeMap<_, _>>();

            let debug_sig_params = if cfg!(debug_assertions) {
                let mut params = BTreeSet::new();
                while first_lt != next_lt {
                    params.insert(first_lt.inc());
                }
                params
            } else {
                BTreeSet::new()
            };

            let (new_arg_tys, bodies) = loop {
                let mut new_arg_tys = BTreeMap::new();
                let mut bodies = BTreeMap::new();
                let assumptions = SignatureAssumptions {
                    known_defs: &funcs_annot,
                    pending_args: &arg_tys,
                    pending_rets: &ret_tys,
                };

                for id in scc.nodes {
                    let func = &funcs[id];

                    let mut ctx = ImmutContext::new();
                    let arg_ty = instantiate_type_unused(
                        &mut constrs,
                        &parameterize_type_simple(customs, &func.arg_type),
                    );
                    let arg_id = ctx.add_local(Rc::new(arg_ty.clone())); // TODO: don't clone; use RC everywhere
                    debug_assert_eq!(arg_id, flat::ARG_LOCAL);

                    let mut scopes = LocalContext::new();
                    let arg_id = scopes.add_local(annot::ARG_SCOPE());
                    debug_assert_eq!(arg_id, flat::ARG_LOCAL);

                    let ret_ty = &ret_tys[id];
                    let (expr, updates) = instantiate_expr(
                        strategy,
                        customs,
                        assumptions,
                        &mut constrs,
                        &mut next_lt,
                        &ctx,
                        &mut scopes,
                        annot::FUNC_BODY_PATH(),
                        ret_ty.modes(),
                        &ret_ty.lts().wrap_params(),
                        &func.body,
                        renderer,
                    );
                    bodies.insert(*id, expr);

                    debug_assert!(updates.len() <= 1);
                    if let Some(update) = updates.local_binding(flat::ARG_LOCAL) {
                        ctx.update_local(flat::ARG_LOCAL, update.clone());
                    }

                    let raw_arg_ty = ctx.local_binding(flat::ARG_LOCAL);
                    new_arg_tys.insert(*id, process_arg_ty(raw_arg_ty));
                }

                debug_assert!(
                    {
                        let params_found = new_arg_tys
                            .values()
                            .flat_map(|ty| ty.lts().iter())
                            .filter_map(|lt: &Lt| match lt {
                                Lt::Empty | Lt::Local(_) => None,
                                Lt::Join(params) => Some(params.iter().copied()),
                            })
                            .flatten()
                            .collect();
                        debug_sig_params.is_superset(&params_found)
                    },
                    "Some temporary lifetime parameters leaked into the function arguments during \
                     expression instantiation. Only parameters from the return type should appear"
                );

                if new_arg_tys
                    .values()
                    .zip_eq(arg_tys.values())
                    .all(|(new, old)| lt_equiv(new.lts(), old.lts()))
                {
                    break (new_arg_tys, bodies);
                }

                arg_tys = new_arg_tys;
            };

            // TODO: we could avoid a lot of the work in this case, but this is the simplest
            // intervention point
            if strategy == Strategy::AlwaysOwned {
                for var in constrs.var_count() {
                    require_owned(&mut constrs, var);
                }
            }

            if strategy == Strategy::OnlyTrivialBorrows {
                for var in ret_tys.values().flat_map(|ty| ty.modes().iter()) {
                    require_owned(&mut constrs, *var);
                }
            }

            SolverScc {
                func_args: new_arg_tys,
                func_rets: ret_tys,
                func_bodies: bodies,
                scc_constrs: constrs,
            }
        }
    }
}

// -------------------
// Step 3: Extraction
// -------------------
// The final step of the algorithm is to extract the annotated program from the solution to the mode
// contraints.

type Solution = in_eq::Solution<ModeVar, ModeParam, Mode>;

fn extract_type(
    solution: &Solution,
    ty: &annot::Type<ModeVar, Lt>,
) -> annot::Type<ModeSolution, Lt> {
    ty.map_modes(|m| ModeSolution {
        lb: solution.lower_bounds[*m].clone(),
        solver_var: *m,
    })
}

fn extract_occur(
    solution: &Solution,
    occur: &Occur<ModeVar, Lt>,
) -> annot::Occur<ModeSolution, Lt> {
    annot::Occur {
        id: occur.id,
        ty: extract_type(solution, &occur.ty),
    }
}

fn extract_condition(
    solution: &Solution,
    cond: &annot::Condition<ModeVar, Lt>,
) -> annot::Condition<ModeSolution, Lt> {
    match cond {
        annot::Condition::Any => annot::Condition::Any,
        annot::Condition::Tuple(conds) => annot::Condition::Tuple(
            conds
                .iter()
                .map(|cond| extract_condition(solution, cond))
                .collect(),
        ),
        annot::Condition::Variant(id, cond) => {
            annot::Condition::Variant(*id, Box::new(extract_condition(solution, cond)))
        }
        annot::Condition::Boxed(cond, ty) => annot::Condition::Boxed(
            Box::new(extract_condition(solution, cond)),
            extract_type(solution, ty),
        ),
        annot::Condition::Custom(id, cond) => {
            annot::Condition::Custom(*id, Box::new(extract_condition(solution, cond)))
        }
        annot::Condition::BoolConst(v) => annot::Condition::BoolConst(*v),
        annot::Condition::ByteConst(v) => annot::Condition::ByteConst(*v),
        annot::Condition::IntConst(v) => annot::Condition::IntConst(*v),
        annot::Condition::FloatConst(v) => annot::Condition::FloatConst(*v),
    }
}

fn extract_expr(
    solution: &Solution,
    expr: &annot::Expr<ModeVar, Lt>,
) -> annot::Expr<ModeSolution, Lt> {
    use annot::Expr as E;
    match expr {
        E::Local(occur) => E::Local(extract_occur(solution, occur)),
        E::Call(purity, func, arg) => E::Call(*purity, *func, extract_occur(solution, arg)),
        E::Branch(discrim, branches, ret_ty) => E::Branch(
            extract_occur(solution, discrim),
            branches
                .iter()
                .map(|(cond, body)| {
                    (
                        extract_condition(solution, cond),
                        extract_expr(solution, body),
                    )
                })
                .collect(),
            extract_type(solution, ret_ty),
        ),
        E::LetMany(bindings, result) => E::LetMany(
            bindings
                .iter()
                .map(|(ty, expr)| (extract_type(solution, ty), extract_expr(solution, expr)))
                .collect(),
            extract_occur(solution, result),
        ),
        E::Tuple(items) => E::Tuple(
            items
                .iter()
                .map(|occur| extract_occur(solution, occur))
                .collect(),
        ),
        E::TupleField(tup, idx) => E::TupleField(extract_occur(solution, tup), *idx),
        E::WrapVariant(variant_tys, id, content) => E::WrapVariant(
            variant_tys.map_refs(|_, ty| extract_type(solution, ty)),
            *id,
            extract_occur(solution, content),
        ),
        E::UnwrapVariant(id, wrapped) => E::UnwrapVariant(*id, extract_occur(solution, wrapped)),
        E::WrapBoxed(content, item_ty) => E::WrapBoxed(
            extract_occur(solution, content),
            extract_type(solution, item_ty),
        ),
        E::UnwrapBoxed(wrapped, item_ty) => E::UnwrapBoxed(
            extract_occur(solution, wrapped),
            extract_type(solution, item_ty),
        ),
        E::WrapCustom(id, content) => E::WrapCustom(*id, extract_occur(solution, content)),
        E::UnwrapCustom(id, wrapped) => E::UnwrapCustom(*id, extract_occur(solution, wrapped)),
        E::Intrinsic(intr, arg) => E::Intrinsic(*intr, extract_occur(solution, arg)),
        E::ArrayOp(annot::ArrayOp::Get(arr, idx, out_ty)) => E::ArrayOp(annot::ArrayOp::Get(
            extract_occur(solution, arr),
            extract_occur(solution, idx),
            extract_type(solution, out_ty),
        )),
        E::ArrayOp(annot::ArrayOp::Extract(arr, idx)) => E::ArrayOp(annot::ArrayOp::Extract(
            extract_occur(solution, arr),
            extract_occur(solution, idx),
        )),
        E::ArrayOp(annot::ArrayOp::Len(arr)) => {
            E::ArrayOp(annot::ArrayOp::Len(extract_occur(solution, arr)))
        }
        E::ArrayOp(annot::ArrayOp::Push(arr, item)) => E::ArrayOp(annot::ArrayOp::Push(
            extract_occur(solution, arr),
            extract_occur(solution, item),
        )),
        E::ArrayOp(annot::ArrayOp::Pop(arr)) => {
            E::ArrayOp(annot::ArrayOp::Pop(extract_occur(solution, arr)))
        }
        E::ArrayOp(annot::ArrayOp::Replace(hole, item)) => E::ArrayOp(annot::ArrayOp::Replace(
            extract_occur(solution, hole),
            extract_occur(solution, item),
        )),
        E::ArrayOp(annot::ArrayOp::Reserve(arr, cap)) => E::ArrayOp(annot::ArrayOp::Reserve(
            extract_occur(solution, arr),
            extract_occur(solution, cap),
        )),
        E::IoOp(annot::IoOp::Input) => E::IoOp(annot::IoOp::Input),
        E::IoOp(annot::IoOp::Output(arr)) => {
            E::IoOp(annot::IoOp::Output(extract_occur(solution, arr)))
        }
        E::Panic(ret_ty, msg) => {
            E::Panic(extract_type(solution, ret_ty), extract_occur(solution, msg))
        }
        E::ArrayLit(item_ty, items) => E::ArrayLit(
            extract_type(solution, item_ty),
            items
                .iter()
                .map(|occur| extract_occur(solution, occur))
                .collect(),
        ),
        E::BoolLit(v) => E::BoolLit(*v),
        E::ByteLit(v) => E::ByteLit(*v),
        E::IntLit(v) => E::IntLit(*v),
        E::FloatLit(v) => E::FloatLit(*v),
    }
}

// ---------
// Main Loop
// ---------
// The main loop of the algorithm which performs parameterization, instantiation, and extraction for
// each SCC of functions.

fn solve_scc(
    strategy: Strategy,
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    funcs: &IdVec<CustomFuncId, TailFuncDef>,
    funcs_annot: &mut IdMap<CustomFuncId, annot::FuncDef>,
    scc: Scc<CustomFuncId>,
    renderer: &CustomTypeRenderer<CustomTypeId>,
) {
    let instantiated = instantiate_scc(strategy, customs, funcs, funcs_annot, scc, renderer);

    let mut sig_vars = BTreeSet::new();
    for func_id in scc.nodes {
        sig_vars.extend(instantiated.func_args[&func_id].modes().iter());
        sig_vars.extend(instantiated.func_rets[&func_id].modes().iter());
    }

    let solution: Solution = instantiated.scc_constrs.solve(&sig_vars);

    // Extract the subset of the constraints relevant to the signature
    let mut sig_constrs = IdMap::new();
    for (var, lb) in &solution.lower_bounds {
        if sig_vars.contains(&var) {
            // `solution.lower_bounds` contains duplicate information if two internal variables get
            // mapped to the same external variable (are in the same SCC). This is convenient some
            // places, but maybe it would be cleaner to avoid doing this.
            let external = solution.internal_to_external[&var];
            if let Some(old_lb) = sig_constrs.get(external) {
                debug_assert_eq!(old_lb, lb);
            } else {
                sig_constrs.insert(external, lb.clone());
            }
        }
    }

    let sig_constrs = sig_constrs.to_id_vec(solution.num_external);

    for func_id in scc.nodes {
        let arg_ty = &instantiated.func_args[&func_id];
        let ret_ty = &instantiated.func_rets[&func_id];

        let func = &funcs[func_id];
        let remap_internal = |internal: &ModeVar| solution.internal_to_external[internal];
        funcs_annot.insert_vacant(
            *func_id,
            annot::FuncDef {
                purity: func.purity,
                arg_ty: arg_ty.map_modes(remap_internal),
                ret_ty: ret_ty.map_modes(remap_internal),
                constrs: annot::Constrs {
                    sig: sig_constrs.clone(),
                    all: instantiated.scc_constrs.clone(),
                },
                body: extract_expr(&solution, &instantiated.func_bodies[&func_id]),
                profile_point: func.profile_point.clone(),
            },
        );
    }
}

fn sanity_check_expr<M, L>(
    renderer: &CustomTypeRenderer<CustomTypeId>,
    funcs: &IdVec<CustomFuncId, annot::FuncDef>,
    param_count: Count<ModeParam>,
    path: &annot::Path,
    ctx: &mut LocalContext<LocalId, LtData<Lt>>,
    ret_ty: &annot::Type<M, L>,
    expr: &annot::Expr<ModeSolution, Lt>,
) {
    // Check that the variable's binding and occurrence types are consistent
    let check_occur = |ctx: &mut LocalContext<_, LtData<Lt>>, occur: &Occur<_, _>| {
        assert!(ctx.local_binding(occur.id).shape() == occur.ty.shape());
    };

    // Check that the variable is live at the current path
    let access = |ctx: &mut LocalContext<_, LtData<Lt>>, occur: &annot::Occur<_, _>| {
        let lt = match ctx.local_binding(occur.id) {
            LtData::Array(lt, _) => lt,
            LtData::HoleArray(lt, _) => lt,
            LtData::Boxed(lt, _) => lt,
            _ => panic!("expected array or boxed type"),
        };
        assert!(lt.contains(path));
    };

    match expr {
        annot::Expr::Local(local) => {
            check_occur(ctx, local);
        }

        annot::Expr::Call(_, func, arg) => {
            check_occur(ctx, arg);

            // Check that the function is called correctly
            let func = &funcs[*func];
            assert!(func.arg_ty.shape() == arg.ty.shape());
            assert!(func.ret_ty.shape() == ret_ty.shape());
        }

        annot::Expr::LetMany(bindings, _) => ctx.with_scope(|ctx| {
            for (i, (ty, body)) in bindings.iter().enumerate() {
                // Check that all type parameters also appear in the signature
                for solution in ty.modes().iter() {
                    for param in &solution.lb.lb_vars {
                        assert!(param_count.contains(param));
                    }
                }

                sanity_check_expr(renderer, funcs, param_count, &path.seq(i), ctx, ty, body);
                ctx.add_local(ty.lts().clone());
            }
        }),

        annot::Expr::Branch(discrim, cases, ty) => {
            assert!(ty.shape() == ret_ty.shape());
            check_occur(ctx, discrim);
            for (i, (_, body)) in cases.iter().enumerate() {
                sanity_check_expr(
                    renderer,
                    funcs,
                    param_count,
                    &path.alt(i, cases.len()),
                    ctx,
                    ret_ty,
                    body,
                );
            }
        }

        annot::Expr::Tuple(items) => {
            for item in items {
                check_occur(ctx, item);
            }
        }
        annot::Expr::TupleField(tup, idx) => {
            let annot::ModeData::Tuple(item_tys) = tup.ty.modes() else {
                panic!("expected tuple type");
            };
            assert!(item_tys[*idx].shape() == ret_ty.modes().shape());
            check_occur(ctx, tup);
        }
        annot::Expr::WrapVariant(variants, _variant_id, wrapped) => {
            let annot::ModeData::Variants(ret_tys) = ret_ty.modes() else {
                panic!("expected variant type");
            };
            for (ty1, ty2) in variants.values().zip_eq(ret_tys.values()) {
                assert!(ty1.shape() == ty2.shape());
            }
            check_occur(ctx, wrapped);
        }
        annot::Expr::UnwrapVariant(_, wrapped) => {
            check_occur(ctx, wrapped);
        }
        annot::Expr::WrapBoxed(content, _) => {
            check_occur(ctx, content);
        }
        annot::Expr::UnwrapBoxed(wrapped, _) => {
            access(ctx, wrapped);
            check_occur(ctx, wrapped);
        }
        annot::Expr::WrapCustom(_, content) => {
            check_occur(ctx, content);
        }
        annot::Expr::UnwrapCustom(_, wrapped) => {
            check_occur(ctx, wrapped);
        }
        annot::Expr::Intrinsic(_, arg) => {
            check_occur(ctx, arg);
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Get(arr, idx, ty)) => {
            assert!(ty.shape() == ret_ty.shape());
            access(ctx, arr);
            check_occur(ctx, arr);
            check_occur(ctx, idx);
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Extract(arr, idx)) => {
            access(ctx, arr);
            check_occur(ctx, arr);
            check_occur(ctx, idx);
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Len(arr)) => {
            check_occur(ctx, arr);
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Push(arr, item)) => {
            access(ctx, arr);
            check_occur(ctx, arr);
            check_occur(ctx, item);
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Pop(arr)) => {
            access(ctx, arr);
            check_occur(ctx, arr);
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Replace(hole, item)) => {
            access(ctx, hole);
            check_occur(ctx, hole);
            check_occur(ctx, item);
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Reserve(arr, cap)) => {
            access(ctx, arr);
            check_occur(ctx, arr);
            check_occur(ctx, cap);
        }
        annot::Expr::IoOp(annot::IoOp::Input) => {}
        annot::Expr::IoOp(annot::IoOp::Output(arr)) => {
            access(ctx, arr);
            check_occur(ctx, arr);
        }
        annot::Expr::Panic(ty, msg) => {
            assert!(ty.shape() == ret_ty.shape());
            check_occur(ctx, msg);
        }
        annot::Expr::ArrayLit(item_ty, items) => {
            for item in items {
                assert!(item_ty.shape() == item.ty.shape());
                check_occur(ctx, item);
            }
        }
        annot::Expr::BoolLit(_) => {
            assert!(ret_ty.shape() == annot::Shape::Bool);
        }
        annot::Expr::ByteLit(_) => {
            assert!(ret_ty.shape() == annot::Shape::Num(NumType::Byte));
        }
        annot::Expr::IntLit(_) => {
            assert!(ret_ty.shape() == annot::Shape::Num(NumType::Int));
        }
        annot::Expr::FloatLit(_) => {
            assert!(ret_ty.shape() == annot::Shape::Num(NumType::Float));
        }
    }
}

fn sanity_check_funcs(
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    _func_renderer: &FuncRenderer<CustomFuncId>,
    funcs: &IdVec<CustomFuncId, annot::FuncDef>,
) {
    for (_func_id, func) in funcs {
        let param_count = func.constrs.sig.count();

        // Check that constrains only refer to signature parameters
        for lb in func.constrs.sig.values() {
            for param in lb.lb_vars.iter() {
                assert!(param_count.contains(param));
            }
        }

        // Check that all signature parameters are used and that there are no missing parameters
        let mut present = IdVec::from_count_with(param_count, |_| false);
        for param in func.arg_ty.modes().iter() {
            present[param] = true;
        }
        for param in func.ret_ty.modes().iter() {
            present[param] = true;
        }
        assert!(present.into_values().all(|b| b));

        // Sanity check the body of the function
        let mut ctx = LocalContext::new();
        ctx.add_local(func.arg_ty.lts().clone());
        sanity_check_expr(
            type_renderer,
            funcs,
            param_count,
            &annot::FUNC_BODY_PATH(),
            &mut ctx,
            &func.ret_ty,
            &func.body,
        );
    }
}

fn add_func_deps(deps: &mut BTreeSet<CustomFuncId>, expr: &TailExpr) {
    match expr {
        TailExpr::Call(_, _, other, _) => {
            deps.insert(*other);
        }
        TailExpr::Branch(_, cases, _) => {
            for (_, body) in cases {
                add_func_deps(deps, body);
            }
        }
        TailExpr::LetMany(bindings, _) => {
            for (_, rhs) in bindings {
                add_func_deps(deps, rhs);
            }
        }
        _ => {}
    }
}

fn convert_type_sccs(
    orig: &IdVec<CustomTypeSccId, old_graph::Scc<CustomTypeId>>,
) -> Sccs<CustomTypeSccId, CustomTypeId> {
    let mut sccs: Sccs<CustomTypeSccId, _> = Sccs::new();
    for (id, scc) in orig {
        let push_id = match scc {
            old_graph::Scc::Acyclic(node) => sccs.push_acyclic_component(*node),
            old_graph::Scc::Cyclic(nodes) => sccs.push_cyclic_component(nodes),
        };
        debug_assert_eq!(push_id, id);
    }
    sccs
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strategy {
    Default,
    AlwaysOwned,        // similar to "Perceus"
    OnlyTrivialBorrows, // similar to "Immutable Beans"
}

pub fn annot_modes(
    program: flat::Program,
    strategy: Strategy,
    progress: impl ProgressLogger,
) -> annot::Program {
    let type_renderer = CustomTypeRenderer::from_symbols(&program.custom_type_symbols);
    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);

    let custom_sccs = convert_type_sccs(&program.custom_types.sccs);
    let mut rev_custom_sccs = IdMap::new();
    for (scc_id, scc) in &custom_sccs {
        for &custom_id in scc.nodes {
            rev_custom_sccs.insert_vacant(custom_id, scc_id);
        }
    }

    let rev_sccs = rev_custom_sccs.to_id_vec(program.custom_types.types.count());
    let customs = parameterize_customs(&program.custom_types, &rev_sccs);

    let funcs = compute_tail_calls(&program.funcs);

    #[id_type]
    struct FuncSccId(usize);

    let func_sccs: Sccs<FuncSccId, _> = find_components(funcs.count(), |id| {
        let mut deps = BTreeSet::new();
        add_func_deps(&mut deps, &funcs[id].body);
        deps
    });

    let mut progress = progress.start_session(Some(program.funcs.len()));

    let mut funcs_annot = IdMap::new();
    for (_, scc) in &func_sccs {
        solve_scc(
            strategy,
            &customs,
            &funcs,
            &mut funcs_annot,
            scc,
            &type_renderer,
        );
        progress.update(scc.nodes.len());
    }

    let funcs = funcs_annot.to_id_vec(funcs.count());

    #[cfg(debug_assertions)]
    sanity_check_funcs(&type_renderer, &func_renderer, &funcs);

    progress.finish();

    annot::Program {
        mod_symbols: program.mod_symbols,
        custom_types: annot::CustomTypes { types: customs },
        custom_type_symbols: program.custom_type_symbols,
        funcs,
        func_symbols: program.func_symbols,
        profile_points: program.profile_points,
        main: program.main,
    }
}
