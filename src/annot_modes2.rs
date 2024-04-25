//! This module implements the specializing variant of first compiler pass described in the borrow
//! inference paper. A signficant proportion of the machinery is dedicated to specialization. The
//! core logic for the pass is contained in `instantiate_expr`.

use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast::{CustomFuncId, CustomTypeId, NumType};
use crate::data::flat_ast::{self as flat, CustomTypeSccId, LocalId};
use crate::data::intrinsics as intr;
use crate::data::mode_annot_ast2::{
    self as annot, Lt, LtParam, Mode, ModeParam, ModeSolution, ModeVar, Occur, OverlaySubst,
    TypeSubst,
};
use crate::intrinsic_config::intrinsic_sig;
// use crate::pretty_print::mode_annot as pp;
use crate::pretty_print::utils::CustomTypeRenderer;
use crate::util::graph as old_graph; // TODO: switch completely to `id_graph_sccs`
use crate::util::inequality_graph2 as in_eq;
use crate::util::iter::IterExt;
use crate::util::local_context::LocalContext;
use crate::util::map_ext::MapExt;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{id_type, Count, Id, IdMap, IdVec};
use id_graph_sccs::{find_components, Scc, SccKind, Sccs};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

type SolverType = annot::Type<ModeVar, Lt>;
type SolverOccur = annot::Occur<ModeVar, Lt>;
type SolverOverlay = annot::Overlay<ModeVar>;
type SolverCondition = annot::Condition<ModeVar, Lt>;
type SolverExpr = annot::Expr<ModeVar, Lt>;

trait Map {
    type K;
    type V;
    fn get(&self, i: Self::K) -> Option<&Self::V>;
}

impl<K: Ord, V> Map for BTreeMap<K, V> {
    type K = K;
    type V = V;
    fn get(&self, k: K) -> Option<&V> {
        self.get(&k)
    }
}

impl<I: Id, V> Map for IdVec<I, V> {
    type K = I;
    type V = V;
    fn get(&self, i: I) -> Option<&V> {
        self.get(i)
    }
}

impl<I: Id, V> Map for IdMap<I, V> {
    type K = I;
    type V = V;
    fn get(&self, i: I) -> Option<&V> {
        self.get(i)
    }
}

// ------------------------
// Step 1: Parameterization
// ------------------------
// We start by lifting the set of custom type definitions from the previous pass into the current
// pass by annotating them with fresh mode and lifetime parameters.

fn count_lt_params<'a, A: 'a, B: 'a, C: 'a, D: 'a>(
    customs: &'a impl Map<K = CustomTypeId, V = annot::TypeDef>,
    ty: annot::TypeLike<'a, A, B, C, D>,
) -> usize {
    ty.map(
        &|id, _| customs.get(id).unwrap().num_lt_params.to_value(),
        &|_| 1,
        &|_, _| 0,
        &|_| 0,
    )
    .fold(0, &|a, b| a + b)
}

fn count_mode_params<'a, A: 'a, B: 'a, C: 'a, D: 'a>(
    customs: &'a impl Map<K = CustomTypeId, V = annot::TypeDef>,
    ty: annot::TypeLike<'a, A, B, C, D>,
) -> usize {
    ty.map(
        &|id, _| {
            let typedef = customs.get(id).unwrap();
            typedef.num_mode_params.to_value() + typedef.overlay_params.len()
        },
        &|_| 1,
        &|id, _| customs.get(id).unwrap().overlay_params.len(),
        &|_| 1,
    )
    .fold(0, &|a, b| a + b)
}

fn collect_overlay_modes(ov: &annot::Overlay<ModeParam>) -> BTreeSet<ModeParam> {
    let mut params = BTreeSet::new();
    let cell = RefCell::new(&mut params);
    ov.items().for_each(
        &|_, osub| {
            for p in osub.0.values() {
                debug_assert!(!cell.borrow().contains(p));
                cell.borrow_mut().insert(*p);
            }
        },
        &|m| {
            debug_assert!(!cell.borrow().contains(m));
            cell.borrow_mut().insert(*m);
        },
    );
    params
}

fn parameterize_type(
    parameterized: &IdMap<CustomTypeId, annot::TypeDef>,
    mode_count: &mut Count<ModeParam>,
    lt_count: &mut Count<LtParam>,
    sccs: &IdVec<CustomTypeId, CustomTypeSccId>,
    self_id: CustomTypeSccId,
    ty: &anon::Type,
) -> annot::Type<ModeParam, LtParam> {
    let mode_count = RefCell::new(mode_count);
    let lt_count = RefCell::new(lt_count);

    let fresh_mode = || mode_count.borrow_mut().inc();
    let fresh_lt = || lt_count.borrow_mut().inc();
    let fresh_overlay_params = |id| {
        OverlaySubst(
            parameterized[id]
                .overlay_params
                .iter()
                .map(|p| (*p, fresh_mode()))
                .collect(),
        )
    };

    ty.items(Some((sccs, self_id)))
        .map(
            &|id, _| {
                let typedef = &parameterized[id];
                (
                    TypeSubst {
                        ms: IdVec::from_count_with(typedef.num_mode_params, |_| fresh_mode()),
                        lts: IdVec::from_count_with(typedef.num_lt_params, |_| fresh_lt()),
                    },
                    fresh_overlay_params(id),
                )
            },
            &|_| (fresh_mode(), fresh_lt()),
            &|id, _| fresh_overlay_params(id),
            &|_| fresh_mode(),
        )
        .collect_ty()
}

fn parameterize_custom_scc(
    parameterized: &IdMap<CustomTypeId, annot::TypeDef>,
    customs: &IdVec<CustomTypeId, flat::CustomTypeDef>,
    custom_sccs: &IdVec<CustomTypeId, CustomTypeSccId>,
    self_id: CustomTypeSccId,
    scc: &old_graph::Scc<CustomTypeId>,
) -> BTreeMap<CustomTypeId, annot::TypeDef> {
    let scc_num_mode_params = Count::from_value(
        scc.iter()
            .map(|id| {
                count_mode_params(
                    parameterized,
                    customs[*id].content.items(Some((custom_sccs, self_id))),
                )
            })
            .sum(),
    );

    let scc_num_lt_params = Count::from_value(
        scc.iter()
            .map(|id| {
                count_lt_params(
                    parameterized,
                    customs[*id].content.items(Some((custom_sccs, self_id))),
                )
            })
            .sum(),
    );

    let mut mode_count = Count::new();
    let mut lt_count = Count::new();

    let mut bodies = BTreeMap::new();
    let mut scc_overlay_params = BTreeSet::new();

    for id in scc.iter() {
        let content = parameterize_type(
            parameterized,
            &mut mode_count,
            &mut lt_count,
            custom_sccs,
            self_id,
            &customs[*id].content,
        );

        let overlay = content
            .overlay_items()
            .map(&|_, osub| osub.clone(), &|m| *m)
            .collect_ov();

        let overlay_params = collect_overlay_modes(&overlay);

        for p in overlay_params {
            debug_assert!(!scc_overlay_params.contains(&p));
            scc_overlay_params.insert(p);
        }

        bodies.insert(*id, (content, overlay));
    }

    debug_assert_eq!(scc_num_mode_params, mode_count);
    debug_assert_eq!(scc_num_lt_params, lt_count);

    bodies
        .into_iter()
        .map(|(id, (content, overlay))| {
            (
                id,
                annot::TypeDef {
                    num_mode_params: scc_num_mode_params,
                    num_lt_params: scc_num_lt_params,
                    overlay_params: scc_overlay_params.clone(),
                    content,
                    overlay,
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
            parameterize_custom_scc(&parameterized, &customs.types, custom_sccs, scc_id, scc);

        debug_assert_eq!(
            to_populate.keys().collect::<BTreeSet<_>>(),
            scc.iter().collect::<BTreeSet<_>>()
        );

        for (id, typedef) in to_populate {
            parameterized.insert(id, typedef);
        }
        // println!("Parameterized SCC {:?}", scc_id);
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
// much simpler than the constraints on modes, we don't address them explictally. Instead, we take
// lifetime meets (i.e. greatest lower bounds) as needed as we go.

type ConstrGraph = in_eq::ConstrGraph<ModeVar, Mode>;

fn mode_bind_overlays(constrs: &mut ConstrGraph, ov1: &SolverOverlay, ov2: &SolverOverlay) {
    let constrs = RefCell::new(constrs);
    ov1.items().zip(ov2.items()).for_each(
        &|_, (subst1, subst2)| {
            for (m1, m2) in subst1.0.values().zip_eq(subst2.0.values()) {
                constrs.borrow_mut().require_eq(*m1, *m2);
            }
        },
        &|(m1, m2)| {
            constrs.borrow_mut().require_eq(*m1, *m2);
        },
    )
}

fn mode_bind<L1, L2>(
    constrs: &mut ConstrGraph,
    ty1: &annot::Type<ModeVar, L1>,
    ty2: &annot::Type<ModeVar, L2>,
) {
    let constrs = RefCell::new(constrs);
    ty1.items().zip(ty2.items()).for_each(
        &|_, ((tsub1, osub1), (tsub2, osub2))| {
            for (m1, m2) in tsub1.ms.values().zip_eq(tsub2.ms.values()) {
                constrs.borrow_mut().require_eq(*m1, *m2);
            }
            for (m1, m2) in osub1.0.values().zip_eq(osub2.0.values()) {
                constrs.borrow_mut().require_eq(*m1, *m2);
            }
        },
        &|((m1, _), (m2, _))| {
            constrs.borrow_mut().require_eq(*m1, *m2);
        },
        &|_, (subst1, subst2)| {
            for (m1, m2) in subst1.0.values().zip_eq(subst2.0.values()) {
                constrs.borrow_mut().require_eq(*m1, *m2);
            }
        },
        &|(m1, m2)| {
            constrs.borrow_mut().require_eq(*m1, *m2);
        },
    )
}

fn require_owned(constrs: &mut ConstrGraph, var: ModeVar) {
    constrs.require_lte_const(&Mode::Owned, var);
}

fn emit_occur_constr(
    constrs: &mut ConstrGraph,
    scope: &annot::Path,
    binding_lt: &Lt,
    use_lt: &Lt,
    binding_mode: ModeVar,
    use_mode: ModeVar,
) {
    if use_lt.does_not_exceed(scope) {
        if *binding_lt == Lt::Empty && *use_lt != Lt::Empty {
            // Case: this is a non-escaping, final ("opportunistic") occurrence.
            constrs.require_lte(use_mode, binding_mode);
        }
    } else {
        // Case: this is an escaping ("move" or "dup") occurrence.
        constrs.require_lte(binding_mode, use_mode);
    }
}

fn emit_occur_constrs_overlay(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    constrs: &mut ConstrGraph,
    scope: &annot::Path,
    binding_ty: &SolverType,
    fut_ty: &SolverType,
    binding_ov: &SolverOverlay,
    fut_ov: &SolverOverlay,
) {
    match (binding_ty, fut_ty, binding_ov, fut_ov) {
        (annot::Type::Bool, annot::Type::Bool, annot::Overlay::Bool, annot::Overlay::Bool) => {}
        (
            annot::Type::Num(n1),
            annot::Type::Num(n2),
            annot::Overlay::Num(n3),
            annot::Overlay::Num(n4),
        ) if n1 == n2 && n1 == n3 && n1 == n4 => {}
        (
            annot::Type::Tuple(tys1),
            annot::Type::Tuple(tys2),
            annot::Overlay::Tuple(os1),
            annot::Overlay::Tuple(os2),
        ) => {
            for (((ty1, ty2), o1), o2) in tys1.iter().zip_eq(tys2).zip_eq(os1).zip_eq(os2) {
                emit_occur_constrs_overlay(customs, constrs, scope, ty1, ty2, o1, o2);
            }
        }
        (
            annot::Type::Variants(tys1),
            annot::Type::Variants(tys2),
            annot::Overlay::Variants(os1),
            annot::Overlay::Variants(os2),
        ) => {
            for (((ty1, ty2), o1), o2) in tys1
                .values()
                .zip_eq(tys2.values())
                .zip_eq(os1.values())
                .zip_eq(os2.values())
            {
                emit_occur_constrs_overlay(customs, constrs, scope, ty1, ty2, o1, o2);
            }
        }
        (
            annot::Type::SelfCustom(id1),
            annot::Type::SelfCustom(id2),
            annot::Overlay::SelfCustom(id3),
            annot::Overlay::SelfCustom(id4),
        ) if id1 == id2 && id1 == id3 && id1 == id4 => {}
        (
            annot::Type::Custom(id1, tsub1, _),
            annot::Type::Custom(id2, tsub2, _),
            annot::Overlay::Custom(id3, osub1),
            annot::Overlay::Custom(id4, osub2),
        ) if id1 == id2 && id1 == id3 && id1 == id4 => {
            let typedef = &customs[id1];
            // println!("\nPanic here");
            // println!("overlay {:?}", typedef.overlay);
            // println!("overlay params {:?}", typedef.overlay_params);
            // println!("osub1 {:?}", osub1);
            // println!("osub2 {:?}", osub2);
            // println!();
            emit_occur_constrs_overlay(
                customs,
                constrs,
                scope,
                &tsub1.apply_to(&typedef.content),
                &tsub2.apply_to(&typedef.content),
                &osub1.apply_to(&typedef.overlay),
                &osub2.apply_to(&typedef.overlay),
            );
        }
        (
            annot::Type::Array(_, lt1, _, _),
            annot::Type::Array(_, lt2, _, _),
            annot::Overlay::Array(m1),
            annot::Overlay::Array(m2),
        )
        | (
            annot::Type::HoleArray(_, lt1, _, _),
            annot::Type::HoleArray(_, lt2, _, _),
            annot::Overlay::HoleArray(m1),
            annot::Overlay::HoleArray(m2),
        )
        | (
            annot::Type::Boxed(_, lt1, _, _),
            annot::Type::Boxed(_, lt2, _, _),
            annot::Overlay::Boxed(m1),
            annot::Overlay::Boxed(m2),
        ) => {
            emit_occur_constr(constrs, scope, lt1, lt2, *m1, *m2);
        }
        _ => panic!("incompatible types"),
    }
}

fn emit_occur_constrs_heap(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    constrs: &mut ConstrGraph,
    scope: &annot::Path,
    binding_ty: &SolverType,
    fut_ty: &SolverType,
) {
    match (binding_ty, fut_ty) {
        (annot::Type::Bool, annot::Type::Bool) => {}
        (annot::Type::Num(n1), annot::Type::Num(n2)) if n1 == n2 => {}
        (annot::Type::Tuple(tys1), annot::Type::Tuple(tys2)) => {
            for (ty1, ty2) in tys1.iter().zip_eq(tys2) {
                emit_occur_constrs_heap(customs, constrs, scope, ty1, ty2);
            }
        }
        (annot::Type::Variants(tys1), annot::Type::Variants(tys2)) => {
            for ((_, ty1), (_, ty2)) in tys1.iter().zip_eq(tys2) {
                emit_occur_constrs_heap(customs, constrs, scope, ty1, ty2);
            }
        }
        (annot::Type::SelfCustom(id1), annot::Type::SelfCustom(id2)) if id1 == id2 => {}
        (annot::Type::Custom(id1, tsub1, osub1), annot::Type::Custom(id2, tsub2, osub2))
            if id1 == id2 =>
        {
            for (m1, m2) in osub1.0.values().zip_eq(osub2.0.values()) {
                constrs.require_eq(*m1, *m2);
            }
            let typedef = &customs[id1];
            emit_occur_constrs_heap(
                customs,
                constrs,
                scope,
                &tsub1.apply_to(&typedef.content),
                &tsub2.apply_to(&typedef.content),
            );
        }
        (annot::Type::Array(m1, _, ty1, o1), annot::Type::Array(m2, _, ty2, o2))
        | (annot::Type::HoleArray(m1, _, ty1, o1), annot::Type::HoleArray(m2, _, ty2, o2))
        | (annot::Type::Boxed(m1, _, ty1, o1), annot::Type::Boxed(m2, _, ty2, o2)) => {
            constrs.require_eq(*m1, *m2);
            emit_occur_constrs_heap(customs, constrs, scope, ty1, ty2);
            emit_occur_constrs_overlay(customs, constrs, scope, ty1, ty2, o1, o2);
        }
        _ => panic!("incompatible types"),
    }
}

fn emit_occur_constrs(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    constrs: &mut ConstrGraph,
    scope: &annot::Path,
    binding_ty: &SolverType,
    fut_ty: &SolverType,
) {
    match (binding_ty, fut_ty) {
        (annot::Type::Bool, annot::Type::Bool) => {}
        (annot::Type::Num(n1), annot::Type::Num(n2)) if n1 == n2 => {}
        (annot::Type::Tuple(tys1), annot::Type::Tuple(tys2)) => {
            for (ty1, ty2) in tys1.iter().zip_eq(tys2) {
                emit_occur_constrs(customs, constrs, scope, ty1, ty2);
            }
        }
        (annot::Type::Variants(tys1), annot::Type::Variants(tys2)) => {
            for ((_, ty1), (_, ty2)) in tys1.iter().zip_eq(tys2) {
                emit_occur_constrs(customs, constrs, scope, ty1, ty2);
            }
        }
        (annot::Type::SelfCustom(id1), annot::Type::SelfCustom(id2)) if id1 == id2 => {}
        (annot::Type::Custom(id1, tsub1, osub1), annot::Type::Custom(id2, tsub2, osub2))
            if id1 == id2 =>
        {
            let typedef = &customs[id1];
            let binding_ty = tsub1.apply_to(&typedef.content);
            let binding_ov = osub1.apply_to(&typedef.overlay);
            let fut_ty = tsub2.apply_to(&typedef.content);
            let fut_ov = osub2.apply_to(&typedef.overlay);
            emit_occur_constrs(customs, constrs, scope, &binding_ty, &fut_ty);
            emit_occur_constrs_overlay(
                customs,
                constrs,
                scope,
                &binding_ty,
                &fut_ty,
                &binding_ov,
                &fut_ov,
            )
        }
        (annot::Type::Array(m1, lt1, ty1, o1), annot::Type::Array(m2, lt2, ty2, o2))
        | (annot::Type::HoleArray(m1, lt1, ty1, o1), annot::Type::HoleArray(m2, lt2, ty2, o2))
        | (annot::Type::Boxed(m1, lt1, ty1, o1), annot::Type::Boxed(m2, lt2, ty2, o2)) => {
            emit_occur_constr(constrs, scope, lt1, lt2, *m1, *m2);
            emit_occur_constrs_heap(customs, constrs, scope, ty1, ty2);
            emit_occur_constrs_overlay(customs, constrs, scope, ty1, ty2, o1, o2);
        }
        _ => panic!("incompatible types"),
    }
}

fn same_shape(ty1: &anon::Type, ty2: &SolverType) -> bool {
    match (ty1, ty2) {
        (anon::Type::Bool, annot::Type::Bool) => true,
        (anon::Type::Num(n1), annot::Type::Num(n2)) => n1 == n2,
        (anon::Type::Tuple(items1), annot::Type::Tuple(items2)) => {
            items1.len() == items2.len()
                && items1
                    .iter()
                    .zip(items2.iter())
                    .all(|(ty1, ty2)| same_shape(ty1, ty2))
        }
        (anon::Type::Variants(variants1), annot::Type::Variants(variants2)) => {
            variants1.len() == variants2.len()
                && variants1
                    .iter()
                    .zip(variants2.iter())
                    .all(|((_, ty1), (_, ty2))| same_shape(ty1, ty2))
        }
        (anon::Type::Custom(id1), annot::Type::SelfCustom(id2)) => id1 == id2,
        (anon::Type::Custom(id1), annot::Type::Custom(id2, _, _)) => id1 == id2,
        (anon::Type::Array(ty1), annot::Type::Array(_, _, ty2, _)) => same_shape(ty1, ty2),
        (anon::Type::HoleArray(ty1), annot::Type::HoleArray(_, _, ty2, _)) => same_shape(ty1, ty2),
        (anon::Type::Boxed(ty1), annot::Type::Boxed(_, _, ty2, _)) => same_shape(ty1, ty2),
        _ => false,
    }
}

fn lt_bind(ty1: &annot::Type<ModeVar, LtParam>, ty2: &SolverType) -> BTreeMap<LtParam, Lt> {
    let mut subst: BTreeMap<_, Lt> = BTreeMap::new();
    let cell = RefCell::new(&mut subst);
    let update = |param: LtParam, lt: &Lt| {
        cell.borrow_mut()
            .entry(param)
            .and_modify(|old| *old = old.join(&lt))
            .or_insert_with(|| lt.clone());
    };

    ty1.items().zip(ty2.items()).for_each(
        &|_, ((tsub1, _), (tsub2, _))| {
            for (lt1, lt2) in tsub1.lts.values().zip_eq(tsub2.lts.values()) {
                update(*lt1, lt2);
            }
        },
        &|((_, lt1), (_, lt2))| {
            update(*lt1, lt2);
        },
        &|_, _| {},
        &|_| {},
    );
    subst
}

fn collect_lt_params(ty: &annot::Type<ModeVar, Lt>) -> BTreeSet<LtParam> {
    let mut res = BTreeSet::new();
    let cell = RefCell::new(&mut res);
    let collect_one = |lt: &Lt| match lt {
        Lt::Empty => {}
        Lt::Local(_) => {}
        Lt::Join(params) => {
            cell.borrow_mut().extend(params.iter().copied());
        }
    };
    ty.items().for_each(
        &|_, (tsub, _)| tsub.lts.values().for_each(collect_one),
        &|(_, lt)| collect_one(lt),
        &|_, _| {},
        &|_| {},
    );
    res
}

fn map_lts<M: Clone, L1, L2>(
    (tsub, osub): (&TypeSubst<M, L1>, &OverlaySubst<M>),
    f: impl Fn(&L1) -> L2,
) -> (TypeSubst<M, L2>, OverlaySubst<M>) {
    (
        TypeSubst {
            ms: tsub.ms.clone(),
            lts: tsub.lts.map_refs(|_, lt| f(lt)),
        },
        osub.clone(),
    )
}

// TODO: This is somewhat duplicative. Should this be part of our general substitution machinery?
// Panics if `subst` does not contain a substitution for every parameter in `ty`.
fn replace_lts(ty: &SolverType, subst: &BTreeMap<LtParam, Lt>) -> SolverType {
    let do_subst = |lt: &Lt| match lt {
        Lt::Empty => Lt::Empty,
        Lt::Local(lt) => Lt::Local(lt.clone()),
        Lt::Join(params) => params
            .iter()
            .map(|p| &subst[p])
            .fold(Lt::Empty, |lt1, lt2| Lt::join(&lt1, lt2)),
    };
    ty.items()
        .map(
            &|_, sub| map_lts(sub, do_subst),
            &|(m, lt)| (*m, do_subst(lt)),
            &|_, ms| ms.clone(),
            &|m| *m,
        )
        .collect_ty()
}

fn wrap_lt_params(ty: &annot::Type<ModeVar, LtParam>) -> annot::Type<ModeVar, Lt> {
    ty.items()
        .map(
            &|_, sub| map_lts(sub, |lt| Lt::var(*lt)),
            &|(m, lt)| (*m, Lt::var(*lt)),
            &|_, ms| ms.clone(),
            &|m| *m,
        )
        .collect_ty()
}

fn join_everywhere(ty: &SolverType, new_lt: &Lt) -> SolverType {
    ty.items()
        .map(
            &|_, sub| map_lts(sub, |lt| lt.join(new_lt)),
            &|(m, lt)| (*m, lt.join(new_lt)),
            &|_, ms| ms.clone(),
            &|m| *m,
        )
        .collect_ty()
}

fn lt_equiv(ty1: &annot::Type<ModeVar, Lt>, ty2: &annot::Type<ModeVar, Lt>) -> bool {
    ty1.items()
        .zip(ty2.items())
        .map(
            &|_, ((tsub1, _), (tsub2, _))| tsub1.lts == tsub2.lts,
            &|((_, lt1), (_, lt2))| lt1 == lt2,
            &|_, _| true,
            &|_| true,
        )
        .fold(true, &|a, b| a && b)
}

fn apply_overlay<L: Clone>(
    ty: &annot::Type<ModeVar, L>,
    overlay: &SolverOverlay,
) -> annot::Type<ModeVar, L> {
    match (ty, overlay) {
        (annot::Type::Bool, annot::Overlay::Bool) => annot::Type::Bool,
        (annot::Type::Num(n1), annot::Overlay::Num(n2)) if n1 == n2 => annot::Type::Num(*n1),
        (annot::Type::Tuple(tys), annot::Overlay::Tuple(os)) => annot::Type::Tuple(
            tys.iter()
                .zip_eq(os.iter())
                .map(|(ty, o)| apply_overlay(ty, o))
                .collect(),
        ),
        (annot::Type::Variants(tys), annot::Overlay::Variants(os)) => {
            annot::Type::Variants(IdVec::from_vec(
                tys.values()
                    .zip_eq(os.values())
                    .map(|(ty, o)| apply_overlay(ty, o))
                    .collect(),
            ))
        }
        (annot::Type::SelfCustom(id1), annot::Overlay::SelfCustom(id2)) if id1 == id2 => {
            annot::Type::SelfCustom(*id1)
        }
        (annot::Type::Custom(id1, tsub, _), annot::Overlay::Custom(id2, osub)) if id1 == id2 => {
            annot::Type::Custom(*id1, tsub.clone(), osub.clone())
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

fn unapply_overlay<L>(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    ty: &annot::Type<ModeVar, L>,
) -> SolverOverlay {
    match ty {
        annot::Type::Bool => annot::Overlay::Bool,
        annot::Type::Num(num_ty) => annot::Overlay::Num(*num_ty),
        annot::Type::Tuple(tys) => {
            annot::Overlay::Tuple(tys.iter().map(|ty| unapply_overlay(customs, ty)).collect())
        }
        annot::Type::Variants(tys) => {
            annot::Overlay::Variants(tys.map_refs(|_, ty| unapply_overlay(customs, ty)))
        }
        annot::Type::SelfCustom(id) => annot::Overlay::SelfCustom(*id),
        annot::Type::Custom(id, _, osub) => annot::Overlay::Custom(*id, osub.clone()),
        annot::Type::Array(m, _, _, _) => annot::Overlay::Array(*m),
        annot::Type::HoleArray(m, _, _, _) => annot::Overlay::HoleArray(*m),
        annot::Type::Boxed(m, _, _, _) => annot::Overlay::Boxed(*m),
    }
}

/// Compute the substitution that replaces the mode parameters in `param` with the corresponding
/// mode variables in `vars`.
fn compute_overlay_subst<'a>(
    params: annot::OverlayItem<'a, ModeParam>,
    vars: annot::OverlayItem<'a, ModeVar>,
) -> OverlaySubst<ModeVar> {
    let mut subst = OverlaySubst(BTreeMap::new());
    let cell = RefCell::new(&mut subst);

    params.zip(vars).for_each(
        &|_, (params, ms)| {
            for (param1, (param2, m)) in params.0.keys().zip_eq(&ms.0) {
                debug_assert_eq!(param1, param2);
                cell.borrow_mut().0.insert_vacant(*param1, *m);
            }
        },
        &|(param, m)| {
            cell.borrow_mut().0.insert_vacant(*param, *m);
        },
    );

    // println!("---------------");
    // println!("subst {:?}", subst.0);
    // println!("---------------");

    subst
}

/// Computes the nominal equivalent of `o'[a |-> mu a. o]` where `o'` is `overlay` and `o` is
/// `self_sub`.
fn unfold_overlay(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    self_sub: &OverlaySubst<ModeVar>,
    overlay: &SolverOverlay,
) -> SolverOverlay {
    match overlay {
        annot::Overlay::Bool => annot::Overlay::Bool,
        annot::Overlay::Num(num_ty) => annot::Overlay::Num(*num_ty),
        annot::Overlay::Tuple(os) => annot::Overlay::Tuple(
            os.iter()
                .map(|o| unfold_overlay(customs, self_sub, o))
                .collect(),
        ),
        annot::Overlay::Variants(os) => {
            annot::Overlay::Variants(os.map_refs(|_, o| unfold_overlay(customs, self_sub, o)))
        }
        annot::Overlay::SelfCustom(id) => annot::Overlay::Custom(*id, self_sub.clone()),
        annot::Overlay::Custom(id, osub) => annot::Overlay::Custom(*id, osub.clone()),
        annot::Overlay::Array(m) => annot::Overlay::Array(*m),
        annot::Overlay::HoleArray(m) => annot::Overlay::HoleArray(*m),
        annot::Overlay::Boxed(m) => annot::Overlay::Boxed(*m),
    }
}

fn unfold_type<L: Clone>(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    extracted: &OverlaySubst<ModeVar>,
    ty_orig: &TypeSubst<ModeVar, L>,
    ov_orig: &OverlaySubst<ModeVar>,
    ty: &annot::Type<ModeVar, L>,
) -> annot::Type<ModeVar, L> {
    match ty {
        annot::Type::Bool => annot::Type::Bool,
        annot::Type::Num(num_ty) => annot::Type::Num(*num_ty),
        annot::Type::Tuple(tys) => annot::Type::Tuple(
            tys.iter()
                .map(|ty| unfold_type(customs, extracted, ty_orig, ov_orig, ty))
                .collect(),
        ),
        annot::Type::Variants(tys) => annot::Type::Variants(
            tys.map_refs(|_, ty| unfold_type(customs, extracted, ty_orig, ov_orig, ty)),
        ),
        annot::Type::SelfCustom(id) => annot::Type::Custom(*id, ty_orig.clone(), extracted.clone()),
        annot::Type::Custom(id, tsub, osub) => annot::Type::Custom(*id, tsub.clone(), osub.clone()),
        annot::Type::Array(m, lt, ty, o) => annot::Type::Array(
            m.clone(),
            lt.clone(),
            Box::new(unfold_type(customs, extracted, ty_orig, ov_orig, ty)),
            unfold_overlay(customs, ov_orig, o),
        ),
        annot::Type::HoleArray(m, lt, ty, o) => annot::Type::HoleArray(
            m.clone(),
            lt.clone(),
            Box::new(unfold_type(customs, extracted, ty_orig, ov_orig, ty)),
            unfold_overlay(customs, ov_orig, o),
        ),
        annot::Type::Boxed(m, lt, ty, o) => annot::Type::Boxed(
            m.clone(),
            lt.clone(),
            Box::new(unfold_type(customs, extracted, ty_orig, ov_orig, ty)),
            unfold_overlay(customs, ov_orig, o),
        ),
    }
}

fn unfold_custom<L: Clone>(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    tsub: &TypeSubst<ModeVar, L>,
    osub: &OverlaySubst<ModeVar>,
    id: CustomTypeId,
) -> annot::Type<ModeVar, L> {
    ////////////////////
    // BUG: osub should include parameters for ALL types in the SCC

    // println!("-------");
    let typedef = &customs[id];
    // println!("content {:?}", typedef.content);
    // println!("overlay {:?}", typedef.overlay);
    // println!("tsub {:?}", tsub.ms);
    // println!("osub {:?}", osub.0);
    let folded = tsub.apply_to(&typedef.content);
    let extracted = OverlaySubst(
        typedef
            .overlay_params
            .iter()
            .map(|p| (*p, tsub.ms[p]))
            .collect(),
    );
    let unfolded = unfold_type(customs, &extracted, tsub, osub, &folded);
    // println!("-------");
    unfolded
}

/// A typing context that can be cheaply cloned.
#[derive(Clone, Debug)]
struct ImmutContext {
    count: Count<LocalId>,
    stack: im_rc::Vector<Rc<SolverType>>, // TODO: `Vector` operations are slow
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

    fn truncate(&mut self, count: Count<LocalId>) {
        if count < self.count {
            self.count = count;
            self.stack.truncate(count.to_value());
        }
    }

    fn update_local(&mut self, local: LocalId, binding: Rc<SolverType>) {
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

    fn len(&self) -> usize {
        self.0.len()
    }

    fn record_update(&mut self, id: LocalId, binding: Rc<SolverType>) {
        self.0.insert(id, binding);
    }

    fn truncate(&mut self, count: Count<LocalId>) {
        // TODO: in practice we only remove the last element, so we could optimize this.
        self.0.retain(|id, _| id.0 < count.to_value());
    }

    fn local_binding(&self, local: LocalId) -> Option<&Rc<SolverType>> {
        self.0.get(&local)
    }

    fn meet(&mut self, _constrs: &mut ConstrGraph, other: &Self) {
        use std::collections::btree_map::Entry;
        for (id, ty) in &other.0 {
            match self.0.entry(*id) {
                Entry::Vacant(entry) => {
                    entry.insert(ty.clone());
                }
                Entry::Occupied(mut entry) => {
                    let old = entry.get_mut();

                    // TODO: do we need this? It's not in the formalism.
                    // mode_bind(constrs, old, ty);

                    *old = Rc::new(old.left_meet(&ty));
                }
            }
        }
    }
}

/// An `ImmutContext` that tracks all updates to local bindings so that they can be replayed on
/// another context.
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
        self.updates.record_update(local, binding);
        local
    }

    fn truncate(&mut self, count: Count<LocalId>) {
        self.ctx.truncate(count);
        self.updates.truncate(count);
    }

    fn update_local(&mut self, local: LocalId, binding: Rc<SolverType>) {
        self.ctx.update_local(local, binding.clone());
        self.updates.record_update(local, binding);
    }

    fn apply_updates(&mut self, updates: &LocalUpdates) {
        for (id, binding) in &updates.0 {
            self.update_local(*id, binding.clone());
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

fn fresh_overlay_subst(
    constrs: &mut ConstrGraph,
    params: &BTreeSet<ModeParam>,
) -> OverlaySubst<ModeVar> {
    // println!("--------------------");
    // println!("fresh_overlay_subst for {:?}", params);
    // println!("--------------------");
    OverlaySubst(
        params
            .into_iter()
            .map(|p| (*p, constrs.fresh_var()))
            .collect(),
    )
}

fn instantiate_overlay<'a, A: 'a, B: 'a>(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    constrs: &mut ConstrGraph,
    ty: annot::OverlayLike<'a, A, B>,
) -> SolverOverlay {
    let constrs = RefCell::new(constrs);
    ty.map(
        &|id, _| fresh_overlay_subst(*constrs.borrow_mut(), &customs[id].overlay_params),
        &|_| constrs.borrow_mut().fresh_var(),
    )
    .collect_ov()
}

fn instantiate_type<'a, A: 'a, B: 'a, C: 'a, D: 'a, L>(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    constrs: &mut ConstrGraph,
    fresh: impl FnMut() -> L,
    ty: annot::TypeLike<'a, A, B, C, D>,
) -> annot::Type<ModeVar, L> {
    let constrs = RefCell::new(constrs);
    let fresh = RefCell::new(fresh);
    ty.map(
        &|id, _| {
            let typedef = &customs[id];
            (
                TypeSubst {
                    ms: IdVec::from_count_with(typedef.num_mode_params, |_| {
                        constrs.borrow_mut().fresh_var()
                    }),
                    lts: IdVec::from_count_with(typedef.num_lt_params, |_| fresh.borrow_mut()()),
                },
                fresh_overlay_subst(*constrs.borrow_mut(), &typedef.overlay_params),
            )
        },
        &|_| (constrs.borrow_mut().fresh_var(), fresh.borrow_mut()()),
        &|id, _| fresh_overlay_subst(*constrs.borrow_mut(), &customs[id].overlay_params),
        &|_| constrs.borrow_mut().fresh_var(),
    )
    .collect_ty()
}

fn instantiate_type_unused_from_items<'a, A: 'a, B: 'a, C: 'a, D: 'a>(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    constrs: &mut ConstrGraph,
    ty: annot::TypeLike<'a, A, B, C, D>,
) -> SolverType {
    instantiate_type(customs, constrs, || Lt::Empty, ty)
}

// Replaces parameters with fresh variables from the constraint graph.
fn instantiate_type_unused(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    constrs: &mut ConstrGraph,
    ty: &anon::Type,
) -> SolverType {
    instantiate_type_unused_from_items(customs, constrs, ty.items(None))
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
            instantiate_type_unused(customs, constrs, ty),
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

/// Generate occurrence constraints and merge `fut_ty` into the typing context. Corresponds to the
/// I-Occur rule.
fn instantiate_occur(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    ctx: &mut TrackedContext,
    scopes: &LocalContext<LocalId, annot::Path>,
    constrs: &mut ConstrGraph,
    id: LocalId,
    fut_ty: &SolverType,
) -> SolverOccur {
    let old_ty = ctx.local_binding(id);
    emit_occur_constrs(customs, constrs, scopes.local_binding(id), old_ty, fut_ty);

    // TODO: do we need this? It's not in the formalism.
    // mode_bind(constrs, old_ty, fut_ty);

    let new_ty = Rc::new(old_ty.left_meet(fut_ty));
    ctx.update_local(id, new_ty);

    annot::Occur {
        local: id,
        ty: fut_ty.clone(),
    }
}

fn instantiate_primitive_type<M, L>(ty: &intr::Type) -> annot::Type<M, L> {
    match ty {
        intr::Type::Bool => annot::Type::Bool,
        intr::Type::Num(n) => annot::Type::Num(*n),
        intr::Type::Tuple(items) => annot::Type::Tuple(
            items
                .iter()
                .map(|ty| instantiate_primitive_type(ty))
                .collect(),
        ),
    }
}

fn instantiate_int_occur(ctx: &TrackedContext, id: LocalId) -> SolverOccur {
    assert!(matches!(
        **ctx.local_binding(id),
        annot::Type::Num(NumType::Int)
    ));
    annot::Occur {
        local: id,
        ty: annot::Type::Num(NumType::Int),
    }
}

// TODO: This is somewhat duplicative. Should this be part of our general substitution machinery?
fn replace_modes<M1: Id, M2, L: Clone>(
    remapping: impl FnMut(M1) -> M2,
    ty: &annot::Type<M1, L>,
) -> annot::Type<M2, L> {
    let remapping = RefCell::new(remapping);
    let lookup = |m: &M1| remapping.borrow_mut()(*m);
    ty.items()
        .map(
            &|_, (tsub, osub)| (tsub.map_vals(lookup, Clone::clone), osub.map_vals(lookup)),
            &|(m, lt)| (lookup(m), lt.clone()),
            &|_, osub| osub.map_vals(lookup),
            &|m| lookup(m),
        )
        .collect_ty()
}

/// Used during lifetime fixed point iteration. `know_defs` contains the definitions of all
/// functions from previous SCCs. `pending_args` and `pending_rets` contain the signatures of types
/// from the current SCC as of the previous iteration.
#[derive(Clone, Copy, Debug)]
struct SignatureAssumptions<'a> {
    known_defs: &'a IdMap<CustomFuncId, annot::FuncDef>,
    pending_args: &'a BTreeMap<CustomFuncId, SolverType>,
    pending_rets: &'a BTreeMap<CustomFuncId, annot::Type<ModeVar, LtParam>>,
}

impl<'a> SignatureAssumptions<'a> {
    fn sig_of(
        &self,
        constrs: &mut ConstrGraph,
        id: CustomFuncId,
    ) -> (SolverType, annot::Type<ModeVar, LtParam>) {
        self.known_defs.get(id).map_or_else(
            || {
                (
                    self.pending_args[&id].clone(),
                    self.pending_rets[&id].clone(),
                )
            },
            |def| {
                let params_to_vars = constrs.instantiate_subgraph(&def.constrs.sig);
                let remapping = |param| params_to_vars[param];
                (
                    replace_modes(&remapping, &def.sig.arg_type),
                    replace_modes(&remapping, &def.sig.ret_type),
                )
            },
        )
    }
}

#[derive(Clone, Debug)]
struct SolverScc {
    func_args: BTreeMap<CustomFuncId, SolverType>,
    func_rets: BTreeMap<CustomFuncId, annot::Type<ModeVar, LtParam>>,
    func_bodies: BTreeMap<CustomFuncId, annot::Expr<ModeVar, Lt>>,
    scc_constrs: ConstrGraph,
}

// This function is the core logic for this pass. It implements the judgement from the paper:
// Δ ; Γ ; S ; q ⊢ e : t ⇝ e ; Q ; Γ'
//
// Note that we must return a set of updates rather than mutating Γ because I-Match requires that we
// check all branches in the initial Γ.
fn instantiate_expr(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    sigs: SignatureAssumptions,
    constrs: &mut ConstrGraph,
    lt_count: &mut Count<LtParam>,
    ctx: &ImmutContext,
    scopes: &mut LocalContext<LocalId, annot::Path>,
    path: annot::Path,
    fut_ty: &SolverType,
    expr: &flat::Expr,
    renderer: &CustomTypeRenderer<CustomTypeId>,
) -> (SolverExpr, LocalUpdates) {
    let mut ctx = TrackedContext::new(ctx);

    let expr_annot = match expr {
        flat::Expr::Local(local) => {
            let occur = instantiate_occur(customs, &mut ctx, scopes, constrs, *local, fut_ty);
            annot::Expr::Local(occur)
        }

        flat::Expr::Call(purity, func, arg) => {
            let (arg_ty, ret_ty) = sigs.sig_of(constrs, *func);

            mode_bind(constrs, &ret_ty, fut_ty);
            let lt_subst = lt_bind(&ret_ty, fut_ty);

            // This `join_everywhere` reflects the fact that we assume that functions access all of
            // their arguments. We could be more precise here.
            let arg_ty = join_everywhere(&replace_lts(&arg_ty, &lt_subst), &path.as_lt());
            let arg = instantiate_occur(customs, &mut ctx, scopes, constrs, *arg, &arg_ty);

            annot::Expr::Call(*purity, *func, arg)
        }

        flat::Expr::Branch(discrim_id, cases, ret_ty) => {
            debug_assert!(same_shape(ret_ty, fut_ty));

            let mut updates = LocalUpdates::new();
            let mut cases_annot = Vec::new();

            for (i, (cond, body)) in cases.iter().enumerate() {
                let cond_annot = instantiate_condition(customs, constrs, cond);
                let (body_annot, body_updates) = instantiate_expr(
                    customs,
                    sigs,
                    constrs,
                    lt_count,
                    ctx.as_untracked(),
                    scopes,
                    path.par(i, cases.len()),
                    fut_ty,
                    body,
                    renderer,
                );

                // Record the updates, but DO NOT apply them to the context. Every branch should be
                // checked in the original context.
                updates.meet(constrs, &body_updates);

                cases_annot.push((cond_annot, body_annot));
            }

            // Finally, apply the updates before instantiating the discriminant.
            ctx.apply_updates(&updates);

            let fut_ty = ctx.local_binding(*discrim_id).clone();
            let discrim_occur =
                instantiate_occur(customs, &mut ctx, scopes, constrs, *discrim_id, &fut_ty);

            annot::Expr::Branch(discrim_occur, cases_annot, (*fut_ty).clone())
        }

        // We're only using `with_scope` here for its debug assertion, and to signal intent; by the
        // time the passed closure returns, we've manually truncated away all the variables which it
        // would usually be `with_scope`'s responsibility to remove.
        flat::Expr::LetMany(bindings, result_id) => scopes.with_scope(|scopes| {
            let locals_offset = scopes.len();
            let end_of_scope = path.seq(bindings.len());

            for (binding_ty, _) in bindings {
                let local_id1 = scopes.add_local(end_of_scope.clone());
                let local_id2 = ctx.add_local(Rc::new(instantiate_type_unused(
                    customs, constrs, binding_ty,
                )));
                debug_assert_eq!(local_id1, local_id2);
            }

            let result_occur =
                instantiate_occur(customs, &mut ctx, scopes, constrs, *result_id, fut_ty);

            let mut bindings_annot_rev = Vec::new();
            for (i, (_, binding_expr)) in bindings.iter().enumerate().rev() {
                let local = LocalId(locals_offset + i);
                let fut_ty = (**ctx.local_binding(local)).clone();

                // Only retain the locals *strictly* before this binding.
                scopes.truncate(Count::from_value(local.0));
                ctx.truncate(Count::from_value(local.0));

                let (expr_annot, expr_updates) = instantiate_expr(
                    customs,
                    sigs,
                    constrs,
                    lt_count,
                    ctx.as_untracked(),
                    scopes,
                    path.seq(i),
                    &fut_ty,
                    binding_expr,
                    renderer,
                );

                // Apply the updates to the context. It is important that the enclosing loop is in
                // reverse order to ensure that each binding is checked in the correct context.
                ctx.apply_updates(&expr_updates);

                bindings_annot_rev.push((fut_ty, expr_annot));
            }

            let bindings_annot = {
                bindings_annot_rev.reverse();
                bindings_annot_rev
            };

            annot::Expr::LetMany(bindings_annot, result_occur)
        }),

        flat::Expr::Tuple(item_ids) => {
            let annot::Type::Tuple(fut_tys) = fut_ty else {
                unreachable!();
            };
            debug_assert_eq!(item_ids.len(), fut_tys.len());
            let mut occurs_rev: Vec<_> = item_ids
                .iter()
                .zip(fut_tys.iter())
                // We must process the items in reverse order to ensure `instantiate_occur` (which
                // updates the lifetimes in `ctx`) generates the correct constraints.
                .rev()
                .map(|(item_id, item_fut_ty)| {
                    instantiate_occur(customs, &mut ctx, scopes, constrs, *item_id, item_fut_ty)
                })
                .collect();
            let occurs = {
                occurs_rev.reverse();
                occurs_rev
            };
            annot::Expr::Tuple(occurs)
        }

        flat::Expr::TupleField(tuple_id, idx) => {
            let annot::Type::Tuple(mut item_tys) = instantiate_type_unused_from_items(
                customs,
                constrs,
                ctx.local_binding(*tuple_id).items(),
            ) else {
                unreachable!();
            };
            item_tys[*idx] = fut_ty.clone();
            let tuple_ty = annot::Type::Tuple(item_tys);

            let tuple_occur =
                instantiate_occur(customs, &mut ctx, scopes, constrs, *tuple_id, &tuple_ty);

            annot::Expr::TupleField(tuple_occur, *idx)
        }

        flat::Expr::WrapVariant(_variant_tys, variant_id, content) => {
            let annot::Type::Variants(fut_variant_tys) = fut_ty else {
                unreachable!();
            };

            let content_occur = instantiate_occur(
                customs,
                &mut ctx,
                scopes,
                constrs,
                *content,
                &fut_variant_tys[*variant_id],
            );

            annot::Expr::WrapVariant(fut_variant_tys.clone(), *variant_id, content_occur)
        }

        flat::Expr::UnwrapVariant(variant_id, wrapped) => {
            let annot::Type::Variants(mut variant_tys) = instantiate_type_unused_from_items(
                customs,
                constrs,
                ctx.local_binding(*wrapped).items(),
            ) else {
                unreachable!();
            };

            variant_tys[*variant_id] = fut_ty.clone();

            let wrapped_ty = annot::Type::Variants(variant_tys);
            let wrapped_occur =
                instantiate_occur(customs, &mut ctx, scopes, constrs, *wrapped, &wrapped_ty);

            annot::Expr::UnwrapVariant(*variant_id, wrapped_occur)
        }

        // See I-Rc; this is the operation that constructs new boxes
        flat::Expr::WrapBoxed(content, _item_ty) => {
            let annot::Type::Boxed(fut_mode, _, fut_item_ty, fut_ov) = fut_ty else {
                unreachable!();
            };

            require_owned(constrs, *fut_mode);
            mode_bind_overlays(constrs, &unapply_overlay(customs, &fut_item_ty), &fut_ov);

            let content_occur =
                instantiate_occur(customs, &mut ctx, scopes, constrs, *content, fut_item_ty);

            annot::Expr::WrapBoxed(content_occur, (**fut_item_ty).clone())
        }

        // See I-Get
        flat::Expr::UnwrapBoxed(wrapped, _item_ty) => {
            let item_ty = replace_modes(|_| constrs.fresh_var(), fut_ty);
            let item_ov = unapply_overlay(customs, &fut_ty);

            let box_ty = annot::Type::Boxed(
                constrs.fresh_var(),
                path.as_lt(),
                Box::new(item_ty.clone()),
                item_ov,
            );

            let box_occur =
                instantiate_occur(customs, &mut ctx, scopes, constrs, *wrapped, &box_ty);

            annot::Expr::UnwrapBoxed(box_occur, item_ty)
        }

        flat::Expr::WrapCustom(custom_id, content) => {
            let annot::Type::Custom(fut_id, fut_tsub, fut_osub) = fut_ty else {
                unreachable!();
            };

            debug_assert_eq!(*custom_id, *fut_id);

            let unfolded_ty = unfold_custom(customs, fut_tsub, fut_osub, *custom_id);
            let unfolded_ov = &unfold_overlay(
                customs,
                &fut_osub,
                &fut_osub.apply_to(&customs[*custom_id].overlay),
            );

            let content_ty = apply_overlay(&unfolded_ty, &unfolded_ov);

            // println!();
            // println!("custom_id: {:?}", custom_id);
            // pp::write_type(
            //     &mut std::io::stdout(),
            //     renderer,
            //     &pp::write_mode_var,
            //     &pp::write_lifetime,
            //     &unfolded_ty,
            // )
            // .unwrap();
            // println!();
            // println!("fut_osub: {:?}", fut_osub);
            // println!("custom overlay: {:?}", customs[*custom_id].overlay);
            // println!("custom content: {:?}", customs[*custom_id].content);
            // println!(
            //     "custom overlay params: {:?}",
            //     customs[*custom_id].overlay_params
            // );
            // println!("unfolded_ov: {:?}", unfolded_ov);
            // println!();
            // pp::write_type(
            //     &mut std::io::stdout(),
            //     renderer,
            //     &pp::write_mode_var,
            //     &pp::write_lifetime,
            //     &ctx.local_binding(*content),
            // )
            // .unwrap();
            // println!();
            // println!();
            // pp::write_type(
            //     &mut std::io::stdout(),
            //     renderer,
            //     &pp::write_mode_var,
            //     &pp::write_lifetime,
            //     &content_ty,
            // )
            // .unwrap();
            // println!();
            // println!();

            let content_occur =
                instantiate_occur(customs, &mut ctx, scopes, constrs, *content, &content_ty);

            annot::Expr::WrapCustom(*custom_id, content_occur)
        }

        flat::Expr::UnwrapCustom(custom_id, folded) => {
            let custom = &customs[custom_id];

            let folded_os = fresh_overlay_subst(constrs, &custom.overlay_params);
            let folded_ov = folded_os.apply_to(&custom.overlay);
            let folded_ts = TypeSubst {
                ms: IdVec::from_count_with(custom.num_mode_params, |_| constrs.fresh_var()),
                lts: IdVec::from_count_with(custom.num_lt_params, |_| lt_count.inc()),
            };

            let unfolded_ty = apply_overlay(
                &unfold_custom(customs, &folded_ts, &folded_os, *custom_id),
                &unfold_overlay(customs, &folded_os, &folded_ov),
            );

            // println!("HERE");
            // pp::write_type(
            //     &mut std::io::stdout(),
            //     renderer,
            //     &pp::write_mode_var,
            //     &pp::write_lifetime_param,
            //     &unfolded_ty,
            // )
            // .unwrap();
            // println!();
            // pp::write_type(
            //     &mut std::io::stdout(),
            //     renderer,
            //     &pp::write_mode_var,
            //     &pp::write_lifetime,
            //     &fut_ty,
            // )
            // .unwrap();
            // println!();
            // println!();

            mode_bind(constrs, &unfolded_ty, fut_ty);

            // println!();
            // println!("folded_ts: {:?}", folded_ts);
            // println!("folded_os: {:?}", folded_os);

            let folded_ty = replace_lts(
                &wrap_lt_params(&annot::Type::Custom(*custom_id, folded_ts, folded_os)),
                &lt_bind(&unfolded_ty, fut_ty),
            );

            // pp::write_type(
            //     &mut std::io::stdout(),
            //     renderer,
            //     &pp::write_mode_var,
            //     &pp::write_lifetime,
            //     &folded_ty,
            // )
            // .unwrap();
            // println!();
            // println!();

            let folded_occur =
                instantiate_occur(customs, &mut ctx, scopes, constrs, *folded, &folded_ty);

            annot::Expr::UnwrapCustom(*custom_id, folded_occur)
        }

        // Right now, all intrinsics are trivial from a mode inference perspective because they
        // operate on arithmetic types. If this changes, we will have to update this.
        flat::Expr::Intrinsic(intr, arg) => {
            let sig = intrinsic_sig(*intr);
            let arg_occur = Occur {
                local: *arg,
                ty: instantiate_primitive_type(&sig.arg),
            };
            annot::Expr::Intrinsic(*intr, arg_occur)
        }

        // See I-Get
        flat::Expr::ArrayOp(flat::ArrayOp::Get(_, arr_id, idx_id)) => {
            let item_ty = replace_modes(|_| constrs.fresh_var(), fut_ty);
            let item_ov = unapply_overlay(customs, &fut_ty);

            let arr_ty = annot::Type::Array(
                constrs.fresh_var(),
                path.as_lt(),
                Box::new(item_ty.clone()),
                item_ov,
            );

            let idx_occur = instantiate_int_occur(&ctx, *idx_id);
            let arr_occur = instantiate_occur(customs, &mut ctx, scopes, constrs, *arr_id, &arr_ty);

            annot::Expr::ArrayOp(annot::ArrayOp::Get(
                item_ty,
                arr_occur,
                idx_occur,
                fut_ty.clone(),
            ))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Extract(item_ty, arr_id, idx_id)) => {
            let annot::Type::Tuple(ret_tys) = fut_ty else {
                unreachable!();
            };
            debug_assert_eq!(ret_tys.len(), 2);
            let annot::Type::HoleArray(fut_mode, _, fut_item_ty, _) = &ret_tys[1] else {
                unreachable!();
            };
            let fut_extracted_ty = &ret_tys[0];

            require_owned(constrs, *fut_mode);
            mode_bind(constrs, fut_extracted_ty, fut_item_ty);

            let arr_mode = constrs.fresh_var();
            require_owned(constrs, arr_mode);

            let arr_ty = annot::Type::Array(
                arr_mode,
                path.as_lt(),
                Box::new(fut_extracted_ty.clone()),
                instantiate_overlay(customs, constrs, item_ty.overlay_items(None)),
            );

            let idx_occur = instantiate_int_occur(&ctx, *idx_id);
            let arr_occur = instantiate_occur(customs, &mut ctx, scopes, constrs, *arr_id, &arr_ty);

            annot::Expr::ArrayOp(annot::ArrayOp::Extract(
                fut_extracted_ty.clone(),
                arr_occur,
                idx_occur,
            ))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Len(item_ty, arr_id)) => {
            debug_assert_eq!(fut_ty, &annot::Type::Num(NumType::Int));

            let annot_item_ty = instantiate_type_unused(customs, constrs, item_ty);
            let arr_ty = annot::Type::Array(
                constrs.fresh_var(),
                path.as_lt(),
                Box::new(annot_item_ty.clone()),
                instantiate_overlay(customs, constrs, item_ty.overlay_items(None)),
            );

            let arr_occur = instantiate_occur(customs, &mut ctx, scopes, constrs, *arr_id, &arr_ty);

            annot::Expr::ArrayOp(annot::ArrayOp::Len(annot_item_ty, arr_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Push(item_ty, arr_id, item_id)) => {
            let annot::Type::Array(fut_mode, _, fut_item_ty, _) = fut_ty else {
                unreachable!();
            };
            require_owned(constrs, *fut_mode);

            let arr_mode = constrs.fresh_var();
            require_owned(constrs, arr_mode);

            let arr_ty = annot::Type::Array(
                arr_mode,
                path.as_lt(),
                Box::new((**fut_item_ty).clone()),
                instantiate_overlay(customs, constrs, item_ty.overlay_items(None)),
            );

            let item_occur =
                instantiate_occur(customs, &mut ctx, scopes, constrs, *item_id, &fut_item_ty);

            let arr_occur = instantiate_occur(customs, &mut ctx, scopes, constrs, *arr_id, &arr_ty);

            annot::Expr::ArrayOp(annot::ArrayOp::Push(
                (**fut_item_ty).clone(),
                arr_occur,
                item_occur,
            ))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Pop(item_ty, arr_id)) => {
            let annot::Type::Tuple(ret_tys) = fut_ty else {
                unreachable!();
            };
            debug_assert_eq!(ret_tys.len(), 2);
            let annot::Type::Array(fut_arr_mode, _, fut_item_ty, _) = &ret_tys[0] else {
                unreachable!();
            };
            let fut_popped_ty = &ret_tys[1];

            require_owned(constrs, *fut_arr_mode);
            mode_bind(constrs, fut_popped_ty, fut_item_ty);

            let arr_mode = constrs.fresh_var();
            require_owned(constrs, arr_mode);

            let arr_ty = annot::Type::Array(
                arr_mode,
                path.as_lt(),
                Box::new(fut_popped_ty.clone()),
                instantiate_overlay(customs, constrs, item_ty.overlay_items(None)),
            );

            let arr_occur = instantiate_occur(customs, &mut ctx, scopes, constrs, *arr_id, &arr_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Pop(fut_popped_ty.clone(), arr_occur))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Replace(item_ty, hole_id, item_id)) => {
            let annot::Type::Array(fut_mode, _, fut_item_ty, _) = fut_ty else {
                unreachable!();
            };
            require_owned(constrs, *fut_mode);

            let item_occur =
                instantiate_occur(customs, &mut ctx, scopes, constrs, *item_id, fut_item_ty);

            let hole_mode = constrs.fresh_var();
            require_owned(constrs, hole_mode);

            let hole_ty = annot::Type::HoleArray(
                hole_mode,
                path.as_lt(),
                fut_item_ty.clone(),
                instantiate_overlay(customs, constrs, item_ty.overlay_items(None)),
            );

            let hole_occur =
                instantiate_occur(customs, &mut ctx, scopes, constrs, *hole_id, &hole_ty);

            annot::Expr::ArrayOp(annot::ArrayOp::Replace(
                (**fut_item_ty).clone(),
                hole_occur,
                item_occur,
            ))
        }

        flat::Expr::ArrayOp(flat::ArrayOp::Reserve(_item_ty, arr_id, cap_id)) => {
            let annot::Type::Array(fut_mode, _, fut_item_ty, _) = fut_ty else {
                unreachable!();
            };
            require_owned(constrs, *fut_mode);

            let cap_occur = instantiate_int_occur(&ctx, *cap_id);
            let arr_occur = instantiate_occur(customs, &mut ctx, scopes, constrs, *arr_id, fut_ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Reserve(
                (**fut_item_ty).clone(),
                arr_occur,
                cap_occur,
            ))
        }

        flat::Expr::IoOp(flat::IoOp::Input) => {
            let annot::Type::Array(fut_mode, _, fut_item_ty, _) = fut_ty else {
                unreachable!();
            };

            require_owned(constrs, *fut_mode);
            assert!(matches!(**fut_item_ty, annot::Type::Num(NumType::Byte)));

            annot::Expr::IoOp(annot::IoOp::Input)
        }

        flat::Expr::IoOp(flat::IoOp::Output(arr_id)) => {
            let arr_ty = annot::Type::Array(
                constrs.fresh_var(),
                path.as_lt(),
                Box::new(annot::Type::Num(NumType::Byte)),
                annot::Overlay::Num(NumType::Byte),
            );
            let arr_occur = instantiate_occur(customs, &mut ctx, scopes, constrs, *arr_id, &arr_ty);
            annot::Expr::IoOp(annot::IoOp::Output(arr_occur))
        }

        flat::Expr::Panic(ret_ty, msg_id) => {
            debug_assert!(same_shape(ret_ty, fut_ty));
            let arr_ty = annot::Type::Array(
                constrs.fresh_var(),
                path.as_lt(),
                Box::new(annot::Type::Num(NumType::Byte)),
                annot::Overlay::Num(NumType::Byte),
            );
            let msg_occur = instantiate_occur(customs, &mut ctx, scopes, constrs, *msg_id, &arr_ty);
            annot::Expr::Panic(fut_ty.clone(), msg_occur)
        }

        // See I-Rc; this is the operation that constructs new arrays
        flat::Expr::ArrayLit(_item_ty, item_ids) => {
            let annot::Type::Array(fut_mode, _, fut_item_ty, _) = fut_ty else {
                unreachable!();
            };
            require_owned(constrs, *fut_mode);

            let mut item_occurs_rev: Vec<_> = item_ids
                .iter()
                // We must process the items in reverse order to ensure `instantiate_occur` (which
                // updates the lifetimes in `ctx`) generates the correct constraints.
                .rev()
                .map(|item_id| {
                    instantiate_occur(customs, &mut ctx, scopes, constrs, *item_id, fut_item_ty)
                })
                .collect();

            let item_occurs = {
                item_occurs_rev.reverse();
                item_occurs_rev
            };
            annot::Expr::ArrayLit((**fut_item_ty).clone(), item_occurs)
        }

        flat::Expr::BoolLit(val) => annot::Expr::BoolLit(*val),

        flat::Expr::ByteLit(val) => annot::Expr::ByteLit(*val),

        flat::Expr::IntLit(val) => annot::Expr::IntLit(*val),

        flat::Expr::FloatLit(val) => annot::Expr::FloatLit(*val),
    };

    (expr_annot, ctx.into_updates())
}

fn instantiate_scc(
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    funcs: &IdVec<CustomFuncId, flat::FuncDef>,
    funcs_annot: &IdMap<CustomFuncId, annot::FuncDef>,
    scc: Scc<CustomFuncId>,
    renderer: &CustomTypeRenderer<CustomTypeId>,
) -> SolverScc {
    match scc.kind {
        SccKind::Acyclic | SccKind::Cyclic => {
            // TODO: if the SCC is acyclic, we can skip lifetime fixed point iteration

            let mut constrs = ConstrGraph::new(); // TODO: when can we clear this?
            let mut next_lt = Count::new();

            let mut arg_tys = scc
                .nodes
                .iter()
                .map(|id| {
                    (
                        *id,
                        instantiate_type_unused(customs, &mut constrs, &funcs[id].arg_type),
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
                            customs,
                            &mut constrs,
                            &mut || next_lt.inc(),
                            funcs[id].ret_type.items(None),
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
                // println!("iter_num: {}", iter_num);
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
                    let arg_ty = instantiate_type_unused(customs, &mut constrs, &func.arg_type);
                    let arg_id = ctx.add_local(Rc::new(arg_ty.clone())); // TODO: don't clone; use RC everywhere
                    debug_assert_eq!(arg_id, flat::ARG_LOCAL);

                    let mut scopes = LocalContext::new();
                    let arg_id = scopes.add_local(annot::Path::root().seq(1));
                    debug_assert_eq!(arg_id, flat::ARG_LOCAL);

                    let (expr, updates) = instantiate_expr(
                        customs,
                        assumptions,
                        &mut constrs,
                        &mut next_lt,
                        &ctx,
                        &mut scopes,
                        // Should end before `scopes[arg_id]`
                        annot::Path::root().seq(0),
                        &wrap_lt_params(&ret_tys[id]),
                        &func.body,
                        renderer,
                    );
                    bodies.insert(*id, expr);

                    debug_assert!(updates.len() <= 1);
                    if let Some(update) = updates.local_binding(flat::ARG_LOCAL) {
                        ctx.update_local(flat::ARG_LOCAL, update.clone());
                    }

                    new_arg_tys.insert(*id, (**ctx.local_binding(flat::ARG_LOCAL)).clone());
                }

                // for (new, old) in new_arg_tys.values().zip_eq(arg_tys.values()) {
                //     if !lt_equiv(new, old) {
                //         pp::write_type(
                //             &mut std::io::stdout(),
                //             renderer,
                //             &pp::write_mode_var,
                //             &pp::write_lifetime,
                //             old,
                //         )
                //         .unwrap();
                //         println!(" =>");
                //         pp::write_type(
                //             &mut std::io::stdout(),
                //             renderer,
                //             &pp::write_mode_var,
                //             &pp::write_lifetime,
                //             new,
                //         )
                //         .unwrap();
                //         println!();
                //     }
                // }

                debug_assert!(
                    {
                        let params_found = new_arg_tys.values().map(collect_lt_params).fold(
                            BTreeSet::new(),
                            |mut acc, params| {
                                acc.extend(params);
                                acc
                            },
                        );
                        debug_sig_params.is_superset(&params_found)
                    },
                    "Some temporary lifetime parameters leaked into the function arguments during \
                     expression instantiation. Only parameters from the return type should appear"
                );

                if new_arg_tys
                    .values()
                    .zip_eq(arg_tys.values())
                    .all(|(new, old)| lt_equiv(new, old))
                {
                    break (new_arg_tys, bodies);
                }

                arg_tys = new_arg_tys;
            };

            // println!("----");
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

fn record_vars<L>(params: &mut BTreeSet<ModeVar>, ty: &annot::Type<ModeVar, L>) {
    let params = RefCell::new(params);
    ty.items().for_each(
        &|_, (tsub, osub)| {
            params.borrow_mut().extend(tsub.ms.values().cloned());
            params.borrow_mut().extend(osub.0.values().cloned());
        },
        &|(m, _)| {
            params.borrow_mut().insert(*m);
        },
        &|_, subst| {
            params.borrow_mut().extend(subst.0.values().cloned());
        },
        &|m| {
            params.borrow_mut().insert(*m);
        },
    );
}

type Solution = in_eq::Solution<ModeVar, ModeParam, Mode>;

// TODO: use `replace_modes` instead
fn extract_type(solution: &Solution, ty: &SolverType) -> annot::Type<ModeSolution, Lt> {
    let get_solution = |m: &ModeVar| ModeSolution {
        lb: solution.lower_bounds[*m].clone(),
        solver_var: *m,
    };

    ty.items()
        .map(
            &|_, (tsub, osub)| {
                (
                    tsub.map_vals(get_solution, Clone::clone),
                    osub.map_vals(get_solution),
                )
            },
            &|(m, lt)| (get_solution(m), lt.clone()),
            &|_, osub| osub.map_vals(get_solution),
            &|m| get_solution(m),
        )
        .collect_ty()
}

fn extract_occur(solution: &Solution, occur: &SolverOccur) -> annot::Occur<ModeSolution, Lt> {
    annot::Occur {
        local: occur.local,
        ty: extract_type(solution, &occur.ty),
    }
}

fn extract_condition(
    solution: &Solution,
    cond: &SolverCondition,
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

fn extract_expr(solution: &Solution, expr: &SolverExpr) -> annot::Expr<ModeSolution, Lt> {
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
        E::ArrayOp(annot::ArrayOp::Get(item_ty, arr, idx, out_ty)) => {
            E::ArrayOp(annot::ArrayOp::Get(
                extract_type(solution, item_ty),
                extract_occur(solution, arr),
                extract_occur(solution, idx),
                extract_type(solution, out_ty),
            ))
        }
        E::ArrayOp(annot::ArrayOp::Extract(item_ty, arr, idx)) => {
            E::ArrayOp(annot::ArrayOp::Extract(
                extract_type(solution, item_ty),
                extract_occur(solution, arr),
                extract_occur(solution, idx),
            ))
        }
        E::ArrayOp(annot::ArrayOp::Len(item_ty, arr)) => E::ArrayOp(annot::ArrayOp::Len(
            extract_type(solution, item_ty),
            extract_occur(solution, arr),
        )),
        E::ArrayOp(annot::ArrayOp::Push(item_ty, arr, item)) => E::ArrayOp(annot::ArrayOp::Push(
            extract_type(solution, item_ty),
            extract_occur(solution, arr),
            extract_occur(solution, item),
        )),
        E::ArrayOp(annot::ArrayOp::Pop(item_ty, arr)) => E::ArrayOp(annot::ArrayOp::Pop(
            extract_type(solution, item_ty),
            extract_occur(solution, arr),
        )),
        E::ArrayOp(annot::ArrayOp::Replace(item_ty, hole, item)) => {
            E::ArrayOp(annot::ArrayOp::Replace(
                extract_type(solution, item_ty),
                extract_occur(solution, hole),
                extract_occur(solution, item),
            ))
        }
        E::ArrayOp(annot::ArrayOp::Reserve(item_ty, arr, cap)) => {
            E::ArrayOp(annot::ArrayOp::Reserve(
                extract_type(solution, item_ty),
                extract_occur(solution, arr),
                extract_occur(solution, cap),
            ))
        }
        E::IoOp(annot::IoOp::Input) => E::IoOp(annot::IoOp::Input),
        E::IoOp(annot::IoOp::Output(arr)) => {
            E::IoOp(annot::IoOp::Output(extract_occur(solution, arr)))
        }
        E::Panic(ty, msg) => E::Panic(extract_type(solution, ty), extract_occur(solution, msg)),
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
    customs: &IdVec<CustomTypeId, annot::TypeDef>,
    funcs: &IdVec<CustomFuncId, flat::FuncDef>,
    funcs_annot: &mut IdMap<CustomFuncId, annot::FuncDef>,
    scc: Scc<CustomFuncId>,
    renderer: &CustomTypeRenderer<CustomTypeId>,
) {
    let instantiated = instantiate_scc(customs, funcs, funcs_annot, scc, renderer);
    // println!("Instantiated SCC: {:?}", scc);

    let mut sig_vars = BTreeSet::new();
    for func_id in scc.nodes {
        record_vars(&mut sig_vars, &instantiated.func_args[&func_id]);
        record_vars(&mut sig_vars, &instantiated.func_rets[&func_id]);
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

        let num_mode_params =
            count_mode_params(customs, arg_ty.items()) + count_mode_params(customs, ret_ty.items());
        let num_lt_params =
            count_lt_params(customs, arg_ty.items()) + count_lt_params(customs, ret_ty.items());

        let func = &funcs[func_id];
        let remap_internal = |internal| {
            // if !solution.internal_to_external.contains_key(&internal) {
            //     println!("MISSING: {:?}", internal);
            // }
            solution.internal_to_external[&internal]
        };
        // println!("remap_internal: {:?}", solution.internal_to_external);
        // println!("arg_ty: {:?}", arg_ty);
        // println!("recorded: {:?}", {
        //     let mut recorded = BTreeSet::new();
        //     record_vars(&mut recorded, arg_ty);
        //     recorded
        // });
        funcs_annot.insert_vacant(
            *func_id,
            annot::FuncDef {
                purity: func.purity,
                sig: annot::Signature {
                    num_mode_params: Count::from_value(num_mode_params),
                    num_lt_params: Count::from_value(num_lt_params),
                    arg_type: replace_modes(remap_internal, arg_ty),
                    ret_type: replace_modes(remap_internal, ret_ty),
                },
                constrs: annot::FuncConstrs {
                    sig: sig_constrs.clone(),
                    internal: instantiated.scc_constrs.clone(),
                },
                body: extract_expr(&solution, &instantiated.func_bodies[&func_id]),
                profile_point: func.profile_point.clone(),
            },
        );
    }
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

fn convert_type_sccs(
    orig: &IdVec<CustomTypeSccId, old_graph::Scc<CustomTypeId>>,
) -> Sccs<CustomTypeSccId, CustomTypeId> {
    let mut sccs = Sccs::new();
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
    Aggressive,
    AlwaysOwned,        // similar to "Perceus"
    OnlyTrivialBorrows, // similar to "Immutable Beans"
}

pub fn annot_modes(
    program: &flat::Program,
    _strat: Strategy,
    progress: impl ProgressLogger,
) -> annot::Program {
    let mut progress = progress.start_session(Some(program.funcs.len()));
    let renderer = CustomTypeRenderer::from_symbols(&program.custom_type_symbols);

    let custom_sccs = convert_type_sccs(&program.custom_types.sccs);
    let mut rev_custom_sccs = IdMap::new();
    for (scc_id, scc) in &custom_sccs {
        for &custom_id in scc.nodes {
            rev_custom_sccs.insert_vacant(custom_id, scc_id);
        }
    }

    let rev_sccs = rev_custom_sccs.to_id_vec(program.custom_types.types.count());
    let customs = parameterize_customs(&program.custom_types, &rev_sccs);

    #[id_type]
    struct FuncSccId(usize);

    let func_sccs: Sccs<FuncSccId, _> = find_components(program.funcs.count(), |id| {
        let mut deps = BTreeSet::new();
        add_func_deps(&mut deps, &program.funcs[id].body);
        deps
    });

    let mut funcs_annot = IdMap::new();
    for (_, scc) in &func_sccs {
        solve_scc(&customs, &program.funcs, &mut funcs_annot, scc, &renderer);
        // println!("Solved SCC {:?}", scc);
        progress.update(scc.nodes.len());
    }

    let funcs_annot = funcs_annot.to_id_vec(program.funcs.count());

    progress.finish();

    annot::Program {
        mod_symbols: program.mod_symbols.clone(),
        custom_types: annot::CustomTypes {
            types: customs,
            sccs: custom_sccs,
        },
        custom_type_symbols: program.custom_type_symbols.clone(),
        funcs: funcs_annot,
        func_symbols: program.func_symbols.clone(),
        profile_points: program.profile_points.clone(),
        main: program.main,
    }
}
