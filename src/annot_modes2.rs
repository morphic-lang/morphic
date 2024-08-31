//! This module implements the specializing variant of first compiler pass described in the borrow
//! inference paper. A signficant proportion of the machinery is dedicated to specialization. The
//! core logic for the pass is contained in `instantiate_expr`.

use crate::data::anon_sum_ast as anon;
use crate::data::borrow_model as model;
use crate::data::first_order_ast::{CustomFuncId, CustomTypeId, VariantId};
use crate::data::flat_ast::{self as flat, CustomTypeSccId, LocalId};
use crate::data::guarded_ast::{self as guarded, CanGuard};
use crate::data::intrinsics as intr;
use crate::data::mode_annot_ast2::{
    self as annot, HeapModes, Interner, Lt, LtParam, Mode, ModeParam, ModeSolution, ModeVar, Occur,
    Position, Res, ResModes, SelfInfo, Shape, ShapeInner, SlotId, Type,
};
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::intrinsic_config::intrinsic_sig;
use crate::pretty_print::borrow_common::{write_lifetime, write_mode};
use crate::pretty_print::mode_annot::{write_shape, write_type};
use crate::pretty_print::utils::{CustomTypeRenderer, FuncRenderer};
use crate::util::collection_ext::FnWrap;
use crate::util::inequality_graph2 as in_eq;
use crate::util::iter::IterExt;
use crate::util::local_context::LocalContext;
use crate::util::non_empty_set::NonEmptySet;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{id_type, Count, Id, IdMap, IdVec};
use id_graph_sccs::{find_components, Scc, SccKind, Sccs};
use std::collections::{BTreeMap, BTreeSet};

// It is crucial that RC specialization (the next pass) does not inhibit tail calls by inserting
// retains/releases after them. Hence, this pass must detect tail calls during constraint
// generation. The machinery here is duplicative of the machinery for the actual tail call
// elimination pass, but it is better to recompute later which calls are tail in case we accidently
// *do* inhibit such a call.

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
enum IsTail {
    Tail,
    NotTail,
}

#[derive(Clone, Debug)]
struct TailFuncDef {
    purity: Purity,
    arg_ty: anon::Type,
    ret_ty: anon::Type,
    body: TailExpr,
    profile_point: Option<prof::ProfilePointId>,
}

/// A `flat::Expr` where all tail calls are marked.
#[derive(Clone, Debug)]
enum TailExpr {
    Local(LocalId),
    Call(Purity, IsTail, CustomFuncId, LocalId),
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
    pos: IsTail,
    vars_in_scope: usize,
    expr: &flat::Expr,
) -> TailExpr {
    match expr {
        flat::Expr::Local(id) => TailExpr::Local(*id),

        flat::Expr::Call(purity, func, arg) => {
            let actual_pos = if pos == IsTail::Tail && tail_candidates.contains(func) {
                IsTail::Tail
            } else {
                IsTail::NotTail
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
                        IsTail::NotTail
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
            let body = mark_tail_calls(&tail_candidates, IsTail::Tail, 1, &func.body);
            tail_funcs.insert(
                func_id,
                TailFuncDef {
                    purity: func.purity,
                    arg_ty: func.arg_type.clone(),
                    ret_ty: func.ret_type.clone(),
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

fn parameterize_type<'a>(
    interner: &Interner,
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    ty: &anon::Type,
) -> Type<ModeParam, LtParam> {
    let shape = Shape::from_anon(
        interner,
        customs,
        FnWrap::wrap(|id| &customs[*id].scc),
        SelfInfo::Structural,
        ty,
    );
    let mut mode_count = Count::new();
    let mut lt_count = Count::new();
    let res = shape.gen_resources(customs, || mode_count.inc(), || lt_count.inc());
    Type { shape, res }
}

fn parameterize_custom_scc(
    interner: &Interner,
    customs: &IdVec<CustomTypeId, guarded::CustomTypeDef>,
    parameterized: &IdMap<CustomTypeId, annot::CustomTypeDef>,
    scc_id: CustomTypeSccId,
    scc: Scc<'_, CustomTypeId>,
) -> BTreeMap<CustomTypeId, annot::CustomTypeDef> {
    scc.nodes
        .iter()
        .map(|&id| {
            let custom = &customs[id];
            let content = Shape::from_anon(
                interner,
                parameterized,
                FnWrap::wrap(|id| &customs[*id].scc),
                SelfInfo::Custom(scc_id),
                &custom.content,
            );
            let pos = content.positions(parameterized);
            (
                id,
                annot::CustomTypeDef {
                    content,
                    pos,
                    scc: custom.scc,
                    can_guard: custom.can_guard,
                },
            )
        })
        .collect()
}

fn parameterize_customs(
    interner: &Interner,
    customs: &guarded::CustomTypes,
) -> IdVec<CustomTypeId, annot::CustomTypeDef> {
    let mut parameterized = IdMap::new();

    for (scc_id, scc) in &customs.sccs {
        let to_populate =
            parameterize_custom_scc(interner, &customs.types, &parameterized, scc_id, scc);
        for (id, typedef) in to_populate {
            parameterized.insert_vacant(id, typedef);
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

fn require_owned(constrs: &mut ConstrGraph, modes: ResModes<ModeVar>) {
    match modes {
        ResModes::Stack(stack) => {
            constrs.require_le_const(&Mode::Owned, stack);
        }
        ResModes::Heap(heap) => {
            constrs.require_le_const(&Mode::Owned, heap.access);
            constrs.require_le_const(&Mode::Owned, heap.storage);
        }
    }
}

fn require_eq(constrs: &mut ConstrGraph, modes1: &ResModes<ModeVar>, modes2: &ResModes<ModeVar>) {
    match (modes1, modes2) {
        (ResModes::Stack(stack1), ResModes::Stack(stack2)) => {
            constrs.require_eq(*stack1, *stack2);
        }
        (ResModes::Heap(heap1), ResModes::Heap(heap2)) => {
            constrs.require_eq(heap1.access, heap2.access);
            constrs.require_eq(heap1.storage, heap2.storage);
        }
        _ => panic!("mismatched modes"),
    }
}

fn bind_modes<L1, L2>(constrs: &mut ConstrGraph, ty1: &Type<ModeVar, L1>, ty2: &Type<ModeVar, L2>) {
    debug_assert_eq!(ty1.shape, ty2.shape);
    for (res1, res2) in ty1.iter().zip_eq(ty2.iter()) {
        require_eq(constrs, &res1.modes, &res2.modes);
    }
}

// Unfortunately, we can't quite use `MapRef` as the type of `subst` here because, for the callers
// of this function to be efficient, `subst` must return values (not references).
fn subst_modes<M1: Clone, M2, L: Clone>(ty: &Type<M1, L>, subst: impl Fn(M1) -> M2) -> Type<M2, L> {
    let f = |res: &Res<M1, L>| {
        let modes = match &res.modes {
            ResModes::Stack(stack) => ResModes::Stack(subst(stack.clone())),
            ResModes::Heap(heap) => ResModes::Heap(HeapModes {
                access: subst(heap.access.clone()),
                storage: subst(heap.storage.clone()),
            }),
        };
        let lt = res.lt.clone();
        Res { modes, lt }
    };
    Type {
        shape: ty.shape.clone(),
        res: IdVec::from_vec(ty.iter().map(f).collect()),
    }
}

fn emit_occur_constr(
    constrs: &mut ConstrGraph,
    scope: &annot::Path,
    binding_modes: &ResModes<ModeVar>,
    use_modes: &ResModes<ModeVar>,
    use_lt: &Lt,
) {
    if use_lt.does_not_exceed(scope) {
        // Case: this is a non-escaping ("opportunistic" or "borrow") occurrence.
        match (binding_modes, use_modes) {
            (ResModes::Stack(binding_stack), ResModes::Stack(use_stack)) => {
                constrs.require_le(*use_stack, *binding_stack);
            }
            (ResModes::Heap(binding_heap), ResModes::Heap(use_heap)) => {
                constrs.require_le(use_heap.access, binding_heap.access);
                constrs.require_eq(use_heap.storage, binding_heap.storage);
            }
            _ => panic!("mismatched modes"),
        }
    } else {
        // Case: this is an escaping ("move" or "dup") occurrence.
        require_eq(constrs, binding_modes, use_modes);
    }
}

fn emit_occur_constrs(
    constrs: &mut ConstrGraph,
    scope: &annot::Path,
    binding_ty: &Type<ModeVar, Lt>,
    use_ty: &Type<ModeVar, Lt>,
) {
    debug_assert_eq!(binding_ty.shape, use_ty.shape);
    for (binding_res, use_res) in binding_ty.iter().zip_eq(use_ty.iter()) {
        emit_occur_constr(
            constrs,
            scope,
            &binding_res.modes,
            &use_res.modes,
            &use_res.lt,
        );
    }
}

/// This meet is left-biased in that the modes of `ty1` are preserved. Note that types are
/// contravariant in their lifetimes (unlike in Rust).
fn left_meet(
    interner: &Interner,
    ty1: &Type<ModeVar, Lt>,
    ty2: &Type<ModeVar, Lt>,
) -> Type<ModeVar, Lt> {
    debug_assert_eq!(ty1.shape, ty2.shape);
    let f = |(res1, res2): (&Res<_, Lt>, &Res<_, Lt>)| Res {
        modes: res1.modes.clone(),
        lt: res1.lt.join(interner, &res2.lt),
    };
    Type {
        shape: ty1.shape.clone(),
        res: IdVec::from_vec(ty1.iter().zip_eq(ty2.iter()).map(f).collect()),
    }
}

fn wrap_lts<M: Clone>(ty: &Type<M, LtParam>) -> Type<M, Lt> {
    let f = |res: &Res<M, LtParam>| Res {
        modes: res.modes.clone(),
        lt: Lt::Join(NonEmptySet::new(res.lt)),
    };
    Type {
        shape: ty.shape.clone(),
        res: IdVec::from_vec(ty.iter().map(f).collect()),
    }
}

fn bind_lts<M>(
    interner: &Interner,
    ty1: &Type<M, LtParam>,
    ty2: &Type<M, Lt>,
) -> BTreeMap<LtParam, Lt> {
    debug_assert_eq!(ty1.shape, ty2.shape);
    let mut result = BTreeMap::new();
    for (res1, res2) in ty1.iter().zip_eq(ty2.iter()) {
        result
            .entry(res1.lt)
            .and_modify(|old: &mut Lt| *old = old.join(interner, &res2.lt))
            .or_insert_with(|| res2.lt.clone());
    }
    result
}

fn subst_lts<M: Clone>(
    interner: &Interner,
    ty: &Type<M, Lt>,
    subst: &BTreeMap<LtParam, Lt>,
) -> Type<M, Lt> {
    let f = |res: &Res<M, Lt>| {
        let modes = res.modes.clone();
        let lt = match &res.lt {
            Lt::Empty => Lt::Empty,
            Lt::Local(lt) => Lt::Local(lt.clone()),
            Lt::Join(params) => params
                .iter()
                .map(|p| &subst[p])
                .fold(Lt::Empty, |lt1, lt2| lt1.join(interner, lt2)),
        };
        Res { modes, lt }
    };
    Type {
        shape: ty.shape.clone(),
        res: IdVec::from_vec(ty.iter().map(f).collect()),
    }
}

fn join_everywhere<M: Clone>(interner: &Interner, ty: &Type<M, Lt>, new_lt: &Lt) -> Type<M, Lt> {
    let f = |res: &Res<M, Lt>| Res {
        modes: res.modes.clone(),
        lt: res.lt.join(interner, new_lt),
    };
    Type {
        shape: ty.shape.clone(),
        res: IdVec::from_vec(ty.iter().map(f).collect()),
    }
}

fn lt_equiv<M>(ty1: &Type<M, Lt>, ty2: &Type<M, Lt>) -> bool {
    debug_assert_eq!(ty1.shape, ty2.shape);
    ty1.iter()
        .zip_eq(ty2.iter())
        .all(|(res1, res2)| res1.lt == res2.lt)
}

fn nth_res_bounds(shapes: &[Shape], n: usize) -> (usize, usize) {
    let start = shapes.iter().map(|shape| shape.num_slots).take(n).sum();
    let end = start + shapes[n].num_slots;
    (start, end)
}

fn split_shapes<M: Clone, L: Clone>(shapes: &[Shape], res: &[Res<M, L>]) -> Vec<Type<M, L>> {
    annot::iter_shapes(shapes, res)
        .map(|(shape, res)| Type {
            shape: shape.clone(),
            res: IdVec::from_vec(res.iter().cloned().collect()),
        })
        .collect()
}

fn elim_tuple<'a, M: Clone, L: Clone>(ty: &Type<M, L>) -> Vec<Type<M, L>> {
    let ShapeInner::Tuple(shapes) = &*ty.shape.inner else {
        panic!("expected `Tuple` type");
    };
    split_shapes(shapes, ty.res.as_slice())
}

fn elim_variants<'a, M: Clone, L: Clone>(ty: &Type<M, L>) -> IdVec<VariantId, Type<M, L>> {
    let ShapeInner::Variants(shapes) = &*ty.shape.inner else {
        panic!("expected `Tuple` type");
    };
    let result = split_shapes(shapes.as_slice(), ty.res.as_slice());
    assert_eq!(result.len(), shapes.len());
    IdVec::from_vec(result)
}

fn elim_box_like<M: Clone, L: Clone>(item: &Shape, res: &[Res<M, L>]) -> (Res<M, L>, Type<M, L>) {
    (
        res[0].clone(),
        Type {
            shape: item.clone(),
            res: IdVec::from_vec(res[1..].iter().cloned().collect()),
        },
    )
}

fn elim_array<M: Clone, L: Clone>(ty: &Type<M, L>) -> (Res<M, L>, Type<M, L>) {
    let ShapeInner::Array(shape) = &*ty.shape.inner else {
        panic!("expected `Array` type");
    };
    elim_box_like(shape, ty.res.as_slice())
}

fn elim_boxed<M: Clone, L: Clone>(ty: &Type<M, L>) -> (Res<M, L>, Type<M, L>) {
    let ShapeInner::Boxed(shape) = &*ty.shape.inner else {
        panic!("expected `Boxed` type");
    };
    elim_box_like(shape, ty.res.as_slice())
}

/// Replaces parameters with fresh variables from the constraint graph.
fn freshen_type<M, L1, L2>(
    constrs: &mut ConstrGraph,
    mut fresh_lt: impl FnMut() -> L2,
    ty: &Type<M, L1>,
) -> Type<ModeVar, L2> {
    let f = |res: &Res<_, _>| {
        let modes = match res.modes {
            ResModes::Stack(_) => ResModes::Stack(constrs.fresh_var()),
            ResModes::Heap(_) => ResModes::Heap(HeapModes {
                access: constrs.fresh_var(),
                storage: constrs.fresh_var(),
            }),
        };
        let lt = fresh_lt();
        Res { modes, lt }
    };
    annot::Type {
        shape: ty.shape.clone(),
        res: IdVec::from_vec(ty.iter().map(f).collect()),
    }
}

fn freshen_type_unused<M, L>(constrs: &mut ConstrGraph, ty: &Type<M, L>) -> Type<ModeVar, Lt> {
    freshen_type(constrs, || Lt::Empty, ty)
}

fn instantiate_condition(
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    constrs: &mut ConstrGraph,
    cond: &flat::Condition,
) -> annot::Condition {
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
        flat::Condition::Boxed(cond, _ty) => {
            annot::Condition::Boxed(Box::new(instantiate_condition(customs, constrs, cond)))
        }
        flat::Condition::Custom(_id, cond) => {
            annot::Condition::Custom(Box::new(instantiate_condition(customs, constrs, cond)))
        }
        flat::Condition::BoolConst(v) => annot::Condition::BoolConst(*v),
        flat::Condition::ByteConst(v) => annot::Condition::ByteConst(*v),
        flat::Condition::IntConst(v) => annot::Condition::IntConst(*v),
        flat::Condition::FloatConst(v) => annot::Condition::FloatConst(*v),
    }
}

fn instantiate_occur_in_position(
    _strategy: Strategy,
    interner: &Interner,
    pos: IsTail,
    ctx: &mut LocalContext<LocalId, LocalInfo>,
    constrs: &mut ConstrGraph,
    id: LocalId,
    use_ty: &Type<ModeVar, Lt>,
) -> Occur<ModeVar, Lt> {
    let binding = ctx.local_binding_mut(id);

    if pos == IsTail::Tail {
        bind_modes(constrs, &binding.ty, use_ty);
    } else {
        emit_occur_constrs(constrs, &binding.scope, &binding.ty, use_ty);
    }

    binding.ty = left_meet(interner, &binding.ty, &use_ty);

    annot::Occur {
        id,
        ty: use_ty.clone(),
    }
}

/// Generate occurrence constraints and merge `use_ty` into the typing context. Corresponds to the
/// I-Occur rule.
fn instantiate_occur(
    strategy: Strategy,
    interner: &Interner,
    ctx: &mut LocalContext<LocalId, LocalInfo>,
    constrs: &mut ConstrGraph,
    id: LocalId,
    use_ty: &Type<ModeVar, Lt>,
) -> Occur<ModeVar, Lt> {
    instantiate_occur_in_position(
        strategy,
        interner,
        IsTail::NotTail,
        ctx,
        constrs,
        id,
        use_ty,
    )
}

fn extract_res_impl(
    model: &model::Type,
    shape: &Shape,
    next_slot: usize,
    out_res: &mut BTreeMap<SlotId, Res<ModeParam, LtParam>>,
) -> usize {
    match (model, &*shape.inner) {
        (model::Type::Var(_), _) => next_slot + shape.num_slots,
        (model::Type::Bool, ShapeInner::Bool) => next_slot,
        (model::Type::Num(model), ShapeInner::Num(shape)) if model == shape => next_slot,
        (model::Type::Tuple(models), ShapeInner::Tuple(shapes)) => {
            let iter = models.iter().zip_eq(shapes);
            iter.fold(next_slot, |start, (model, shape)| {
                extract_res_impl(model, shape, start, out_res)
            })
        }
        (model::Type::Array(res, model), ShapeInner::Array(shape)) => {
            out_res.insert(SlotId::from_index(next_slot), res.clone());
            extract_res_impl(model, shape, next_slot + 1, out_res)
        }
        (model::Type::HoleArray(res, model), ShapeInner::HoleArray(shape)) => {
            out_res.insert(SlotId::from_index(next_slot), res.clone());
            extract_res_impl(model, shape, next_slot + 1, out_res)
        }
        (model::Type::Boxed(res, model), ShapeInner::Boxed(shape)) => {
            out_res.insert(SlotId::from_index(next_slot), res.clone());
            extract_res_impl(model, shape, next_slot + 1, out_res)
        }
        _ => panic!("type does not match model"),
    }
}

fn extract_res(model: &model::Type, shape: &Shape) -> BTreeMap<SlotId, Res<ModeParam, LtParam>> {
    let mut out_res = BTreeMap::new();
    extract_res_impl(model, shape, 0, &mut out_res);
    out_res
}

fn extract_vars(
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    model: &model::Type,
    shape: &Shape,
    res: &[Res<ModeVar, Lt>],
    out_vars: &mut IdMap<model::TypeVar, Vec<Type<ModeVar, Lt>>>,
) {
    match (model, &*shape.inner) {
        (model::Type::Var(var), _) => {
            let entry = out_vars.entry(*var).or_insert_with(Vec::new);
            entry.push(Type {
                shape: shape.clone(),
                res: IdVec::from_vec(res.iter().cloned().collect()),
            });
        }
        (model::Type::Bool, ShapeInner::Bool) => {}
        (model::Type::Num(model), ShapeInner::Num(shape)) if model == shape => {}
        (model::Type::Tuple(models), ShapeInner::Tuple(shapes)) => {
            for (model, (shape, res)) in models.iter().zip_eq(annot::iter_shapes(shapes, res)) {
                extract_vars(customs, model, shape, res, out_vars);
            }
        }
        (model::Type::Array(_res, model), ShapeInner::Array(shape)) => {
            extract_vars(customs, model, shape, &res[1..], out_vars);
        }
        (model::Type::HoleArray(_res, model), ShapeInner::HoleArray(shape)) => {
            extract_vars(customs, model, shape, &res[1..], out_vars);
        }
        (model::Type::Boxed(_res, model), ShapeInner::Boxed(shape)) => {
            extract_vars(customs, model, shape, &res[1..], out_vars);
        }
        _ => panic!("type does not match model"),
    }
}

fn extract_prop(prop: model::Prop, res: &ResModes<ModeVar>) -> ModeVar {
    match prop {
        model::Prop::Stack => match res {
            ResModes::Stack(stack) => *stack,
            _ => panic!("expected stack resource"),
        },
        model::Prop::Access => match res {
            ResModes::Heap(heap) => heap.access,
            _ => panic!("expected heap resource"),
        },
        model::Prop::Storage => match res {
            ResModes::Heap(heap) => heap.storage,
            _ => panic!("expected heap resource"),
        },
    }
}

fn instantiate_model(
    sig: &model::Signature,
    _strategy: Strategy,
    interner: &Interner,
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    constrs: &mut ConstrGraph,
    ctx: &mut LocalContext<LocalId, LocalInfo>,
    path: &annot::Path,
    args: &[LocalId],
    ret: &Type<ModeVar, Lt>,
) -> Vec<annot::Occur<ModeVar, Lt>> {
    assert!(args.len() >= sig.args.fixed.len());

    // Create fresh occurrences for each function argument.
    let mut occurs = args
        .iter()
        .map(|&id| {
            let ty = freshen_type_unused(constrs, &ctx.local_binding(id).ty);
            annot::Occur { id, ty }
        })
        .collect::<Vec<_>>();

    // Set up the mapping from model modes to concrete modes.
    let mode_mapping = IdVec::from_count_with(sig.mode_count, |_| constrs.fresh_var());
    for param in &sig.owned_modes {
        constrs.require_le_const(&Mode::Owned, mode_mapping[param]);
    }

    let subst_modes = |modes| match modes {
        ResModes::Stack(stack) => ResModes::Stack(mode_mapping[stack]),
        ResModes::Heap(heap) => ResModes::Heap(HeapModes {
            access: mode_mapping[heap.access],
            storage: mode_mapping[heap.storage],
        }),
    };

    // - Impose top-level mode constraints on the return type.
    // - Record the mapping from model lifetimes to concrete lifetimes.
    let mut lt_mapping = IdVec::from_count_with(sig.lt_count, |_| None);
    for (slot, model_res) in extract_res(&sig.ret, &ret.shape) {
        let res = &ret.res[slot];
        require_eq(constrs, &subst_modes(model_res.modes), &res.modes);

        if sig.unused_lts.contains(&model_res.lt) {
            panic!("unused model lifetimes cannot be supplied in return position");
        }
        assert!(matches!(res.lt, Lt::Join(_)));
        match &mut lt_mapping[model_res.lt] {
            entry @ None => *entry = Some(res.lt.clone()),
            Some(_) => {
                panic!("a lifetime variable cannot appear more than once in a model return type");
            }
        }
    }

    let lt_mapping = lt_mapping;

    // For each argument type:
    // - Impose top-level mode constraints.
    // - Substitute for model lifetimes using the mapping constructed from the return type.
    for (arg, occur) in sig.args.iter().zip(&mut occurs) {
        for (slot, model_res) in extract_res(arg, &occur.ty.shape) {
            let res = &mut occur.ty.res[slot];
            require_eq(constrs, &subst_modes(model_res.modes), &res.modes);

            res.lt = if let Some(lt) = &lt_mapping[model_res.lt] {
                lt.clone()
            } else if sig.unused_lts.contains(&model_res.lt) {
                Lt::Empty
            } else {
                path.as_lt(interner)
            };
        }
    }

    // Accumulate the resources for each occurrence of each type variable.
    let mut vars = IdMap::new();
    for (model, occur) in sig.args.iter().zip(&occurs) {
        extract_vars(
            customs,
            model,
            &occur.ty.shape,
            occur.ty.res.as_slice(),
            &mut vars,
        );
    }
    extract_vars(customs, &sig.ret, &ret.shape, ret.res.as_slice(), &mut vars);
    let vars = vars.to_id_vec(sig.var_count);

    // Impose equality constraints between all occurrences of the same type variable.
    for occurs in vars.values() {
        if occurs.len() > 1 {
            let rep = &occurs[0];
            for occur in &occurs[1..] {
                bind_modes(constrs, &rep, occur);
            }
        }
    }

    // Handle any constraints on type variables.
    for constr in &sig.constrs {
        let rep1 = &vars[constr.lhs.type_var][0];
        let rep2 = &vars[constr.rhs.type_var][0];
        debug_assert_eq!(rep1.shape, rep2.shape);

        let prop1 = constr.lhs.prop;
        let prop2 = constr.rhs.prop;

        let pos = rep1.shape.positions(customs);

        for (pos, (res1, res2)) in pos.iter().zip_eq(rep1.iter().zip_eq(rep2.iter())) {
            match pos {
                Position::Stack => {
                    let mode1 = extract_prop(prop1, &res1.modes);
                    let mode2 = extract_prop(prop2, &res2.modes);
                    constrs.require_eq(mode1, mode2);
                }
                Position::Heap => {
                    require_eq(constrs, &res1.modes, &res2.modes);
                }
            }
        }
    }

    occurs
}

/// Used during lifetime fixed point iteration. `know_defs` contains the definitions of all
/// functions from previous SCCs. `pending_args` and `pending_rets` contain the signatures of types
/// from the current SCC as of the previous iteration.
#[derive(Clone, Copy, Debug)]
struct SignatureAssumptions<'a> {
    known_defs: &'a IdMap<CustomFuncId, annot::FuncDef>,
    pending_args: &'a BTreeMap<CustomFuncId, Type<ModeVar, Lt>>,
    pending_rets: &'a BTreeMap<CustomFuncId, Type<ModeVar, LtParam>>,
}

impl<'a> SignatureAssumptions<'a> {
    fn sig_of(
        &self,
        constrs: &mut ConstrGraph,
        id: CustomFuncId,
    ) -> (Type<ModeVar, Lt>, Type<ModeVar, LtParam>) {
        self.known_defs.get(id).map_or_else(
            || {
                (
                    self.pending_args[&id].clone(),
                    self.pending_rets[&id].clone(),
                )
            },
            |def| {
                let subst = constrs.instantiate_subgraph(&def.constrs.sig);
                (
                    subst_modes(&def.arg_ty, |p| subst[p]),
                    subst_modes(&def.ret_ty, |p| subst[p]),
                )
            },
        )
    }
}

struct LocalInfo {
    scope: annot::Path,
    ty: Type<ModeVar, Lt>,
}

/// Our analysis makes the following approximation: from the perspective of a function's caller all
/// accesses the callee makes to its arguments happen at the same time. To implement this behavior,
/// we use `prepare_arg_type` to replace all local lifetimes in the argument with the caller's
/// current path. Even if we didn't make this approximation, we would have to somehow relativize the
/// local lifetimes in the argument since they are not meaningful in the caller's scope.
fn prepare_arg_type(
    interner: &Interner,
    path: &annot::Path,
    ty: &Type<ModeVar, Lt>,
) -> Type<ModeVar, Lt> {
    let f = |res: &Res<ModeVar, Lt>| {
        let modes = res.modes.clone();
        let lt = match &res.lt {
            Lt::Empty => Lt::Empty,
            Lt::Local(_) => path.as_lt(interner),
            Lt::Join(vars) => Lt::Join(vars.clone()),
        };
        Res { modes, lt }
    };
    Type {
        shape: ty.shape.clone(),
        res: IdVec::from_vec(ty.res.values().map(f).collect()),
    }
}

fn guard_type_impl<L: Clone>(
    interner: &Interner,
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    all_res: &[Res<ModeVar, L>],
    shape: &Shape,
    res: &[Res<ModeVar, L>],
    out_res: &mut IdVec<SlotId, Res<ModeVar, L>>,
) -> Shape {
    match &*shape.inner {
        ShapeInner::Bool => {
            debug_assert!(res.is_empty());
            shape.clone()
        }
        ShapeInner::Num(_) => {
            debug_assert!(res.is_empty());
            shape.clone()
        }
        ShapeInner::Tuple(shapes) => {
            let shapes = annot::iter_shapes(shapes, res)
                .map(|(shape, res)| {
                    guard_type_impl(interner, customs, all_res, shape, res, out_res)
                })
                .collect::<Vec<_>>();

            let num_slots = shapes.iter().map(|shape| shape.num_slots).sum();
            let inner = interner.shape.new(ShapeInner::Tuple(shapes));
            Shape { inner, num_slots }
        }
        ShapeInner::Variants(shapes) => {
            let shapes = annot::iter_shapes(shapes.as_slice(), res)
                .map(|(shape, res)| {
                    guard_type_impl(interner, customs, all_res, shape, res, out_res)
                })
                .collect::<Vec<_>>();

            let num_slots = shapes.iter().map(|shape| shape.num_slots).sum();
            let inner = interner
                .shape
                .new(ShapeInner::Variants(IdVec::from_vec(shapes)));
            Shape { inner, num_slots }
        }
        // The non-trival base case.
        ShapeInner::SelfCustom(id) => {
            debug_assert!(res.is_empty());
            let _ = out_res.extend(all_res.iter().cloned());
            customs[*id].content.clone()
        }
        ShapeInner::Custom(_) => {
            let _ = out_res.extend(res.iter().cloned());
            shape.clone()
        }
        ShapeInner::Array(shape) => {
            let _ = out_res.push(res[0].clone());
            let shape = guard_type_impl(interner, customs, all_res, shape, &res[1..], out_res);

            let num_slots = 1 + shape.num_slots;
            let inner = interner.shape.new(ShapeInner::Array(shape));
            Shape { inner, num_slots }
        }
        ShapeInner::HoleArray(shape) => {
            let _ = out_res.push(res[0].clone());
            let shape = guard_type_impl(interner, customs, all_res, shape, &res[1..], out_res);

            let num_slots = 1 + shape.num_slots;
            let inner = interner.shape.new(ShapeInner::HoleArray(shape));
            Shape { inner, num_slots }
        }
        ShapeInner::Boxed(shape) => {
            let _ = out_res.push(res[0].clone());
            let shape = guard_type_impl(interner, customs, all_res, shape, &res[1..], out_res);

            let num_slots = 1 + shape.num_slots;
            let inner = interner.shape.new(ShapeInner::Boxed(shape));
            Shape { inner, num_slots }
        }
    }
}

fn unfold_type<L: Clone>(
    interner: &Interner,
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    ty: &Type<ModeVar, L>,
) -> Type<ModeVar, L> {
    let mut res = IdVec::new();
    let all_res = ty.res.as_slice();
    let shape = guard_type_impl(interner, customs, all_res, &ty.shape, all_res, &mut res);

    debug_assert!(res.len() == shape.num_slots);
    Type { shape, res }
}

// This function is the core logic for this pass. It implements the judgement from the paper:
// Δ ; Γ ; S ; q ⊢ e : t ⇝ e ; Q ; Γ'
//
// Note that we must return a set of updates rather than mutating Γ because I-Match requires that we
// check all branches in the initial Γ.
fn instantiate_expr(
    strategy: Strategy,
    interner: &Interner,
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    sigs: SignatureAssumptions,
    constrs: &mut ConstrGraph,
    ctx: &mut LocalContext<LocalId, LocalInfo>,
    path: annot::Path,
    fut_ty: &Type<ModeVar, Lt>,
    expr: &TailExpr,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
) -> annot::Expr<ModeVar, Lt> {
    match expr {
        TailExpr::Local(local) => {
            let occur = instantiate_occur(strategy, interner, ctx, constrs, *local, fut_ty);
            annot::Expr::Local(occur)
        }

        TailExpr::Call(purity, pos, func, arg) => {
            let (arg_ty, ret_ty) = sigs.sig_of(constrs, *func);

            bind_modes(constrs, &ret_ty, fut_ty);
            let lt_subst = bind_lts(interner, &ret_ty, fut_ty);
            let arg_ty = prepare_arg_type(interner, &path, &arg_ty);
            let path = path.as_lt(interner);

            // This `join_everywhere` reflects the fact that we assume that functions access all of
            // their arguments. We could be more precise here.
            let arg_ty = join_everywhere(interner, &subst_lts(interner, &arg_ty, &lt_subst), &path);
            let arg = instantiate_occur_in_position(
                strategy, interner, *pos, ctx, constrs, *arg, &arg_ty,
            );

            annot::Expr::Call(*purity, *func, arg)
        }

        TailExpr::Branch(discrim_id, cases, _ret_ty) => {
            // This loop updates `ctx` in place on each iteration despite the fact that the branch
            // arms happen "in parallel". This is fine: only the lifetimes of bindings are updated,
            // these lifetimes are only used for the purpose of generating occurrence constraints,
            // and the relevant lifetime comparisons are unaffected by joining the bindings'
            // lifetimes with data from parallel arms.
            let mut cases_annot_rev = Vec::new();
            for (i, (cond, body)) in cases.iter().enumerate().rev() {
                let cond_annot = instantiate_condition(customs, constrs, cond);
                let body_annot = instantiate_expr(
                    strategy,
                    interner,
                    customs,
                    sigs,
                    constrs,
                    ctx,
                    // The discriminate happens at `path.seq(0)`
                    path.seq(1).alt(i, cases.len()),
                    fut_ty,
                    body,
                    type_renderer,
                );

                cases_annot_rev.push((cond_annot, body_annot));
            }

            let cases_annot = {
                cases_annot_rev.reverse();
                cases_annot_rev
            };

            let discrim_fut_ty = freshen_type_unused(constrs, &ctx.local_binding(*discrim_id).ty);
            let discrim_occur = instantiate_occur(
                strategy,
                interner,
                ctx,
                constrs,
                *discrim_id,
                &discrim_fut_ty,
            );

            annot::Expr::Branch(discrim_occur, cases_annot, fut_ty.clone())
        }

        // We're only using `with_scope` here for its debug assertion, and to signal intent; by the
        // time the passed closure returns, we've manually truncated away all the variables which it
        // would usually be `with_scope`'s responsibility to remove.
        TailExpr::LetMany(bindings, result_id) => ctx.with_scope(|ctx| {
            let locals_offset = ctx.len();

            // Leave space for the result, which happens after all the bindings. During this pass we
            // only care about paths where borrows are accessed, so nothing relevant can happen at
            // this path. But, we will care about it when we compute obligations.
            let end_of_scope = path.seq(bindings.len() + 1);

            for (binding_ty, _) in bindings {
                let annot_ty =
                    freshen_type_unused(constrs, &parameterize_type(interner, customs, binding_ty));
                let _ = ctx.add_local(LocalInfo {
                    scope: end_of_scope.clone(),
                    ty: annot_ty,
                });
            }

            let result_occur =
                instantiate_occur(strategy, interner, ctx, constrs, *result_id, fut_ty);

            let mut bindings_annot_rev = Vec::new();
            for (i, (_, binding_expr)) in bindings.iter().enumerate().rev() {
                let local = LocalId(locals_offset + i);
                let fut_ty = ctx.local_binding(local).ty.clone();

                // Only retain the locals *strictly* before this binding.
                ctx.truncate(Count::from_value(local.0));

                let expr_annot = instantiate_expr(
                    strategy,
                    interner,
                    customs,
                    sigs,
                    constrs,
                    ctx,
                    path.seq(i),
                    &fut_ty,
                    binding_expr,
                    type_renderer,
                );

                bindings_annot_rev.push((fut_ty, expr_annot));
            }

            let bindings_annot = {
                bindings_annot_rev.reverse();
                bindings_annot_rev
            };

            annot::Expr::LetMany(bindings_annot, result_occur)
        }),

        TailExpr::Tuple(item_ids) => {
            let fut_item_tys = elim_tuple(fut_ty);
            // We must process the items in reverse order to ensure `instantiate_occur` (which
            // updates the lifetimes in `ctx`) generates the correct constraints.
            let mut occurs_rev = item_ids
                .iter()
                .zip_eq(fut_item_tys)
                .rev()
                .map(|(item_id, item_ty)| {
                    instantiate_occur(strategy, interner, ctx, constrs, *item_id, &item_ty)
                })
                .collect::<Vec<_>>();
            let occurs = {
                occurs_rev.reverse();
                occurs_rev
            };
            annot::Expr::Tuple(occurs)
        }

        TailExpr::TupleField(tuple_id, idx) => {
            let mut tuple_ty = freshen_type_unused(constrs, &ctx.local_binding(*tuple_id).ty);
            let ShapeInner::Tuple(shapes) = &*tuple_ty.shape.inner else {
                panic!("expected `Tuple` type");
            };

            let (start, end) = nth_res_bounds(shapes, *idx);
            tuple_ty.res.as_mut_slice()[start..end].clone_from_slice(fut_ty.res.as_slice());

            let occur = instantiate_occur(strategy, interner, ctx, constrs, *tuple_id, &tuple_ty);
            annot::Expr::TupleField(occur, *idx)
        }

        TailExpr::WrapVariant(_variant_tys, variant_id, content) => {
            let fut_variant_tys = elim_variants(fut_ty);
            let occur = instantiate_occur(
                strategy,
                interner,
                ctx,
                constrs,
                *content,
                &fut_variant_tys[*variant_id],
            );
            annot::Expr::WrapVariant(fut_variant_tys, *variant_id, occur)
        }

        TailExpr::UnwrapVariant(variant_id, wrapped) => {
            let mut variants_ty = freshen_type_unused(constrs, &ctx.local_binding(*wrapped).ty);
            let ShapeInner::Variants(shapes) = &*variants_ty.shape.inner else {
                panic!("expected `Variants` type");
            };

            let (start, end) = nth_res_bounds(shapes.as_slice(), variant_id.to_index());
            variants_ty.res.as_mut_slice()[start..end].clone_from_slice(fut_ty.res.as_slice());

            let occur = instantiate_occur(strategy, interner, ctx, constrs, *wrapped, &variants_ty);
            annot::Expr::UnwrapVariant(*variant_id, occur)
        }

        TailExpr::WrapBoxed(content, _item_ty) => {
            let mut occurs = instantiate_model(
                &*model::box_new,
                strategy,
                interner,
                customs,
                constrs,
                ctx,
                &path,
                &[*content],
                fut_ty,
            );
            let (_, fut_item_ty) = elim_boxed(fut_ty);
            annot::Expr::WrapBoxed(occurs.pop().unwrap(), fut_item_ty)
        }

        TailExpr::UnwrapBoxed(wrapped, _item_ty) => {
            let mut occurs = instantiate_model(
                &*model::box_get,
                strategy,
                interner,
                customs,
                constrs,
                ctx,
                &path,
                &[*wrapped],
                fut_ty,
            );
            annot::Expr::UnwrapBoxed(occurs.pop().unwrap(), fut_ty.clone())
        }

        TailExpr::WrapCustom(custom_id, unfolded) => {
            let fut_unfolded = unfold_type(interner, customs, fut_ty);
            print!("unfolded: ");
            write_type(
                &mut std::io::stdout(),
                Some(type_renderer),
                |w, m: &ModeVar| write!(w, "{}", m.0),
                write_lifetime,
                &ctx.local_binding(*unfolded).ty,
            )
            .unwrap();
            println!();
            print!("fut_ty: ");
            write_type(
                &mut std::io::stdout(),
                Some(type_renderer),
                |w, m: &ModeVar| write!(w, "{}", m.0),
                write_lifetime,
                fut_ty,
            )
            .unwrap();
            println!();
            print!("fut_unfolded: ");
            write_type(
                &mut std::io::stdout(),
                Some(type_renderer),
                |w, m: &ModeVar| write!(w, "{}", m.0),
                write_lifetime,
                &fut_unfolded,
            )
            .unwrap();
            println!();
            let occur =
                instantiate_occur(strategy, interner, ctx, constrs, *unfolded, &fut_unfolded);
            annot::Expr::WrapCustom(*custom_id, occur)
        }

        TailExpr::UnwrapCustom(custom_id, folded) => {
            let fresh_folded = {
                let mut lt_count = Count::new();
                freshen_type(constrs, || lt_count.inc(), &ctx.local_binding(*folded).ty)
            };

            let fresh_folded = {
                // Instead of folding `fut_ty`, we unfold a fresh type, duplicating the modes and
                // lifetimes which would be identified under folding into the proper positions.
                // Imposing constraints between this unfolded type and `fut_ty` yields the same
                // constraint system as folding `fut_ty`.
                let fresh_unfolded = unfold_type(interner, customs, &fresh_folded);

                // Equate the modes in `fut_ty` which are identified under folding.
                bind_modes(constrs, &fresh_unfolded, fut_ty);

                // Join the lifetimes in `fut_ty` which are identified under folding.
                let lt_subst = bind_lts(interner, &fresh_unfolded, fut_ty);
                subst_lts(interner, &wrap_lts(&fresh_folded), &lt_subst)
            };

            let occur = instantiate_occur(strategy, interner, ctx, constrs, *folded, &fresh_folded);
            annot::Expr::UnwrapCustom(*custom_id, occur)
        }

        // Right now, all intrinsics are trivial from a mode inference perspective because they
        // operate on arithmetic types. If this changes, we will have to update this.
        TailExpr::Intrinsic(intr, arg) => {
            let sig = intrinsic_sig(*intr);
            let ty = Type {
                shape: Shape::from_anon(
                    interner,
                    customs,
                    FnWrap::wrap(|id| &customs[*id].scc),
                    SelfInfo::Structural,
                    &anon::Type::from_intr(&sig.arg),
                ),
                res: IdVec::new(),
            };
            annot::Expr::Intrinsic(*intr, Occur { id: *arg, ty })
        }

        TailExpr::ArrayOp(flat::ArrayOp::Get(_, arr_id, idx_id)) => {
            let occurs = instantiate_model(
                &*model::array_get,
                strategy,
                interner,
                customs,
                constrs,
                ctx,
                &path,
                &[*arr_id, *idx_id],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::ArrayOp(annot::ArrayOp::Get(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
                fut_ty.clone(),
            ))
        }

        TailExpr::ArrayOp(flat::ArrayOp::Extract(_item_ty, arr_id, idx_id)) => {
            let occurs = instantiate_model(
                &*model::array_extract,
                strategy,
                interner,
                customs,
                constrs,
                ctx,
                &path,
                &[*arr_id, *idx_id],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::ArrayOp(annot::ArrayOp::Extract(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        TailExpr::ArrayOp(flat::ArrayOp::Len(_item_ty, arr_id)) => {
            let occurs = instantiate_model(
                &*model::array_len,
                strategy,
                interner,
                customs,
                constrs,
                ctx,
                &path,
                &[*arr_id],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::ArrayOp(annot::ArrayOp::Len(occurs.next().unwrap()))
        }

        TailExpr::ArrayOp(flat::ArrayOp::Push(_item_ty, arr_id, item_id)) => {
            let occurs = instantiate_model(
                &*model::array_push,
                strategy,
                interner,
                customs,
                constrs,
                ctx,
                &path,
                &[*arr_id, *item_id],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::ArrayOp(annot::ArrayOp::Push(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        TailExpr::ArrayOp(flat::ArrayOp::Pop(_item_ty, arr_id)) => {
            let occurs = instantiate_model(
                &*model::array_pop,
                strategy,
                interner,
                customs,
                constrs,
                ctx,
                &path,
                &[*arr_id],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::ArrayOp(annot::ArrayOp::Pop(occurs.next().unwrap()))
        }

        TailExpr::ArrayOp(flat::ArrayOp::Replace(_item_ty, hole_id, item_id)) => {
            let occurs = instantiate_model(
                &*model::array_replace,
                strategy,
                interner,
                customs,
                constrs,
                ctx,
                &path,
                &[*hole_id, *item_id],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::ArrayOp(annot::ArrayOp::Replace(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        TailExpr::ArrayOp(flat::ArrayOp::Reserve(_item_ty, arr_id, cap_id)) => {
            let occurs = instantiate_model(
                &*model::array_reserve,
                strategy,
                interner,
                customs,
                constrs,
                ctx,
                &path,
                &[*arr_id, *cap_id],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::ArrayOp(annot::ArrayOp::Reserve(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        TailExpr::IoOp(flat::IoOp::Input) => {
            let _ = instantiate_model(
                &*model::io_input,
                strategy,
                interner,
                customs,
                constrs,
                ctx,
                &path,
                &[],
                fut_ty,
            );
            annot::Expr::IoOp(annot::IoOp::Input)
        }

        TailExpr::IoOp(flat::IoOp::Output(arr_id)) => {
            let occurs = instantiate_model(
                &*model::io_output,
                strategy,
                interner,
                customs,
                constrs,
                ctx,
                &path,
                &[*arr_id],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::IoOp(annot::IoOp::Output(occurs.next().unwrap()))
        }

        TailExpr::Panic(_ret_ty, msg_id) => {
            let occurs = instantiate_model(
                &*model::panic,
                strategy,
                interner,
                customs,
                constrs,
                ctx,
                &path,
                &[*msg_id],
                &Type {
                    shape: Shape::unit(interner),
                    res: IdVec::new(),
                },
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::Panic(fut_ty.clone(), occurs.next().unwrap())
        }

        TailExpr::ArrayLit(_item_ty, item_ids) => {
            let occurs = instantiate_model(
                &*model::array_new,
                strategy,
                interner,
                customs,
                constrs,
                ctx,
                &path,
                item_ids,
                fut_ty,
            );
            let (_, fut_item_ty) = elim_array(fut_ty);
            annot::Expr::ArrayLit(fut_item_ty, occurs)
        }

        TailExpr::BoolLit(val) => annot::Expr::BoolLit(*val),

        TailExpr::ByteLit(val) => annot::Expr::ByteLit(*val),

        TailExpr::IntLit(val) => annot::Expr::IntLit(*val),

        TailExpr::FloatLit(val) => annot::Expr::FloatLit(*val),
    }
}

#[derive(Clone, Debug)]
struct SolverScc {
    func_args: BTreeMap<CustomFuncId, Type<ModeVar, Lt>>,
    func_rets: BTreeMap<CustomFuncId, Type<ModeVar, LtParam>>,
    func_bodies: BTreeMap<CustomFuncId, annot::Expr<ModeVar, Lt>>,
    scc_constrs: ConstrGraph,
}

fn instantiate_scc(
    strategy: Strategy,
    interner: &Interner,
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    funcs: &IdVec<CustomFuncId, TailFuncDef>,
    funcs_annot: &IdMap<CustomFuncId, annot::FuncDef>,
    scc: Scc<CustomFuncId>,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    _func_renderer: &FuncRenderer<CustomFuncId>,
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
                        freshen_type_unused(
                            &mut constrs,
                            &parameterize_type(interner, customs, &funcs[id].arg_ty),
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
                        freshen_type(
                            &mut constrs,
                            &mut || next_lt.inc(),
                            &parameterize_type(interner, customs, &funcs[id].ret_ty),
                        ),
                    )
                })
                .collect::<BTreeMap<_, _>>();

            let sig_params = {
                let mut params = BTreeSet::new();
                while first_lt != next_lt {
                    params.insert(first_lt.inc());
                }
                params
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
                    let mut ctx = LocalContext::new();

                    let arg_ty = freshen_type_unused(
                        &mut constrs,
                        &parameterize_type(interner, customs, &func.arg_ty),
                    );
                    let arg_id = ctx.add_local(LocalInfo {
                        scope: annot::ARG_SCOPE(),
                        ty: arg_ty,
                    });
                    debug_assert_eq!(arg_id, flat::ARG_LOCAL);

                    let ret_ty = wrap_lts(&ret_tys[id]);
                    let expr = instantiate_expr(
                        strategy,
                        interner,
                        customs,
                        assumptions,
                        &mut constrs,
                        &mut ctx,
                        annot::FUNC_BODY_PATH(),
                        &ret_ty,
                        &func.body,
                        type_renderer,
                    );
                    bodies.insert(*id, expr);

                    new_arg_tys.insert(*id, (ctx.local_binding(flat::ARG_LOCAL).ty).clone());
                }

                debug_assert!(
                    {
                        let params_found = new_arg_tys
                            .values()
                            .flat_map(|ty| ty.iter().map(|res| &res.lt))
                            .filter_map(|lt| match lt {
                                Lt::Empty | Lt::Local(_) => None,
                                Lt::Join(params) => Some(params.iter().copied()),
                            })
                            .flatten()
                            .collect::<BTreeSet<_>>();
                        params_found.is_subset(&sig_params)
                    },
                    "Some temporary lifetime parameters leaked into the function arguments during \
                     expression instantiation. Only parameters from the return type should appear."
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

            // We could avoid a lot of the work in the "always owned" case, but this is the simplest
            // intervention point
            if strategy == Strategy::AlwaysOwned {
                for var in constrs.var_count() {
                    constrs.require_le_const(&Mode::Owned, var);
                }
            } else if strategy == Strategy::OnlyTrivialBorrows {
                for var in ret_tys
                    .values()
                    .flat_map(|ty| ty.iter_flat())
                    .map(|(m, _)| *m)
                {
                    constrs.require_le_const(&Mode::Owned, var);
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

fn extract_type(solution: &Solution, ty: &Type<ModeVar, Lt>) -> Type<ModeSolution, Lt> {
    subst_modes(ty, |m| ModeSolution {
        lb: solution.lower_bounds[m].clone(),
        solver_var: m,
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
                .map(|(cond, body)| (cond.clone(), extract_expr(solution, body)))
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
    interner: &Interner,
    customs: &IdVec<CustomTypeId, annot::CustomTypeDef>,
    funcs: &IdVec<CustomFuncId, TailFuncDef>,
    funcs_annot: &mut IdMap<CustomFuncId, annot::FuncDef>,
    scc: Scc<CustomFuncId>,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    func_renderer: &FuncRenderer<CustomFuncId>,
) {
    let instantiated = instantiate_scc(
        strategy,
        interner,
        customs,
        funcs,
        funcs_annot,
        scc,
        type_renderer,
        func_renderer,
    );

    let mut sig_vars = BTreeSet::new();
    for func_id in scc.nodes {
        sig_vars.extend(instantiated.func_args[&func_id].iter_flat().map(|(m, _)| m));
        sig_vars.extend(instantiated.func_rets[&func_id].iter_flat().map(|(m, _)| m));
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
        funcs_annot.insert_vacant(
            *func_id,
            annot::FuncDef {
                purity: func.purity,
                arg_ty: subst_modes(arg_ty, |m| solution.internal_to_external[&m]),
                ret_ty: subst_modes(ret_ty, |m| solution.internal_to_external[&m]),
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strategy {
    Default,
    AlwaysOwned,        // similar to "Perceus"
    OnlyTrivialBorrows, // similar to "Immutable Beans"
}

pub fn annot_modes(
    strategy: Strategy,
    interner: &Interner,
    program: guarded::Program,
    progress: impl ProgressLogger,
) -> annot::Program {
    let type_renderer = CustomTypeRenderer::from_symbols(&program.custom_type_symbols);
    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);

    let customs = parameterize_customs(interner, &program.custom_types);

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
            interner,
            &customs,
            &funcs,
            &mut funcs_annot,
            scc,
            &type_renderer,
            &func_renderer,
        );
        progress.update(scc.nodes.len());
    }

    let funcs = funcs_annot.to_id_vec(funcs.count());

    progress.finish();

    annot::Program {
        mod_symbols: program.mod_symbols,
        custom_types: annot::CustomTypes {
            types: customs,
            sccs: program.custom_types.sccs,
        },
        custom_type_symbols: program.custom_type_symbols,
        funcs,
        func_symbols: program.func_symbols,
        profile_points: program.profile_points,
        main: program.main,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parameterize() {
        let list = anon::Type::Variants(IdVec::from_vec(vec![
            anon::Type::Tuple(vec![]),
            anon::Type::Boxed(Box::new(anon::Type::Custom(CustomTypeId(0)))),
        ]));
        let list_def = guarded::CustomTypeDef {
            content: list,
            scc: CustomTypeSccId(0),
            can_guard: guarded::CanGuard::Yes,
        };
        let sccs = {
            let mut sccs = Sccs::new();
            sccs.push_acyclic_component(CustomTypeId(0));
            sccs
        };
        let customs = guarded::CustomTypes {
            types: IdVec::from_vec(vec![list_def]),
            sccs,
        };
        let interner = Interner::empty();
        let parameterized = parameterize_customs(&interner, &customs);

        assert_eq!(parameterized.len(), 1);
        let annot_list = &parameterized[CustomTypeId(0)];

        let expected_shape = Shape {
            num_slots: 1,
            inner: interner
                .shape
                .new(ShapeInner::Variants(IdVec::from_vec(vec![
                    Shape {
                        num_slots: 0,
                        inner: interner.shape.new(ShapeInner::Tuple(vec![])),
                    },
                    Shape {
                        num_slots: 1,
                        inner: interner.shape.new(ShapeInner::Boxed(Shape {
                            num_slots: 0,
                            inner: interner.shape.new(ShapeInner::SelfCustom(CustomTypeId(0))),
                        })),
                    },
                ]))),
        };
        let expected_pos = vec![Position::Stack];
        assert_eq!(annot_list.content, expected_shape);
        assert_eq!(annot_list.pos, expected_pos);
    }
}
