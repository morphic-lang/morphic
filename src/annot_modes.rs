//! This module implements the specializing variant of first compiler pass described in the borrow
//! inference paper. A signficant proportion of the machinery is dedicated to specialization. The
//! core logic for the pass is contained in `instantiate_expr`.

use crate::cli::RcStrategy;
use crate::data::borrow_model as model;
use crate::data::first_order_ast::{CustomFuncId, CustomTypeId, VariantId};
use crate::data::flat_ast::CustomTypeSccId;
use crate::data::guarded_ast::{self as guard, LocalId};
use crate::data::intrinsics as intr;
use crate::data::metadata::Metadata;
use crate::data::mode_annot_ast::{
    self as annot, HeapModes, Lt, LtParam, Mode, ModeParam, ModeSolution, ModeVar, Occur, Position,
    Res, ResModes, ShapeFo, ShapeInner, SlotId, SubstHelper, TypeFo,
};
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::intrinsic_config::intrinsic_sig;
use crate::pretty_print::utils::{CustomTypeRenderer, FuncRenderer};
use crate::util::collection_ext::VecExt;
use crate::util::inequality_graph2 as in_eq;
use crate::util::iter::IterExt;
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{id_type, Count, Id, IdMap, IdVec};
use id_graph_sccs::{find_components, Scc, SccKind, Sccs};
use std::collections::{BTreeMap, BTreeSet};
use std::iter;

type Interner = annot::Interner<CustomTypeId>;
type UnfoldRecipe = guard::UnfoldRecipe<CustomTypeId>;

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
fn add_tail_call_deps(deps: &mut BTreeSet<CustomFuncId>, vars_in_scope: usize, expr: &guard::Expr) {
    match expr {
        guard::Expr::Call(_purity, id, _arg) => {
            deps.insert(*id);
        }

        guard::Expr::If(_discrim, then_case, else_case) => {
            add_tail_call_deps(deps, vars_in_scope, then_case);
            add_tail_call_deps(deps, vars_in_scope, else_case);
        }

        guard::Expr::LetMany(bindings, final_local) => {
            if let Some(last_i) = last_index(bindings) {
                if *final_local == guard::LocalId(vars_in_scope + last_i) {
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
    arg_ty: guard::Type,
    ret_ty: guard::Type,
    body: TailExpr,
    profile_point: Option<prof::ProfilePointId>,
}

/// A `flat::Expr` where all tail calls are marked.
#[derive(Clone, Debug)]
enum TailExpr {
    Local(LocalId),
    Call(Purity, IsTail, CustomFuncId, LocalId),
    LetMany(Vec<(guard::Type, TailExpr, Metadata)>, LocalId),

    If(LocalId, Box<TailExpr>, Box<TailExpr>),
    CheckVariant(VariantId, LocalId), // Returns a bool
    Unreachable(guard::Type),

    Tuple(Vec<LocalId>),
    TupleField(LocalId, usize),
    WrapVariant(IdVec<VariantId, guard::Type>, VariantId, LocalId),
    UnwrapVariant(IdVec<VariantId, guard::Type>, VariantId, LocalId),
    WrapBoxed(LocalId, guard::Type),
    UnwrapBoxed(LocalId, guard::Type),
    WrapCustom(CustomTypeId, UnfoldRecipe, LocalId),
    UnwrapCustom(CustomTypeId, UnfoldRecipe, LocalId),

    Intrinsic(intr::Intrinsic, LocalId),
    ArrayOp(guard::ArrayOp),
    IoOp(guard::IoOp),
    Panic(guard::Type, LocalId),

    ArrayLit(guard::Type, Vec<LocalId>),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

fn mark_tail_calls(
    tail_candidates: &BTreeSet<CustomFuncId>,
    pos: IsTail,
    vars_in_scope: usize,
    expr: &guard::Expr,
) -> TailExpr {
    match expr {
        guard::Expr::Local(id) => TailExpr::Local(*id),

        guard::Expr::Call(purity, func, arg) => {
            let actual_pos = if pos == IsTail::Tail && tail_candidates.contains(func) {
                IsTail::Tail
            } else {
                IsTail::NotTail
            };
            TailExpr::Call(*purity, actual_pos, *func, *arg)
        }

        guard::Expr::LetMany(bindings, final_local) => TailExpr::LetMany(
            bindings
                .iter()
                .enumerate()
                .map(|(i, (ty, binding, metadata))| {
                    let is_final_binding = i + 1 == bindings.len()
                        && *final_local == guard::LocalId(vars_in_scope + i);

                    let sub_pos = if is_final_binding {
                        pos
                    } else {
                        IsTail::NotTail
                    };

                    (
                        ty.clone(),
                        mark_tail_calls(tail_candidates, sub_pos, vars_in_scope + i, binding),
                        metadata.clone(),
                    )
                })
                .collect(),
            *final_local,
        ),

        guard::Expr::If(discrim, then_case, else_case) => TailExpr::If(
            *discrim,
            Box::new(mark_tail_calls(
                tail_candidates,
                pos,
                vars_in_scope,
                then_case,
            )),
            Box::new(mark_tail_calls(
                tail_candidates,
                pos,
                vars_in_scope,
                else_case,
            )),
        ),
        guard::Expr::CheckVariant(variant_id, variant) => {
            TailExpr::CheckVariant(*variant_id, *variant)
        }
        guard::Expr::Unreachable(ret_ty) => TailExpr::Unreachable(ret_ty.clone()),

        guard::Expr::Tuple(items) => TailExpr::Tuple(items.clone()),
        guard::Expr::TupleField(tuple, idx) => TailExpr::TupleField(*tuple, *idx),
        guard::Expr::WrapVariant(variant_types, variant, content) => {
            TailExpr::WrapVariant(variant_types.clone(), *variant, *content)
        }
        guard::Expr::UnwrapVariant(variant_types, variant, wrapped) => {
            TailExpr::UnwrapVariant(variant_types.clone(), *variant, *wrapped)
        }
        guard::Expr::WrapBoxed(content, content_type) => {
            TailExpr::WrapBoxed(*content, content_type.clone())
        }
        guard::Expr::UnwrapBoxed(content, content_type) => {
            TailExpr::UnwrapBoxed(*content, content_type.clone())
        }
        guard::Expr::WrapCustom(custom, recipe, content) => {
            TailExpr::WrapCustom(*custom, recipe.clone(), *content)
        }
        guard::Expr::UnwrapCustom(custom, recipe, wrapped) => {
            TailExpr::UnwrapCustom(*custom, recipe.clone(), *wrapped)
        }
        guard::Expr::Intrinsic(intr, arg) => TailExpr::Intrinsic(*intr, *arg),
        guard::Expr::ArrayOp(op) => TailExpr::ArrayOp(op.clone()),
        guard::Expr::IoOp(op) => TailExpr::IoOp(*op),
        guard::Expr::Panic(ret_type, message) => TailExpr::Panic(ret_type.clone(), *message),
        guard::Expr::ArrayLit(item_type, items) => {
            TailExpr::ArrayLit(item_type.clone(), items.clone())
        }
        guard::Expr::BoolLit(val) => TailExpr::BoolLit(*val),
        guard::Expr::ByteLit(val) => TailExpr::ByteLit(*val),
        guard::Expr::IntLit(val) => TailExpr::IntLit(*val),
        guard::Expr::FloatLit(val) => TailExpr::FloatLit(*val),
    }
}

fn compute_tail_calls(
    funcs: &IdVec<CustomFuncId, guard::FuncDef>,
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

fn count_num_slots(
    customs: &IdMap<CustomTypeId, annot::CustomTypeDefFo>,
    ty: &guard::Type,
) -> usize {
    match ty {
        guard::Type::Bool => 0,
        guard::Type::Num(_) => 0,
        guard::Type::Tuple(items) => items
            .iter()
            .map(|item| count_num_slots(customs, item))
            .sum(),
        guard::Type::Variants(variants) => variants
            .values()
            .map(|item| count_num_slots(customs, item))
            .sum(),
        guard::Type::Custom(id) => match customs.get(*id) {
            Some(custom) => custom.num_slots,
            // This is a typedef in the same SCC; the reference to it here contributes no additional
            // parameters to the entire SCC.
            None => 0,
        },
        guard::Type::Array(content) => 1 + count_num_slots(customs, content),
        guard::Type::HoleArray(content) => 1 + count_num_slots(customs, content),
        guard::Type::Boxed(content) => 1 + count_num_slots(customs, content),
    }
}

// We separate this out because there is code depends on `access` and `storage` creating in a
// consistent order (see where this is called).
fn next_heap<M: Id>(next_mode: &mut Count<M>) -> HeapModes<M> {
    HeapModes {
        access: next_mode.inc(),
        storage: next_mode.inc(),
    }
}

struct SccParameterizer<'a> {
    interner: &'a Interner,
    customs: &'a guard::CustomTypes,
    parameterized: &'a IdMap<CustomTypeId, annot::CustomTypeDefFo>,
    scc_id: CustomTypeSccId,
    scc_num_slots: usize,
    next_slot: Count<SlotId>,
}

impl<'a> SccParameterizer<'a> {
    fn parameterize_impl(&mut self, ty: &guard::Type, out_res: &mut Vec<SlotId>) -> ShapeFo {
        match ty {
            guard::Type::Bool => ShapeFo {
                inner: self.interner.shape.new(ShapeInner::Bool),
                num_slots: 0,
            },
            guard::Type::Num(num_ty) => ShapeFo {
                inner: self.interner.shape.new(ShapeInner::Num(*num_ty)),
                num_slots: 0,
            },
            guard::Type::Tuple(tys) => {
                let tys = tys.map_refs(|ty| self.parameterize_impl(ty, out_res));
                let num_slots = tys.iter().map(|ty| ty.num_slots).sum();
                ShapeFo {
                    inner: self.interner.shape.new(ShapeInner::Tuple(tys)),
                    num_slots,
                }
            }
            guard::Type::Variants(tys) => {
                let tys = tys.map_refs(|_, ty| self.parameterize_impl(ty, out_res));
                let num_slots = tys.values().map(|ty| ty.num_slots).sum();
                ShapeFo {
                    inner: self.interner.shape.new(ShapeInner::Variants(tys)),
                    num_slots,
                }
            }
            guard::Type::Custom(id) => {
                if self.customs.types[*id].scc == self.scc_id {
                    // This is a typedef in the same SCC, so we need to parameterize it by all the
                    // SCC parameters.
                    let mut next_slot = Count::<SlotId>::new();
                    let slots = iter::repeat_with(move || next_slot.inc());
                    let num_slots = self.scc_num_slots;
                    out_res.extend(slots.take(num_slots));
                    ShapeFo {
                        inner: self.interner.shape.new(ShapeInner::SelfCustom(*id)),
                        num_slots,
                    }
                } else {
                    let num_slots = self.parameterized[*id].num_slots;
                    let slots = iter::repeat_with(|| self.next_slot.inc());
                    out_res.extend(slots.take(num_slots));
                    ShapeFo {
                        inner: self.interner.shape.new(ShapeInner::Custom(*id)),
                        num_slots,
                    }
                }
            }
            guard::Type::Array(ty) => {
                out_res.push(self.next_slot.inc());
                let shape = self.parameterize_impl(ty, out_res);
                ShapeFo {
                    num_slots: 1 + shape.num_slots,
                    inner: self.interner.shape.new(ShapeInner::Array(shape)),
                }
            }
            guard::Type::HoleArray(ty) => {
                out_res.push(self.next_slot.inc());
                let shape = self.parameterize_impl(ty, out_res);
                ShapeFo {
                    num_slots: 1 + shape.num_slots,
                    inner: self.interner.shape.new(ShapeInner::HoleArray(shape)),
                }
            }
            guard::Type::Boxed(ty) => {
                out_res.push(self.next_slot.inc());
                let shape = self.parameterize_impl(ty, out_res);
                ShapeFo {
                    num_slots: 1 + shape.num_slots,
                    inner: self.interner.shape.new(ShapeInner::Boxed(shape)),
                }
            }
        }
    }

    fn parameterize(&mut self, kind: SccKind, ty: &guard::Type) -> (ShapeFo, SubstHelper) {
        let mut res = Vec::new();
        let shape = self.parameterize_impl(ty, &mut res);
        debug_assert_eq!(res.len(), shape.num_slots);
        (shape, SubstHelper::new(kind, res))
    }
}

fn parameterize_custom_scc(
    interner: &Interner,
    customs: &guard::CustomTypes,
    parameterized: &IdMap<CustomTypeId, annot::CustomTypeDefFo>,
    scc: (CustomTypeSccId, Scc<'_, CustomTypeId>),
) -> BTreeMap<CustomTypeId, annot::CustomTypeDefFo> {
    let (scc_id, scc) = scc;

    let scc_num_slots = scc
        .nodes
        .iter()
        .map(|&id| count_num_slots(parameterized, &customs.types[id].content))
        .sum();

    let mut parameterizer = SccParameterizer {
        interner,
        customs,
        parameterized,
        scc_id,
        scc_num_slots,
        // Because each custom in the SCC is parameterized by the total set of modes and lifetimes
        // for the SCC, we use a single counter as we traverse.
        next_slot: Count::new(),
    };

    let result = scc
        .nodes
        .iter()
        .map(|&id| {
            let custom = &customs.types[id];
            let (content, subst_helper) = parameterizer.parameterize(scc.kind, &custom.content);
            (
                id,
                annot::CustomTypeDefFo {
                    content,
                    subst_helper,
                    num_slots: scc_num_slots,
                    scc: custom.scc,
                    can_guard: custom.can_guard,
                },
            )
        })
        .collect();

    debug_assert_eq!(parameterizer.next_slot.to_value(), scc_num_slots);
    result
}

fn parameterize_customs(
    interner: &Interner,
    customs: &guard::CustomTypes,
) -> IdVec<CustomTypeId, annot::CustomTypeDefFo> {
    let mut parameterized = IdMap::new();
    for scc in &customs.sccs {
        let to_populate = parameterize_custom_scc(interner, &customs, &parameterized, scc);
        for (id, typedef) in to_populate {
            parameterized.insert_vacant(id, typedef);
        }
    }
    parameterized.to_id_vec(customs.types.count())
}

fn parameterize_type<'a>(
    interner: &Interner,
    customs: &IdVec<CustomTypeId, annot::CustomTypeDefFo>,
    sccs: &Sccs<CustomTypeSccId, CustomTypeId>,
    ty: &guard::Type,
) -> TypeFo<ModeParam, LtParam> {
    // All the machinery we use here is *very* similar to the machinery above for parameterizing
    // customs, but just different enough that it's hard to merge them.
    let shape = ShapeFo::from_guarded(interner, customs, ty);
    let mut mode_count = Count::new();
    let mut lt_count = Count::new();
    let res = shape.gen_resources(customs, sccs, || mode_count.inc(), || lt_count.inc());
    TypeFo::new(shape, res)
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

fn bind_modes<L1, L2>(
    constrs: &mut ConstrGraph,
    ty1: &TypeFo<ModeVar, L1>,
    ty2: &TypeFo<ModeVar, L2>,
) {
    debug_assert_eq!(ty1.shape(), ty2.shape());
    for (res1, res2) in ty1.iter().zip_eq(ty2.iter()) {
        require_eq(constrs, &res1.modes, &res2.modes);
    }
}

// Unfortunately, we can't quite use `MapRef` as the type of `subst` here because, for the callers
// of this function to be efficient, `subst` must return values (not references).
fn subst_modes<M1: Clone, M2, L: Clone>(
    ty: &TypeFo<M1, L>,
    subst: impl Fn(M1) -> M2,
) -> TypeFo<M2, L> {
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
    TypeFo::new(
        ty.shape().clone(),
        IdVec::from_vec(ty.iter().map(f).collect()),
    )
}

fn emit_occur_constr(
    constrs: &mut ConstrGraph,
    scope: &annot::Path,
    binding_modes: &ResModes<ModeVar>,
    use_modes: &ResModes<ModeVar>,
    use_lt: &Lt,
) {
    // println!("{} <? {}", use_lt.display(), scope.display());
    if use_lt.cmp_path(scope).leq() {
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
    binding_ty: &TypeFo<ModeVar, Lt>,
    use_ty: &TypeFo<ModeVar, Lt>,
) {
    debug_assert_eq!(binding_ty.shape(), use_ty.shape());
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
    ty1: &TypeFo<ModeVar, Lt>,
    ty2: &TypeFo<ModeVar, Lt>,
) -> TypeFo<ModeVar, Lt> {
    debug_assert_eq!(ty1.shape(), ty2.shape());
    let f = |(res1, res2): (&Res<_, Lt>, &Res<_, Lt>)| Res {
        modes: res1.modes.clone(),
        lt: res1.lt.join(interner, &res2.lt),
    };
    TypeFo::new(
        ty1.shape().clone(),
        IdVec::from_vec(ty1.iter().zip_eq(ty2.iter()).map(f).collect()),
    )
}

/// Replaces parameters with fresh variables from the constraint graph.
fn freshen_type<M, L1, L2>(
    constrs: &mut ConstrGraph,
    mut fresh_lt: impl FnMut() -> L2,
    ty: &TypeFo<M, L1>,
) -> TypeFo<ModeVar, L2> {
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
    annot::TypeFo::new(
        ty.shape().clone(),
        IdVec::from_vec(ty.iter().map(f).collect()),
    )
}

fn freshen_type_unused<M, L>(constrs: &mut ConstrGraph, ty: &TypeFo<M, L>) -> TypeFo<ModeVar, Lt> {
    freshen_type(constrs, || Lt::Empty, ty)
}

fn instantiate_occur_in_position(
    _strategy: RcStrategy,
    interner: &Interner,
    pos: IsTail,
    ctx: &mut LocalContext<LocalId, LocalInfo>,
    constrs: &mut ConstrGraph,
    id: LocalId,
    use_ty: &TypeFo<ModeVar, Lt>,
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
    strategy: RcStrategy,
    interner: &Interner,
    ctx: &mut LocalContext<LocalId, LocalInfo>,
    constrs: &mut ConstrGraph,
    id: LocalId,
    use_ty: &TypeFo<ModeVar, Lt>,
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

fn create_occurs_from_model(
    sig: &model::Signature,
    _strategy: RcStrategy,
    interner: &Interner,
    customs: &IdVec<CustomTypeId, annot::CustomTypeDefFo>,
    sccs: &Sccs<CustomTypeSccId, CustomTypeId>,
    constrs: &mut ConstrGraph,
    ctx: &mut LocalContext<LocalId, LocalInfo>,
    path: &annot::Path,
    args: &[LocalId],
    ret: &TypeFo<ModeVar, Lt>,
) -> Vec<annot::Occur<ModeVar, Lt>> {
    assert!(args.len() >= sig.args.fixed.len());

    // Create a fresh occurrence for each function argument.
    let mut arg_occurs = args
        .iter()
        .map(|&id| {
            let ty = freshen_type_unused(constrs, &ctx.local_binding(id).ty);
            annot::Occur { id, ty }
        })
        .collect::<Vec<_>>();

    ///////////////////////////////////////
    // Step 1: Handle constraints which arise from model mode and lifetime variables.
    ///////////////////////////////////////

    // Set up a mapping from model modes to mode variables.
    let get_mode = IdVec::from_count_with(sig.mode_count, |_| constrs.fresh_var());

    let get_modes = |modes| match modes {
        ResModes::Stack(stack) => ResModes::Stack(get_mode[stack]),
        ResModes::Heap(heap) => ResModes::Heap(HeapModes {
            access: get_mode[heap.access],
            storage: get_mode[heap.storage],
        }),
    };

    // Set up a mapping from model lifetimes to lifetimes.
    let mut get_lt = IdVec::from_count_with(sig.lt_count, |_| None);

    // Impose any explicit 'owned' constraints.
    for param in &sig.owned_modes {
        constrs.require_le_const(&Mode::Owned, get_mode[param]);
    }

    for (slot, model_res) in sig.ret.get_res(&ret.shape()) {
        // Impose mode constraints on the return.
        let res = &ret.res()[slot];
        require_eq(constrs, &get_modes(model_res.modes), &res.modes);

        if sig.unused_lts.contains(&model_res.lt) {
            panic!("unused model lifetimes cannot be supplied in return position");
        }

        // Update the lifetime mapping based on the return.
        match &mut get_lt[model_res.lt] {
            entry @ None => *entry = Some(res.lt.clone()),
            Some(_) => {
                panic!("a lifetime variable cannot appear more than once in a model return type");
            }
        }
    }

    let get_lt = get_lt;

    for (i, (arg, occur)) in sig.args.iter().zip(&mut arg_occurs).enumerate() {
        for (slot, model_res) in arg.get_res(&occur.ty.shape()) {
            // Impose mode constraints on the argument.
            let res = &mut occur.ty.res_mut()[slot];
            require_eq(constrs, &get_modes(model_res.modes), &res.modes);

            // Substitute for model lifetimes using the mapping constructed from the return.
            res.lt = if let Some(lt) = &get_lt[model_res.lt] {
                lt.clone()
            } else if sig.unused_lts.contains(&model_res.lt) {
                Lt::Empty
            } else {
                annot::arg_path(path, i, args.len()).as_lt(interner)
            };
        }
    }

    ///////////////////////////////////////
    // Step 2: Handle constraints which arise from repeated uses of the same model type variable.
    ///////////////////////////////////////

    // Accumulate the resources for each occurrence of each type variable.
    let mut vars = IdMap::new();
    for ((i, model), occur) in sig.args.iter().enumerate().zip(&arg_occurs) {
        model.extract_vars(
            |shape, res| TypeFo::new(shape.clone(), IdVec::from_vec(res.to_vec())),
            model::VarOccurKind::Arg(i),
            &occur.ty.shape(),
            occur.ty.res().as_slice(),
            &mut vars,
        );
    }
    sig.ret.extract_vars(
        |shape, res| TypeFo::new(shape.clone(), IdVec::from_vec(res.to_vec())),
        model::VarOccurKind::Ret,
        &ret.shape(),
        ret.res().as_slice(),
        &mut vars,
    );

    // At this point, it would seem natural to convert `vars` from an `IdMap` to an `IdVec`.
    // However, if the model signature has an empty variadic argument, then the `IdMap` will not
    // contain entries for any type variables which appear only in the type of that argument.

    for var_occurs in vars.values_mut() {
        if let Some(rep) = var_occurs.rep() {
            // Impose equality constraints between all occurrences of the same type variable.
            // TODO: Avoid unnecessarily generating reflexive constraints.
            for occur in var_occurs.all() {
                bind_modes(constrs, rep, occur);
            }

            // Propagate lifetimes from return occurrences of variables to argument occurrences of
            // variables.
            for ret in var_occurs.rets.iter() {
                for arg in var_occurs.args.iter_mut() {
                    let loc = arg.loc;
                    let arg_res = &mut arg_occurs[loc.occur_idx].ty.res_mut().as_mut_slice()
                        [loc.start..loc.end];

                    for (arg_res, ret_res) in arg_res.iter_mut().zip_eq(ret.res().values()) {
                        arg_res.lt = arg_res.lt.join(interner, &ret_res.lt);
                    }
                }
            }
        }
    }

    ///////////////////////////////////////
    // Step 3: Handle any explicit constraints (as given in the 'where' clause of the model).
    ///////////////////////////////////////

    for constr in &sig.constrs {
        match constr {
            model::Constr::Mode { lhs, rhs } => {
                // We check when we construct a signature that any type variables that appear in
                // constraints also appear in the signature. This can only happen if there is an
                // empty variadic argument.
                if !vars.contains_key(lhs.type_var) || !vars.contains_key(rhs.type_var) {
                    continue;
                }

                let rep1 = &vars[lhs.type_var].rep().unwrap();
                let rep2 = &vars[rhs.type_var].rep().unwrap();
                debug_assert_eq!(rep1.shape(), rep2.shape());

                let prop1 = lhs.prop;
                let prop2 = rhs.prop;
                let pos = rep1.shape().positions(customs, sccs);

                for (pos, (res1, res2)) in pos.iter().zip_eq(rep1.iter().zip_eq(rep2.iter())) {
                    match pos {
                        Position::Stack => {
                            let mode1 = prop1.extract(&res1.modes);
                            let mode2 = prop2.extract(&res2.modes);
                            constrs.require_eq(mode1, mode2);
                        }
                        Position::Heap => {
                            require_eq(constrs, &res1.modes, &res2.modes);
                        }
                    }
                }
            }
            model::Constr::Lt { lhs, rhs } => {
                // See the comment in the `Constr::Mode` case above.
                if !vars.contains_key(lhs.type_var) || !vars.contains_key(rhs.type_var) {
                    continue;
                }

                let (lhs_vars, rhs_vars) = vars.get_pair_mut(lhs.type_var, rhs.type_var).unwrap();

                for ret in rhs_vars.rets.iter() {
                    for arg in lhs_vars.args.iter_mut() {
                        let loc = arg.loc;
                        let arg_res = &mut arg_occurs[loc.occur_idx].ty.res_mut().as_mut_slice()
                            [loc.start..loc.end];

                        for (arg_res, ret_res) in arg_res.iter_mut().zip_eq(ret.res().values()) {
                            arg_res.lt = arg_res.lt.join(interner, &ret_res.lt);
                        }
                    }
                }
            }
        }
    }

    arg_occurs
}

fn instantiate_model(
    sig: &model::Signature,
    strategy: RcStrategy,
    interner: &Interner,
    customs: &IdVec<CustomTypeId, annot::CustomTypeDefFo>,
    sccs: &Sccs<CustomTypeSccId, CustomTypeId>,
    constrs: &mut ConstrGraph,
    ctx: &mut LocalContext<LocalId, LocalInfo>,
    path: &annot::Path,
    args: &[LocalId],
    ret: &TypeFo<ModeVar, Lt>,
) -> Vec<annot::Occur<ModeVar, Lt>> {
    let occurs = create_occurs_from_model(
        sig, strategy, interner, customs, sccs, constrs, ctx, path, args, ret,
    );

    for occur in &occurs {
        instantiate_occur(strategy, interner, ctx, constrs, occur.id, &occur.ty);
    }

    occurs
}

/// Used during lifetime fixed point iteration. `know_defs` contains the definitions of all
/// functions from previous SCCs. `pending_args` and `pending_rets` contain the signatures of types
/// from the current SCC as of the previous iteration.
#[derive(Clone, Copy, Debug)]
struct SignatureAssumptions<'a> {
    known_defs: &'a IdMap<CustomFuncId, annot::FuncDef>,
    pending_args: &'a BTreeMap<CustomFuncId, TypeFo<ModeVar, Lt>>,
    pending_rets: &'a BTreeMap<CustomFuncId, TypeFo<ModeVar, LtParam>>,
}

impl<'a> SignatureAssumptions<'a> {
    fn sig_of(
        &self,
        constrs: &mut ConstrGraph,
        id: CustomFuncId,
    ) -> (TypeFo<ModeVar, Lt>, TypeFo<ModeVar, LtParam>) {
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
    ty: TypeFo<ModeVar, Lt>,
}

// This function is the core logic for this pass. It implements the judgment from the paper:
// Δ ; Γ ; S ; q ⊢ e : t ⇝ e ; Q ; Γ'
//
// Note that we must return a set of updates rather than mutating Γ because I-Match requires that we
// check all branches in the initial Γ.
fn instantiate_expr(
    strategy: RcStrategy,
    interner: &Interner,
    customs: &IdVec<CustomTypeId, annot::CustomTypeDefFo>,
    sccs: &Sccs<CustomTypeSccId, CustomTypeId>,
    sigs: SignatureAssumptions,
    constrs: &mut ConstrGraph,
    ctx: &mut LocalContext<LocalId, LocalInfo>,
    path: annot::Path,
    fut_ty: &TypeFo<ModeVar, Lt>,
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
            let lt_subst = annot::bind_lts(interner, &ret_ty, fut_ty);
            let arg_ty = annot::prepare_arg_type(interner, &path, &arg_ty);
            let path = path.as_lt(interner);

            // This `join_everywhere` reflects the fact that we assume that functions access all of
            // their arguments. We could be more precise here.
            let arg_ty = annot::join_everywhere(
                interner,
                &annot::subst_lts(interner, &arg_ty, &lt_subst),
                &path,
            );
            let arg = instantiate_occur_in_position(
                strategy, interner, *pos, ctx, constrs, *arg, &arg_ty,
            );

            annot::Expr::Call(*purity, *func, arg)
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

            for (binding_ty, _, _) in bindings {
                let annot_ty = freshen_type_unused(
                    constrs,
                    &parameterize_type(interner, customs, sccs, binding_ty),
                );
                let _ = ctx.add_local(LocalInfo {
                    scope: end_of_scope.clone(),
                    ty: annot_ty,
                });
            }

            let result_occur =
                instantiate_occur(strategy, interner, ctx, constrs, *result_id, fut_ty);

            let mut bindings_annot_rev = Vec::new();
            for (i, (_, binding_expr, metadata)) in bindings.iter().enumerate().rev() {
                let local = LocalId(locals_offset + i);
                let fut_ty = ctx.local_binding(local).ty.clone();

                // Only retain the locals *strictly* before this binding.
                ctx.truncate(Count::from_value(local.0));

                let expr_annot = instantiate_expr(
                    strategy,
                    interner,
                    customs,
                    sccs,
                    sigs,
                    constrs,
                    ctx,
                    path.seq(i),
                    &fut_ty,
                    binding_expr,
                    type_renderer,
                );

                bindings_annot_rev.push((fut_ty, expr_annot, metadata.clone()));
            }

            let bindings_annot = {
                bindings_annot_rev.reverse();
                bindings_annot_rev
            };

            annot::Expr::LetMany(bindings_annot, result_occur)
        }),

        TailExpr::If(discrim, then_expr, else_expr) => {
            // We update `ctx` in place on each iteration despite the fact that the branch arms
            // happen "in parallel". This is fine: only the lifetimes of bindings are updated, these
            // lifetimes are only used for the purpose of generating occurrence constraints, and the
            // relevant lifetime comparisons are unaffected by joining the bindings' lifetimes with
            // parallel arms.
            let else_case = instantiate_expr(
                strategy,
                interner,
                customs,
                sccs,
                sigs,
                constrs,
                ctx,
                path.seq(1).alt(1, 2),
                fut_ty,
                else_expr,
                type_renderer,
            );
            let then_case = instantiate_expr(
                strategy,
                interner,
                customs,
                sccs,
                sigs,
                constrs,
                ctx,
                path.seq(1).alt(0, 2),
                fut_ty,
                then_expr,
                type_renderer,
            );
            let discrim = instantiate_occur(
                strategy,
                interner,
                ctx,
                constrs,
                *discrim,
                &TypeFo::bool_(interner),
            );
            annot::Expr::If(discrim, Box::new(then_case), Box::new(else_case))
        }

        TailExpr::CheckVariant(variant_id, variant) => {
            assert!(fut_ty.shape() == &ShapeFo::bool_(interner));
            let variants_ty = ctx.local_binding(*variant).ty.clone(); // appease the borrow checker
            annot::Expr::CheckVariant(
                *variant_id,
                instantiate_occur(strategy, interner, ctx, constrs, *variant, &variants_ty),
            )
        }

        TailExpr::Unreachable(_) => annot::Expr::Unreachable(fut_ty.clone()),

        TailExpr::Tuple(item_ids) => {
            let fut_item_tys = annot::elim_tuple(fut_ty);
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
            let ShapeInner::Tuple(shapes) = &*tuple_ty.shape().inner else {
                panic!("expected `Tuple` type");
            };

            let (start, end) = annot::nth_res_bounds(shapes, *idx);
            tuple_ty.res_mut().as_mut_slice()[start..end].clone_from_slice(fut_ty.res().as_slice());

            let occur = instantiate_occur(strategy, interner, ctx, constrs, *tuple_id, &tuple_ty);
            annot::Expr::TupleField(occur, *idx)
        }

        TailExpr::WrapVariant(_variant_tys, variant_id, content) => {
            let fut_variant_tys = annot::elim_variants(fut_ty);
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

        TailExpr::UnwrapVariant(_variant_tys, variant_id, wrapped) => {
            let mut variants_ty = freshen_type_unused(constrs, &ctx.local_binding(*wrapped).ty);
            let ShapeInner::Variants(shapes) = &*variants_ty.shape().inner else {
                panic!("expected `Variants` type");
            };

            let (start, end) = annot::nth_res_bounds(shapes.as_slice(), variant_id.to_index());
            variants_ty.res_mut().as_mut_slice()[start..end]
                .clone_from_slice(fut_ty.res().as_slice());

            let occur = instantiate_occur(strategy, interner, ctx, constrs, *wrapped, &variants_ty);
            annot::Expr::UnwrapVariant(*variant_id, occur)
        }

        TailExpr::WrapBoxed(content, _item_ty) => {
            let mut occurs = instantiate_model(
                &*model::box_new,
                strategy,
                interner,
                customs,
                sccs,
                constrs,
                ctx,
                &path,
                &[*content],
                fut_ty,
            );
            annot::Expr::WrapBoxed(occurs.pop().unwrap(), fut_ty.clone())
        }

        TailExpr::UnwrapBoxed(wrapped, _item_ty) => {
            let mut occurs = instantiate_model(
                &*model::box_get,
                strategy,
                interner,
                customs,
                sccs,
                constrs,
                ctx,
                &path,
                &[*wrapped],
                fut_ty,
            );
            annot::Expr::UnwrapBoxed(occurs.pop().unwrap(), fut_ty.clone())
        }

        TailExpr::WrapCustom(custom_id, recipe, unfolded) => {
            let fut_unfolded = annot::unfold(interner, customs, sccs, recipe, fut_ty);
            let occur =
                instantiate_occur(strategy, interner, ctx, constrs, *unfolded, &fut_unfolded);
            annot::Expr::WrapCustom(*custom_id, recipe.clone(), occur)
        }

        TailExpr::UnwrapCustom(custom_id, recipe, folded) => {
            let fresh_folded = {
                let mut lt_count = Count::new();
                freshen_type(constrs, || lt_count.inc(), &ctx.local_binding(*folded).ty)
            };

            let fresh_folded = {
                // Instead of folding `fut_ty`, we unfold a fresh type, duplicating the modes and
                // lifetimes which would be identified under folding into the proper positions.
                // Imposing constraints between this unfolded type and `fut_ty` yields the same
                // constraint system as folding `fut_ty`.
                let fresh_unfolded = annot::unfold(interner, customs, sccs, recipe, &fresh_folded);

                // Equate the modes in `fut_ty` which are identified under folding.
                bind_modes(constrs, &fresh_unfolded, fut_ty);

                // Join the lifetimes in `fut_ty` which are identified under folding.
                let lt_subst = annot::bind_lts(interner, &fresh_unfolded, fut_ty);
                annot::subst_lts(interner, &annot::wrap_lts(&fresh_folded), &lt_subst)
            };

            let occur = instantiate_occur(strategy, interner, ctx, constrs, *folded, &fresh_folded);
            annot::Expr::UnwrapCustom(*custom_id, recipe.clone(), occur)
        }

        // Right now, all intrinsics are trivial from a mode inference perspective because they
        // operate on arithmetic types. If this changes, we will have to update this.
        TailExpr::Intrinsic(intr, arg) => {
            let sig = intrinsic_sig(*intr);
            let ty = TypeFo::new(
                ShapeFo::from_guarded(interner, customs, &guard::Type::from_intr(&sig.arg)),
                IdVec::new(),
            );
            annot::Expr::Intrinsic(*intr, Occur { id: *arg, ty })
        }

        TailExpr::ArrayOp(guard::ArrayOp::Get(_, arr_id, idx_id)) => {
            let occurs = instantiate_model(
                &*model::array_get,
                strategy,
                interner,
                customs,
                sccs,
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

        TailExpr::ArrayOp(guard::ArrayOp::Extract(_item_ty, arr_id, idx_id)) => {
            let occurs = instantiate_model(
                &*model::array_extract,
                strategy,
                interner,
                customs,
                sccs,
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

        TailExpr::ArrayOp(guard::ArrayOp::Len(_item_ty, arr_id)) => {
            let occurs = instantiate_model(
                &*model::array_len,
                strategy,
                interner,
                customs,
                sccs,
                constrs,
                ctx,
                &path,
                &[*arr_id],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::ArrayOp(annot::ArrayOp::Len(occurs.next().unwrap()))
        }

        TailExpr::ArrayOp(guard::ArrayOp::Push(_item_ty, arr_id, item_id)) => {
            let occurs = instantiate_model(
                &*model::array_push,
                strategy,
                interner,
                customs,
                sccs,
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

        TailExpr::ArrayOp(guard::ArrayOp::Pop(_item_ty, arr_id)) => {
            let occurs = instantiate_model(
                &*model::array_pop,
                strategy,
                interner,
                customs,
                sccs,
                constrs,
                ctx,
                &path,
                &[*arr_id],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            annot::Expr::ArrayOp(annot::ArrayOp::Pop(occurs.next().unwrap()))
        }

        TailExpr::ArrayOp(guard::ArrayOp::Replace(_item_ty, hole_id, item_id)) => {
            let occurs = instantiate_model(
                &*model::array_replace,
                strategy,
                interner,
                customs,
                sccs,
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

        TailExpr::ArrayOp(guard::ArrayOp::Reserve(_item_ty, arr_id, cap_id)) => {
            let occurs = instantiate_model(
                &*model::array_reserve,
                strategy,
                interner,
                customs,
                sccs,
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

        TailExpr::IoOp(guard::IoOp::Input) => {
            let _ = instantiate_model(
                &*model::io_input,
                strategy,
                interner,
                customs,
                sccs,
                constrs,
                ctx,
                &path,
                &[],
                fut_ty,
            );
            annot::Expr::IoOp(annot::IoOp::Input)
        }

        TailExpr::IoOp(guard::IoOp::Output(arr_id)) => {
            let occurs = instantiate_model(
                &*model::io_output,
                strategy,
                interner,
                customs,
                sccs,
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
                sccs,
                constrs,
                ctx,
                &path,
                &[*msg_id],
                &TypeFo::unit(interner),
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
                sccs,
                constrs,
                ctx,
                &path,
                item_ids,
                fut_ty,
            );
            let (_, fut_item_ty) = annot::elim_array(fut_ty);
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
    func_args: BTreeMap<CustomFuncId, TypeFo<ModeVar, Lt>>,
    func_rets: BTreeMap<CustomFuncId, TypeFo<ModeVar, LtParam>>,
    func_bodies: BTreeMap<CustomFuncId, annot::Expr<ModeVar, Lt>>,
    scc_constrs: ConstrGraph,
}

fn instantiate_scc(
    strategy: RcStrategy,
    interner: &Interner,
    customs: &IdVec<CustomTypeId, annot::CustomTypeDefFo>,
    sccs: &Sccs<CustomTypeSccId, CustomTypeId>,
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
                            &parameterize_type(interner, customs, sccs, &funcs[id].arg_ty),
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
                            &parameterize_type(interner, customs, sccs, &funcs[id].ret_ty),
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
                    known_defs: funcs_annot,
                    pending_args: &arg_tys,
                    pending_rets: &ret_tys,
                };

                for id in scc.nodes {
                    let func = &funcs[id];
                    let mut ctx = LocalContext::new();

                    let arg_ty = freshen_type_unused(
                        &mut constrs,
                        &parameterize_type(interner, customs, sccs, &func.arg_ty),
                    );
                    let arg_id = ctx.add_local(LocalInfo {
                        scope: annot::ARG_SCOPE(),
                        ty: arg_ty,
                    });
                    debug_assert_eq!(arg_id, guard::ARG_LOCAL);

                    let ret_ty = annot::wrap_lts(&ret_tys[id]);
                    let expr = instantiate_expr(
                        strategy,
                        interner,
                        customs,
                        sccs,
                        assumptions,
                        &mut constrs,
                        &mut ctx,
                        annot::FUNC_BODY_PATH(),
                        &ret_ty,
                        &func.body,
                        type_renderer,
                    );
                    bodies.insert(*id, expr);

                    new_arg_tys.insert(*id, (ctx.local_binding(guard::ARG_LOCAL).ty).clone());
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
                    .all(|(new, old)| annot::lt_equiv(new, old))
                {
                    break (new_arg_tys, bodies);
                }

                arg_tys = new_arg_tys;
            };

            // We could avoid a lot of the work in the "always owned" case, but this is the simplest
            // intervention point
            if strategy == RcStrategy::Perceus {
                for var in constrs.var_count() {
                    constrs.require_le_const(&Mode::Owned, var);
                }
            } else if strategy == RcStrategy::ImmutableBeans {
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

fn extract_type(solution: &Solution, ty: &TypeFo<ModeVar, Lt>) -> TypeFo<ModeSolution, Lt> {
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
        E::LetMany(bindings, result) => E::LetMany(
            bindings
                .iter()
                .map(|(ty, expr, metadata)| {
                    (
                        extract_type(solution, ty),
                        extract_expr(solution, expr),
                        metadata.clone(),
                    )
                })
                .collect(),
            extract_occur(solution, result),
        ),
        E::If(discrim, then_case, else_case) => E::If(
            extract_occur(solution, discrim),
            Box::new(extract_expr(solution, then_case)),
            Box::new(extract_expr(solution, else_case)),
        ),
        E::CheckVariant(variant_id, variant) => {
            E::CheckVariant(*variant_id, extract_occur(solution, variant))
        }
        E::Unreachable(ret_ty) => E::Unreachable(extract_type(solution, ret_ty)),
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
        E::WrapBoxed(content, output_ty) => E::WrapBoxed(
            extract_occur(solution, content),
            extract_type(solution, output_ty),
        ),
        E::UnwrapBoxed(wrapped, output_ty) => E::UnwrapBoxed(
            extract_occur(solution, wrapped),
            extract_type(solution, output_ty),
        ),
        E::WrapCustom(id, recipe, content) => {
            E::WrapCustom(*id, recipe.clone(), extract_occur(solution, content))
        }
        E::UnwrapCustom(id, recipe, wrapped) => {
            E::UnwrapCustom(*id, recipe.clone(), extract_occur(solution, wrapped))
        }
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
    strategy: RcStrategy,
    interner: &Interner,
    customs: &IdVec<CustomTypeId, annot::CustomTypeDefFo>,
    sccs: &Sccs<CustomTypeSccId, CustomTypeId>,
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
        sccs,
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
        TailExpr::If(_, then_case, else_case) => {
            add_func_deps(deps, then_case);
            add_func_deps(deps, else_case);
        }
        TailExpr::LetMany(bindings, _) => {
            for (_, rhs, _) in bindings {
                add_func_deps(deps, rhs);
            }
        }
        _ => {}
    }
}

pub fn annot_modes(
    strategy: RcStrategy,
    interner: &Interner,
    program: guard::Program,
    progress: impl ProgressLogger,
) -> annot::Program {
    let type_renderer = CustomTypeRenderer::from_symbols(&program.custom_type_symbols);
    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);

    let customs = parameterize_customs(interner, &program.custom_types);

    let funcs = compute_tail_calls(&program.funcs);

    let func_sccs: Sccs<usize, _> = find_components(funcs.count(), |id| {
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
            &program.custom_types.sccs,
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
