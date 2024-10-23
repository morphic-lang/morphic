use crate::data::guarded_ast as guard;
use crate::data::metadata::Metadata;
use crate::data::mode_annot_ast2::{
    self as annot, Interner, LocalLt, Lt, Mode, Path, Shape, ShapeInner, SlotId,
};
use crate::data::obligation_annot_ast::{self as ob, StackLt, Type};
use crate::data::rc_annot_ast::{self as rc, Expr, LocalId, RcOp, Selector};
use crate::pretty_print::utils::FuncRenderer;
use crate::util::let_builder::{FromBindings, LetManyBuilder};
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{Count, IdVec};
use once_cell::sync::Lazy;
use std::collections::BTreeMap;

impl FromBindings for Expr {
    type LocalId = LocalId;
    type Type = Type;

    fn from_bindings(bindings: Vec<(Type, Expr, Metadata)>, ret: LocalId) -> Self {
        Expr::LetMany(bindings, ret)
    }
}

type Builder = LetManyBuilder<Expr>;
type Context = LocalContext<guard::LocalId, LocalInfo>;

fn assert_transition_ok(src_mode: Mode, dst_mode: Mode) {
    debug_assert!(
        !(src_mode == Mode::Borrowed && dst_mode == Mode::Owned),
        "borrowed to owned transitions should be prevented by constraint generation"
    );
}

fn should_dup(path: &Path, src_mode: Mode, dst_mode: Mode, lt: &Lt) -> bool {
    assert_transition_ok(src_mode, dst_mode);
    dst_mode == Mode::Owned && !lt.does_not_exceed(path)
}

fn select_dups(path: &Path, src_ty: &Type, dst_ty: &Type, lt_obligation: &StackLt) -> Selector {
    debug_assert_eq!(dst_ty.shape(), &lt_obligation.shape);
    debug_assert_eq!(src_ty.shape(), &lt_obligation.shape);

    let mut result = Selector::none(&lt_obligation.shape);
    for (&slot, lt) in lt_obligation.iter() {
        let src_mode = *src_ty.res()[slot].unwrap_stack();
        let dst_mode = *dst_ty.res()[slot].unwrap_stack();

        if should_dup(path, src_mode, dst_mode, lt) {
            result.insert(slot);
        }
    }
    result
}

fn should_move(path: &Path, src_mode: Mode, dst_mode: Mode, lt: &Lt) -> bool {
    assert_transition_ok(src_mode, dst_mode);
    dst_mode == Mode::Owned && lt.does_not_exceed(path)
}

fn select_moves(path: &Path, src_ty: &Type, dst_ty: &Type, lt_obligation: &StackLt) -> Selector {
    debug_assert_eq!(dst_ty.shape(), &lt_obligation.shape);
    debug_assert_eq!(src_ty.shape(), &lt_obligation.shape);

    let mut result = Selector::none(&lt_obligation.shape);
    for (&slot, lt) in lt_obligation.iter() {
        let src_mode = *src_ty.res()[slot].unwrap_stack();
        let dst_mode = *dst_ty.res()[slot].unwrap_stack();

        if should_move(path, src_mode, dst_mode, lt) {
            result.insert(slot);
        }
    }
    result
}

fn select_owned(customs: &ob::CustomTypes, ty: &Type) -> Selector {
    let mut result = Selector::none(&ty.shape());
    for slot in ty.shape().top_level_slots(customs.view_shapes()) {
        if *ty.res()[slot].unwrap_stack() == Mode::Owned {
            result.insert(slot);
        }
    }
    result
}

fn build_rc_op(
    interner: &Interner,
    op: RcOp,
    slots: Selector,
    target: LocalId,
    builder: &mut Builder,
) {
    if slots.nonempty() {
        builder.add_binding(Type::unit(interner), rc::Expr::RcOp(op, slots, target));
    }
}

type LocalDrops = BTreeMap<guard::LocalId, Selector>;

#[derive(Clone, Debug)]
struct LetManyDrops {
    epilogues: Vec<LocalDrops>,
    sub_drops: Vec<Option<BodyDrops>>,
}

#[derive(Clone, Debug)]
struct IfDrops {
    then_prologue: LocalDrops,
    then_drops: Option<Box<BodyDrops>>,
    else_prologue: LocalDrops,
    else_drops: Option<Box<BodyDrops>>,
}

#[derive(Clone, Debug)]
enum BodyDrops {
    LetMany(LetManyDrops),
    If(IfDrops),
}

/// The points in a function where bindings' obligations end. This represent the set of candidate
/// drop points for the bindings. To make the final decision about whether to drop, we need to
/// compute moves.
#[derive(Clone, Debug)]
struct FuncDrops {
    arg_drops: Selector,
    body_drops: Option<BodyDrops>,
}

fn empty_drops(expr: &ob::Expr) -> Option<BodyDrops> {
    match expr {
        ob::Expr::LetMany(bindings, _) => {
            let epilogues = bindings.iter().map(|_| LocalDrops::new()).collect();
            let sub_drops = bindings
                .iter()
                .map(|(_, _, expr, _)| empty_drops(expr))
                .collect();
            Some(BodyDrops::LetMany(LetManyDrops {
                epilogues,
                sub_drops,
            }))
        }

        ob::Expr::If(_, then_case, else_case) => Some(BodyDrops::If(IfDrops {
            then_prologue: LocalDrops::new(),
            then_drops: empty_drops(then_case).map(Box::new),
            else_prologue: LocalDrops::new(),
            else_drops: empty_drops(else_case).map(Box::new),
        })),

        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[must_use]
enum Registration {
    Handled,
    Unhandled,
}

fn register_let_drops_for_slot(
    drops: &mut LetManyDrops,
    num_locals: Count<guard::LocalId>,
    binding_shape: &Shape,
    binding: guard::LocalId,
    slot: SlotId,
    obligation: &LocalLt,
) {
    let register_to = |drops: &mut LocalDrops| {
        drops
            .entry(binding)
            .and_modify(|selected| selected.insert(slot))
            .or_insert_with(|| Selector::one(binding_shape, slot));
    };

    let LocalLt::Seq(obligation, idx) = obligation else {
        unreachable!();
    };

    if *idx == drops.sub_drops.len() {
        // This slot's obligation ends in the return position of the `LetMany`. We don't
        // need to register any drops. Usually, we defer the final decision about whether to
        // drop until we compute the move status in `annot_expr`, but it is convenient to
        // "short circuit" here.
        return;
    }

    if let Some(sub_drops) = drops.sub_drops[*idx].as_mut() {
        // Since `sub_drops` is `Some`, `obligation` points into an `If` or `LetMany`.
        let num_locals = Count::from_value(num_locals.to_value() + idx);
        match sub_drops {
            BodyDrops::LetMany(sub_drops) => {
                register_let_drops_for_slot(
                    sub_drops,
                    num_locals,
                    binding_shape,
                    binding,
                    slot,
                    obligation,
                );
            }

            BodyDrops::If(sub_drops) => {
                let registration = register_if_drops_for_slot(
                    sub_drops,
                    num_locals,
                    binding_shape,
                    binding,
                    slot,
                    obligation,
                );
                if registration == Registration::Unhandled {
                    register_to(&mut drops.epilogues[*idx]);
                }
            }
        }
    } else {
        // If there are no sub-drops, then the expression that matches up with this path is
        // a "leaf" and either `obligation` is `LtLocal::Final` or obligation consists
        // "ghost" nodes used to track argument order e.g. in a tuple expression.
        register_to(&mut drops.epilogues[*idx]);
    }
}

fn register_if_drops_for_slot(
    drops: &mut IfDrops,
    num_locals: Count<guard::LocalId>,
    binding_shape: &Shape,
    binding: guard::LocalId,
    slot: SlotId,
    obligation: &LocalLt,
) -> Registration {
    let register_to = |drops: &mut LocalDrops| {
        drops
            .entry(binding)
            .and_modify(|selected| selected.insert(slot))
            .or_insert_with(|| Selector::one(binding_shape, slot));
    };

    let (obligation, idx) = match obligation {
        LocalLt::Seq(obligation, idx) => (obligation, idx),
        LocalLt::Alt(_) => unreachable!(),
        LocalLt::Final => {
            // The result of the 'if' expression is unused, so it's obligation (the obligation must
            // be processing) ends immediately. We delegate this drop to the enclosing `LetMany`.
            return Registration::Unhandled;
        }
    };

    match idx {
        0 => {
            panic!(
                "An obligation points to the discriminant of an 'if' expression, but that has type \
                 `Bool` and therefore no slots!"
            )
        }

        1 => {
            // The obligation points inside the 'then' or 'else' branch
            let LocalLt::Alt(obligations) = &**obligation else {
                unreachable!();
            };

            let handle_case = |drops: &mut Option<Box<_>>, prologue, obligation| {
                if let Some(obligation) = obligation {
                    // It's an invariant of the flattening pass (which converts the AST to ANF) that
                    // the child of an 'if' is always a 'let'.
                    let Some(BodyDrops::LetMany(drops)) = drops.as_deref_mut() else {
                        unreachable!();
                    };

                    register_let_drops_for_slot(
                        drops,
                        num_locals,
                        binding_shape,
                        binding,
                        slot,
                        obligation,
                    )
                } else {
                    if num_locals.contains(binding) {
                        // This binding is declared in an enclosing scope and this slot
                        // unused in this branch (but moved along the other branch), so we
                        // drop the slot immediately.
                        register_to(prologue);
                    }
                }
            };

            assert_eq!(obligations.len(), 2);
            handle_case(
                &mut drops.then_drops,
                &mut drops.then_prologue,
                obligations[0].as_deref(),
            );
            handle_case(
                &mut drops.else_drops,
                &mut drops.else_prologue,
                obligations[1].as_deref(),
            );

            Registration::Handled
        }

        _ => unreachable!(),
    }
}

fn register_drops_for_slot(
    drops: &mut BodyDrops,
    binding_shape: &Shape,
    binding: guard::LocalId,
    slot: SlotId,
    obligation: &LocalLt,
) {
    // Every path starts `Seq(0)` since the scope of the function argument is `Seq(1)`
    let LocalLt::Seq(obligation, idx) = obligation else {
        unreachable!()
    };
    debug_assert_eq!(*idx, 0);

    // Every function starts with a 'let'
    let BodyDrops::LetMany(drops) = drops else {
        unreachable!();
    };

    // We must start `num_locals` at 1 to account for the function argument
    register_let_drops_for_slot(
        drops,
        Count::from_value(1),
        binding_shape,
        binding,
        slot,
        obligation,
    );
}

fn register_drops_for_binding(
    interner: &Interner,
    drops: &mut BodyDrops,
    binding_shape: &Shape,
    binding_id: guard::LocalId,
    binding_path: &Path,
    obligation: &StackLt,
) {
    let binding_path = Lazy::new(|| binding_path.as_local_lt(interner));
    for (&slot, lt) in obligation.iter() {
        match lt {
            Lt::Join(_) => panic!("`Join` should not appear in a binding's obligation"),
            Lt::Empty => {
                // The binding is unused, so we can drop it immediately.
                register_drops_for_slot(drops, binding_shape, binding_id, slot, &*binding_path);
            }
            Lt::Local(lt) => {
                register_drops_for_slot(drops, binding_shape, binding_id, slot, lt);
            }
        }
    }
}

fn register_drops_for_expr(
    interner: &Interner,
    drops: &mut BodyDrops,
    mut num_locals: Count<guard::LocalId>,
    path: &Path,
    expr: &ob::Expr,
) {
    match expr {
        ob::Expr::LetMany(bindings, _) => {
            for (i, (ty, obligation, sub_expr, _)) in bindings.iter().enumerate() {
                let path = path.seq(i);
                register_drops_for_expr(interner, drops, num_locals, &path, sub_expr);

                // Only increment `num_locals` after recursing into `sub_expr`.
                let binding_id = num_locals.inc();

                register_drops_for_binding(
                    interner,
                    drops,
                    &ty.shape(),
                    binding_id,
                    &path,
                    obligation,
                );
            }
        }

        ob::Expr::If(_, then_case, else_case) => {
            register_drops_for_expr(
                interner,
                drops,
                num_locals,
                &path.seq(1).alt(0, 2),
                then_case,
            );
            register_drops_for_expr(
                interner,
                drops,
                num_locals,
                &path.seq(1).alt(1, 2),
                else_case,
            );
        }

        _ => {}
    }
}

fn drops_for_func(interner: &Interner, func: &ob::FuncDef) -> FuncDrops {
    let mut arg_drops = Selector::none(&func.arg_ty.shape());
    let mut body_drops = empty_drops(&func.body);

    for (&slot, lt) in func.arg_obligation.iter() {
        match lt {
            Lt::Join(_) => panic!("`Join` should not appear in a binding's obligation"),
            Lt::Empty => {
                arg_drops.insert(slot);
            }
            Lt::Local(lt) => {
                let body_drops = body_drops.as_mut().unwrap();
                register_drops_for_slot(
                    body_drops,
                    &func.arg_ty.shape(),
                    guard::ARG_LOCAL,
                    slot,
                    lt,
                );
            }
        }
    }

    // We must start `num_locals` at 1 to account for the function argument.
    register_drops_for_expr(
        interner,
        body_drops.as_mut().unwrap(),
        Count::from_value(1),
        &annot::FUNC_BODY_PATH(),
        &func.body,
    );

    FuncDrops {
        arg_drops,
        body_drops,
    }
}

#[derive(Clone, Debug)]
struct LocalInfo {
    new_id: LocalId,
    ty: Type,
    obligation: StackLt,
}

#[derive(Clone, Debug)]
struct Moves(BTreeMap<guard::LocalId, Selector>);

impl Moves {
    fn empty() -> Self {
        Moves(BTreeMap::new())
    }

    fn new(local: guard::LocalId, slots: Selector) -> Self {
        let mut map = BTreeMap::new();
        map.insert(local, slots);
        Moves(map)
    }

    fn merge(&mut self, other: Moves) {
        for (binding, slots) in other.0 {
            if let Some(existing) = self.0.get_mut(&binding) {
                *existing = &*existing | &slots;
            } else {
                self.0.insert(binding, slots);
            }
        }
    }

    fn merge_with_scope(&mut self, scope: Count<guard::LocalId>, other: Moves) {
        for (binding, slots) in other.0 {
            if binding.0 < scope.to_value() {
                if let Some(existing) = self.0.get_mut(&binding) {
                    *existing = &*existing | &slots;
                } else {
                    self.0.insert(binding, slots);
                }
            }
        }
    }
}

fn annot_occur(
    interner: &Interner,
    _customs: &ob::CustomTypes,
    ctx: &mut Context,
    path: &Path,
    occur: ob::Occur,
    builder: &mut Builder,
) -> (LocalId, Moves) {
    let binding = ctx.local_binding_mut(occur.id);

    let dups = select_dups(path, &binding.ty, &occur.ty, &binding.obligation);
    build_rc_op(interner, RcOp::Retain, dups, binding.new_id, builder);

    let moves = select_moves(path, &binding.ty, &occur.ty, &binding.obligation);
    (binding.new_id, Moves::new(occur.id, moves))
}

fn unwrap_item(ty: &Type) -> Type {
    let item = match &*ty.shape().inner {
        ShapeInner::Array(item) => item,
        ShapeInner::HoleArray(item) => item,
        ShapeInner::Boxed(item) => item,
        _ => panic!("expected array, hole array, or boxed type"),
    };
    Type::new(
        item.clone(),
        IdVec::from_vec(ty.res().as_slice()[1..].iter().cloned().collect()),
    )
}

fn annot_expr(
    interner: &Interner,
    customs: &ob::CustomTypes,
    ctx: &mut Context,
    path: &Path,
    expr: ob::Expr,
    ret_ty: &Type,
    metadata: Metadata,
    drops: Option<&BodyDrops>,
    builder: &mut Builder,
) -> (rc::LocalId, Moves) {
    let (new_expr, moves) = match expr {
        ob::Expr::Local(local) => {
            let (new_local, moves) = annot_occur(interner, customs, ctx, path, local, builder);
            (rc::Expr::Local(new_local), moves)
        }

        ob::Expr::Call(purity, func_id, arg) => {
            let (new_arg, moves) = annot_occur(interner, customs, ctx, path, arg, builder);
            (rc::Expr::Call(purity, func_id, new_arg), moves)
        }

        ob::Expr::LetMany(bindings, ret) => {
            let BodyDrops::LetMany(LetManyDrops {
                epilogues,
                sub_drops,
            }) = drops.as_ref().unwrap()
            else {
                unreachable!();
            };

            let num_enclosing_vars = ctx.count();
            let mut moves = Moves::empty();

            let final_local = ctx.with_scope(|ctx| {
                for (i, (ty, obligation, body, metadata)) in bindings.into_iter().enumerate() {
                    let (final_local, rhs_moves) = annot_expr(
                        interner,
                        customs,
                        ctx,
                        &path.seq(i),
                        body,
                        &ty,
                        metadata,
                        sub_drops[i].as_ref(),
                        builder,
                    );

                    ctx.add_local(LocalInfo {
                        new_id: final_local,
                        ty,
                        obligation,
                    });

                    for (old_id, candidate_drops) in &epilogues[i] {
                        // It suffices to just use `rhs_moves` here because if the move were
                        // earlier, the obligation would have ended earlier, and there would be no
                        // candidate drop here.
                        let drops = if let Some(rhs_moves) = rhs_moves.0.get(old_id) {
                            candidate_drops - rhs_moves
                        } else {
                            candidate_drops.clone()
                        };
                        build_rc_op(
                            interner,
                            RcOp::Release,
                            drops,
                            ctx.local_binding(*old_id).new_id,
                            builder,
                        );
                    }

                    moves.merge_with_scope(num_enclosing_vars, rhs_moves);
                }

                ctx.local_binding(ret.id).new_id
            });

            // Note: Early return! We circumvent the usual return flow because we don't actually
            // want to create an expression directly corresponding to this 'let' block. The 'let'
            // block's bindings just get absorbed into the ambient `builder`.
            return (final_local, moves);
        }

        ob::Expr::If(discrim, then_case, else_case) => {
            let BodyDrops::If(IfDrops {
                then_prologue,
                then_drops,
                else_prologue,
                else_drops,
            }) = drops.as_ref().unwrap()
            else {
                unreachable!();
            };

            let mut handle_case = |prologue: &LocalDrops, sub_drops, case, path| {
                let mut case_builder = builder.child();

                for (binding_id, drops) in prologue {
                    build_rc_op(
                        interner,
                        RcOp::Release,
                        // Every candidate drop in the prologue is an actual drop. If the binding
                        // were moved along this branch, it would have a non-trivial obligation
                        // along this branch, and it's candidate drop would end up somewhere else.
                        drops.clone(),
                        ctx.local_binding(*binding_id).new_id,
                        &mut case_builder,
                    );
                }

                let (final_local, moves) = annot_expr(
                    interner,
                    customs,
                    ctx,
                    &path,
                    case,
                    ret_ty,
                    Metadata::default(),
                    sub_drops,
                    &mut case_builder,
                );

                (case_builder.to_expr(final_local), moves)
            };

            let (then_case, then_moves) = handle_case(
                then_prologue,
                then_drops.as_deref(),
                *then_case,
                path.seq(1).alt(0, 2),
            );
            let (else_case, else_moves) = handle_case(
                else_prologue,
                else_drops.as_deref(),
                *else_case,
                path.seq(1).alt(1, 2),
            );

            let (new_discrim, discrim_moves) =
                annot_occur(interner, customs, ctx, path, discrim, builder);

            let mut moves = then_moves;
            moves.merge(else_moves);
            moves.merge(discrim_moves);

            (
                rc::Expr::If(new_discrim, Box::new(then_case), Box::new(else_case)),
                moves,
            )
        }

        ob::Expr::CheckVariant(variant_id, variant) => {
            let (new_variant, moves) = annot_occur(interner, customs, ctx, path, variant, builder);
            (rc::Expr::CheckVariant(variant_id, new_variant), moves)
        }

        ob::Expr::Unreachable(ret_ty) => (rc::Expr::Unreachable(ret_ty), Moves::empty()),

        ob::Expr::Tuple(fields) => {
            let (new_fields, moves): (Vec<_>, Vec<_>) = fields
                .into_iter()
                .enumerate()
                .map(|(i, field)| annot_occur(interner, customs, ctx, &path.seq(i), field, builder))
                .unzip();
            let moves = moves.into_iter().fold(Moves::empty(), |mut acc, m| {
                acc.merge(m);
                acc
            });
            (rc::Expr::Tuple(new_fields), moves)
        }

        ob::Expr::TupleField(tuple, idx) => {
            let (new_tuple, moves) = annot_occur(interner, customs, ctx, path, tuple, builder);
            (rc::Expr::TupleField(new_tuple, idx), moves)
        }
        ob::Expr::WrapVariant(variants, variant_id, content) => {
            let (new_content, moves) = annot_occur(interner, customs, ctx, path, content, builder);
            (
                rc::Expr::WrapVariant(variants, variant_id, new_content),
                moves,
            )
        }

        ob::Expr::UnwrapVariant(variant_id, wrapped) => {
            let (new_wrapped, moves) = annot_occur(interner, customs, ctx, path, wrapped, builder);
            (rc::Expr::UnwrapVariant(variant_id, new_wrapped), moves)
        }

        ob::Expr::WrapBoxed(content, item_ty) => {
            let (new_content, moves) = annot_occur(interner, customs, ctx, path, content, builder);
            (rc::Expr::WrapBoxed(new_content, item_ty), moves)
        }

        ob::Expr::UnwrapBoxed(wrapped, item_ty) => {
            let (new_wrapped, moves) = annot_occur(interner, customs, ctx, path, wrapped, builder);
            (rc::Expr::UnwrapBoxed(new_wrapped, item_ty), moves)
        }

        ob::Expr::WrapCustom(id, content) => {
            let (new_content, moves) = annot_occur(interner, customs, ctx, path, content, builder);
            (rc::Expr::WrapCustom(id, new_content), moves)
        }

        ob::Expr::UnwrapCustom(id, wrapped) => {
            let (new_wrapped, moves) = annot_occur(interner, customs, ctx, path, wrapped, builder);
            (rc::Expr::UnwrapCustom(id, new_wrapped), moves)
        }

        ob::Expr::Intrinsic(intr, arg) => {
            let (new_arg, moves) = annot_occur(interner, customs, ctx, path, arg, builder);
            (rc::Expr::Intrinsic(intr, new_arg), moves)
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Get(arr, idx, ret_ty)) => {
            let item_retains = select_owned(customs, &ret_ty);

            let arr_ty = arr.ty.clone();
            let (new_arr, moves1) = annot_occur(interner, customs, ctx, path, arr, builder);
            let (new_idx, moves2) = annot_occur(interner, customs, ctx, path, idx, builder);

            let mut moves = moves1;
            moves.merge(moves2);

            let get_op = rc::Expr::ArrayOp(rc::ArrayOp::Get(arr_ty, new_arr, new_idx));
            let get_id = builder.add_binding(ret_ty, get_op);

            build_rc_op(interner, RcOp::Retain, item_retains, get_id, builder);
            return (get_id, moves);
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Extract(arr, idx)) => {
            let arr_ty = arr.ty.clone();
            let (new_arr, moves1) = annot_occur(interner, customs, ctx, path, arr, builder);
            let (new_idx, moves2) = annot_occur(interner, customs, ctx, path, idx, builder);

            let mut moves = moves1;
            moves.merge(moves2);

            (
                rc::Expr::ArrayOp(rc::ArrayOp::Extract(arr_ty, new_arr, new_idx)),
                moves,
            )
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Len(arr)) => {
            let arr_ty = arr.ty.clone();
            let (new_arr, moves) = annot_occur(interner, customs, ctx, path, arr, builder);

            (rc::Expr::ArrayOp(rc::ArrayOp::Len(arr_ty, new_arr)), moves)
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Push(arr, item)) => {
            let arr_ty = arr.ty.clone();
            let (new_arr, moves1) = annot_occur(interner, customs, ctx, path, arr, builder);
            let (new_item, moves2) = annot_occur(interner, customs, ctx, path, item, builder);

            let mut moves = moves1;
            moves.merge(moves2);

            (
                rc::Expr::ArrayOp(rc::ArrayOp::Push(arr_ty, new_arr, new_item)),
                moves,
            )
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Pop(arr)) => {
            let arr_ty = arr.ty.clone();
            let (new_arr, moves) = annot_occur(interner, customs, ctx, path, arr, builder);

            (rc::Expr::ArrayOp(rc::ArrayOp::Pop(arr_ty, new_arr)), moves)
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Replace(arr, item)) => {
            let arr_ty = arr.ty.clone();
            let (new_arr, moves1) = annot_occur(interner, customs, ctx, path, arr, builder);
            let (new_item, moves2) = annot_occur(interner, customs, ctx, path, item, builder);

            let mut moves = moves1;
            moves.merge(moves2);

            (
                rc::Expr::ArrayOp(rc::ArrayOp::Replace(arr_ty, new_arr, new_item)),
                moves,
            )
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Reserve(arr, cap)) => {
            let arr_ty = arr.ty.clone();
            let (new_arr, moves1) = annot_occur(interner, customs, ctx, path, arr, builder);
            let (new_cap, moves2) = annot_occur(interner, customs, ctx, path, cap, builder);

            let mut moves = moves1;
            moves.merge(moves2);

            (
                rc::Expr::ArrayOp(rc::ArrayOp::Reserve(arr_ty, new_arr, new_cap)),
                moves,
            )
        }

        ob::Expr::IoOp(ob::IoOp::Input) => (rc::Expr::IoOp(rc::IoOp::Input), Moves::empty()),

        ob::Expr::IoOp(ob::IoOp::Output(val)) => {
            let (new_val, moves) = annot_occur(interner, customs, ctx, path, val, builder);
            (rc::Expr::IoOp(rc::IoOp::Output(new_val)), moves)
        }

        ob::Expr::Panic(ret_ty, msg) => {
            let (new_msg, moves) = annot_occur(interner, customs, ctx, path, msg, builder);
            (rc::Expr::Panic(ret_ty, new_msg), moves)
        }

        ob::Expr::ArrayLit(item_ty, items) => {
            let (new_items, moves): (Vec<_>, Vec<_>) = items
                .into_iter()
                .enumerate()
                .map(|(i, item)| annot_occur(interner, customs, ctx, &path.seq(i), item, builder))
                .unzip();

            let moves = moves.into_iter().fold(Moves::empty(), |mut acc, m| {
                acc.merge(m);
                acc
            });

            (rc::Expr::ArrayLit(item_ty, new_items), moves)
        }

        ob::Expr::BoolLit(lit) => (rc::Expr::BoolLit(lit), Moves::empty()),

        ob::Expr::ByteLit(lit) => (rc::Expr::ByteLit(lit), Moves::empty()),

        ob::Expr::IntLit(lit) => (rc::Expr::IntLit(lit), Moves::empty()),

        ob::Expr::FloatLit(lit) => (rc::Expr::FloatLit(lit), Moves::empty()),
    };

    (
        builder.add_binding_with_metadata(ret_ty.clone(), new_expr, metadata),
        moves,
    )
}

fn annot_func(
    interner: &Interner,
    _func_renderer: &FuncRenderer<ob::CustomFuncId>,
    customs: &ob::CustomTypes,
    _func_id: ob::CustomFuncId,
    func: ob::FuncDef,
) -> rc::FuncDef {
    let drops = drops_for_func(interner, &func);

    let mut ctx = Context::new();
    ctx.add_local(LocalInfo {
        new_id: rc::ARG_LOCAL,
        ty: func.arg_ty.clone(),
        obligation: func.arg_obligation,
    });

    let mut builder = Builder::new(Count::from_value(1));
    build_rc_op(
        interner,
        RcOp::Release,
        drops.arg_drops,
        rc::ARG_LOCAL,
        &mut builder,
    );

    let (ret_local, _) = annot_expr(
        interner,
        customs,
        &mut ctx,
        &annot::FUNC_BODY_PATH(),
        func.body,
        &func.ret_ty,
        Metadata::default(),
        drops.body_drops.as_ref(),
        &mut builder,
    );

    let body = builder.to_expr(ret_local);
    rc::FuncDef {
        purity: func.purity,
        arg_ty: func.arg_ty,
        ret_ty: func.ret_ty,
        body: body,
        profile_point: func.profile_point,
    }
}

pub fn annot_rcs(
    interner: &Interner,
    program: ob::Program,
    progress: impl ProgressLogger,
) -> rc::Program {
    let mut progress = progress.start_session(Some(program.funcs.len()));

    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);
    let funcs = IdVec::from_vec(
        program
            .funcs
            .into_iter()
            .map(|(func_id, func)| {
                let annot = annot_func(
                    interner,
                    &func_renderer,
                    &program.custom_types,
                    func_id,
                    func,
                );
                progress.update(1);
                annot
            })
            .collect(),
    );

    progress.finish();

    let custom_types = rc::CustomTypes {
        types: program.custom_types.types,
    };
    rc::Program {
        mod_symbols: program.mod_symbols,
        custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs,
        func_symbols: program.func_symbols,
        profile_points: program.profile_points,
        main: program.main,
    }
}
