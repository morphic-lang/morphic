use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mode_annot_ast2::{
    self as annot, CollectOverlay, LocalLt, Lt, Mode, Overlay, Path, SlotId,
};
use crate::data::obligation_annot_ast::{self as ob, StackLt};
use crate::data::rc_annot_ast::{self as rc, Expr, LocalId, RcOp, Selector};
use crate::pretty_print::borrow_common::{write_lifetime, write_path};
use crate::pretty_print::obligation_annot::{self, write_type};
use crate::util::iter::IterExt;
use crate::util::let_builder::{FromBindings, LetManyBuilder};
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{Count, IdVec};
use once_cell::sync::Lazy;
use std::collections::BTreeMap;
use std::iter;

fn assert_transition_ok(src_mode: Mode, dst_mode: Mode) {
    debug_assert!(
        !(src_mode == Mode::Borrowed && dst_mode == Mode::Owned),
        "borrowed to owned transitions should be prevented by constraint generation"
    );
}

fn should_dup(path: &Path, src_mode: Mode, dst_mode: Mode, lt: &Lt) -> bool {
    print!("should_dup: ");
    write_path(&mut std::io::stdout(), path).unwrap();
    print!("    ");
    write_lifetime(&mut std::io::stdout(), lt).unwrap();
    println!();
    assert_transition_ok(src_mode, dst_mode);
    dst_mode == Mode::Owned && !lt.does_not_exceed(path)
}

fn select_dups(
    customs: &ob::CustomTypes,
    path: &Path,
    src_ty: &ob::Type,
    dst_ty: &ob::Type,
    lt_obligation: &StackLt,
) -> Selector {
    write_type(
        &mut std::io::stdout(),
        None,
        &|w, mode| write!(w, "{mode}"),
        src_ty,
    )
    .unwrap();
    println!();
    write_type(
        &mut std::io::stdout(),
        None,
        &|w, mode| write!(w, "{mode}"),
        dst_ty,
    )
    .unwrap();
    println!();
    src_ty
        .iter_stack(customs.view_types())
        .zip_eq(dst_ty.iter_stack(customs.view_types()))
        .zip_eq(lt_obligation.iter())
        .map(|((src_mode, dst_mode), lt)| should_dup(path, *src_mode, *dst_mode, lt))
        .collect_overlay(lt_obligation)
}

fn should_move(path: &Path, src_mode: Mode, dst_mode: Mode, lt: &Lt) -> bool {
    assert_transition_ok(src_mode, dst_mode);
    dst_mode == Mode::Owned && lt.does_not_exceed(path)
}

fn select_moves(
    customs: &ob::CustomTypes,
    path: &Path,
    src_ty: &ob::Type,
    dst_ty: &ob::Type,
    lt_obligation: &StackLt,
) -> Selector {
    src_ty
        .iter_stack(customs.view_types())
        .zip_eq(dst_ty.iter_stack(customs.view_types()))
        .zip_eq(lt_obligation.iter())
        .map(|((src_mode, dst_mode), lt)| should_move(path, *src_mode, *dst_mode, lt))
        .collect_overlay(lt_obligation)
}

fn select_owned(customs: &ob::CustomTypes, ty: &ob::Type) -> Selector {
    ty.iter_stack(customs.view_types())
        .map(|&mode| mode == Mode::Owned)
        .collect_overlay(&ty.unapply_overlay())
}

#[derive(Clone, Debug)]
enum Field<T> {
    TupleField(usize),
    VariantCase(first_ord::VariantId),
    Custom(first_ord::CustomTypeId, SlotId, T),
    Slot(T),
}

/// Identifies a "slot" e.g. an array or box.
type SlotPath<T> = im_rc::Vector<Field<T>>;

fn get_slot_data<T: Clone>(path: &SlotPath<T>) -> T {
    match path.last().expect("expected non-empty slot path") {
        Field::Custom(_, _, data) | Field::Slot(data) => data.clone(),
        _ => panic!("invalid slot path: should end in custom or slot field"),
    }
}

fn set_selector_slot<T: Clone>(sel: &mut Selector, path: &SlotPath<T>) {
    let mut cursor = sel;
    for elem in path.iter() {
        match elem {
            Field::TupleField(i) => {
                let Overlay::Tuple(fields) = cursor else {
                    panic!("field path does not match selector");
                };
                cursor = &mut fields[*i];
            }
            Field::VariantCase(i) => {
                let Overlay::Variants(variants) = cursor else {
                    panic!("field path does not match selector");
                };
                cursor = &mut variants[*i];
            }
            Field::Custom(id, i, _) => {
                let Overlay::Custom(other_id, subst) = cursor else {
                    panic!("field path does not match selector");
                };
                debug_assert_eq!(id, other_id);
                subst.insert(*i, true);
            }
            Field::Slot(_) => match cursor {
                Overlay::Array(status) | Overlay::HoleArray(status) | Overlay::Boxed(status) => {
                    *status = true;
                }
                _ => panic!("field path does not match selector"),
            },
        }
    }
}

fn iterate_slots<'a, T>(ov: &'a Overlay<T>) -> Box<dyn Iterator<Item = SlotPath<&'a T>> + 'a> {
    fn iterate_slots_impl<'a, T>(
        root: SlotPath<&'a T>,
        ov: &'a Overlay<T>,
    ) -> Box<dyn Iterator<Item = SlotPath<&'a T>> + 'a> {
        match ov {
            Overlay::Bool => Box::new(iter::empty()),
            Overlay::Num(_) => Box::new(iter::empty()),
            Overlay::Tuple(fields) => {
                Box::new(fields.iter().enumerate().flat_map(move |(idx, lt)| {
                    let mut new_root = root.clone();
                    new_root.push_back(Field::TupleField(idx));
                    iterate_slots_impl(new_root, lt)
                }))
            }
            Overlay::Variants(variants) => {
                Box::new(variants.iter().flat_map(move |(variant_id, lt)| {
                    let mut new_root = root.clone();
                    new_root.push_back(Field::VariantCase(variant_id));
                    iterate_slots_impl(new_root, lt)
                }))
            }
            Overlay::SelfCustom(_) => Box::new(iter::empty()),
            Overlay::Custom(id, subst) => Box::new(subst.iter().map(move |(slot, x)| {
                let mut leaf = root.clone();
                leaf.push_back(Field::Custom(*id, *slot, x));
                leaf
            })),
            Overlay::Array(x) | Overlay::HoleArray(x) | Overlay::Boxed(x) => {
                Box::new(iter::once({
                    let mut leaf = root.clone();
                    leaf.push_back(Field::Slot(x));
                    leaf
                }))
            }
        }
    }
    iterate_slots_impl(im_rc::Vector::new(), ov)
}

impl FromBindings for Expr {
    type LocalId = LocalId;
    type Binding = (rc::Type, Expr);

    fn from_bindings(bindings: Vec<Self::Binding>, ret: LocalId) -> Self {
        Expr::LetMany(bindings, ret)
    }
}

fn build_rc_op(op: RcOp, slots: Selector, target: LocalId, builder: &mut LetManyBuilder<Expr>) {
    if slots.iter().any(|x| *x) {
        builder.add_binding((rc::Type::Tuple(vec![]), rc::Expr::RcOp(op, slots, target)));
    }
}

type LocalDrops = BTreeMap<flat::LocalId, Selector>;

#[derive(Clone, Debug)]
enum BodyDrops {
    Branch {
        prologues: Vec<LocalDrops>,
        sub_drops: Vec<Option<BodyDrops>>,
    },
    LetMany {
        epilogues: Vec<LocalDrops>,
        sub_drops: Vec<Option<BodyDrops>>,
    },
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
        ob::Expr::Branch(_, arms, _) => {
            let prologues = arms.iter().map(|_| LocalDrops::new()).collect();
            let sub_drops = arms.iter().map(|(_, expr)| empty_drops(expr)).collect();
            Some(BodyDrops::Branch {
                prologues,
                sub_drops,
            })
        }

        ob::Expr::LetMany(bindings, _) => {
            let epilogues = bindings.iter().map(|_| LocalDrops::new()).collect();
            let sub_drops = bindings
                .iter()
                .map(|(_, _, expr)| empty_drops(expr))
                .collect();
            Some(BodyDrops::LetMany {
                epilogues,
                sub_drops,
            })
        }

        _ => None,
    }
}

// TODO: using `Selector`s here (as we've currently defined them) is quite inefficient. We
// should use a data structure which can *sparsely* represent a subset of fields.
fn register_drops_for_slot_rec(
    drops: &mut BodyDrops,
    num_locals: Count<flat::LocalId>,
    binding: flat::LocalId,
    slot: &Selector,
    obligation: &LocalLt,
) {
    let register_to = |drops: &mut LocalDrops| {
        drops
            .entry(binding)
            .and_modify(|old_slots| *old_slots = &*old_slots | slot)
            .or_insert_with(|| slot.clone());
    };

    match drops {
        BodyDrops::LetMany {
            epilogues,
            sub_drops,
        } => {
            let LocalLt::Seq(obligation, idx) = obligation else {
                unreachable!();
            };

            if *idx == sub_drops.len() {
                // This slot's obligation ends in the return position of a `LetMany`. We don't need
                // to register any drops. Usually, we defer the final decision about whether to drop
                // until we've compute the move status in `annot_expr`, but it is convenient to
                // "short circuit" here.
                return;
            }

            if let Some(drops) = sub_drops[*idx].as_mut() {
                // Since `sub_drops` is `Some`, the obligation points into a `Branch` or `LetMany`.
                let num_locals = Count::from_value(num_locals.to_value() + idx);
                register_drops_for_slot_rec(drops, num_locals, binding, slot, obligation);
            } else {
                // If there are no sub-drops, then the expression that matches up with this path is
                // a "leaf" and either `obligation` is `LtLocal::Final` or obligation consists
                // "ghost" nodes used to track argument order e.g. in a tuple expression
                register_to(&mut epilogues[*idx]);
            }
        },
        BodyDrops::Branch {
            prologues,
            sub_drops,
        } => {
            let LocalLt::Seq(obligation, idx) = obligation else {
                unreachable!();
            };

            if *idx == 0 {
                // The obligation points to the discriminant of a `Branch`.
                assert_eq!(**obligation, LocalLt::Final);
                for prologue in prologues.iter_mut() {
                    register_to(prologue);
                }
            } else {
                // The obligation points inside a `Branch` arm.
                assert_eq!(*idx, 1);
                let LocalLt::Alt(obligations) = &**obligation else {
                    unreachable!();
                };

                for (idx, obligation) in obligations.iter().enumerate() {
                    if let Some(obligation) = obligation {
                        let drops = sub_drops[idx].as_mut().unwrap();
                        register_drops_for_slot_rec(drops, num_locals, binding, slot, obligation);
                    } else {
                        if num_locals.contains(binding) {
                            // This binding is declared in an enclosing scope and this slot unused
                            // in this branch (but moved along some other branch), so we drop the
                            // slot immediately.
                            register_to(&mut prologues[idx]);
                        }
                    }
                }
            }
        }
    }

    /*
    match obligation {
        LocalLt::Final => unreachable!(),

        LocalLt::Seq(obligation, idx) => {
            let BodyDrops::LetMany {
                epilogues,
                sub_drops,
            } = drops
            else {
                unreachable!()
            };

            if *idx == sub_drops.len() {
                // This slot's obligation ends in the return position of a `LetMany`. We don't need
                // to register any drops. Usually, we defer the final decision about whether to drop
                // until we've compute the move status in `annot_expr`, but it is convenient to
                // "short circuit" here.
                return;
            }

            if let Some(drops) = sub_drops[*idx].as_mut() {
                // Since `sub_drops` is `Some`, the obligation points into a `Branch` or `LetMany`.
                if let BodyDrops::Branch { prologues, .. } = drops {
                    let LocalLt::Seq(obligation, idx) = &**obligation else {
                        unreachable!();
                    };
                    if *idx == 0 {
                        // The obligation points to the discriminant of a `Branch`.
                        for prologue in prologues.iter_mut() {
                            register_to(prologue);
                        }
                    } else {
                        // The obligation points inside a `Branch` arm.
                        assert_eq!(*idx, 1);
                        register_drops_for_slot_rec(drops, num_locals, binding, slot, obligation);
                    }
                } else {
                    let num_locals = Count::from_value(num_locals.to_value() + idx);
                    register_drops_for_slot_rec(drops, num_locals, binding, slot, obligation);
                }
            } else {
                // If there are no sub-drops, then the expression that matches up with this path is
                // a "leaf" and either `obligation` is `LtLocal::Final` or obligation consists
                // "ghost" nodes used to track argument order e.g. in a tuple expression
                register_to(&mut epilogues[*idx]);
            }
        }

        LocalLt::Alt(obligations) => {
            debug_assert!(obligations.iter().any(|x| x.is_some()));

            let BodyDrops::Branch {
                prologues,
                sub_drops,
            } = drops
            else {
                unreachable!()
            };

            for (idx, obligation) in obligations.iter().enumerate() {
                if let Some(obligation) = obligation {
                    let drops = sub_drops[idx].as_mut().unwrap();
                    register_drops_for_slot_rec(drops, num_locals, binding, slot, obligation);
                } else {
                    if num_locals.contains(binding) {
                        // This binding is declared in an enclosing scope and this slot unused in
                        // this branch (but moved along some other branch), so we drop the slot
                        // immediately.
                        register_to(&mut prologues[idx]);
                    }
                }
            }
        }
    }
    */
}

fn register_drops_for_slot(
    drops: &mut BodyDrops,
    binding: flat::LocalId,
    slot: &Selector,
    obligation: &LocalLt,
) {
    // Every path starts `Seq(0)` since the scope of the function argument is `Seq(1)`
    let LocalLt::Seq(obligation, idx) = obligation else {
        unreachable!()
    };
    debug_assert_eq!(*idx, 0);

    // We must start `num_locals` at 1 to account for the function argument.
    register_drops_for_slot_rec(drops, Count::from_value(1), binding, slot, obligation);
}

fn register_drops_for_binding(
    drops: &mut BodyDrops,
    binding_id: flat::LocalId,
    binding_ty: &ob::Type,
    binding_path: &Path,
    obligation: &StackLt,
) {
    let absent = Selector::from_const(&binding_ty.unapply_overlay(), false);
    let binding_path = Lazy::new(|| binding_path.as_local_lt());

    for path in iterate_slots(obligation) {
        let mut slot = absent.clone();
        set_selector_slot(&mut slot, &path);
        match get_slot_data(&path) {
            Lt::Join(_) => panic!("`Join` should not appear in a binding's obligation"),
            // The binding is unused, so we can drop it immediately.
            Lt::Empty => {
                register_drops_for_slot(drops, binding_id, &slot, &*binding_path);
            }
            Lt::Local(lt) => {
                register_drops_for_slot(drops, binding_id, &slot, lt);
            }
        }
    }
}

fn register_drops_for_expr(
    drops: &mut BodyDrops,
    mut num_locals: Count<flat::LocalId>,
    path: &Path,
    expr: &ob::Expr,
) {
    match expr {
        ob::Expr::Branch(_, arms, _) => {
            for (i, (_, expr)) in arms.iter().enumerate() {
                let path = path.seq(0).alt(i, arms.len());
                register_drops_for_expr(drops, num_locals, &path, expr);
            }
        }

        ob::Expr::LetMany(bindings, _) => {
            for (i, (ty, obligation, sub_expr)) in bindings.iter().enumerate() {
                let path = path.seq(i);
                register_drops_for_expr(drops, num_locals, &path, sub_expr);

                // Only increment `num_locals` after recursing into `sub_expr`.
                let binding_id = num_locals.inc();
                register_drops_for_binding(drops, binding_id, ty, &path, obligation);
            }
        }

        _ => {}
    }
}

fn drops_for_func(func: &ob::FuncDef) -> FuncDrops {
    let none = Selector::from_const(&func.arg_ty.unapply_overlay(), false);
    let mut arg_drops = none.clone();
    let mut body_drops = empty_drops(&func.body);

    for path in iterate_slots(&func.arg_obligation) {
        let mut sel = none.clone();
        set_selector_slot(&mut sel, &path);
        match get_slot_data(&path) {
            Lt::Join(_) => panic!("`Join` should not appear in a binding's obligation"),
            Lt::Empty => {
                arg_drops = &arg_drops | &sel;
            }
            Lt::Local(lt) => {
                let body_drops = body_drops.as_mut().unwrap();
                register_drops_for_slot(body_drops, flat::ARG_LOCAL, &sel, lt);
            }
        }
    }

    // We must start `num_locals` at 1 to account for the function argument.
    register_drops_for_expr(
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
    ty: rc::Type,
    obligation: StackLt,
    moves: Selector,
}

fn annot_occur(
    customs: &ob::CustomTypes,
    ctx: &mut LocalContext<flat::LocalId, LocalInfo>,
    path: &Path,
    occur: ob::Occur,
    builder: &mut LetManyBuilder<Expr>,
) -> LocalId {
    let binding = ctx.local_binding_mut(occur.id);

    let dups = select_dups(customs, path, &binding.ty, &occur.ty, &binding.obligation);
    build_rc_op(RcOp::Retain, dups, binding.new_id, builder);

    let moves = select_moves(customs, path, &binding.ty, &occur.ty, &binding.obligation);
    binding.moves = &binding.moves | &moves;

    binding.new_id
}

fn annot_expr(
    customs: &ob::CustomTypes,
    ctx: &mut LocalContext<flat::LocalId, LocalInfo>,
    path: &Path,
    expr: ob::Expr,
    ret_ty: &ob::Type,
    drops: &Option<BodyDrops>,
    builder: &mut LetManyBuilder<Expr>,
) -> rc::LocalId {
    let new_expr = match expr {
        ob::Expr::Local(local) => rc::Expr::Local(annot_occur(customs, ctx, path, local, builder)),

        ob::Expr::Call(purity, func_id, arg) => rc::Expr::Call(
            purity,
            func_id,
            annot_occur(customs, ctx, path, arg, builder),
        ),

        ob::Expr::Branch(discrim, arms, ret_ty) => {
            let BodyDrops::Branch {
                prologues,
                sub_drops,
            } = drops.as_ref().unwrap()
            else {
                unreachable!();
            };

            let n = arms.len();
            let mut new_arms = Vec::new();

            for (i, (cond, expr)) in arms.into_iter().enumerate() {
                let mut case_builder = builder.child();

                for (old_id, candidate_drops) in &prologues[i] {
                    let binding = ctx.local_binding(*old_id);
                    let drops = candidate_drops & &!(&binding.moves);
                    build_rc_op(RcOp::Release, drops, binding.new_id, &mut case_builder);
                }

                let final_local = annot_expr(
                    customs,
                    ctx,
                    &path.seq(0).alt(i, n),
                    expr,
                    &ret_ty,
                    &sub_drops[i],
                    &mut case_builder,
                );

                new_arms.push((cond, case_builder.to_expr(final_local)));
            }

            let discrim = annot_occur(customs, ctx, path, discrim, builder);
            rc::Expr::Branch(discrim, new_arms, ret_ty)
        }

        ob::Expr::LetMany(bindings, ret) => {
            let BodyDrops::LetMany {
                epilogues,
                sub_drops,
            } = drops.as_ref().unwrap()
            else {
                unreachable!();
            };

            let final_local = ctx.with_scope(|ctx| {
                for (i, (ty, obligation, body)) in bindings.into_iter().enumerate() {
                    let final_local = annot_expr(
                        customs,
                        ctx,
                        &path.seq(i),
                        body,
                        &ty,
                        &sub_drops[i],
                        builder,
                    );

                    let moves = Selector::from_const(&ty.unapply_overlay(), false);
                    ctx.add_local(LocalInfo {
                        new_id: final_local,
                        ty,
                        obligation,
                        moves,
                    });

                    for (old_id, candidate_drops) in &epilogues[i] {
                        let binding = ctx.local_binding(*old_id);
                        let drops = candidate_drops & &!(&binding.moves);
                        build_rc_op(RcOp::Release, drops, binding.new_id, builder);
                    }
                }
                ctx.local_binding(ret.id).new_id
            });

            // Note: Early return! We circumvent the usual return flow because we don't actually
            // want to create an expression directly corresponding to this 'let' block. The 'let'
            // block's bindings just get absorbed into the ambient `builder`.
            return final_local;
        }

        ob::Expr::Tuple(fields) => rc::Expr::Tuple(
            fields
                .into_iter()
                .enumerate()
                .map(|(i, field)| annot_occur(customs, ctx, &path.seq(i), field, builder))
                .collect(),
        ),

        ob::Expr::TupleField(tuple, idx) => {
            rc::Expr::TupleField(annot_occur(customs, ctx, path, tuple, builder), idx)
        }

        ob::Expr::WrapVariant(variants, variant_id, content) => rc::Expr::WrapVariant(
            variants,
            variant_id,
            annot_occur(customs, ctx, path, content, builder),
        ),

        ob::Expr::UnwrapVariant(variant_id, wrapped) => rc::Expr::UnwrapVariant(
            variant_id,
            annot_occur(customs, ctx, path, wrapped, builder),
        ),

        ob::Expr::WrapBoxed(content, item_ty) => {
            rc::Expr::WrapBoxed(annot_occur(customs, ctx, path, content, builder), item_ty)
        }

        ob::Expr::UnwrapBoxed(wrapped, item_ty) => {
            rc::Expr::UnwrapBoxed(annot_occur(customs, ctx, path, wrapped, builder), item_ty)
        }

        ob::Expr::WrapCustom(id, content) => {
            rc::Expr::WrapCustom(id, annot_occur(customs, ctx, path, content, builder))
        }

        ob::Expr::UnwrapCustom(id, wrapped) => {
            rc::Expr::UnwrapCustom(id, annot_occur(customs, ctx, path, wrapped, builder))
        }

        ob::Expr::Intrinsic(intr, arg) => {
            rc::Expr::Intrinsic(intr, annot_occur(customs, ctx, path, arg, builder))
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Get(arr, idx, ret_ty)) => {
            let item_retains = select_owned(customs, &ret_ty);

            let get_op = rc::Expr::ArrayOp(rc::ArrayOp::Get(
                arr.ty.unwrap_item_modes().clone(),
                annot_occur(customs, ctx, path, arr, builder),
                annot_occur(customs, ctx, path, idx, builder),
            ));
            let get_id = builder.add_binding((ret_ty, get_op));

            build_rc_op(RcOp::Retain, item_retains, get_id, builder);
            return get_id;
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Extract(arr, idx)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Extract(
                arr.ty.unwrap_item_modes().clone(),
                annot_occur(customs, ctx, path, arr, builder),
                annot_occur(customs, ctx, path, idx, builder),
            ))
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Len(arr)) => rc::Expr::ArrayOp(rc::ArrayOp::Len(
            arr.ty.unwrap_item_modes().clone(),
            annot_occur(customs, ctx, path, arr, builder),
        )),

        ob::Expr::ArrayOp(ob::ArrayOp::Push(arr, item)) => rc::Expr::ArrayOp(rc::ArrayOp::Push(
            arr.ty.unwrap_item_modes().clone(),
            annot_occur(customs, ctx, path, arr, builder),
            annot_occur(customs, ctx, path, item, builder),
        )),

        ob::Expr::ArrayOp(ob::ArrayOp::Pop(arr)) => rc::Expr::ArrayOp(rc::ArrayOp::Pop(
            arr.ty.unwrap_item_modes().clone(),
            annot_occur(customs, ctx, path, arr, builder),
        )),

        ob::Expr::ArrayOp(ob::ArrayOp::Replace(arr, item)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Replace(
                arr.ty.unwrap_item_modes().clone(),
                annot_occur(customs, ctx, path, arr, builder),
                annot_occur(customs, ctx, path, item, builder),
            ))
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Reserve(arr, cap)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Reserve(
                arr.ty.unwrap_item_modes().clone(),
                annot_occur(customs, ctx, path, arr, builder),
                annot_occur(customs, ctx, path, cap, builder),
            ))
        }

        ob::Expr::IoOp(ob::IoOp::Input) => rc::Expr::IoOp(rc::IoOp::Input),

        ob::Expr::IoOp(ob::IoOp::Output(val)) => rc::Expr::IoOp(rc::IoOp::Output(annot_occur(
            customs, ctx, path, val, builder,
        ))),

        ob::Expr::Panic(ret_ty, msg) => {
            rc::Expr::Panic(ret_ty, annot_occur(customs, ctx, path, msg, builder))
        }

        ob::Expr::ArrayLit(item_ty, items) => rc::Expr::ArrayLit(
            item_ty,
            items
                .into_iter()
                .enumerate()
                .map(|(i, item)| annot_occur(customs, ctx, &path.seq(i), item, builder))
                .collect(),
        ),

        ob::Expr::BoolLit(lit) => rc::Expr::BoolLit(lit),

        ob::Expr::ByteLit(lit) => rc::Expr::ByteLit(lit),

        ob::Expr::IntLit(lit) => rc::Expr::IntLit(lit),

        ob::Expr::FloatLit(lit) => rc::Expr::FloatLit(lit),
    };

    builder.add_binding((ret_ty.clone(), new_expr))
}

fn annot_func(customs: &ob::CustomTypes, func: ob::FuncDef) -> rc::FuncDef {
    let drops = drops_for_func(&func);

    let mut ctx = LocalContext::new();
    let moves = Selector::from_const(&func.arg_ty.unapply_overlay(), false);
    ctx.add_local(LocalInfo {
        new_id: rc::ARG_LOCAL,
        ty: func.arg_ty.clone(),
        obligation: func.arg_obligation,
        moves,
    });

    let mut builder = LetManyBuilder::new(Count::from_value(1));
    build_rc_op(RcOp::Release, drops.arg_drops, rc::ARG_LOCAL, &mut builder);

    let ret_local = annot_expr(
        customs,
        &mut ctx,
        &annot::FUNC_BODY_PATH(),
        func.body,
        &func.ret_ty,
        &drops.body_drops,
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

pub fn annot_rcs(program: ob::Program, progress: impl ProgressLogger) -> rc::Program {
    let mut progress = progress.start_session(Some(program.funcs.len()));

    let funcs = IdVec::from_vec(
        program
            .funcs
            .into_iter()
            .map(|(func_id, func)| {
                println!(
                    "\n\nannotating function: {:?}\n",
                    program.func_symbols[func_id]
                );
                let annot = annot_func(&program.custom_types, func);
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
