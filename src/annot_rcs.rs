use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mode_annot_ast2::{
    self as annot, CollectOverlay, LocalLt, Lt, Mode, Overlay, Path, SlotId,
};
use crate::data::obligation_annot_ast::{self as ob, StackLt};
use crate::data::rc_annot_ast::{self as rc, Expr, LocalId, RcOp, Selector};
use crate::util::iter::IterExt;
use crate::util::let_builder::{FromBindings, LetManyBuilder};
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{Count, IdVec};
use std::collections::BTreeMap;
use std::iter;

impl FromBindings for Expr {
    type LocalId = LocalId;
    type Binding = (rc::Type, Expr);

    fn from_bindings(bindings: Vec<Self::Binding>, ret: LocalId) -> Self {
        Expr::LetMany(bindings, ret)
    }
}

fn should_dup(path: &Path, src_mode: Mode, dst_mode: Mode, lt: &Lt) -> bool {
    match (src_mode, dst_mode) {
        (_, Mode::Borrowed) => false,
        (Mode::Borrowed, Mode::Owned) => {
            panic!("borrowed to owned transitions should be prevented by constraint generation")
        }
        (Mode::Owned, Mode::Owned) => !lt.does_not_exceed(path),
    }
}

fn select_dups(
    path: &Path,
    src_ty: &ob::Type,
    dst_ty: &ob::Type,
    lt_obligation: &StackLt,
) -> Selector {
    src_ty
        .iter_overlay()
        .zip_eq(dst_ty.iter_overlay())
        .zip_eq(lt_obligation.iter())
        .map(|((src_mode, dst_mode), lt)| should_dup(path, *src_mode, *dst_mode, lt))
        .collect_overlay(lt_obligation)
}

fn should_drop(path: &Path, _src_mode: Mode, dst_mode: Mode, lt: &Lt) -> bool {
    // If the destination is owned, either this is a dup, and therefore not the final occurrence of
    // this variable, or this is a move
    dst_mode == Mode::Borrowed && lt.does_not_exceed(path)
}

fn select_drops(
    path: &Path,
    src_ty: &ob::Type,
    dst_ty: &ob::Type,
    lt_obligation: &StackLt,
) -> Selector {
    src_ty
        .iter_overlay()
        .zip_eq(dst_ty.iter_overlay())
        .zip_eq(lt_obligation.iter())
        .map(|((src_mode, dst_mode), lt)| should_drop(path, *src_mode, *dst_mode, lt))
        .collect_overlay(lt_obligation)
}

fn select_owned(ty: &ob::Type) -> Selector {
    ty.iter_overlay()
        .map(|&mode| mode == Mode::Owned)
        .collect_overlay(&ty.unapply_overlay())
}

fn select_empty(lt: &StackLt) -> Selector {
    lt.iter().map(|lt| *lt == Lt::Empty).collect_overlay(&lt)
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

#[derive(Clone, Debug)]
struct LocalInfo {
    new_id: LocalId,
    ty: rc::Type,
    obligation: StackLt,
}

fn annot_occur(
    ctx: &mut LocalContext<flat::LocalId, LocalInfo>,
    path: &Path,
    occur: ob::Occur,
    builder: &mut LetManyBuilder<Expr>,
) -> LocalId {
    let binding = ctx.local_binding(occur.id);

    let dups = select_dups(path, &binding.ty, &occur.ty, &binding.obligation);
    builder.add_binding((
        rc::Type::Tuple(vec![]),
        rc::Expr::RcOp(RcOp::Retain, dups, binding.new_id),
    ));

    let drops = select_drops(path, &binding.ty, &occur.ty, &binding.obligation);
    builder.add_binding((
        rc::Type::Tuple(vec![]),
        rc::Expr::RcOp(RcOp::Release, drops, binding.new_id),
    ));

    binding.new_id
}

fn annot_expr(
    ctx: &mut LocalContext<flat::LocalId, LocalInfo>,
    path: &Path,
    expr: ob::Expr,
    ret_ty: &ob::Type,
    builder: &mut LetManyBuilder<Expr>,
) -> rc::LocalId {
    let new_expr = match expr {
        ob::Expr::Local(local) => rc::Expr::Local(annot_occur(ctx, path, local, builder)),

        ob::Expr::Call(purity, func_id, arg) => {
            rc::Expr::Call(purity, func_id, annot_occur(ctx, path, arg, builder))
        }

        ob::Expr::Branch(discrim, arms, ret_ty) => {
            let num_arms = arms.len();
            let mut drops = vec![BTreeMap::new(); num_arms];

            // Determine the variables which are used along some, but not all, branches
            // TODO: These loops are expensive!
            for info in ctx.inner().values() {
                for slot in iterate_slots(&info.obligation) {
                    match get_slot_data(&slot) {
                        Lt::Empty | Lt::Join(_) => {}
                        Lt::Local(slot_lt) => {
                            if let Some(suffix_lt) = slot_lt.zoom(&path) {
                                let LocalLt::Par(arm_lts) = suffix_lt else {
                                    unreachable!();
                                };
                                for (arm_lt, drops) in arm_lts.iter().zip_eq(drops.iter_mut()) {
                                    if *arm_lt == None {
                                        let sel = drops.entry(info.new_id).or_insert_with(|| {
                                            Selector::from_const(&info.ty.unapply_overlay(), false)
                                        });
                                        set_selector_slot(sel, &slot);
                                    }
                                }
                            }
                        }
                    }
                }
            }

            let discrim = annot_occur(ctx, path, discrim, builder);
            let mut new_arms = Vec::new();
            for entry in arms.into_iter().zip_eq(drops.into_iter()).enumerate() {
                let (i, ((cond, expr), drops)) = entry;
                let mut case_builder = builder.child();
                for (drop_id, drop_sel) in drops {
                    case_builder.add_binding((
                        rc::Type::Tuple(vec![]),
                        rc::Expr::RcOp(RcOp::Retain, drop_sel, drop_id),
                    ));
                }
                let final_local = annot_expr(
                    ctx,
                    &path.par(i, num_arms),
                    expr,
                    &ret_ty,
                    &mut case_builder,
                );
                new_arms.push((cond, case_builder.to_expr(final_local)));
            }

            rc::Expr::Branch(discrim, new_arms, ret_ty)
        }

        ob::Expr::LetMany(bindings, ret) => {
            let final_local = ctx.with_scope(|ctx| {
                for (i, (ty, obligation, expr)) in bindings.into_iter().enumerate() {
                    let drop_immediately = select_empty(&obligation);
                    let final_local = annot_expr(ctx, &path.seq(i), expr, &ty, builder);
                    ctx.add_local(LocalInfo {
                        new_id: final_local,
                        ty,
                        obligation,
                    });
                    builder.add_binding((
                        rc::Type::Tuple(vec![]),
                        rc::Expr::RcOp(RcOp::Release, drop_immediately, final_local),
                    ));
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
                .map(|field| annot_occur(ctx, path, field, builder))
                .collect(),
        ),

        ob::Expr::TupleField(tuple, idx) => {
            rc::Expr::TupleField(annot_occur(ctx, path, tuple, builder), idx)
        }

        ob::Expr::WrapVariant(variants, variant_id, content) => rc::Expr::WrapVariant(
            variants,
            variant_id,
            annot_occur(ctx, path, content, builder),
        ),

        ob::Expr::UnwrapVariant(variant_id, wrapped) => {
            rc::Expr::UnwrapVariant(variant_id, annot_occur(ctx, path, wrapped, builder))
        }

        ob::Expr::WrapBoxed(content, item_ty) => {
            rc::Expr::WrapBoxed(annot_occur(ctx, path, content, builder), item_ty)
        }

        ob::Expr::UnwrapBoxed(wrapped, item_ty) => {
            rc::Expr::UnwrapBoxed(annot_occur(ctx, path, wrapped, builder), item_ty)
        }

        ob::Expr::WrapCustom(id, content) => {
            rc::Expr::WrapCustom(id, annot_occur(ctx, path, content, builder))
        }

        ob::Expr::UnwrapCustom(id, wrapped) => {
            rc::Expr::UnwrapCustom(id, annot_occur(ctx, path, wrapped, builder))
        }

        ob::Expr::Intrinsic(intr, arg) => {
            rc::Expr::Intrinsic(intr, annot_occur(ctx, path, arg, builder))
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Get(arr, idx, ret_ty)) => {
            let item_retains = select_owned(&ret_ty);

            let get_op = rc::Expr::ArrayOp(rc::ArrayOp::Get(
                arr.ty.unwrap_item_modes().clone(),
                annot_occur(ctx, path, arr, builder),
                annot_occur(ctx, path, idx, builder),
            ));
            let get_id = builder.add_binding((ret_ty, get_op));

            builder.add_binding((
                rc::Type::Tuple(vec![]),
                rc::Expr::RcOp(RcOp::Retain, item_retains, get_id),
            ));
            return get_id;
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Extract(arr, idx)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Extract(
                arr.ty.unwrap_item_modes().clone(),
                annot_occur(ctx, path, arr, builder),
                annot_occur(ctx, path, idx, builder),
            ))
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Len(arr)) => rc::Expr::ArrayOp(rc::ArrayOp::Len(
            arr.ty.unwrap_item_modes().clone(),
            annot_occur(ctx, path, arr, builder),
        )),

        ob::Expr::ArrayOp(ob::ArrayOp::Push(arr, item)) => rc::Expr::ArrayOp(rc::ArrayOp::Push(
            arr.ty.unwrap_item_modes().clone(),
            annot_occur(ctx, path, arr, builder),
            annot_occur(ctx, path, item, builder),
        )),

        ob::Expr::ArrayOp(ob::ArrayOp::Pop(arr)) => rc::Expr::ArrayOp(rc::ArrayOp::Pop(
            arr.ty.unwrap_item_modes().clone(),
            annot_occur(ctx, path, arr, builder),
        )),

        ob::Expr::ArrayOp(ob::ArrayOp::Replace(arr, item)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Replace(
                arr.ty.unwrap_item_modes().clone(),
                annot_occur(ctx, path, arr, builder),
                annot_occur(ctx, path, item, builder),
            ))
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Reserve(arr, cap)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Reserve(
                arr.ty.unwrap_item_modes().clone(),
                annot_occur(ctx, path, arr, builder),
                annot_occur(ctx, path, cap, builder),
            ))
        }

        ob::Expr::IoOp(ob::IoOp::Input) => rc::Expr::IoOp(rc::IoOp::Input),

        ob::Expr::IoOp(ob::IoOp::Output(val)) => {
            rc::Expr::IoOp(rc::IoOp::Output(annot_occur(ctx, path, val, builder)))
        }

        ob::Expr::Panic(ret_ty, msg) => {
            rc::Expr::Panic(ret_ty, annot_occur(ctx, path, msg, builder))
        }

        ob::Expr::ArrayLit(item_ty, items) => rc::Expr::ArrayLit(
            item_ty,
            items
                .into_iter()
                .map(|item| annot_occur(ctx, path, item, builder))
                .collect(),
        ),

        ob::Expr::BoolLit(lit) => rc::Expr::BoolLit(lit),

        ob::Expr::ByteLit(lit) => rc::Expr::ByteLit(lit),

        ob::Expr::IntLit(lit) => rc::Expr::IntLit(lit),

        ob::Expr::FloatLit(lit) => rc::Expr::FloatLit(lit),
    };

    builder.add_binding((ret_ty.clone(), new_expr))
}

fn annot_func(func: ob::FuncDef) -> rc::FuncDef {
    let arg_drops = select_empty(&func.arg_obligation);

    let mut ctx = LocalContext::new();
    ctx.add_local(LocalInfo {
        new_id: rc::ARG_LOCAL,
        ty: func.arg_ty.clone(),
        obligation: func.arg_obligation,
    });

    let mut builder = LetManyBuilder::new(Count::from_value(1));
    builder.add_binding((
        rc::Type::Tuple(vec![]),
        rc::Expr::RcOp(RcOp::Release, arg_drops, rc::ARG_LOCAL),
    ));

    let ret_local = annot_expr(
        &mut ctx,
        &annot::FUNC_BODY_PATH(),
        func.body,
        &func.ret_ty,
        &mut builder,
    );

    rc::FuncDef {
        purity: func.purity,
        arg_ty: func.arg_ty,
        ret_ty: func.ret_ty,
        body: builder.to_expr(ret_local),
        profile_point: func.profile_point,
    }
}

pub fn annot_rcs(program: ob::Program, progress: impl ProgressLogger) -> rc::Program {
    let mut progress = progress.start_session(Some(program.funcs.len()));

    let funcs = IdVec::from_vec(
        program
            .funcs
            .into_values()
            .map(|func| {
                let annot = annot_func(func);
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
        funcs,
        profile_points: program.profile_points,
        main: program.main,
    }
}
