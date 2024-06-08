use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mode_annot_ast2::{CollectOverlay, LocalLt, Lt, Mode, Overlay, Path, SlotId};
use crate::data::obligation_annot_ast::{self as ob, StackLt};
use crate::data::rc_annot_ast::{self as rc, Expr, LocalId, Selector};
use crate::util::iter::IterExt;
use crate::util::let_builder::{FromBindings, LetManyBuilder};
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::{ProgressLogger, ProgressSession};
use id_collections::{Count, IdVec};
use once_cell::sync::Lazy;
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
        .modes()
        .iter_overlay()
        .zip_eq(dst_ty.modes().iter_overlay())
        .zip_eq(lt_obligation.iter())
        .map(|((src_mode, dst_mode), lt)| should_dup(path, *src_mode, *dst_mode, lt))
        .collect_overlay(lt_obligation)
}

fn select_owned(ty: &ob::Type) -> Selector {
    ty.modes()
        .iter_overlay()
        .map(|&mode| mode == Mode::Owned)
        .collect_overlay(&ty.modes().unapply_overlay())
}

fn should_drop(path: &Path, src_mode: Mode, dst_mode: Mode, lt: &Lt) -> bool {
    src_mode == Mode::Owned && dst_mode == Mode::Owned && lt.does_not_exceed(path)
}

fn select_drops(
    path: &Path,
    src_ty: &ob::Type,
    dst_ty: &ob::Type,
    lt_obligation: &StackLt,
) -> Selector {
    src_ty
        .modes()
        .iter_overlay()
        .zip_eq(dst_ty.modes().iter_overlay())
        .zip_eq(lt_obligation.iter())
        .map(|((src_mode, dst_mode), lt)| should_drop(path, *src_mode, *dst_mode, lt))
        .collect_overlay(lt_obligation)
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

// TODO: using `Selector`s here (as we've currently defined them) is quite inefficient. We should
// use a data structure which can *sparsely* represent a subset of fields.
type DropSet = BTreeMap<LocalId, Selector>;

/// Because the program is in ANF and occurences do not count toward lifetime obligations (only
/// accesses do), *local* lifetimes always end inside let many statements, except when a variable is
/// used along one branch of a match and unused along another.
enum Drops {
    Branch {
        /// drops `before[i]` are executed before the body of the ith arm
        before: Vec<DropSet>,
        in_: Vec<Option<Drops>>,
    },
    LetMany {
        /// drops `after[i]` are executed after the ith binding
        after: Vec<DropSet>,
        in_: Vec<Option<Drops>>,
    },
}

impl Drops {
    fn none(expr: &ob::Expr) -> Option<Self> {
        match expr {
            ob::Expr::Branch(_, arms, _) => {
                let before = arms.iter().map(|_| DropSet::new()).collect();
                let in_ = arms.iter().map(|(_, body)| Self::none(body)).collect();
                Some(Self::Branch { before, in_ })
            }

            ob::Expr::LetMany(bindings, _) => {
                let after = bindings.iter().map(|_| DropSet::new()).collect();
                let in_ = bindings
                    .iter()
                    .map(|(_, _, body)| Self::none(body))
                    .collect();
                Some(Self::LetMany { after, in_ })
            }

            _ => None,
        }
    }

    fn register_drops_for_slot(
        &mut self,
        slot: &Selector,
        id: LocalId,
        mode: Mode,
        obligation: &LocalLt,
        expr: &ob::Expr,
    ) {
        let register_to = |drops: &mut DropSet| {
            drops
                .entry(id)
                .and_modify(|old_slots| *old_slots = &*old_slots | slot)
                .or_insert_with(|| slot.clone());
        };

        match obligation {
            LocalLt::Final => unreachable!(),

            LocalLt::Seq(obligation, idx) => {
                let Drops::LetMany { after, in_ } = self else {
                    unreachable!()
                };

                let ob::Expr::LetMany(bindings, _) = expr else {
                    unreachable!()
                };

                if **obligation == LocalLt::Final {
                    register_to(&mut after[*idx]);
                } else {
                    let drops = in_[*idx].as_mut().unwrap();
                    drops.register_drops_for_slot(slot, id, mode, obligation, &bindings[*idx].2);
                }
            }

            LocalLt::Par(obligations) => {
                let Drops::Branch { before, in_ } = self else {
                    unreachable!()
                };

                let ob::Expr::Branch(_, arms, _) = expr else {
                    unreachable!()
                };

                for (idx, obligation) in obligations.iter().enumerate() {
                    if let Some(obligation) = obligation {
                        let drops = in_[idx].as_mut().unwrap();
                        drops.register_drops_for_slot(slot, id, mode, obligation, &arms[idx].1);
                    } else {
                        register_to(&mut before[idx]);
                    }
                }
            }
        }
    }

    fn register_drops_for_binding(
        &mut self,
        binding_id: LocalId,
        binding_ty: &ob::Type,
        binding_path: &Path,
        obligation: &StackLt,
        expr: &ob::Expr,
    ) {
        let none = Selector::from_const(&binding_ty.modes().unapply_overlay(), false);
        let binding_path = Lazy::new(|| binding_path.as_local_lt());

        let binding_ov = binding_ty.modes().unapply_overlay();
        let slots = iterate_slots(obligation).zip_eq(iterate_slots(&binding_ov));

        for (lt_slot, mode_slot) in slots {
            let mut sel = none.clone();
            set_selector_slot(&mut sel, &lt_slot);
            let mode = *get_slot_data(&mode_slot);

            match get_slot_data(&lt_slot) {
                // We don't need to do anything since the binding escapes into the caller's scope.
                Lt::Join(_) => {}
                // The binding is unused, so we can drop it immediately.
                Lt::Empty => {
                    self.register_drops_for_slot(&sel, binding_id, mode, &*binding_path, expr);
                }
                Lt::Local(lt) => {
                    self.register_drops_for_slot(&sel, binding_id, mode, lt, expr);
                }
            }
        }
    }

    fn register_drops_for_expr(
        &mut self,
        mut num_locals: Count<LocalId>,
        path: &Path,
        expr: &ob::Expr,
    ) {
        match expr {
            ob::Expr::Branch(_, arms, _) => {
                for (i, (_, expr)) in arms.iter().enumerate() {
                    let path = path.par(i, arms.len());
                    self.register_drops_for_expr(num_locals, &path, expr);
                }
            }

            ob::Expr::LetMany(bindings, _) => {
                for (i, (ty, obligation, expr)) in bindings.iter().enumerate() {
                    let path = path.seq(i);
                    self.register_drops_for_expr(num_locals, &path, expr);

                    // Only increment `num_locals` after recursing into `sub_expr`
                    let binding_id = num_locals.inc();
                    self.register_drops_for_binding(binding_id, ty, &path, obligation, expr);
                }
            }

            _ => {}
        }
    }
}

#[derive(Clone, Debug)]
struct LocalInfo {
    ty: rc::Type,
    new_id: LocalId,
    obligation: StackLt,
}

fn annot_occur(
    ctx: &mut LocalContext<flat::LocalId, LocalInfo>,
    local_id: flat::LocalId,
) -> LocalId {
    *ctx.local_binding(local_id)
}

fn annot_expr(
    context: &mut LocalContext<LocalId, ob::Type>,
    ctx: &mut LocalContext<flat::LocalId, LocalInfo>,
    path: &Path,
    expr: ob::Expr,
    ret_ty: ob::Type,
    drops: Option<&Drops>,
    builder: &mut LetManyBuilder<Expr>,
) -> rc::LocalId {
    let new_expr = match expr {
        ob::Expr::Local(local) => rc::Expr::Local(annot_occur(ctx, local.id)),

        ob::Expr::Call(purity, func_id, arg) => {
            rc::Expr::Call(purity, func_id, annot_occur(ctx, arg.id))
        }

        ob::Expr::Branch(_, _, _) => todo!(),

        ob::Expr::LetMany(_, _) => todo!(),

        ob::Expr::Tuple(fields) => rc::Expr::Tuple(
            fields
                .into_iter()
                .map(|field| annot_occur(ctx, field.id))
                .collect(),
        ),

        ob::Expr::TupleField(tuple, idx) => rc::Expr::TupleField(annot_occur(ctx, tuple.id), idx),

        ob::Expr::WrapVariant(variants, variant_id, content) => rc::Expr::WrapVariant(
            IdVec::from_vec(variants.into_values().map(|ty| ty.into_modes()).collect()),
            variant_id,
            annot_occur(ctx, content.id),
        ),

        ob::Expr::UnwrapVariant(variant_id, wrapped) => {
            rc::Expr::UnwrapVariant(variant_id, annot_occur(ctx, wrapped.id))
        }

        ob::Expr::WrapBoxed(content, item_ty) => {
            rc::Expr::WrapBoxed(annot_occur(ctx, content.id), item_ty.into_modes())
        }

        ob::Expr::UnwrapBoxed(wrapped, item_ty) => {
            rc::Expr::UnwrapBoxed(annot_occur(ctx, wrapped.id), item_ty.into_modes())
        }

        ob::Expr::WrapCustom(id, content, ret_ty) => {
            rc::Expr::WrapCustom(id, annot_occur(ctx, content.id), ret_ty.into_modes())
        }

        ob::Expr::UnwrapCustom(id, wrapped) => {
            rc::Expr::UnwrapCustom(id, annot_occur(ctx, wrapped.id))
        }

        ob::Expr::Intrinsic(intr, arg) => rc::Expr::Intrinsic(intr, annot_occur(ctx, arg.id)),

        ob::Expr::ArrayOp(ob::ArrayOp::Get(arr, idx, ret_ty)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Get(
                annot_occur(ctx, arr.id),
                annot_occur(ctx, idx.id),
                ret_ty.into_modes(),
            ))
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Extract(arr, idx)) => rc::Expr::ArrayOp(
            rc::ArrayOp::Extract(annot_occur(ctx, arr.id), annot_occur(ctx, idx.id)),
        ),

        ob::Expr::ArrayOp(ob::ArrayOp::Len(arr)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Len(annot_occur(ctx, arr.id)))
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Push(arr, item)) => rc::Expr::ArrayOp(rc::ArrayOp::Push(
            annot_occur(ctx, arr.id),
            annot_occur(ctx, item.id),
        )),

        ob::Expr::ArrayOp(ob::ArrayOp::Pop(arr)) => {
            rc::Expr::ArrayOp(rc::ArrayOp::Pop(annot_occur(ctx, arr.id)))
        }

        ob::Expr::ArrayOp(ob::ArrayOp::Replace(arr, item)) => rc::Expr::ArrayOp(
            rc::ArrayOp::Replace(annot_occur(ctx, arr.id), annot_occur(ctx, item.id)),
        ),

        ob::Expr::ArrayOp(ob::ArrayOp::Reserve(arr, cap)) => rc::Expr::ArrayOp(
            rc::ArrayOp::Reserve(annot_occur(ctx, arr.id), annot_occur(ctx, cap.id)),
        ),

        ob::Expr::IoOp(ob::IoOp::Input) => rc::Expr::IoOp(rc::IoOp::Input),

        ob::Expr::IoOp(ob::IoOp::Output(val)) => {
            rc::Expr::IoOp(rc::IoOp::Output(annot_occur(ctx, val.id)))
        }

        ob::Expr::Panic(ret_ty, msg) => {
            rc::Expr::Panic(ret_ty.into_modes(), annot_occur(ctx, msg.id))
        }

        ob::Expr::ArrayLit(item_ty, items) => rc::Expr::ArrayLit(
            item_ty.into_modes(),
            items
                .into_iter()
                .map(|item| annot_occur(ctx, item.id))
                .collect(),
        ),

        ob::Expr::BoolLit(lit) => rc::Expr::BoolLit(lit),

        ob::Expr::ByteLit(lit) => rc::Expr::ByteLit(lit),

        ob::Expr::IntLit(lit) => rc::Expr::IntLit(lit),

        ob::Expr::FloatLit(lit) => rc::Expr::FloatLit(lit),
    };

    builder.add_binding(ret_ty.into_modes(), new_expr)
}

fn annot_func(func: ob::FuncDef) -> rc::FuncDef {
    let mut builder = LetManyBuilder::new(Count::from_value(1));

    let mut drops = Drops::none(&func.body);
    drops.register_drops_for_expr(Count::from_value(1), &Path::empty(), &func.body);

    let mut context = LocalContext::new();
    let ret_local = annot_expr(&mut context, func.body, func.ret_ty, &drops, &mut builder);

    rc::FuncDef {
        purity: func.purity,
        arg_ty: func.arg_ty.into_modes(),
        ret_ty: func.ret_ty.into_modes(),
        body: builder.to_expr(ret_local),
        profile_point: func.profile_point,
    }
}

pub fn annot_rcs(program: ob::Program, progress: impl ProgressLogger) -> rc::Program {
    let mut progress = progress.start_session(Some(program.funcs.len()));

    let types = IdVec::from_vec(
        program
            .custom_types
            .types
            .into_values()
            .map(|typedef| rc::TypeDef {
                ty: typedef.ty.into_modes(),
                ov: typedef.ov,
                slot_count: typedef.slot_count,
                ov_slots: typedef.ov_slots,
            })
            .collect(),
    );

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

    rc::Program {
        mod_symbols: program.mod_symbols,
        custom_types: rc::CustomTypes { types },
        funcs,
        profile_points: program.profile_points,
        main: program.main,
    }
}
