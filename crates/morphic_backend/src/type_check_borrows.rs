use crate::data::mode_annot_ast::{self as annot, Mode, Path, ShapeInner, SlotId};
use crate::data::num_type::NumType;
use crate::data::obligation_annot_ast::{
    as_value_type, wrap_lts, BindRes, BindType, CustomFuncId, CustomTypeId, Shape, Type,
};
use crate::data::rc_annot_ast::{
    ArrayOp, CustomTypes, Expr, FuncDef, IoOp, LocalId, Occur, Program, RcOp,
};
use crate::pretty_print::mode_annot as annot_pp;
use crate::pretty_print::utils::{CustomTypeRenderer, FuncRenderer};
use core::panic;
use id_collections::IdVec;
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq, Eq)]
struct Moves(BTreeMap<SlotId, u32>);

impl Moves {
    fn rc1(customs: &CustomTypes, ty: &BindType) -> Self {
        let modes = ty
            .shape()
            .top_level_slots(customs.view_shapes())
            .iter()
            .map(|&slot| match ty.res()[slot].mode() {
                Mode::Owned => (slot, 1),
                Mode::Borrowed => (slot, 0),
            })
            .collect();
        Self(modes)
    }

    fn rc0(customs: &CustomTypes, ty: &BindType) -> Self {
        let modes = ty
            .shape()
            .top_level_slots(customs.view_shapes())
            .iter()
            .map(|&slot| (slot, 0))
            .collect();
        Self(modes)
    }

    fn all_moved(&self) -> bool {
        self.0.values().all(|&count| count == 0)
    }

    fn inc(&mut self, slot: SlotId) {
        *self.0.get_mut(&slot).unwrap() += 1;
    }

    fn dec(&mut self, slot: SlotId) {
        assert!(self.0[&slot] > 0, "variable already moved");
        *self.0.get_mut(&slot).unwrap() -= 1;
    }

    fn to_string(&self, type_renderer: &CustomTypeRenderer<CustomTypeId>, shape: &Shape) -> String {
        let counts = (0..shape.num_slots)
            .map(|slot| {
                if let Some(count) = self.0.get(&SlotId(slot)) {
                    count.to_string()
                } else {
                    "_".to_string()
                }
            })
            .collect::<Vec<_>>();

        let mut pretty_counts: Vec<u8> = Vec::new();
        annot_pp::write_type_raw(
            &mut pretty_counts,
            Some(&type_renderer),
            &|w, count| write!(w, "{}", count),
            shape,
            counts.as_slice(),
        )
        .unwrap();

        String::from_utf8(pretty_counts).unwrap()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LocalInfo {
    ty: BindType,
    moves: Moves,
}

type LocalContext = morphic_common::util::local_context::LocalContext<LocalId, LocalInfo>;
type Interner = annot::Interner<CustomTypeId>;

fn record_moves(customs: &CustomTypes, ctx: &mut LocalContext, local: &Occur) {
    let local_info = ctx.local_binding_mut(local.id);

    let slots = local.ty.shape().top_level_slots(customs.view_shapes());
    for slot in slots {
        if local.ty.res()[slot].mode() == Mode::Owned {
            local_info.moves.dec(slot);
        }
    }
}

fn extract_item_type(ty: &Type) -> Type {
    let item_shape = match &*ty.shape().inner {
        ShapeInner::Array(item_shape)
        | ShapeInner::HoleArray(item_shape)
        | ShapeInner::Boxed(item_shape) => item_shape,
        _ => panic!("expected array, hole array, or boxed type"),
    };
    Type::new(
        item_shape.clone(),
        IdVec::from_vec(ty.res().as_slice()[1..].to_vec()),
    )
}

fn assert_all_borrowed(customs: &CustomTypes, ty: &Type) {
    assert!(ty
        .shape()
        .top_level_slots(customs.view_shapes())
        .iter()
        .all(|&slot| { ty.res()[slot].mode() == Mode::Borrowed }));
}

fn assert_all_live(customs: &CustomTypes, ctx: &mut LocalContext, path: &Path, local_id: LocalId) {
    let ty = &ctx.local_binding(local_id).ty;
    let ok = ty
        .shape()
        .top_level_slots(customs.view_shapes())
        .iter()
        .all(|&slot| {
            ty.res()[slot]
                .lt()
                .map_or(true, |lt| lt.cmp_path(path).geq())
        });
    assert!(
        ok,
        "variable %{} is not live where it is accessed",
        local_id.0
    );
}

fn type_check_expr(
    func_id: CustomFuncId,
    func_renderer: &FuncRenderer<CustomFuncId>,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    interner: &Interner,
    customs: &CustomTypes,
    funcs: &IdVec<CustomFuncId, FuncDef>,
    ctx: &mut LocalContext,
    path: &Path,
    expr: &Expr,
    ret_ty: &Type,
) {
    match expr {
        Expr::Local(local) => {
            assert_eq!(&local.ty, ret_ty);
            record_moves(customs, ctx, local)
        }
        Expr::Call(_purity, _func_id, arg) => {
            assert_all_live(customs, ctx, path, arg.id);
            record_moves(customs, ctx, arg);
        }
        Expr::LetMany(bindings, final_local) => ctx.with_scope(|ctx| {
            let num_locals = ctx.len();
            let mut i: usize = 0;
            for (binding_ty, expr, _) in bindings {
                // XXX: Lifetimes were computed in the pass before retain/release insertion, so we
                // need to update `path` as if the retains/releases are not present.
                match expr {
                    Expr::RcOp(RcOp::Retain, selector, local_id) => {
                        let local_info = ctx.local_binding_mut(*local_id);
                        for &slot in &selector.true_ {
                            local_info.moves.inc(slot);
                        }
                    }
                    Expr::RcOp(RcOp::Release, selector, local_id) => {
                        let effective_i = i.saturating_sub(1);
                        let local_info = ctx.local_binding_mut(*local_id);
                        for &slot in &selector.true_ {
                            let res = &local_info.ty.res()[slot];
                            match res {
                                BindRes::StackOwned(lt) => {
                                    local_info.moves.dec(slot);
                                    assert!(lt.cmp_path(&path.seq(effective_i)).leq_right_biased());
                                }
                                BindRes::HeapOwned => {
                                    local_info.moves.dec(slot);
                                }
                                BindRes::Borrowed(_) => {}
                            };
                        }
                    }
                    _ => {
                        type_check_expr(
                            func_id,
                            func_renderer,
                            type_renderer,
                            interner,
                            customs,
                            funcs,
                            ctx,
                            &path.seq(i),
                            expr,
                            &as_value_type(binding_ty),
                        );
                        i += 1;
                    }
                }

                let moves = match expr {
                    Expr::UnwrapBoxed(_, _) | Expr::ArrayOp(ArrayOp::Get(_, _)) => {
                        Moves::rc0(customs, binding_ty)
                    }
                    _ => Moves::rc1(customs, binding_ty),
                };

                ctx.add_local(LocalInfo {
                    ty: binding_ty.clone(),
                    moves,
                });
            }

            assert_eq!(&final_local.ty, ret_ty);
            record_moves(customs, ctx, final_local);

            for local in num_locals..ctx.len() {
                let local_info = ctx.local_binding(LocalId(local));
                if !local_info.moves.all_moved() {
                    panic!(
                        "variable not moved in {} (func {}):\n%{}: {}\ncounts: {}",
                        func_renderer.render(func_id),
                        func_id.0,
                        local,
                        local_info.ty.display_with(type_renderer),
                        local_info
                            .moves
                            .to_string(type_renderer, local_info.ty.shape()),
                    );
                }
            }
        }),
        Expr::If(_discrim_id, then_expr, else_expr) => {
            let mut then_ctx = ctx.clone();
            type_check_expr(
                func_id,
                func_renderer,
                type_renderer,
                interner,
                customs,
                funcs,
                &mut then_ctx,
                &path.seq(1).alt(0, 2),
                then_expr,
                ret_ty,
            );
            type_check_expr(
                func_id,
                func_renderer,
                type_renderer,
                interner,
                customs,
                funcs,
                ctx,
                &path.seq(1).alt(1, 2),
                else_expr,
                ret_ty,
            );
            assert_eq!(then_ctx, *ctx);
        }
        Expr::CheckVariant(_variant_id, local) => {
            assert_all_borrowed(customs, &local.ty);
        }
        Expr::Unreachable(_ty) => {}
        Expr::Tuple(items) => {
            let ret_tys = annot::elim_tuple(ret_ty);
            for (item, ret_ty) in items.iter().zip(&ret_tys) {
                assert_eq!(&item.ty, ret_ty);
                record_moves(customs, ctx, item);
            }
        }
        Expr::TupleField(local, idx) => {
            let item_tys = annot::elim_tuple(&local.ty);
            assert_eq!(&item_tys[*idx], ret_ty);
            record_moves(customs, ctx, local);
        }
        Expr::WrapVariant(variants, variant_id, local) => {
            let ret_tys = annot::elim_variants(ret_ty);
            assert_eq!(&variants[variant_id], &local.ty);
            assert_eq!(&variants[variant_id], &ret_tys[variant_id]);
            record_moves(customs, ctx, local);
        }
        Expr::UnwrapVariant(variant_id, local) => {
            let variant_tys = annot::elim_variants(&local.ty);
            assert_eq!(&variant_tys[variant_id], ret_ty);
            record_moves(customs, ctx, local);
        }
        Expr::WrapBoxed(local, output_ty) => {
            assert_eq!(output_ty, ret_ty);
            record_moves(customs, ctx, local);
        }
        Expr::UnwrapBoxed(local, output_ty) => {
            assert_eq!(output_ty, ret_ty);
            assert_all_live(customs, ctx, path, local.id);
            record_moves(customs, ctx, local);
        }
        Expr::WrapCustom(_custom_type_id, local) => {
            record_moves(customs, ctx, local);
        }
        Expr::UnwrapCustom(_custom_type_id, local) => {
            record_moves(customs, ctx, local);
        }
        Expr::RcOp(_op, _selector, _local_id) => {
            panic!("the type checker should handle `RcOp` in `LetMany`")
        }
        Expr::Intrinsic(_intr, _local_id) => {}
        Expr::ArrayOp(ArrayOp::Get(arr, _idx)) => {
            assert_all_borrowed(customs, &arr.ty);
            assert_all_live(customs, ctx, &path.seq(0), arr.id);
            record_moves(customs, ctx, arr);
        }
        Expr::ArrayOp(ArrayOp::Extract(arr, _idx)) => {
            record_moves(customs, ctx, arr);
        }
        Expr::ArrayOp(ArrayOp::Len(arr)) => {
            assert_all_borrowed(customs, &arr.ty);
        }
        Expr::ArrayOp(ArrayOp::Push(arr, item)) => {
            record_moves(customs, ctx, arr);
            record_moves(customs, ctx, item);
        }
        Expr::ArrayOp(ArrayOp::Pop(arr)) => {
            record_moves(customs, ctx, arr);
        }
        Expr::ArrayOp(ArrayOp::Replace(hole_arr, item)) => {
            record_moves(customs, ctx, hole_arr);
            record_moves(customs, ctx, item);
        }
        Expr::ArrayOp(ArrayOp::Reserve(arr, _cap)) => {
            record_moves(customs, ctx, arr);
        }
        Expr::IoOp(IoOp::Input) => {
            let ShapeInner::Array(item_shape) = &*ret_ty.shape().inner else {
                panic!("expected array type");
            };
            let ShapeInner::Num(NumType::Byte) = &*item_shape.inner else {
                panic!("expected byte array type");
            };
            assert_eq!(ret_ty.res().len(), 1, "expected byte array type");
            assert_eq!(ret_ty.res()[SlotId(0)].mode(), Mode::Owned);
        }
        Expr::IoOp(IoOp::Output(local)) => {
            assert_all_borrowed(customs, &local.ty);
        }
        Expr::Panic(output_ty, local) => {
            assert_eq!(output_ty, ret_ty);
            assert_all_borrowed(customs, &local.ty);
        }
        Expr::ArrayLit(_item_ty, items) => {
            // TODO: assert the right thing about the item type
            // let item_ty = extract_item_type(ret_ty);
            for item in items {
                // assert_eq!(item_ty.shape(), item.ty.shape());
                record_moves(customs, ctx, item);
            }
        }
        Expr::BoolLit(_lit) => {}
        Expr::ByteLit(_lit) => {}
        Expr::IntLit(_lit) => {}
        Expr::FloatLit(_lit) => {}
    }
}

pub fn type_check(interner: &Interner, program: &Program) {
    let type_renderer = CustomTypeRenderer::from_symbols(&program.custom_type_symbols);
    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);
    for (func_id, func) in &program.funcs {
        let mut ctx = LocalContext::new();
        ctx.add_local(LocalInfo {
            ty: func.arg_ty.clone(),
            moves: Moves::rc1(&program.custom_types, &func.arg_ty),
        });
        type_check_expr(
            func_id,
            &func_renderer,
            &type_renderer,
            interner,
            &program.custom_types,
            &program.funcs,
            &mut ctx,
            &annot::FUNC_BODY_PATH(),
            &func.body,
            &wrap_lts(&func.ret_ty),
        );
    }
}
