use crate::data::first_order_ast as first_ord;
use crate::data::guarded_ast as guard;
use crate::data::metadata::Metadata;
use crate::data::mode_annot_ast2::{
    self as annot, enumerate_shapes, iter_shapes, HeapModes, Interner, Lt, Mode, ModeParam,
    ModeSolution, Path, Res, ResModes, Shape, ShapeInner, SlotId,
};
use crate::data::obligation_annot_ast::{
    self as ob, ArrayOp, CustomFuncId, Expr, FuncDef, IoOp, Occur, StackLt, Type,
};
use crate::pretty_print::utils::FuncRenderer;
use crate::util::collection_ext::BTreeMapExt;
use crate::util::instance_queue::InstanceQueue;
use crate::util::iter::IterExt;
use crate::util::local_context;
use crate::util::progress_logger::ProgressLogger;
use crate::util::progress_logger::ProgressSession;
use id_collections::IdVec;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FuncSpec {
    old_id: first_ord::CustomFuncId,
    subst: IdVec<ModeParam, Mode>,
}

type FuncInstances = InstanceQueue<FuncSpec, CustomFuncId>;

fn join_inner_obligations(
    interner: &Interner,
    customs: &annot::CustomTypes,
    seen: &mut BTreeSet<(first_ord::CustomTypeId, Vec<Res<Mode, Lt>>)>,
    shape: &Shape,
    res: &[Res<Mode, Lt>],
) -> Lt {
    match &*shape.inner {
        ShapeInner::Bool | ShapeInner::Num(_) => Lt::Empty,
        ShapeInner::Tuple(shapes) => {
            iter_shapes(shapes, res).fold(Lt::Empty, |acc, (shape, res)| {
                let ob = join_inner_obligations(interner, customs, seen, shape, res);
                acc.join(interner, &ob)
            })
        }
        ShapeInner::Variants(shapes) => {
            iter_shapes(shapes.as_slice(), res).fold(Lt::Empty, |acc, (shape, res)| {
                let ob = join_inner_obligations(interner, customs, seen, shape, res);
                acc.join(interner, &ob)
            })
        }
        &ShapeInner::Custom(id) | &ShapeInner::SelfCustom(id) => {
            let this = (id, res.to_vec());
            if !seen.contains(&this) {
                seen.insert(this);
                let custom = &customs.types[id];
                join_inner_obligations(
                    interner,
                    customs,
                    seen,
                    &custom.content,
                    &custom.subst_helper.do_subst(res),
                )
            } else {
                Lt::Empty
            }
        }
        ShapeInner::Array(shape) | ShapeInner::HoleArray(shape) | ShapeInner::Boxed(shape) => {
            let HeapModes { access, storage } = *res[0].modes.unwrap_heap();
            if access == Mode::Borrowed && storage == Mode::Owned {
                let ob = join_inner_obligations(interner, customs, seen, shape, &res[1..]);
                res[0].lt.join(interner, &ob)
            } else {
                Lt::Empty
            }
        }
    }
}

fn get_occur_obligation_impl(
    interner: &Interner,
    customs: &annot::CustomTypes,
    occur_path: &Path,
    shape: &Shape,
    slot: usize,
    src: &[Res<Mode, Lt>],
    dst: &[Res<Mode, Lt>],
    out: &mut BTreeMap<SlotId, Lt>,
) {
    match &*shape.inner {
        ShapeInner::Bool | ShapeInner::Num(_) => {}
        ShapeInner::Tuple(shapes) => {
            let iter = enumerate_shapes(shapes, src, slot).zip_eq(iter_shapes(shapes, dst));
            for ((shape, (slot, _), src), (_, dst)) in iter {
                get_occur_obligation_impl(
                    interner, customs, occur_path, shape, slot, src, dst, out,
                );
            }
        }
        ShapeInner::Variants(shapes) => {
            let iter = enumerate_shapes(shapes.as_slice(), src, slot)
                .zip_eq(iter_shapes(shapes.as_slice(), dst));
            for ((shape, (slot, _), src), (_, dst)) in iter {
                get_occur_obligation_impl(
                    interner, customs, occur_path, shape, slot, src, dst, out,
                );
            }
        }
        // Since non-trivial cyclic customs are always guarded, this case only occurs if the custom
        // is trivial, i.e. has no slots.
        ShapeInner::SelfCustom(_) => {
            debug_assert_eq!(src.len(), 0);
            debug_assert_eq!(dst.len(), 0);
        }
        ShapeInner::Custom(id) => {
            let custom = &customs.types[id];
            get_occur_obligation_impl(
                interner,
                customs,
                occur_path,
                &custom.content,
                slot,
                // We are on the stack. The custom is acyclic and the substitution is trivial.
                src,
                dst,
                out,
            )
        }
        ShapeInner::Array(_shape) | ShapeInner::HoleArray(_shape) | ShapeInner::Boxed(_shape) => {
            let src_mode = *src[0].modes.unwrap_stack();
            let dst_mode = *dst[0].modes.unwrap_stack();
            let dst_lt = &dst[0].lt;

            let ob = match (src_mode, dst_mode) {
                (Mode::Owned, Mode::Borrowed) => {
                    // let inner = join_inner_obligations(
                    //     interner,
                    //     customs,
                    //     &mut BTreeSet::new(),
                    //     shape,
                    //     &dst[1..],
                    // );
                    // dst_lt.join(interner, &inner)
                    dst_lt.clone()
                }
                _ => occur_path.as_lt(interner),
            };

            out.insert_vacant(SlotId(slot), ob);
        }
    }
}

fn get_occur_obligation(
    interner: &Interner,
    customs: &annot::CustomTypes,
    occur_path: &Path,
    shape: &Shape,
    src: &[Res<Mode, Lt>],
    dst: &[Res<Mode, Lt>],
) -> StackLt {
    let mut data = BTreeMap::new();
    get_occur_obligation_impl(interner, customs, occur_path, shape, 0, src, dst, &mut data);

    debug_assert_eq!(
        data.keys().copied().collect::<BTreeSet<_>>(),
        shape.top_level_slots(customs.view_shapes())
    );

    StackLt {
        shape: shape.clone(),
        data,
    }
}

fn instantiate_type_with<M, L>(ty: &annot::Type<M, L>, f: impl Fn(&M) -> Mode) -> Type {
    Type::new(
        ty.shape().clone(),
        ty.res().map_refs(|_, res| res.modes.map(&f)),
    )
}

fn instantiate_type(
    inst_params: &IdVec<ModeParam, Mode>,
    ty: &annot::Type<ModeSolution, Lt>,
) -> Type {
    instantiate_type_with(ty, |solution| solution.lb.instantiate(inst_params))
}

fn instantiate_occur(
    inst_params: &IdVec<ModeParam, Mode>,
    occur: &annot::Occur<ModeSolution, Lt>,
) -> Occur {
    Occur {
        id: occur.id,
        ty: instantiate_type(inst_params, &occur.ty),
    }
}

struct LocalInfo {
    shape: Shape,
    ob: StackLt,
    res: IdVec<SlotId, Res<Mode, Lt>>,
    metadata: Metadata,
}

type LocalContext = local_context::LocalContext<guard::LocalId, LocalInfo>;

fn add_unused_local<M>(
    customs: &annot::CustomTypes,
    ctx: &mut LocalContext,
    ty: &Type,
    orig_ty: &annot::Type<M, Lt>,
    metadata: &Metadata,
) -> guard::LocalId {
    let ob = StackLt {
        shape: ty.shape().clone(),
        data: ty
            .shape()
            .top_level_slots(customs.view_shapes())
            .into_iter()
            .map(|slot| (slot, Lt::Empty))
            .collect(),
    };

    let modes = ty.res().values().cloned();
    let lts = orig_ty.res().values().map(|res| res.lt.clone());
    let res = modes
        .zip(lts)
        .map(|(modes, lt)| Res { modes, lt })
        .collect::<Vec<_>>();

    let info = LocalInfo {
        shape: ty.shape().clone(),
        ob,
        res: IdVec::from_vec(res),
        metadata: metadata.clone(),
    };
    ctx.add_local(info)
}

fn annot_expr(
    interner: &Interner,
    customs: &annot::CustomTypes,
    funcs: &IdVec<first_ord::CustomFuncId, annot::FuncDef>,
    func_renderer: &FuncRenderer<first_ord::CustomFuncId>,
    insts: &mut FuncInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    path: &Path,
    ctx: &mut LocalContext,
    expr: &annot::Expr<ModeSolution, Lt>,
    ret_ty: &Type,
) -> Expr {
    let handle_occur =
        |ctx: &mut LocalContext, path: &Path, orig_occur: &annot::Occur<ModeSolution, _>| {
            let occur = instantiate_occur(inst_params, orig_occur);
            let src = ctx.local_binding_mut(occur.id);

            let dst_modes = occur.ty.res().values().cloned();
            let dst_lts = orig_occur.ty.res().values().map(|res| res.lt.clone());
            let dst = dst_modes
                .zip(dst_lts)
                .map(|(modes, lt)| Res { modes, lt })
                .collect::<Vec<_>>();

            debug_assert_eq!(&src.shape, occur.ty.shape());
            let obligation = get_occur_obligation(
                interner,
                customs,
                path,
                &src.shape,
                src.res.as_slice(),
                &dst,
            );

            // We must update the lifetime obligation of the binding to reflect this occurrence.
            src.ob = src.ob.join(interner, &obligation);

            occur
        };

    match expr {
        annot::Expr::Local(occur) => Expr::Local(handle_occur(ctx, path, occur)),

        annot::Expr::Call(purity, func_id, arg) => {
            let func = &funcs[*func_id];
            let arg = handle_occur(ctx, path, arg);

            // Mode inference solves for all functions in an SCC jointly and annotates each function
            // with the complete set of signature vairables for the SCC. Therefore, in general,
            // `arg.ty` and `ret_ty` constrain only a subset of the parameters. It suffices to let
            // the rest of the parameters be `Mode::Borrow`, which will ultimately result in them
            // being assigned their minimal solutions according to the signature constraints.
            let mut call_params =
                IdVec::from_count_with(func.constrs.sig.count(), |_| Mode::Borrowed);

            for (param, value) in func.arg_ty.iter_modes().zip_eq(arg.ty.res().values()) {
                match (param, value) {
                    (ResModes::Stack(param), ResModes::Stack(value)) => {
                        call_params[*param] = *value;
                    }
                    (ResModes::Heap(param), ResModes::Heap(value)) => {
                        call_params[param.access] = value.access;
                        call_params[param.storage] = value.storage;
                    }
                    _ => unreachable!(),
                }
            }
            for (param, value) in func.ret_ty.iter_modes().zip_eq(ret_ty.res().values()) {
                match (param, value) {
                    (ResModes::Stack(param), ResModes::Stack(value)) => {
                        call_params[*param] = *value;
                    }
                    (ResModes::Heap(param), ResModes::Heap(value)) => {
                        call_params[param.access] = value.access;
                        call_params[param.storage] = value.storage;
                    }
                    _ => unreachable!(),
                }
            }

            let call_subst = func
                .constrs
                .sig
                .map_refs(|_, solution| solution.instantiate(&call_params));

            let new_func_id = insts.resolve(FuncSpec {
                old_id: *func_id,
                subst: call_subst,
            });

            Expr::Call(*purity, new_func_id, arg)
        }

        // We use `with_scope` to express our intent. In fact, all the bindings we add are popped
        // from the context before we return.
        annot::Expr::LetMany(bindings, ret) => ctx.with_scope(|ctx| {
            let mut new_exprs = Vec::new();
            for (i, (ty, expr, metadata)) in bindings.into_iter().enumerate() {
                let ret_ty = instantiate_type(inst_params, &ty);
                let new_expr = annot_expr(
                    interner,
                    customs,
                    funcs,
                    func_renderer,
                    insts,
                    inst_params,
                    &path.seq(i),
                    ctx,
                    expr,
                    &ret_ty,
                );
                let _ = add_unused_local(customs, ctx, &ret_ty, &ty, metadata);
                new_exprs.push(new_expr);
            }

            let ret_occur = handle_occur(ctx, &path.seq(bindings.len()), ret);

            let mut new_bindings_rev = Vec::new();

            for expr in new_exprs.into_iter().rev() {
                let (_, info) = ctx.pop_local();
                let ty = Type::new(info.shape, info.res.map_refs(|_, res| res.modes.clone()));
                new_bindings_rev.push((ty, info.ob, expr, info.metadata));
            }

            let new_bindings = {
                new_bindings_rev.reverse();
                new_bindings_rev
            };

            Expr::LetMany(new_bindings, ret_occur)
        }),

        annot::Expr::If(discrim, then_case, else_case) => {
            let discrim = handle_occur(ctx, &path.seq(0), discrim);
            let then_case = annot_expr(
                interner,
                customs,
                funcs,
                func_renderer,
                insts,
                inst_params,
                &path.seq(1).alt(0, 2),
                ctx,
                then_case,
                ret_ty,
            );
            let else_case = annot_expr(
                interner,
                customs,
                funcs,
                func_renderer,
                insts,
                inst_params,
                &path.seq(1).alt(1, 2),
                ctx,
                else_case,
                ret_ty,
            );
            Expr::If(discrim, Box::new(then_case), Box::new(else_case))
        }

        annot::Expr::CheckVariant(variant_id, variant) => {
            Expr::CheckVariant(*variant_id, handle_occur(ctx, path, variant))
        }

        annot::Expr::Unreachable(ty) => Expr::Unreachable(instantiate_type(inst_params, ty)),

        annot::Expr::Tuple(fields) => {
            let fields = fields
                .into_iter()
                .enumerate()
                .map(|(i, occur)| handle_occur(ctx, &path.seq(i), occur))
                .collect();
            Expr::Tuple(fields)
        }

        annot::Expr::TupleField(tup, idx) => Expr::TupleField(handle_occur(ctx, path, tup), *idx),

        annot::Expr::WrapVariant(variants, variant, content) => Expr::WrapVariant(
            variants.map_refs(|_, ty| instantiate_type(inst_params, ty)),
            *variant,
            handle_occur(ctx, path, content),
        ),

        annot::Expr::UnwrapVariant(variant, wrapped) => {
            Expr::UnwrapVariant(*variant, handle_occur(ctx, path, wrapped))
        }

        annot::Expr::WrapBoxed(content, output_ty) => Expr::WrapBoxed(
            handle_occur(ctx, path, content),
            instantiate_type(inst_params, output_ty),
        ),

        annot::Expr::UnwrapBoxed(wrapped, input_ty, output_ty) => Expr::UnwrapBoxed(
            handle_occur(ctx, path, wrapped),
            instantiate_type(inst_params, input_ty),
            instantiate_type(inst_params, output_ty),
        ),

        annot::Expr::WrapCustom(id, content) => {
            Expr::WrapCustom(*id, handle_occur(ctx, path, content))
        }

        annot::Expr::UnwrapCustom(id, wrapped) => {
            Expr::UnwrapCustom(*id, handle_occur(ctx, path, wrapped))
        }

        annot::Expr::Intrinsic(intrinsic, occur) => {
            Expr::Intrinsic(*intrinsic, handle_occur(ctx, path, occur))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Get(arr, idx, ty)) => {
            let idx = handle_occur(ctx, path, idx);
            let arr = handle_occur(ctx, path, arr);
            Expr::ArrayOp(ArrayOp::Get(arr, idx, instantiate_type(inst_params, &ty)))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Extract(arr, idx)) => {
            let idx = handle_occur(ctx, path, idx);
            let arr = handle_occur(ctx, path, arr);
            Expr::ArrayOp(ArrayOp::Extract(arr, idx))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Len(arr)) => {
            Expr::ArrayOp(ArrayOp::Len(handle_occur(ctx, path, arr)))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Push(arr, item)) => {
            let item = handle_occur(ctx, path, item);
            let arr = handle_occur(ctx, path, arr);
            Expr::ArrayOp(ArrayOp::Push(arr, item))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Pop(arr)) => {
            Expr::ArrayOp(ArrayOp::Pop(handle_occur(ctx, path, arr)))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Replace(arr, item)) => {
            let item = handle_occur(ctx, path, item);
            let arr = handle_occur(ctx, path, arr);
            Expr::ArrayOp(ArrayOp::Replace(arr, item))
        }
        annot::Expr::ArrayOp(annot::ArrayOp::Reserve(arr, cap)) => {
            let cap = handle_occur(ctx, path, cap);
            let arr = handle_occur(ctx, path, arr);
            Expr::ArrayOp(ArrayOp::Reserve(arr, cap))
        }
        annot::Expr::IoOp(annot::IoOp::Input) => Expr::IoOp(IoOp::Input),
        annot::Expr::IoOp(annot::IoOp::Output(occur)) => {
            Expr::IoOp(IoOp::Output(handle_occur(ctx, path, occur)))
        }

        annot::Expr::Panic(ret_ty, occur) => Expr::Panic(
            instantiate_type(inst_params, &ret_ty),
            handle_occur(ctx, path, occur),
        ),
        annot::Expr::ArrayLit(ty, elems) => {
            let elems = elems
                .into_iter()
                .enumerate()
                .map(|(i, occur)| handle_occur(ctx, &path.seq(i), occur))
                .collect();

            Expr::ArrayLit(instantiate_type(inst_params, &ty), elems)
        }

        annot::Expr::BoolLit(lit) => Expr::BoolLit(*lit),
        annot::Expr::ByteLit(lit) => Expr::ByteLit(*lit),
        annot::Expr::IntLit(lit) => Expr::IntLit(*lit),
        annot::Expr::FloatLit(lit) => Expr::FloatLit(*lit),
    }
}

fn annot_func(
    interner: &Interner,
    customs: &annot::CustomTypes,
    funcs: &IdVec<first_ord::CustomFuncId, annot::FuncDef>,
    func_renderer: &FuncRenderer<first_ord::CustomFuncId>,
    func_insts: &mut FuncInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    id: first_ord::CustomFuncId,
) -> FuncDef {
    let func = &funcs[id];

    let mut ctx = LocalContext::new();
    let arg_ty = instantiate_type_with(&func.arg_ty, |param| inst_params[*param]);
    let arg_id = add_unused_local(
        customs,
        &mut ctx,
        &arg_ty,
        &func.arg_ty,
        &Metadata::default(),
    );
    debug_assert_eq!(arg_id, guard::ARG_LOCAL);

    let ret_ty = instantiate_type_with(&func.ret_ty, |param| inst_params[*param]);

    let body = annot_expr(
        interner,
        customs,
        funcs,
        func_renderer,
        func_insts,
        inst_params,
        &annot::FUNC_BODY_PATH(),
        &mut ctx,
        &func.body,
        &ret_ty,
    );

    let (_, arg_info) = ctx.pop_local();
    FuncDef {
        purity: func.purity,
        arg_ty,
        ret_ty,
        arg_obligation: arg_info.ob,
        body,
        profile_point: func.profile_point,
    }
}

pub fn annot_obligations(
    interner: &Interner,
    program: annot::Program,
    progress: impl ProgressLogger,
) -> ob::Program {
    let mut progress = progress.start_session(Some(program.funcs.len()));
    let mut func_insts = FuncInstances::new();

    let main_params = program.funcs[program.main]
        .constrs
        .sig
        .map_refs(|_, solution| solution.lb_const);
    let main = func_insts.resolve(FuncSpec {
        old_id: program.main,
        subst: main_params,
    });

    let mut funcs = IdVec::new();
    let mut func_symbols = IdVec::new();

    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);
    while let Some((new_id, spec)) = func_insts.pop_pending() {
        let annot = annot_func(
            interner,
            &program.custom_types,
            &program.funcs,
            &func_renderer,
            &mut func_insts,
            &spec.subst,
            spec.old_id,
        );

        let pushed_id1 = funcs.push(annot);
        let pushed_id2 = func_symbols.push(program.func_symbols[spec.old_id].clone());
        debug_assert_eq!(pushed_id1, new_id);
        debug_assert_eq!(pushed_id2, new_id);
        progress.update(1);
    }

    progress.finish();

    let custom_types = ob::CustomTypes {
        types: IdVec::from_vec(
            program
                .custom_types
                .types
                .into_values()
                .map(|typedef| ob::CustomTypeDef {
                    content: typedef.content,
                    subst_helper: typedef.subst_helper,
                })
                .collect(),
        ),
    };

    ob::Program {
        mod_symbols: program.mod_symbols,
        custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs,
        profile_points: program.profile_points,
        func_symbols,
        main,
    }
}
