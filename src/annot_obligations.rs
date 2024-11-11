use crate::data::borrow_model as model;
use crate::data::first_order_ast::{self as first_ord};
use crate::data::flat_ast as flat;
use crate::data::guarded_ast as guard;
use crate::data::metadata::Metadata;
use crate::data::mode_annot_ast::{
    self as annot, Lt, LtParam, Mode, ModeParam, ModeSolution, Path, Position, Res, ResModes,
    ShapeInner,
};
use crate::data::obligation_annot_ast::{
    self as ob, wrap_lts, ArrayOp, BindRes, BindType, CustomFuncId, CustomTypeId, Expr, FuncDef,
    IoOp, Occur, RetType, Shape, Type, ValueRes,
};
use crate::data::profile as prof;
use crate::data::purity::Purity;
use crate::data::resolved_ast as res;
use crate::intrinsic_config::intrinsic_sig;
use crate::pretty_print::utils::{CustomTypeRenderer, FuncRenderer};
use crate::util::instance_queue::InstanceQueue;
use crate::util::iter::IterExt;
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::ProgressLogger;
use crate::util::progress_logger::ProgressSession;
use id_collections::{Count, Id, IdMap, IdVec};
use id_graph_sccs::{find_components, Scc, SccKind, Sccs};
use std::collections::{BTreeMap, BTreeSet};

type Interner = annot::Interner<CustomTypeId>;

// --------------------
// Step 1: Mode solving
// --------------------
// Solve the mode constraints for concrete modes and perform monomorphization with respect to those
// mode choices.

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FuncSpec {
    old_id: first_ord::CustomFuncId,
    subst: IdVec<ModeParam, Mode>,
}

type FuncInstances = InstanceQueue<FuncSpec, CustomFuncId>;

fn solve_type_full(
    inst_params: &IdVec<ModeParam, Mode>,
    ty: &annot::Type<annot::Res<ModeSolution, Lt>, first_ord::CustomTypeId>,
) -> annot::Type<ResModes<Mode>, CustomTypeId> {
    let res = ty
        .res()
        .map_refs(|_, res| res.modes.map(|mode| mode.lb.instantiate(inst_params)));
    annot::Type::new(ty.shape().clone(), res)
}

fn solve_occur_full(
    inst_params: &IdVec<ModeParam, Mode>,
    occur: &annot::Occur<Res<ModeSolution, Lt>, first_ord::CustomTypeId>,
) -> annot::Occur<ResModes<Mode>, CustomTypeId> {
    annot::Occur {
        id: occur.id,
        ty: solve_type_full(inst_params, &occur.ty),
    }
}

fn solve_type(
    inst_params: &IdVec<ModeParam, Mode>,
    ty: &annot::Type<annot::Res<ModeSolution, Lt>, first_ord::CustomTypeId>,
) -> annot::Type<Mode, CustomTypeId> {
    let res = ty
        .res()
        .map_refs(|_, res| res.modes.stack_or_storage().lb.instantiate(inst_params));
    annot::Type::new(ty.shape().clone(), res)
}

fn solve_occur(
    inst_params: &IdVec<ModeParam, Mode>,
    occur: &annot::Occur<Res<ModeSolution, Lt>, first_ord::CustomTypeId>,
) -> annot::Occur<Mode, CustomTypeId> {
    annot::Occur {
        id: occur.id,
        ty: solve_type(inst_params, &occur.ty),
    }
}

fn strip_access(ty: &annot::Type<ResModes<Mode>, CustomTypeId>) -> annot::Type<Mode, CustomTypeId> {
    let res = ty.res().map_refs(|_, res| *res.stack_or_storage());
    annot::Type::new(ty.shape().clone(), res)
}

struct LocalInfo1 {
    ty: annot::Type<ResModes<Mode>, CustomTypeId>,
    metadata: Metadata,
}

fn solve_expr(
    interner: &Interner,
    customs: &annot::CustomTypes<first_ord::CustomTypeId, flat::CustomTypeSccId>,
    funcs: &IdVec<first_ord::CustomFuncId, annot::FuncDef>,
    func_renderer: &FuncRenderer<first_ord::CustomFuncId>,
    insts: &mut FuncInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    path: &Path,
    ctx: &mut LocalContext<guard::LocalId, LocalInfo1>,
    expr: &annot::Expr<Res<ModeSolution, Lt>, first_ord::CustomTypeId, first_ord::CustomFuncId>,
    fut_ty: &annot::Type<ResModes<Mode>, CustomTypeId>,
) -> annot::Expr<Mode, CustomTypeId, CustomFuncId> {
    match expr {
        annot::Expr::Local(occur) => annot::Expr::Local(solve_occur(inst_params, occur)),

        annot::Expr::Call(purity, func_id, arg) => {
            let func = &funcs[*func_id];
            let arg = solve_occur_full(inst_params, arg);

            // Mode inference solves for all functions in an SCC jointly and annotates each function
            // with the complete set of signature vairables for the SCC. Therefore, in general,
            // `arg.ty` and `ret_ty` constrain only a subset of the parameters. It suffices to let
            // the rest of the parameters be `Mode::Borrow`, which will ultimately result in them
            // being assigned their minimal solutions according to the signature constraints.
            let mut call_params =
                IdVec::from_count_with(func.constrs.sig.count(), |_| Mode::Borrowed);

            for (param, value) in func.arg_ty.iter_modes().zip_eq(arg.ty.iter()) {
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
            for (param, value) in func.ret_ty.iter_modes().zip_eq(fut_ty.iter()) {
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

            let arg = annot::Occur {
                id: arg.id,
                ty: strip_access(&arg.ty),
            };
            annot::Expr::Call(*purity, new_func_id, arg)
        }

        // We use `with_scope` to express our intent. In fact, all the bindings we add are popped
        // from the context before we return.
        annot::Expr::LetMany(bindings, ret) => ctx.with_scope(|ctx| {
            let locals_offset = ctx.len();

            for (binding_ty, _, _) in bindings {
                let _ = ctx.add_local(LocalInfo1 {
                    ty: solve_type_full(inst_params, binding_ty),
                    metadata: Metadata::default(),
                });
            }

            let mut new_bindings_rev = Vec::new();
            for (i, (_, expr, metadata)) in bindings.into_iter().enumerate().rev() {
                let local = guard::LocalId(locals_offset + i);

                let ret_ty = ctx.local_binding(local).ty.clone();

                // Only retain the locals *strictly* before this binding.
                ctx.truncate(Count::from_value(local.0));

                let new_expr = solve_expr(
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

                new_bindings_rev.push((strip_access(&ret_ty), new_expr, metadata.clone()));
            }

            let ret_occur = solve_occur(inst_params, ret);

            let new_bindings = {
                new_bindings_rev.reverse();
                new_bindings_rev
            };

            annot::Expr::LetMany(new_bindings, ret_occur)
        }),

        annot::Expr::If(discrim, then_case, else_case) => {
            let else_case = solve_expr(
                interner,
                customs,
                funcs,
                func_renderer,
                insts,
                inst_params,
                &path.seq(1).alt(1, 2),
                ctx,
                else_case,
                fut_ty,
            );
            let then_case = solve_expr(
                interner,
                customs,
                funcs,
                func_renderer,
                insts,
                inst_params,
                &path.seq(1).alt(0, 2),
                ctx,
                then_case,
                fut_ty,
            );
            let discrim = solve_occur(inst_params, discrim);
            annot::Expr::If(discrim, Box::new(then_case), Box::new(else_case))
        }

        annot::Expr::CheckVariant(variant_id, variant) => {
            annot::Expr::CheckVariant(*variant_id, solve_occur(inst_params, variant))
        }

        annot::Expr::Unreachable(ty) => annot::Expr::Unreachable(solve_type(inst_params, ty)),

        annot::Expr::Tuple(fields) => {
            let mut fields_rev = fields
                .into_iter()
                .rev()
                .map(|occur| solve_occur(inst_params, occur))
                .collect::<Vec<_>>();
            let fields = {
                fields_rev.reverse();
                fields_rev
            };
            annot::Expr::Tuple(fields)
        }

        annot::Expr::TupleField(tup, idx) => {
            annot::Expr::TupleField(solve_occur(inst_params, tup), *idx)
        }

        annot::Expr::WrapVariant(variants, variant, content) => annot::Expr::WrapVariant(
            variants.map_refs(|_, ty| solve_type(inst_params, ty)),
            *variant,
            solve_occur(inst_params, content),
        ),

        annot::Expr::UnwrapVariant(variant, wrapped) => {
            annot::Expr::UnwrapVariant(*variant, solve_occur(inst_params, wrapped))
        }

        annot::Expr::WrapBoxed(content, output_ty) => annot::Expr::WrapBoxed(
            solve_occur(inst_params, content),
            solve_type(inst_params, output_ty),
        ),

        annot::Expr::UnwrapBoxed(wrapped, output_ty) => annot::Expr::UnwrapBoxed(
            solve_occur(inst_params, wrapped),
            solve_type(inst_params, output_ty),
        ),

        annot::Expr::WrapCustom(id, recipe, content) => {
            annot::Expr::WrapCustom(*id, recipe.clone(), solve_occur(inst_params, content))
        }

        annot::Expr::UnwrapCustom(id, recipe, wrapped) => {
            annot::Expr::UnwrapCustom(*id, recipe.clone(), solve_occur(inst_params, wrapped))
        }

        annot::Expr::Intrinsic(intr, arg) => {
            let ty = solve_type(&IdVec::new(), &arg.ty);
            annot::Expr::Intrinsic(*intr, annot::Occur { id: arg.id, ty })
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Get(arr, idx, ty)) => {
            let arr = solve_occur(inst_params, arr);
            let idx = solve_occur(inst_params, idx);
            let ty = solve_type(inst_params, ty);
            annot::Expr::ArrayOp(annot::ArrayOp::Get(arr, idx, ty))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Extract(arr, idx)) => {
            let arr = solve_occur(inst_params, arr);
            let idx = solve_occur(inst_params, idx);
            annot::Expr::ArrayOp(annot::ArrayOp::Extract(arr, idx))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Len(arr)) => {
            let arr = solve_occur(inst_params, arr);
            annot::Expr::ArrayOp(annot::ArrayOp::Len(arr))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Push(arr, item)) => {
            let arr = solve_occur(inst_params, arr);
            let item = solve_occur(inst_params, item);
            annot::Expr::ArrayOp(annot::ArrayOp::Push(arr, item))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Pop(arr)) => {
            let arr = solve_occur(inst_params, arr);
            annot::Expr::ArrayOp(annot::ArrayOp::Pop(arr))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Replace(hole, item)) => {
            let hole = solve_occur(inst_params, hole);
            let item = solve_occur(inst_params, item);
            annot::Expr::ArrayOp(annot::ArrayOp::Replace(hole, item))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Reserve(arr, cap)) => {
            let arr = solve_occur(inst_params, arr);
            let cap = solve_occur(inst_params, cap);
            annot::Expr::ArrayOp(annot::ArrayOp::Reserve(arr, cap))
        }

        annot::Expr::IoOp(annot::IoOp::Input) => annot::Expr::IoOp(annot::IoOp::Input),

        annot::Expr::IoOp(annot::IoOp::Output(arr)) => {
            let arr = solve_occur(inst_params, arr);
            annot::Expr::IoOp(annot::IoOp::Output(arr))
        }

        annot::Expr::Panic(ret_ty, msg) => {
            let ret_ty = solve_type(inst_params, ret_ty);
            let msg = solve_occur(inst_params, msg);
            annot::Expr::Panic(ret_ty, msg)
        }

        annot::Expr::ArrayLit(item_ty, items) => {
            let item_ty = solve_type(inst_params, item_ty);
            let items = items
                .iter()
                .map(|item| solve_occur(inst_params, item))
                .collect();
            annot::Expr::ArrayLit(item_ty, items)
        }

        annot::Expr::BoolLit(val) => annot::Expr::BoolLit(*val),

        annot::Expr::ByteLit(val) => annot::Expr::ByteLit(*val),

        annot::Expr::IntLit(val) => annot::Expr::IntLit(*val),

        annot::Expr::FloatLit(val) => annot::Expr::FloatLit(*val),
    }
}

#[derive(Clone, Debug)]

pub struct SolvedFuncDef {
    pub purity: Purity,
    pub arg_ty: annot::Type<Mode, CustomTypeId>,
    pub ret_ty: annot::Type<Mode, CustomTypeId>,

    pub body: annot::Expr<Mode, CustomTypeId, CustomFuncId>,
    pub profile_point: Option<prof::ProfilePointId>,
}

#[derive(Clone, Debug)]
pub struct SolvedProgram {
    pub mod_symbols: IdVec<res::ModId, res::ModSymbols>,
    pub custom_types: annot::CustomTypes<CustomTypeId, ob::CustomTypeSccId>,
    pub custom_type_symbols: IdVec<CustomTypeId, first_ord::CustomTypeSymbols>,
    pub funcs: IdVec<CustomFuncId, SolvedFuncDef>,
    pub func_symbols: IdVec<CustomFuncId, first_ord::FuncSymbols>,
    pub profile_points: IdVec<prof::ProfilePointId, prof::ProfilePoint>,
    pub main: CustomFuncId,
}

fn solve_func(
    interner: &Interner,
    customs: &annot::CustomTypes<first_ord::CustomTypeId, flat::CustomTypeSccId>,
    funcs: &IdVec<first_ord::CustomFuncId, annot::FuncDef>,
    func_renderer: &FuncRenderer<first_ord::CustomFuncId>,
    func_insts: &mut FuncInstances,
    inst_params: &IdVec<ModeParam, Mode>,
    id: first_ord::CustomFuncId,
) -> SolvedFuncDef {
    let func = &funcs[id];

    let mut ctx = LocalContext::new();
    let arg_id = ctx.add_local(LocalInfo1 {
        ty: annot::Type::new(
            func.arg_ty.shape().clone(),
            func.arg_ty
                .res()
                .map_refs(|_, res| res.modes.map(|mode| inst_params[*mode])),
        ),
        metadata: Metadata::default(),
    });

    debug_assert_eq!(arg_id, guard::ARG_LOCAL);

    let ret_ty = annot::Type::new(
        func.ret_ty.shape().clone(),
        func.ret_ty
            .res()
            .map_refs(|_, res| res.modes.map(|mode| inst_params[*mode])),
    );

    let body = solve_expr(
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
    SolvedFuncDef {
        purity: func.purity,
        arg_ty: strip_access(&arg_info.ty),
        ret_ty: strip_access(&ret_ty),
        body,
        profile_point: func.profile_point,
    }
}

pub fn solve_program(interner: &Interner, program: annot::Program) -> SolvedProgram {
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
        let solved = solve_func(
            interner,
            &program.custom_types,
            &program.funcs,
            &func_renderer,
            &mut func_insts,
            &spec.subst,
            spec.old_id,
        );

        let pushed_id1 = funcs.push(solved);
        let pushed_id2 = func_symbols.push(program.func_symbols[spec.old_id].clone());
        debug_assert_eq!(pushed_id1, new_id);
        debug_assert_eq!(pushed_id2, new_id);
    }

    SolvedProgram {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs,
        profile_points: program.profile_points,
        func_symbols,
        main,
    }
}

// ----------------------------------
// Step 2: Lifetime inference (again)
// ----------------------------------
// Perform flow analysis to recompute lifetimes, this time mediated by the concrete modes we have
// inferred.

struct LocalInfo2 {
    ty: BindType,
    metadata: Metadata,
}

fn init_bind_res<L>(
    customs: &annot::CustomTypes<first_ord::CustomTypeId, flat::CustomTypeSccId>,
    ty: &annot::Type<Mode, CustomTypeId>,
    mut f: impl FnMut() -> L,
) -> annot::Type<BindRes<L>, CustomTypeId> {
    let pos = ty.shape().positions(&customs.types, &customs.sccs);
    let res = ty
        .res()
        .values()
        .zip_eq(pos.iter())
        .map(|(mode, pos)| match mode {
            Mode::Borrowed => BindRes::Borrowed(f()),
            Mode::Owned => match pos {
                Position::Stack => BindRes::StackOwned(f()),
                Position::Heap => BindRes::HeapOwned,
            },
        })
        .collect();
    annot::Type::new(ty.shape().clone(), IdVec::from_vec(res))
}

fn init_value_res<L>(
    ty: &annot::Type<Mode, CustomTypeId>,
    mut f: impl FnMut() -> L,
) -> annot::Type<ValueRes<L>, CustomTypeId> {
    let res = ty
        .res()
        .values()
        .map(|mode| match mode {
            Mode::Borrowed => ValueRes::Borrowed(f()),
            Mode::Owned => ValueRes::Owned,
        })
        .collect();
    annot::Type::new(ty.shape().clone(), IdVec::from_vec(res))
}

fn as_value_type(ty: &BindType) -> Type {
    let f = |res: &BindRes<Lt>| match res {
        BindRes::StackOwned(_) => ValueRes::Owned,
        BindRes::HeapOwned => ValueRes::Owned,
        BindRes::Borrowed(lt) => ValueRes::Borrowed(lt.clone()),
    };
    annot::Type::new(
        ty.shape().clone(),
        IdVec::from_vec(ty.iter().map(f).collect()),
    )
}

fn join_everywhere(interner: &Interner, ty: &Type, new_lt: &Lt) -> Type {
    let f = |res: &ValueRes<Lt>| match res {
        ValueRes::Owned => ValueRes::Owned,
        ValueRes::Borrowed(lt) => ValueRes::Borrowed(lt.join(interner, new_lt)),
    };
    annot::Type::new(
        ty.shape().clone(),
        IdVec::from_vec(ty.iter().map(f).collect()),
    )
}

fn lt_equiv(ty1: &BindType, ty2: &BindType) -> bool {
    debug_assert!(ty1.shape() == ty2.shape());
    ty1.iter()
        .zip_eq(ty2.iter())
        .all(|(res1, res2)| match (res1, res2) {
            (BindRes::StackOwned(lt1), BindRes::StackOwned(lt2)) => lt1 == lt2,
            (BindRes::HeapOwned, BindRes::HeapOwned) => true,
            (BindRes::Borrowed(lt1), BindRes::Borrowed(lt2)) => lt1 == lt2,
            _ => unreachable!("mismatched types"),
        })
}

fn bind_lts(interner: &Interner, ty1: &RetType, ty2: &Type) -> BTreeMap<LtParam, Lt> {
    debug_assert!(ty1.shape() == ty2.shape());
    let mut result = BTreeMap::new();
    for (res1, res2) in ty1.iter().zip_eq(ty2.iter()) {
        match (res1, res2) {
            (ValueRes::Owned, ValueRes::Owned) => {}
            (ValueRes::Borrowed(param), ValueRes::Borrowed(value)) => {
                result
                    .entry(*param)
                    .and_modify(|old: &mut Lt| *old = old.join(interner, &value))
                    .or_insert_with(|| value.clone());
            }
            (ValueRes::Owned, ValueRes::Borrowed(_)) => unreachable!("impossible by construction"),
            (ValueRes::Borrowed(_), ValueRes::Owned) => unreachable!("impossible by construction"),
        };
    }
    result
}

fn subst_lts(interner: &Interner, ty: &Type, subst: &BTreeMap<LtParam, Lt>) -> Type {
    let f = |res: &ValueRes<Lt>| match res {
        ValueRes::Owned => ValueRes::Owned,
        ValueRes::Borrowed(lt) => {
            let new_lt = match &lt {
                Lt::Empty => Lt::Empty,
                Lt::Local(lt) => Lt::Local(lt.clone()),
                Lt::Join(params) => params
                    .iter()
                    .map(|p| &subst[p])
                    .fold(Lt::Empty, |lt1, lt2| lt1.join(interner, lt2)),
            };
            ValueRes::Borrowed(new_lt)
        }
    };
    annot::Type::new(
        ty.shape().clone(),
        IdVec::from_vec(ty.iter().map(f).collect()),
    )
}

fn prepare_arg_type(interner: &Interner, path: &Path, ty: &BindType) -> Type {
    let f = |res: &BindRes<Lt>| match res {
        BindRes::StackOwned(_) => ValueRes::Owned,
        BindRes::HeapOwned => ValueRes::Owned,
        BindRes::Borrowed(lt) => {
            let effective_lt = match &lt {
                Lt::Empty => Lt::Empty,
                Lt::Local(_) => path.as_lt(interner),
                Lt::Join(vars) => Lt::Join(vars.clone()),
            };
            ValueRes::Borrowed(effective_lt)
        }
    };
    annot::Type::new(
        ty.shape().clone(),
        IdVec::from_vec(ty.iter().map(f).collect()),
    )
}

fn propagate_temporal(
    interner: &Interner,
    occur_path: &Path,
    bind_res: &BindRes<Lt>,
    use_res: &ValueRes<Lt>,
) -> BindRes<Lt> {
    match (bind_res, use_res) {
        (BindRes::StackOwned(bind_lt), ValueRes::Owned) => {
            BindRes::StackOwned(bind_lt.join(interner, &occur_path.as_lt(interner)))
        }
        (BindRes::StackOwned(bind_lt), ValueRes::Borrowed(use_lt)) => {
            BindRes::StackOwned(bind_lt.join(interner, use_lt))
        }
        (BindRes::HeapOwned, ValueRes::Owned) => BindRes::HeapOwned,
        (BindRes::HeapOwned, ValueRes::Borrowed(_)) => unreachable!("impossible by construction"),
        (BindRes::Borrowed(_), ValueRes::Owned) => unreachable!("impossible by construction"),
        (BindRes::Borrowed(bind_lt), ValueRes::Borrowed(use_lt)) => {
            BindRes::Borrowed(bind_lt.join(interner, use_lt))
        }
    }
}

fn propagate_get(interner: &Interner, input_ty: &Type, output_ty: &Type) -> Type {
    match &*input_ty.shape().inner {
        ShapeInner::Array(_) | ShapeInner::Boxed(_) => {}
        _ => unreachable!("expected array or boxed"),
    }

    let input_res = input_ty.res().as_slice();
    let input_lt = input_res[0].clone();
    let input_item_res = &input_res[1..];

    let ValueRes::Borrowed(mut input_lt) = input_lt else {
        unreachable!("impossible by construction")
    };

    for (input_item_res, output_res) in input_item_res.iter().zip_eq(output_ty.iter()) {
        match (input_item_res, output_res) {
            (ValueRes::Owned, ValueRes::Borrowed(lt)) => {
                input_lt = input_lt.join(interner, lt);
            }
            (ValueRes::Borrowed(_), ValueRes::Owned) => {
                unreachable!("impossible by construction")
            }
            (ValueRes::Owned, ValueRes::Owned) => {}
            (ValueRes::Borrowed(_), ValueRes::Borrowed(_)) => {}
        }
    }

    let mut res = vec![ValueRes::Borrowed(input_lt)];
    res.extend(input_ty.res().as_slice()[1..].iter().cloned());
    annot::Type::new(input_ty.shape().clone(), IdVec::from_vec(res))
}

fn create_occurs_from_model(
    sig: &model::Signature,
    interner: &Interner,
    path: &Path,
    args: &[&annot::Occur<Mode, CustomTypeId>],
    ret: &Type,
) -> Vec<Occur> {
    assert!(args.len() >= sig.args.fixed.len());

    // Create a fresh occurrence for each function argument.
    let mut arg_occurs = args
        .iter()
        .map(|arg| {
            let ty = init_value_res(&arg.ty, || Lt::Empty);
            Occur { id: arg.id, ty }
        })
        .collect::<Vec<_>>();

    ///////////////////////////////////////
    // Step 1: Handle constraints which arise from model lifetime variables.
    ///////////////////////////////////////

    // Set up a mapping from model lifetimes to lifetimes.
    let mut get_lt = IdVec::from_count_with(sig.lt_count, |_| None);

    for (slot, model_res) in sig.ret.get_res(&ret.shape()) {
        let res = &ret.res()[slot];

        // Update the lifetime mapping based on the return.
        match &mut get_lt[model_res.lt] {
            entry @ None => {
                if let ValueRes::Borrowed(lt) = res {
                    *entry = Some(lt.clone());
                }
            }
            Some(_) => {
                panic!("a lifetime variable cannot appear more than once in a model return type");
            }
        }
    }

    let get_lt = get_lt;

    for (i, (arg, occur)) in sig.args.iter().zip(&mut arg_occurs).enumerate() {
        for (slot, model_res) in arg.get_res(&occur.ty.shape()) {
            let res = &mut occur.ty.res_mut()[slot];

            // Substitute for model lifetimes using the mapping constructed from the return.
            if let ValueRes::Borrowed(arg_lt) = res {
                *arg_lt = if let Some(lt) = &get_lt[model_res.lt] {
                    lt.clone()
                } else if sig.unused_lts.contains(&model_res.lt) {
                    Lt::Empty
                } else {
                    annot::arg_path(path, i, args.len()).as_lt(interner)
                };
            }
        }
    }

    ///////////////////////////////////////
    // Step 2: Handle constraints which arise from repeated uses of the same model type variable.
    ///////////////////////////////////////

    // Accumulate the resources for each occurrence of each type variable.
    let mut vars = IdMap::new();
    for ((i, model), occur) in sig.args.iter().enumerate().zip(&arg_occurs) {
        model.extract_vars(
            |shape, res| Type::new(shape.clone(), IdVec::from_vec(res.to_vec())),
            model::VarOccurKind::Arg(i),
            &occur.ty.shape(),
            occur.ty.res().as_slice(),
            &mut vars,
        );
    }
    sig.ret.extract_vars(
        |shape, res| Type::new(shape.clone(), IdVec::from_vec(res.to_vec())),
        model::VarOccurKind::Ret,
        &ret.shape(),
        ret.res().as_slice(),
        &mut vars,
    );

    // At this point, it would seem natural to convert `vars` from an `IdMap` to an `IdVec`.
    // However, if the model signature has an empty variadic argument, then the `IdMap` will not
    // contain entries for any type variables which appear only in the type of that argument.

    for var_occurs in vars.values_mut() {
        // Propagate lifetimes from return occurrences of variables to argument occurrences of
        // variables.
        for ret in var_occurs.rets.iter() {
            for arg in var_occurs.args.iter_mut() {
                let loc = arg.loc;
                let arg_res =
                    &mut arg_occurs[loc.occur_idx].ty.res_mut().as_mut_slice()[loc.start..loc.end];

                for (arg_res, ret_res) in arg_res.iter_mut().zip_eq(ret.iter()) {
                    match (arg_res, ret_res) {
                        (ValueRes::Owned, ValueRes::Owned) => {}
                        (ValueRes::Borrowed(arg_lt), ValueRes::Borrowed(ret_lt)) => {
                            *arg_lt = arg_lt.join(interner, ret_lt);
                        }
                        (ValueRes::Borrowed(_), ValueRes::Owned) => {
                            unreachable!("impossible by construction")
                        }
                        (ValueRes::Owned, ValueRes::Borrowed(_)) => {
                            unreachable!("impossible by construction")
                        }
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
            model::Constr::Mode { .. } => {
                // Do nothing. These constraints are only relevant to the previous pass.
            }
            model::Constr::Lt { lhs, rhs } => {
                // We check when we construct a signature that any type variables that appear in
                // constraints also appear in the signature. This can only happen if there is an
                // empty variadic argument.
                if !vars.contains_key(lhs.type_var) || !vars.contains_key(rhs.type_var) {
                    continue;
                }

                let (lhs_vars, rhs_vars) = vars.get_pair_mut(lhs.type_var, rhs.type_var).unwrap();

                for ret in rhs_vars.rets.iter() {
                    for arg in lhs_vars.args.iter_mut() {
                        let loc = arg.loc;
                        let arg_res = &mut arg_occurs[loc.occur_idx].ty.res_mut().as_mut_slice()
                            [loc.start..loc.end];

                        for (arg_res, ret_res) in arg_res.iter_mut().zip_eq(ret.iter()) {
                            match (arg_res, ret_res) {
                                (ValueRes::Owned, ValueRes::Owned) => {}
                                (ValueRes::Borrowed(arg_lt), ValueRes::Borrowed(ret_lt)) => {
                                    *arg_lt = arg_lt.join(interner, ret_lt);
                                }
                                (ValueRes::Borrowed(_), ValueRes::Owned) => {}
                                (ValueRes::Owned, ValueRes::Borrowed(_)) => {}
                            }
                        }
                    }
                }
            }
        }
    }

    arg_occurs
}

fn propagate_occur(
    interner: &Interner,
    ctx: &mut LocalContext<guard::LocalId, LocalInfo2>,
    path: &Path,
    local: guard::LocalId,
    ty: &Type,
) {
    let binding = ctx.local_binding_mut(local);

    let new_src_res = binding
        .ty
        .res()
        .values()
        .zip_eq(ty.iter())
        .map(|(src_res, dst_res)| propagate_temporal(interner, path, src_res, dst_res))
        .collect::<Vec<_>>();

    binding.ty = annot::Type::new(binding.ty.shape().clone(), IdVec::from_vec(new_src_res));
}

fn instantiate_model(
    sig: &model::Signature,
    interner: &Interner,
    ctx: &mut LocalContext<guard::LocalId, LocalInfo2>,
    path: &annot::Path,
    args: &[&annot::Occur<Mode, CustomTypeId>],
    ret: &Type,
) -> Vec<Occur> {
    let occurs = create_occurs_from_model(sig, interner, path, args, ret);

    for (i, occur) in occurs.iter().enumerate() {
        propagate_occur(
            interner,
            ctx,
            &annot::arg_path(path, i, occurs.len()),
            occur.id,
            &occur.ty,
        );
    }

    occurs
}

#[derive(Clone, Copy, Debug)]
struct SignatureAssumptions<'a> {
    known_defs: &'a IdMap<CustomFuncId, FuncDef>,
    pending_args: &'a BTreeMap<CustomFuncId, BindType>,
    pending_rets: &'a BTreeMap<CustomFuncId, RetType>,
}

impl SignatureAssumptions<'_> {
    fn sig_of(&self, id: CustomFuncId) -> (&BindType, &RetType) {
        self.known_defs.get(id).map_or_else(
            || {
                let arg_type = self.pending_args.get(&id).unwrap();
                let ret_type = self.pending_rets.get(&id).unwrap();
                (arg_type, ret_type)
            },
            |def| (&def.arg_ty, &def.ret_ty),
        )
    }
}

fn handle_occur(
    interner: &Interner,
    ctx: &mut LocalContext<guard::LocalId, LocalInfo2>,
    path: &Path,
    occur: guard::LocalId,
    use_ty: &Type,
) -> Occur {
    // Throw out the existing lifetimes; we are recomputing them. Keep the modes.
    propagate_occur(interner, ctx, path, occur, &use_ty);
    Occur {
        id: occur,
        ty: use_ty.clone(),
    }
}

fn annot_expr(
    interner: &Interner,
    customs: &ob::CustomTypes,
    sigs: SignatureAssumptions<'_>,
    func_renderer: &FuncRenderer<ob::CustomFuncId>,
    type_renderer: &CustomTypeRenderer<ob::CustomTypeId>,
    path: &Path,
    ctx: &mut LocalContext<guard::LocalId, LocalInfo2>,
    expr: &annot::Expr<Mode, CustomTypeId, CustomFuncId>,
    fut_ty: &Type,
) -> Expr {
    match expr {
        annot::Expr::Local(occur) => {
            Expr::Local(handle_occur(interner, ctx, path, occur.id, fut_ty))
        }

        annot::Expr::Call(purity, func_id, arg) => {
            let (arg_ty, ret_ty) = sigs.sig_of(*func_id);

            let lt_subst = bind_lts(interner, &ret_ty, fut_ty);
            let arg_ty = prepare_arg_type(interner, &path, arg_ty);

            // This `join_everywhere` reflects the fact that we assume that functions access all of
            // their arguments. We could be more precise here.
            let arg_ty = join_everywhere(
                interner,
                &subst_lts(interner, &arg_ty, &lt_subst),
                &path.as_lt(interner),
            );

            let arg = handle_occur(interner, ctx, path, arg.id, &arg_ty);
            Expr::Call(*purity, *func_id, arg)
        }

        // We use `with_scope` to express our intent. In fact, all the bindings we add are popped
        // from the context before we return.
        annot::Expr::LetMany(bindings, ret) => ctx.with_scope(|ctx| {
            let locals_offset = ctx.len();

            for (binding_ty, _, _) in bindings {
                let _ = ctx.add_local(LocalInfo2 {
                    ty: init_bind_res(customs, binding_ty, || Lt::Empty),
                    metadata: Metadata::default(),
                });
            }

            let ret_occur = handle_occur(interner, ctx, &path.seq(bindings.len()), ret.id, fut_ty);

            let mut new_bindings_rev = Vec::new();
            for (i, (_, expr, metadata)) in bindings.into_iter().enumerate().rev() {
                let local = guard::LocalId(locals_offset + i);

                let fut_ty = ctx.local_binding(local).ty.clone();

                // Only retain the locals *strictly* before this binding.
                ctx.truncate(Count::from_value(local.0));

                let new_expr = annot_expr(
                    interner,
                    customs,
                    sigs,
                    func_renderer,
                    type_renderer,
                    &path.seq(i),
                    ctx,
                    expr,
                    &as_value_type(&fut_ty),
                );

                new_bindings_rev.push((fut_ty, new_expr, metadata.clone()));
            }

            let new_bindings = {
                new_bindings_rev.reverse();
                new_bindings_rev
            };

            Expr::LetMany(new_bindings, ret_occur)
        }),

        annot::Expr::If(discrim, then_case, else_case) => {
            let else_case = annot_expr(
                interner,
                customs,
                sigs,
                func_renderer,
                type_renderer,
                &path.seq(1).alt(1, 2),
                ctx,
                else_case,
                fut_ty,
            );
            let then_case = annot_expr(
                interner,
                customs,
                sigs,
                func_renderer,
                type_renderer,
                &path.seq(1).alt(0, 2),
                ctx,
                then_case,
                fut_ty,
            );
            let discrim = handle_occur(
                interner,
                ctx,
                &path.seq(0),
                discrim.id,
                &Type::bool_(interner),
            );
            Expr::If(discrim, Box::new(then_case), Box::new(else_case))
        }

        annot::Expr::CheckVariant(variant_id, variant) => {
            assert!(fut_ty.shape() == &Shape::bool_(interner));
            // You can match on something whose fields are dead!
            let variants_ty = init_value_res(&variant.ty, || Lt::Empty);
            Expr::CheckVariant(
                *variant_id,
                handle_occur(interner, ctx, path, variant.id, &variants_ty),
            )
        }

        annot::Expr::Unreachable(_ty) => Expr::Unreachable(fut_ty.clone()),

        annot::Expr::Tuple(fields) => {
            let fut_item_tys = annot::elim_tuple(fut_ty);
            let mut fields_rev = fields
                .into_iter()
                .zip_eq(fut_item_tys.iter())
                .enumerate()
                .rev()
                .map(|(i, (occur, item_ty))| {
                    handle_occur(interner, ctx, &path.seq(i), occur.id, item_ty)
                })
                .collect::<Vec<_>>();
            let fields = {
                fields_rev.reverse();
                fields_rev
            };
            Expr::Tuple(fields)
        }

        annot::Expr::TupleField(tup, idx) => {
            let mut tuple_ty = init_value_res(&tup.ty, || Lt::Empty);
            let ShapeInner::Tuple(shapes) = &*tuple_ty.shape().inner else {
                panic!("expected `Tuple` type");
            };

            let (start, end) = annot::nth_res_bounds(shapes, *idx);
            tuple_ty.res_mut().as_mut_slice()[start..end].clone_from_slice(fut_ty.res().as_slice());

            let occur = handle_occur(interner, ctx, path, tup.id, &tuple_ty);
            Expr::TupleField(occur, *idx)
        }

        annot::Expr::WrapVariant(_variants, variant_id, content) => {
            let fut_variant_tys = annot::elim_variants(fut_ty);
            let occur = handle_occur(
                interner,
                ctx,
                path,
                content.id,
                &fut_variant_tys[*variant_id],
            );
            Expr::WrapVariant(fut_variant_tys, *variant_id, occur)
        }

        annot::Expr::UnwrapVariant(variant_id, wrapped) => {
            let mut variants_ty = init_value_res(&wrapped.ty, || Lt::Empty);
            let ShapeInner::Variants(shapes) = &*variants_ty.shape().inner else {
                panic!("expected `Variants` type");
            };

            let (start, end) = annot::nth_res_bounds(shapes.as_slice(), variant_id.to_index());
            variants_ty.res_mut().as_mut_slice()[start..end]
                .clone_from_slice(fut_ty.res().as_slice());

            let occur = handle_occur(interner, ctx, path, wrapped.id, &variants_ty);
            Expr::UnwrapVariant(*variant_id, occur)
        }

        annot::Expr::WrapBoxed(content, _output_ty) => {
            let mut occurs =
                instantiate_model(&*model::box_new, interner, ctx, path, &[content], fut_ty);
            Expr::WrapBoxed(occurs.pop().unwrap(), fut_ty.clone())
        }

        annot::Expr::UnwrapBoxed(wrapped, _output_ty) => {
            let mut occurs =
                create_occurs_from_model(&*model::box_get, interner, path, &[wrapped], fut_ty);

            let mut new_wrapped = occurs.pop().unwrap();
            new_wrapped.ty = propagate_get(interner, &new_wrapped.ty, fut_ty);
            propagate_occur(interner, ctx, path, new_wrapped.id, &new_wrapped.ty);

            Expr::UnwrapBoxed(new_wrapped, fut_ty.clone())
        }

        annot::Expr::WrapCustom(custom_id, recipe, unfolded) => {
            let fut_unfolded =
                annot::unfold(interner, &customs.types, &customs.sccs, recipe, fut_ty);
            let occur = handle_occur(interner, ctx, path, unfolded.id, &fut_unfolded);
            Expr::WrapCustom(*custom_id, recipe.clone(), occur)
        }

        annot::Expr::UnwrapCustom(custom_id, recipe, folded) => {
            let fresh_folded = {
                let mut lt_count = Count::new();
                init_value_res(&folded.ty, move || lt_count.inc())
            };

            let fresh_folded = {
                let fresh_unfolded = annot::unfold(
                    interner,
                    &customs.types,
                    &customs.sccs,
                    recipe,
                    &fresh_folded,
                );

                // Join the lifetimes in `fut_ty` which are identified under folding.
                let lt_subst = bind_lts(interner, &fresh_unfolded, fut_ty);
                subst_lts(interner, &wrap_lts(&fresh_folded), &lt_subst)
            };

            let occur = handle_occur(interner, ctx, path, folded.id, &fresh_folded);
            Expr::UnwrapCustom(*custom_id, recipe.clone(), occur)
        }

        annot::Expr::Intrinsic(intr, arg) => {
            let sig = intrinsic_sig(*intr);
            let ty = annot::Type::from_intr(interner, &sig.arg);
            Expr::Intrinsic(*intr, Occur { id: arg.id, ty })
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Get(arr, idx, _)) => {
            let mut occurs =
                create_occurs_from_model(&*model::array_get, interner, path, &[arr, idx], fut_ty);
            let new_idx = occurs.pop().unwrap();
            let mut new_arr = occurs.pop().unwrap();

            new_arr.ty = propagate_get(interner, &new_arr.ty, fut_ty);
            propagate_occur(
                interner,
                ctx,
                &annot::arg_path(path, 0, 2),
                new_arr.id,
                &new_arr.ty,
            );

            Expr::ArrayOp(ArrayOp::Get(new_arr, new_idx, fut_ty.clone()))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Extract(arr, idx)) => {
            let occurs = instantiate_model(
                &*model::array_extract,
                interner,
                ctx,
                path,
                &[arr, idx],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            Expr::ArrayOp(ArrayOp::Extract(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Len(arr)) => {
            let occurs = instantiate_model(&*model::array_len, interner, ctx, path, &[arr], fut_ty);
            let mut occurs = occurs.into_iter();
            Expr::ArrayOp(ArrayOp::Len(occurs.next().unwrap()))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Push(arr, item)) => {
            let occurs = instantiate_model(
                &*model::array_push,
                interner,
                ctx,
                path,
                &[arr, item],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            Expr::ArrayOp(ArrayOp::Push(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Pop(arr)) => {
            let occurs = instantiate_model(&*model::array_pop, interner, ctx, path, &[arr], fut_ty);
            let mut occurs = occurs.into_iter();
            Expr::ArrayOp(ArrayOp::Pop(occurs.next().unwrap()))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Replace(hole, item)) => {
            let occurs = instantiate_model(
                &*model::array_replace,
                interner,
                ctx,
                path,
                &[hole, item],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            Expr::ArrayOp(ArrayOp::Replace(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        annot::Expr::ArrayOp(annot::ArrayOp::Reserve(arr, cap)) => {
            let occurs = instantiate_model(
                &*model::array_reserve,
                interner,
                ctx,
                path,
                &[arr, cap],
                fut_ty,
            );
            let mut occurs = occurs.into_iter();
            Expr::ArrayOp(ArrayOp::Reserve(
                occurs.next().unwrap(),
                occurs.next().unwrap(),
            ))
        }

        annot::Expr::IoOp(annot::IoOp::Input) => {
            let _ = instantiate_model(&*model::io_input, interner, ctx, path, &[], fut_ty);
            Expr::IoOp(IoOp::Input)
        }

        annot::Expr::IoOp(annot::IoOp::Output(arr)) => {
            let occurs = instantiate_model(&*model::io_output, interner, ctx, path, &[arr], fut_ty);
            let mut occurs = occurs.into_iter();
            Expr::IoOp(IoOp::Output(occurs.next().unwrap()))
        }

        annot::Expr::Panic(_ret_ty, msg) => {
            let occurs = instantiate_model(
                &*model::panic,
                interner,
                ctx,
                path,
                &[msg],
                &Type::unit(interner),
            );
            let mut occurs = occurs.into_iter();
            Expr::Panic(fut_ty.clone(), occurs.next().unwrap())
        }

        annot::Expr::ArrayLit(_item_ty, items) => {
            let item_refs = items.iter().collect::<Vec<_>>();
            let occurs =
                instantiate_model(&*model::array_new, interner, ctx, path, &item_refs, fut_ty);
            let (_, ret_item_ty) = annot::elim_array(fut_ty);
            Expr::ArrayLit(ret_item_ty, occurs)
        }

        annot::Expr::BoolLit(val) => Expr::BoolLit(*val),

        annot::Expr::ByteLit(val) => Expr::ByteLit(*val),

        annot::Expr::IntLit(val) => Expr::IntLit(*val),

        annot::Expr::FloatLit(val) => Expr::FloatLit(*val),
    }
}

#[derive(Clone, Debug)]
struct SolverScc {
    func_args: BTreeMap<CustomFuncId, BindType>,
    func_rets: BTreeMap<CustomFuncId, RetType>,
    func_bodies: BTreeMap<CustomFuncId, Expr>,
}

fn annot_scc(
    interner: &Interner,
    customs: &ob::CustomTypes,
    funcs: &IdVec<ob::CustomFuncId, SolvedFuncDef>,
    funcs_annot: &IdMap<ob::CustomFuncId, FuncDef>,
    func_renderer: &FuncRenderer<ob::CustomFuncId>,
    type_renderer: &CustomTypeRenderer<ob::CustomTypeId>,
    scc: Scc<ob::CustomFuncId>,
) -> SolverScc {
    match scc.kind {
        SccKind::Acyclic | SccKind::Cyclic => {
            // TODO: if the SCC is acyclic, we can skip lifetime fixed point iteration

            let mut next_lt = Count::new();

            let mut arg_tys = scc
                .nodes
                .iter()
                .map(|id| (*id, init_bind_res(customs, &funcs[id].arg_ty, || Lt::Empty)))
                .collect::<BTreeMap<_, _>>();

            let ret_tys = scc
                .nodes
                .iter()
                .map(|id| (*id, init_value_res(&funcs[id].ret_ty, || next_lt.inc())))
                .collect::<BTreeMap<_, _>>();

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

                    let arg_id = ctx.add_local(LocalInfo2 {
                        ty: init_bind_res(customs, &func.arg_ty, || Lt::Empty),
                        metadata: Metadata::default(),
                    });
                    debug_assert_eq!(arg_id, guard::ARG_LOCAL);

                    let ret_ty = wrap_lts(&ret_tys[id]);
                    let expr = annot_expr(
                        interner,
                        customs,
                        assumptions,
                        func_renderer,
                        type_renderer,
                        &annot::FUNC_BODY_PATH(),
                        &mut ctx,
                        &func.body,
                        &ret_ty,
                    );
                    bodies.insert(*id, expr);

                    new_arg_tys.insert(*id, ctx.local_binding(arg_id).ty.clone());
                }

                if new_arg_tys
                    .values()
                    .zip_eq(arg_tys.values())
                    .all(|(new, old)| lt_equiv(new, old))
                {
                    break (new_arg_tys, bodies);
                }

                arg_tys = new_arg_tys;
            };

            SolverScc {
                func_args: new_arg_tys,
                func_rets: ret_tys,
                func_bodies: bodies,
            }
        }
    }
}

fn add_func_deps(
    deps: &mut BTreeSet<CustomFuncId>,
    expr: &annot::Expr<Mode, CustomTypeId, CustomFuncId>,
) {
    match expr {
        annot::Expr::Call(_, other, _) => {
            deps.insert(*other);
        }
        annot::Expr::If(_, then_case, else_case) => {
            add_func_deps(deps, then_case);
            add_func_deps(deps, else_case);
        }
        annot::Expr::LetMany(bindings, _) => {
            for (_, rhs, _) in bindings {
                add_func_deps(deps, rhs);
            }
        }
        _ => {}
    }
}

fn annot_program(
    interner: &Interner,
    program: SolvedProgram,
    progress: impl ProgressLogger,
) -> ob::Program {
    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);
    let type_renderer = CustomTypeRenderer::from_symbols(&program.custom_type_symbols);

    let func_sccs: Sccs<usize, _> = find_components(program.funcs.count(), |id| {
        let mut deps = BTreeSet::new();
        add_func_deps(&mut deps, &program.funcs[id].body);
        deps
    });

    let mut progress = progress.start_session(Some(program.funcs.len()));

    let mut funcs_annot = IdMap::new();
    for (_func_id, scc) in &func_sccs {
        let annotated = annot_scc(
            interner,
            &program.custom_types,
            &program.funcs,
            &funcs_annot,
            &func_renderer,
            &type_renderer,
            scc,
        );

        for func_id in scc.nodes {
            let func = &program.funcs[func_id];
            funcs_annot.insert_vacant(
                *func_id,
                FuncDef {
                    purity: func.purity,
                    arg_ty: annotated.func_args[&func_id].clone(),
                    ret_ty: annotated.func_rets[&func_id].clone(),
                    body: annotated.func_bodies[&func_id].clone(),
                    profile_point: func.profile_point.clone(),
                },
            );
        }

        progress.update(scc.nodes.len());
    }

    let funcs = funcs_annot.to_id_vec(program.funcs.count());

    progress.finish();

    ob::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs,
        profile_points: program.profile_points,
        func_symbols: program.func_symbols,
        main: program.main,
    }
}

pub fn annot_obligations(
    interner: &Interner,
    program: annot::Program,
    progress: impl ProgressLogger,
) -> ob::Program {
    let program = solve_program(interner, program);
    let program = annot_program(interner, program, progress);
    program
}
