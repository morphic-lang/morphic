use crate::data::anon_sum_ast::Type;
use crate::data::first_order_ast::CustomTypeId;
use crate::data::flat_ast::{
    self as flat, ArrayOp, Condition, CustomTypeSccId, Expr, FuncDef, IoOp,
};
use crate::data::guarded_ast::{self as guarded, CanGuard};
use crate::util::collection_ext::VecExt;
use id_collections::{id_type, IdMap, IdVec};
use id_graph_sccs::{SccKind, Sccs};
use std::collections::BTreeSet;

fn add_size_deps(ty: &Type, deps: &mut BTreeSet<CustomTypeId>) {
    match ty {
        Type::Bool | Type::Num(_) | Type::Array(_) | Type::HoleArray(_) | Type::Boxed(_) => {}
        Type::Tuple(tys) => {
            for ty in tys {
                add_size_deps(ty, deps);
            }
        }
        Type::Variants(tys) => {
            for (_, ty) in tys {
                add_size_deps(ty, deps);
            }
        }
        Type::Custom(id) => {
            deps.insert(*id);
        }
    }
}

fn can_guard_customs(customs: &flat::CustomTypes) -> IdVec<CustomTypeId, CanGuard> {
    #[id_type]
    struct SccId(usize);

    let sccs: Sccs<SccId, _> = id_graph_sccs::find_components(customs.types.count(), |id| {
        let mut deps = BTreeSet::new();
        add_size_deps(&customs.types[id].content, &mut deps);
        deps
    });

    let mut can_guard = IdMap::new();
    for (_, component) in &sccs {
        let can_guard_component = match component.kind {
            SccKind::Acyclic => CanGuard::Yes,
            SccKind::Cyclic => CanGuard::No,
        };
        for id in component.nodes {
            can_guard.insert(*id, can_guard_component);
        }
    }

    can_guard.to_id_vec(customs.types.count())
}

fn guard(
    customs: &flat::CustomTypes,
    can_guard: &IdVec<CustomTypeId, CanGuard>,
    scc: Option<CustomTypeSccId>,
    ty: &Type,
) -> Type {
    match ty {
        Type::Bool => Type::Bool,
        Type::Num(num_ty) => Type::Num(*num_ty),
        Type::Tuple(tys) => Type::Tuple(tys.map_refs(|ty| guard(customs, can_guard, scc, ty))),
        Type::Variants(tys) => {
            Type::Variants(tys.map_refs(|_, ty| guard(customs, can_guard, scc, ty)))
        }
        Type::Custom(id) => {
            let custom = &customs.types[*id];
            if can_guard[*id] == CanGuard::Yes
                && customs.sccs.component(custom.scc).kind == SccKind::Cyclic
                && scc.map_or(true, |scc| scc != custom.scc)
            {
                guard(customs, can_guard, Some(custom.scc), &custom.content)
            } else {
                Type::Custom(*id)
            }
        }
        Type::Array(ty) => Type::Array(Box::new(guard(customs, can_guard, scc, ty))),
        Type::HoleArray(ty) => Type::HoleArray(Box::new(guard(customs, can_guard, scc, ty))),
        Type::Boxed(ty) => Type::Boxed(Box::new(guard(customs, can_guard, scc, ty))),
    }
}

struct Context<'a> {
    customs: &'a flat::CustomTypes,
    can_guard: &'a IdVec<CustomTypeId, CanGuard>,
}

impl Context<'_> {
    fn guard(&self, ty: &Type, scc: Option<CustomTypeSccId>) -> Type {
        guard(self.customs, self.can_guard, scc, ty)
    }
}

fn guard_cond(ctx: &Context, cond: Condition) -> Condition {
    match cond {
        Condition::Any => Condition::Any,
        Condition::Tuple(conds) => Condition::Tuple(
            conds
                .into_iter()
                .map(|cond| guard_cond(ctx, cond))
                .collect(),
        ),
        Condition::Variant(variant_id, cond) => {
            Condition::Variant(variant_id, Box::new(guard_cond(ctx, *cond)))
        }
        Condition::Boxed(cond, item_ty) => {
            Condition::Boxed(Box::new(guard_cond(ctx, *cond)), ctx.guard(&item_ty, None))
        }
        Condition::Custom(custom_id, cond) => {
            Condition::Custom(custom_id, Box::new(guard_cond(ctx, *cond)))
        }
        Condition::BoolConst(lit) => Condition::BoolConst(lit),
        Condition::ByteConst(lit) => Condition::ByteConst(lit),
        Condition::IntConst(lit) => Condition::IntConst(lit),
        Condition::FloatConst(lit) => Condition::FloatConst(lit),
    }
}

fn guard_expr(ctx: &Context, expr: Expr) -> Expr {
    match expr {
        Expr::Local(local) => Expr::Local(local),
        Expr::Call(purity, func, arg) => Expr::Call(purity, func, arg),
        Expr::Branch(discrim, arms, ret_ty) => Expr::Branch(
            discrim,
            arms.into_iter()
                .map(|(cond, expr)| (guard_cond(ctx, cond), guard_expr(ctx, expr)))
                .collect(),
            ctx.guard(&ret_ty, None),
        ),
        Expr::LetMany(bindings, ret) => Expr::LetMany(
            bindings
                .into_iter()
                .map(|(ty, expr)| (ctx.guard(&ty, None), guard_expr(ctx, expr)))
                .collect(),
            ret,
        ),
        Expr::Tuple(items) => Expr::Tuple(items),
        Expr::TupleField(tup, idx) => Expr::TupleField(tup, idx),
        Expr::WrapVariant(variants, variant_id, content) => {
            Expr::WrapVariant(variants, variant_id, content)
        }
        Expr::UnwrapVariant(variant_id, wrapped) => Expr::UnwrapVariant(variant_id, wrapped),
        Expr::WrapBoxed(content, item_ty) => Expr::WrapBoxed(content, ctx.guard(&item_ty, None)),
        Expr::UnwrapBoxed(wrapped, item_ty) => {
            Expr::UnwrapBoxed(wrapped, ctx.guard(&item_ty, None))
        }
        Expr::WrapCustom(custom_id, content) => Expr::WrapCustom(custom_id, content),
        Expr::UnwrapCustom(custom_id, wrapped) => Expr::UnwrapCustom(custom_id, wrapped),
        Expr::Intrinsic(intr, arg) => Expr::Intrinsic(intr, arg),

        Expr::ArrayOp(ArrayOp::Get(item_ty, arr, idx)) => {
            Expr::ArrayOp(ArrayOp::Get(ctx.guard(&item_ty, None), arr, idx))
        }
        Expr::ArrayOp(ArrayOp::Extract(item_ty, arr, idx)) => {
            Expr::ArrayOp(ArrayOp::Extract(ctx.guard(&item_ty, None), arr, idx))
        }
        Expr::ArrayOp(ArrayOp::Len(item_ty, arr)) => {
            Expr::ArrayOp(ArrayOp::Len(ctx.guard(&item_ty, None), arr))
        }
        Expr::ArrayOp(ArrayOp::Push(item_ty, arr, item)) => {
            Expr::ArrayOp(ArrayOp::Push(ctx.guard(&item_ty, None), arr, item))
        }
        Expr::ArrayOp(ArrayOp::Pop(item_ty, arr)) => {
            Expr::ArrayOp(ArrayOp::Pop(ctx.guard(&item_ty, None), arr))
        }
        Expr::ArrayOp(ArrayOp::Replace(item_ty, hole_arr, item)) => {
            Expr::ArrayOp(ArrayOp::Replace(ctx.guard(&item_ty, None), hole_arr, item))
        }
        Expr::ArrayOp(ArrayOp::Reserve(item_ty, arr, cap)) => {
            Expr::ArrayOp(ArrayOp::Reserve(ctx.guard(&item_ty, None), arr, cap))
        }

        Expr::IoOp(IoOp::Input) => Expr::IoOp(IoOp::Input),
        Expr::IoOp(IoOp::Output(msg)) => Expr::IoOp(IoOp::Output(msg)),

        Expr::Panic(ret_ty, msg) => Expr::Panic(ctx.guard(&ret_ty, None), msg),
        Expr::ArrayLit(item_ty, items) => Expr::ArrayLit(ctx.guard(&item_ty, None), items),
        Expr::BoolLit(lit) => Expr::BoolLit(lit),
        Expr::ByteLit(lit) => Expr::ByteLit(lit),
        Expr::IntLit(lit) => Expr::IntLit(lit),
        Expr::FloatLit(lit) => Expr::FloatLit(lit),
    }
}

pub fn guard_types(prog: flat::Program) -> guarded::Program {
    let can_guard = can_guard_customs(&prog.custom_types);

    let ctx = Context {
        customs: &prog.custom_types,
        can_guard: &can_guard,
    };
    let funcs = prog.funcs.map(|_, func| FuncDef {
        purity: func.purity,
        arg_type: ctx.guard(&func.arg_type, None),
        ret_type: ctx.guard(&func.ret_type, None),
        body: guard_expr(&ctx, func.body),
        profile_point: func.profile_point,
    });

    let types = prog
        .custom_types
        .types
        .map_refs(|id, def| guarded::CustomTypeDef {
            content: ctx.guard(&def.content, Some(def.scc)),
            scc: def.scc,
            can_guard: can_guard[id],
        });

    let custom_types = guarded::CustomTypes {
        types,
        sccs: prog.custom_types.sccs,
    };

    guarded::Program {
        mod_symbols: prog.mod_symbols,
        custom_types,
        custom_type_symbols: prog.custom_type_symbols,
        funcs,
        func_symbols: prog.func_symbols,
        profile_points: prog.profile_points,
        main: prog.main,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_guard() {
        let list = |tail, item| {
            Type::Variants(IdVec::from_vec(vec![
                Type::Tuple(vec![]),
                Type::Tuple(vec![item, Type::Boxed(Box::new(Type::Custom(tail)))]),
            ]))
        };

        //  list0 = () + bool * rc list0
        let list0 = list(CustomTypeId(0), Type::Bool);
        //  list1 = () + rc list0 * rc list1
        let list1 = list(
            CustomTypeId(1),
            Type::Boxed(Box::new(Type::Custom(CustomTypeId(0)))),
        );

        let customs = flat::CustomTypes {
            types: IdVec::from_vec(vec![
                flat::CustomTypeDef {
                    content: list0.clone(),
                    scc: CustomTypeSccId(0),
                },
                flat::CustomTypeDef {
                    content: list1,
                    scc: CustomTypeSccId(1),
                },
            ]),
            sccs: {
                let mut sccs = Sccs::new();
                sccs.push_cyclic_component(&[CustomTypeId(0)]);
                sccs.push_cyclic_component(&[CustomTypeId(1)]);
                sccs
            },
        };
        let kinds = IdVec::from_vec(vec![CanGuard::Yes, CanGuard::Yes]);

        //  guarded_list0 = () + bool * rc list0
        let guarded_list0 = guard(&customs, &kinds, None, &Type::Custom(CustomTypeId(0)));
        assert_eq!(guarded_list0, list0);

        //  guarded_list1 = () + rc (() + bool * rc list0) * rc list1
        let guarded_list1 = guard(&customs, &kinds, None, &Type::Custom(CustomTypeId(1)));
        assert_eq!(
            guarded_list1,
            list(CustomTypeId(1), Type::Boxed(Box::new(list0)))
        );
    }
}
