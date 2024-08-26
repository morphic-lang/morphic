use crate::data::anon_sum_ast::Type;
use crate::data::first_order_ast::CustomTypeId;
use crate::data::flat_ast::{self as flat, ArrayOp, Condition, Expr, FuncDef, IoOp};
use crate::data::guarded_ast::{self as guarded, CanGuard};
use id_collections::{id_type, IdMap, IdVec};
use id_graph_sccs::{SccKind, Sccs};
use std::collections::{BTreeMap, BTreeSet};

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

fn guard_type(
    customs: &flat::CustomTypes,
    kinds: &IdVec<CustomTypeId, CanGuard>,
    ty: &Type,
) -> Type {
    match ty {
        Type::Bool => Type::Bool,
        Type::Num(num_ty) => Type::Num(*num_ty),
        Type::Tuple(tys) => Type::Tuple(
            tys.iter()
                .map(|ty| guard_type(customs, kinds, ty))
                .collect(),
        ),
        Type::Variants(tys) => Type::Variants(tys.map_refs(|_, ty| guard_type(customs, kinds, ty))),
        Type::Custom(id) => match kinds[*id] {
            CanGuard::Yes => guard_type(customs, kinds, &customs.types[*id].content),
            CanGuard::No => Type::Custom(*id),
        },
        Type::Array(ty) => Type::Array(ty.clone()),
        Type::HoleArray(ty) => Type::HoleArray(ty.clone()),
        Type::Boxed(ty) => Type::Boxed(ty.clone()),
    }
}

struct Trans<'a> {
    customs: &'a flat::CustomTypes,
    can_guard: &'a IdVec<CustomTypeId, CanGuard>,
    cache: BTreeMap<Type, Type>,
}

impl<'a> Trans<'a> {
    fn new(customs: &'a flat::CustomTypes, can_guard: &'a IdVec<CustomTypeId, CanGuard>) -> Self {
        Self {
            customs,
            can_guard,
            cache: BTreeMap::new(),
        }
    }

    fn guard(&mut self, ty: Type) -> Type {
        self.cache
            .entry(ty)
            .or_insert_with_key(|ty| guard_type(self.customs, self.can_guard, ty))
            .clone()
    }
}

fn guard_cond(trans: &mut Trans, cond: Condition) -> Condition {
    match cond {
        Condition::Any => Condition::Any,
        Condition::Tuple(conds) => Condition::Tuple(
            conds
                .into_iter()
                .map(|cond| guard_cond(trans, cond))
                .collect(),
        ),
        Condition::Variant(variant_id, cond) => {
            Condition::Variant(variant_id, Box::new(guard_cond(trans, *cond)))
        }
        Condition::Boxed(cond, item_ty) => {
            Condition::Boxed(Box::new(guard_cond(trans, *cond)), trans.guard(item_ty))
        }
        Condition::Custom(custom_id, cond) => {
            Condition::Custom(custom_id, Box::new(guard_cond(trans, *cond)))
        }
        Condition::BoolConst(lit) => Condition::BoolConst(lit),
        Condition::ByteConst(lit) => Condition::ByteConst(lit),
        Condition::IntConst(lit) => Condition::IntConst(lit),
        Condition::FloatConst(lit) => Condition::FloatConst(lit),
    }
}

fn guard_expr(trans: &mut Trans, expr: Expr) -> Expr {
    match expr {
        Expr::Local(local) => Expr::Local(local),
        Expr::Call(purity, func, arg) => Expr::Call(purity, func, arg),
        Expr::Branch(discrim, arms, ret_ty) => Expr::Branch(
            discrim,
            arms.into_iter()
                .map(|(cond, expr)| (guard_cond(trans, cond), guard_expr(trans, expr)))
                .collect(),
            trans.guard(ret_ty),
        ),
        Expr::LetMany(bindings, ret) => Expr::LetMany(
            bindings
                .into_iter()
                .map(|(ty, expr)| (trans.guard(ty), guard_expr(trans, expr)))
                .collect(),
            ret,
        ),
        Expr::Tuple(items) => Expr::Tuple(items),
        Expr::TupleField(tup, idx) => Expr::TupleField(tup, idx),
        Expr::WrapVariant(variants, variant_id, content) => {
            Expr::WrapVariant(variants, variant_id, content)
        }
        Expr::UnwrapVariant(variant_id, wrapped) => Expr::UnwrapVariant(variant_id, wrapped),
        Expr::WrapBoxed(content, item_ty) => Expr::WrapBoxed(content, trans.guard(item_ty)),
        Expr::UnwrapBoxed(wrapped, item_ty) => Expr::UnwrapBoxed(wrapped, trans.guard(item_ty)),
        Expr::WrapCustom(custom_id, content) => Expr::WrapCustom(custom_id, content),
        Expr::UnwrapCustom(custom_id, wrapped) => Expr::UnwrapCustom(custom_id, wrapped),
        Expr::Intrinsic(intr, arg) => Expr::Intrinsic(intr, arg),

        Expr::ArrayOp(ArrayOp::Get(item_ty, arr, idx)) => {
            Expr::ArrayOp(ArrayOp::Get(trans.guard(item_ty), arr, idx))
        }
        Expr::ArrayOp(ArrayOp::Extract(item_ty, arr, idx)) => {
            Expr::ArrayOp(ArrayOp::Extract(trans.guard(item_ty), arr, idx))
        }
        Expr::ArrayOp(ArrayOp::Len(item_ty, arr)) => {
            Expr::ArrayOp(ArrayOp::Len(trans.guard(item_ty), arr))
        }
        Expr::ArrayOp(ArrayOp::Push(item_ty, arr, item)) => {
            Expr::ArrayOp(ArrayOp::Push(trans.guard(item_ty), arr, item))
        }
        Expr::ArrayOp(ArrayOp::Pop(item_ty, arr)) => {
            Expr::ArrayOp(ArrayOp::Pop(trans.guard(item_ty), arr))
        }
        Expr::ArrayOp(ArrayOp::Replace(item_ty, hole_arr, item)) => {
            Expr::ArrayOp(ArrayOp::Replace(trans.guard(item_ty), hole_arr, item))
        }
        Expr::ArrayOp(ArrayOp::Reserve(item_ty, arr, cap)) => {
            Expr::ArrayOp(ArrayOp::Reserve(trans.guard(item_ty), arr, cap))
        }

        Expr::IoOp(IoOp::Input) => Expr::IoOp(IoOp::Input),
        Expr::IoOp(IoOp::Output(msg)) => Expr::IoOp(IoOp::Output(msg)),

        Expr::Panic(ret_ty, msg) => Expr::Panic(trans.guard(ret_ty), msg),
        Expr::ArrayLit(item_ty, items) => Expr::ArrayLit(trans.guard(item_ty), items),
        Expr::BoolLit(lit) => Expr::BoolLit(lit),
        Expr::ByteLit(lit) => Expr::ByteLit(lit),
        Expr::IntLit(lit) => Expr::IntLit(lit),
        Expr::FloatLit(lit) => Expr::FloatLit(lit),
    }
}

pub fn guard_types(prog: flat::Program) -> guarded::Program {
    let can_guard = can_guard_customs(&prog.custom_types);

    let mut trans = Trans::new(&prog.custom_types, &can_guard);
    let funcs = prog.funcs.map(|_, func| FuncDef {
        purity: func.purity,
        arg_type: trans.guard(func.arg_type),
        ret_type: trans.guard(func.ret_type),
        body: guard_expr(&mut trans, func.body),
        profile_point: func.profile_point,
    });

    let types = prog
        .custom_types
        .types
        .map(|id, def| guarded::CustomTypeDef {
            content: def.content,
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
