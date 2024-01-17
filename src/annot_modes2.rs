use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast::{CustomTypeId, NumType};
use crate::data::flat_ast as flat;
use crate::data::mode_annot_ast2::{
    self as annot, Lt, LtParam, LtVar, ModeConstr, ModeParam, ModeTerm, ModeVar,
};
use crate::util::graph;
use crate::util::id_gen::IdGen;
use crate::util::local_context::LocalContext;
use crate::util::progress_logger::ProgressLogger;
use id_collections::{Count, IdMap, IdVec};
use std::collections::HashSet;

type SolverType = annot::Type<ModeTerm, LtVar>;
type SolverIntrinsicType = annot::IntrinsicType<ModeTerm>;
type SolverExpr = annot::Expr<ModeTerm, LtVar>;

type Type = annot::Type<ModeParam, LtParam>;
type IntrinsicType = annot::IntrinsicType<ModeParam>;
type Expr = annot::Expr<ModeParam, LtParam>;

struct ModeConstrGraph {
    // a -> b means a <= b, i.e. if a is owned then b is owned
    inner: graph::Graph<ModeVar>,
    sig: HashSet<ModeVar>,
}

impl ModeConstrGraph {
    fn new() -> Self {
        Self {
            inner: graph::Graph {
                edges_out: IdVec::new(),
            },
            sig: HashSet::new(),
        }
    }

    fn add_constr(&mut self, constr: ModeConstr) {
        self.inner.edges_out[constr.0].push(constr.1);
    }

    fn mark_external(&mut self, var: ModeVar) {
        self.sig.insert(var);
    }

    fn find_lower_bounds(&self) -> IdVec<ModeVar, ModeTerm> {
        let sccs = graph::acyclic_and_cyclic_sccs(&self.inner);

        let mut lower_bounds = IdMap::new();
        for scc in &sccs {
            todo!()
        }

        let len = lower_bounds.len();
        lower_bounds.to_id_vec(Count::from_value(len))
    }
}

fn count_params_rec(
    lifted: IdMap<CustomTypeId, annot::CustomTypeDef>,
    ty: &anon::Type,
    branches: usize,
) -> (usize, usize) {
    match ty {
        anon::Type::Bool => (0, 0),
        anon::Type::Num(_) => (0, 0),
        anon::Type::Tuple(tys) => tys
            .iter()
            .map(|ty| count_params_rec(lifted, ty, branches))
            .fold((0, 0), |(a1, b1), (a2, b2)| (a1 + a2, b1 + b2)),
        anon::Type::Variants(tys) => tys
            .values()
            .map(|ty| count_params_rec(lifted, ty, branches))
            .fold((0, 0), |(a1, b1), (a2, b2)| (a1 + a2, b1 + b2)),
        // Consider the tree representation of the `annot` type which corresponds to this `anon`
        // type. At any given depth, only one branch of the tree tracks an extrinsic type. Every
        // time we hit an annotated type, the extrinsic branch splits off a new intrinsic branch.
        // Since intrinsic branches have mode but not lifetime parameters, we must add `branches` to
        // the count of the former and `1` to the count of the latter.
        anon::Type::Custom(id) => match lifted.get(*id) {
            Some(def) => (
                def.num_mode_params.to_value() * branches,
                def.num_lt_params.to_value(),
            ),
            // This is a typedef in the same SCC; the reference to it here contributes no additional
            // parameters to the entire SCC.
            None => (0, 0),
        },
        anon::Type::Array(ty) => {
            let (a, b) = count_params_rec(lifted, ty, branches + 1);
            (a + branches, b + 1)
        }
        anon::Type::HoleArray(ty) => {
            let (a, b) = count_params_rec(lifted, ty, branches + 1);
            (a + branches, b + 1)
        }
        anon::Type::Boxed(ty) => {
            let (a, b) = count_params_rec(lifted, ty, branches + 1);
            (a + branches, b + 1)
        }
    }
}

fn count_params(
    lifted: IdMap<CustomTypeId, annot::CustomTypeDef>,
    ty: &anon::Type,
) -> (Count<ModeParam>, Count<LtParam>) {
    let (a, b) = count_params_rec(lifted, ty, 1);
    (Count::from_value(a), Count::from_value(b))
}

fn fresh_annot(
    mode_gen: &mut IdGen<ModeParam>,
    lt_gen: &mut IdGen<LtParam>,
    intrinsic_type: IntrinsicType,
) -> annot::ModeAnnot<ModeParam, LtParam> {
    annot::ModeAnnot {
        mode: mode_gen.fresh(),
        lifetime: lt_gen.fresh(),
        intrinsic_type,
    }
}

fn parameterize(
    lifted: IdMap<CustomTypeId, annot::CustomTypeDef>,
    scc_num_mode_params: Count<ModeParam>,
    scc_num_lt_params: Count<LtParam>,
    mode_gen: &mut IdGen<ModeParam>,
    lt_gen: &mut IdGen<LtParam>,
    ty: &anon::Type,
) -> Type {
    match ty {
        anon::Type::Bool => Type::Bool,
        anon::Type::Num(ty) => Type::Num(*ty),
        anon::Type::Tuple(tys) => Type::Tuple(
            tys.iter()
                .map(|ty| {
                    parameterize(
                        lifted,
                        scc_num_mode_params,
                        scc_num_lt_params,
                        mode_gen,
                        lt_gen,
                        ty,
                    )
                })
                .collect(),
        ),
        anon::Type::Variants(tys) => Type::Variants(tys.map_refs(|_, ty| {
            parameterize(
                lifted,
                scc_num_mode_params,
                scc_num_lt_params,
                mode_gen,
                lt_gen,
                ty,
            )
        })),
        anon::Type::Custom(id) => {
            match lifted.get(id) {
                Some(def) => Type::Custom(
                    id,
                    IdVec::from_count_with(def.num_mode_params, |_| mode_gen.fresh()),
                    IdVec::from_count_with(def.num_lt_params, |_| lt_gen.fresh()),
                ),
                None => {
                    // This is a typedef in the same SCC, so we need to parameterize it by all the SCC
                    // parameters.
                    Type::Custom(
                        id,
                        IdVec::from_count_with(scc_num_mode_params, |id| id),
                        IdVec::from_count_with(scc_num_lt_params, |id| id),
                    )
                }
            }
        }
        anon::Type::Array(ty) => {
            let intrinsic_type =
                parameterize_intr(lifted, scc_num_mode_params, scc_num_lt_params, mode_gen, ty);
            Type::Array(
                Box::new(parameterize(
                    lifted,
                    scc_num_mode_params,
                    scc_num_lt_params,
                    mode_gen,
                    lt_gen,
                    ty,
                )),
                fresh_annot(mode_gen, lt_gen, intrinsic_type),
            )
        }
        anon::Type::HoleArray(ty) => {
            let intrinsic_type =
                parameterize_intr(lifted, scc_num_mode_params, scc_num_lt_params, mode_gen, ty);
            Type::HoleArray(
                Box::new(parameterize(
                    lifted,
                    scc_num_mode_params,
                    scc_num_lt_params,
                    mode_gen,
                    lt_gen,
                    ty,
                )),
                fresh_annot(mode_gen, lt_gen, intrinsic_type),
            )
        }
        anon::Type::Boxed(ty) => {
            let intrinsic_type =
                parameterize_intr(lifted, scc_num_mode_params, scc_num_lt_params, mode_gen, ty);
            Type::Boxed(
                Box::new(parameterize(
                    lifted,
                    scc_num_mode_params,
                    scc_num_lt_params,
                    mode_gen,
                    lt_gen,
                    ty,
                )),
                fresh_annot(mode_gen, lt_gen, intrinsic_type),
            )
        }
    }
}

fn parameterize_intr(
    lifted: IdMap<CustomTypeId, annot::CustomTypeDef>,
    scc_mode_n: Count<ModeParam>,
    scc_lt_n: Count<LtParam>,
    mode_gen: &mut IdGen<ModeParam>,
    ty: &anon::Type,
) {
    match ty {
        anon::Type::Bool => IntrinsicType::Bool,
        anon::Type::Num(ty) => IntrinsicType::Num(*ty),
        anon::Type::Tuple(tys) => IntrinsicType::Tuple(
            tys.iter()
                .map(|ty| parameterize_intr(lifted, scc_mode_n, scc_lt_n, mode_gen, ty))
                .collect(),
        ),
        anon::Type::Variants(tys) => IntrinsicType::Variants(
            tys.map_refs(|_, ty| parameterize_intr(lifted, scc_mode_n, scc_lt_n, mode_gen, ty)),
        ),
        anon::Type::Custom(id) => {
            match lifted.get(id) {
                Some(def) => Type::Custom(
                    id,
                    IdVec::from_count_with(def.num_mode_params, |_| mode_gen.fresh()),
                    IdVec::from_count_with(def.num_lt_params, |_| lt_gen.fresh()),
                ),
                None => {
                    // This is a typedef in the same SCC, so we need to parameterize it by all the SCC
                    // parameters.
                    Type::Custom(
                        id,
                        IdVec::from_count_with(scc_mode_n, |id| id),
                        IdVec::from_count_with(scc_lt_n, |id| id),
                    )
                }
            }
        }
        anon::Type::Array(ty) => {
            let intrinsic_type = parameterize_intr(lifted, scc_mode_n, scc_lt_n, mode_gen, ty);
            Type::Array(
                Box::new(parameterize(
                    lifted, scc_mode_n, scc_lt_n, mode_gen, lt_gen, ty,
                )),
                fresh_annot(mode_gen, lt_gen, intrinsic_type),
            )
        }
        anon::Type::HoleArray(ty) => {
            let intrinsic_type = parameterize_intr(lifted, scc_mode_n, scc_lt_n, mode_gen, ty);
            Type::HoleArray(
                Box::new(parameterize(
                    lifted, scc_mode_n, scc_lt_n, mode_gen, lt_gen, ty,
                )),
                fresh_annot(mode_gen, lt_gen, intrinsic_type),
            )
        }
        anon::Type::Boxed(ty) => {
            let intrinsic_type = parameterize_intr(lifted, scc_mode_n, scc_lt_n, mode_gen, ty);
            Type::Boxed(
                Box::new(parameterize(
                    lifted, scc_mode_n, scc_lt_n, mode_gen, lt_gen, ty,
                )),
                fresh_annot(mode_gen, lt_gen, intrinsic_type),
            )
        }
    }
}

// pub fn annot_modes(program: flat::Program, progress: impl ProgressLogger) -> annot::Program {
//     let types = program.custom_types.types.map(|_, def| {
//         let mut lt_gen = IdGen::new();
//         let mut mode_gen = IdGen::new();
//         let content = lift_type(&mut lt_gen, &mut mode_gen, &def.content);
//         annot::CustomTypeDef {
//             num_lt_params: lt_gen.count(),
//             num_mode_params: mode_gen.count(),
//             content,
//             scc: def.scc,
//         }
//     });
//     let custom_types = annot::CustomTypes {
//         types,
//         sccs: program.custom_types.sccs,
//     };
//
//     annot::Program {
//         mod_symbols: todo!(),
//         custom_types: todo!(),
//         custom_type_symbols: todo!(),
//         funcs: todo!(),
//         func_symbols: todo!(),
//         profile_points: todo!(),
//         main: todo!(),
//     }
// }

// fn inst_scheme(
//     subst: &IdVec<ModeParam, ModeTerm>,
//     ty: &annot::Type<ModeParam>,
// ) -> annot::Type<ModeTerm> {
//     let inst_annot = |annot: &annot::Annot<ModeParam>| annot::Annot {
//         mode: subst[annot.mode].clone(),
//         lifetime: annot.lifetime.clone(),
//         intrinsic_type: inst_scheme_intrinsic(subst, &annot.intrinsic_ty),
//     };
//
//     match ty {
//         annot::Type::Bool => annot::Type::Bool,
//         annot::Type::Num(ty) => annot::Type::Num(*ty),
//         annot::Type::Tuple(tys) => {
//             annot::Type::Tuple(tys.into_iter().map(|ty| inst_scheme(subst, ty)).collect())
//         }
//         annot::Type::Variants(tys) => {
//             annot::Type::Variants(tys.map(|_, ty| inst_scheme(subst, ty)))
//         }
//         annot::Type::Custom(id) => annot::Type::Custom(*id),
//         annot::Type::Array(ty, annot) => {
//             annot::Type::Array(Box::new(inst_scheme(subst, ty)), inst_annot(annot))
//         }
//         annot::Type::HoleArray(ty, annot) => {
//             annot::Type::HoleArray(Box::new(inst_scheme(subst, ty)), inst_annot(annot))
//         }
//         annot::Type::Boxed(ty, annot) => {
//             annot::Type::Boxed(Box::new(inst_scheme(subst, ty)), inst_annot(annot))
//         }
//     }
// }
//
// fn inst_scheme_intrinsic(
//     subst: &IdVec<ModeParam, ModeTerm>,
//     ty: &annot::IntrinsicType<ModeParam>,
// ) -> annot::IntrinsicType<ModeTerm> {
//     match ty {
//         annot::IntrinsicType::Bool => annot::IntrinsicType::Bool,
//         annot::IntrinsicType::Num(ty) => annot::IntrinsicType::Num(*ty),
//         annot::IntrinsicType::Tuple(tys) => annot::IntrinsicType::Tuple(
//             tys.into_iter()
//                 .map(|ty| inst_scheme_intrinsic(subst, ty))
//                 .collect(),
//         ),
//         annot::IntrinsicType::Variants(tys) => {
//             annot::IntrinsicType::Variants(tys.map(|_, ty| inst_scheme_intrinsic(subst, ty)))
//         }
//         annot::IntrinsicType::Custom(id) => annot::IntrinsicType::Custom(*id),
//         annot::IntrinsicType::Array(ty, mode) => annot::IntrinsicType::Array(
//             Box::new(inst_scheme_intrinsic(subst, ty)),
//             subst[*mode].clone(),
//         ),
//         annot::IntrinsicType::HoleArray(ty, mode) => annot::IntrinsicType::HoleArray(
//             Box::new(inst_scheme_intrinsic(subst, ty)),
//             subst[*mode].clone(),
//         ),
//         annot::IntrinsicType::Boxed(ty, mode) => annot::IntrinsicType::Boxed(
//             Box::new(inst_scheme_intrinsic(subst, ty)),
//             subst[*mode].clone(),
//         ),
//     }
// }

// fn lift_type(
//     lt_gen: &mut IdGen<LtParam>,
//     mode_gen: &mut IdGen<ModeParam>,
//     ty: &anon::Type,
// ) -> Type {
//     let fresh_annot = |mode_gen: &mut IdGen<ModeParam>, intrinsic_type| annot::ModeAnnot {
//         mode: mode_gen(),
//         lifetime: Lt::Empty,
//         intrinsic_type,
//     };
//
//     match ty {
//         anon::Type::Bool => annot::Type::Bool,
//         anon::Type::Num(ty) => annot::Type::Num(*ty),
//         anon::Type::Tuple(tys) => annot::Type::Tuple(
//             tys.into_iter()
//                 .map(|ty| lift_type(mode_gen, lt_gen, ty))
//                 .collect(),
//         ),
//         anon::Type::Variants(tys) => {
//             annot::Type::Variants(tys.map_refs(|_, ty| lift_type(mode_gen, lt_gen, ty)))
//         }
//         anon::Type::Custom(id) => annot::Type::Custom(*id),
//         anon::Type::Array(ty) => {
//             let intrinsic_type = lift_type_intrinsic(mode_gen, ty);
//             annot::Type::Array(
//                 Box::new(lift_type(mode_gen, lt_gen, ty)),
//                 fresh_annot(mode_gen, intrinsic_type),
//             )
//         }
//         anon::Type::HoleArray(ty) => {
//             let intrinsic_type = lift_type_intrinsic(mode_gen, ty);
//             annot::Type::HoleArray(
//                 Box::new(lift_type(mode_gen, lt_gen, ty)),
//                 fresh_annot(mode_gen, intrinsic_type),
//             )
//         }
//         anon::Type::Boxed(ty) => {
//             let intrinsic_type = lift_type_intrinsic(mode_gen, ty);
//             annot::Type::Boxed(
//                 Box::new(lift_type(mode_gen, lt_gen, ty)),
//                 fresh_annot(mode_gen, intrinsic_type),
//             )
//         }
//     }
// }
//
// fn lift_type_intrinsic<Mode, F>(mode_gen: &mut F, ty: &anon::Type) -> annot::IntrinsicType<Mode>
// where
//     F: FnMut() -> Mode,
// {
//     match ty {
//         anon::Type::Bool => annot::IntrinsicType::Bool,
//         anon::Type::Num(ty) => annot::IntrinsicType::Num(*ty),
//         anon::Type::Tuple(tys) => annot::IntrinsicType::Tuple(
//             tys.into_iter()
//                 .map(|ty| lift_type_intrinsic(mode_gen, ty))
//                 .collect(),
//         ),
//         anon::Type::Variants(tys) => {
//             annot::IntrinsicType::Variants(tys.map(|_, ty| lift_type_intrinsic(mode_gen, ty)))
//         }
//         anon::Type::Custom(id) => annot::IntrinsicType::Custom(*id),
//         anon::Type::Array(ty) => {
//             annot::IntrinsicType::Array(Box::new(lift_type_intrinsic(mode_gen, ty)), mode_gen())
//         }
//         anon::Type::HoleArray(ty) => {
//             annot::IntrinsicType::HoleArray(Box::new(lift_type_intrinsic(mode_gen, ty)), mode_gen())
//         }
//         anon::Type::Boxed(ty) => {
//             annot::IntrinsicType::Boxed(Box::new(lift_type_intrinsic(mode_gen, ty)), mode_gen())
//         }
//     }
// }
//
// /// Given a context, an expression, and a type, which tracks any future uses of this expression,
// /// updates `ctx.types` to reflect any variable occurences in this expression and accumulates
// /// constraints into `constrs`.
// fn annot_expr(
//     mode_gen: &mut IdGen<ModeVar>,
//     def_ctx: &mut LocalContext<flat::LocalId, annot::FuncDef>,
//     scope_ctx: &mut LocalContext<flat::LocalId, Lt>,
//     ty_ctx: &mut LocalContext<flat::LocalId, annot::SigType>,
//     constrs: &mut Vec<ModeConstr>,
//     expr: &flat::Expr,
//     future: &annot::SigType,
// ) -> annot::SigExpr {
//     match (expr, future) {
//         (flat::Expr::Local(id), _) => annot::Expr::Local(*id),
//         (flat::Expr::Call(_, _, _), _) => todo!(),
//         (flat::Expr::Branch(_, _, _), _) => todo!(),
//         (flat::Expr::LetMany(bindings, body), future) => {
//             ty_ctx.with_scope(|ty_ctx| {
//                 let locals_offset = ty_ctx.len();
//
//                 for (ty, _) in bindings {
//                     if ty_ctx.len() == body.0 {
//                         ty_ctx.add_local(future.clone());
//                     } else {
//                         ty_ctx.add_local(lift_type(&mut || ModeTerm::var(mode_gen.fresh()), ty));
//                     }
//                 }
//
//                 let mut new_bindings = Vec::with_capacity(bindings.len());
//
//                 for (i, (_, expr)) in bindings.iter().enumerate().rev() {
//                     let binding_local = flat::LocalId(locals_offset + i);
//                     let new_type = ty_ctx.local_binding(binding_local).clone();
//
//                     // Note: After truncation, `ty_ctx` contains all locals *strictly* before
//                     // `binding_local`.
//                     ty_ctx.truncate(binding_local.0);
//                     let new_expr = annot_expr(
//                         mode_gen, def_ctx, scope_ctx, ty_ctx, constrs, expr, &new_type,
//                     );
//                     new_bindings.push((new_type, new_expr));
//                 }
//
//                 annot::Expr::LetMany(new_bindings, *body)
//             })
//         }
//         (flat::Expr::Tuple(_), _) => todo!(),
//         (flat::Expr::TupleField(_, _), _) => todo!(),
//         (flat::Expr::WrapVariant(_, _, _), _) => todo!(),
//         (flat::Expr::UnwrapVariant(_, _), _) => todo!(),
//         (flat::Expr::WrapBoxed(_, _), _) => todo!(),
//         (flat::Expr::UnwrapBoxed(_, _), _) => todo!(),
//         (flat::Expr::WrapCustom(_, _), _) => todo!(),
//         (flat::Expr::UnwrapCustom(_, _), _) => todo!(),
//         (flat::Expr::Intrinsic(op, id), _) => annot::Expr::Intrinsic(*op, *id),
//         (flat::Expr::ArrayOp(_), _) => todo!(),
//         (flat::Expr::IoOp(op), _) => annot::Expr::IoOp(*op),
//         (flat::Expr::Panic(_, _), _) => todo!(),
//         (flat::Expr::ArrayLit(_, _), _) => todo!(),
//         (flat::Expr::BoolLit(val), annot::Type::Bool) => annot::Expr::BoolLit(*val),
//         (flat::Expr::ByteLit(val), annot::Type::Num(NumType::Byte)) => annot::Expr::ByteLit(*val),
//         (flat::Expr::IntLit(val), annot::Type::Num(NumType::Int)) => annot::Expr::IntLit(*val),
//         (flat::Expr::FloatLit(val), annot::Type::Num(NumType::Float)) => {
//             annot::Expr::FloatLit(*val)
//         }
//         _ => panic!("Type mismatch"),
//     }
// }
//
// fn push_constr_le(constrs: &mut Vec<ModeConstr>, lhs: &ModeTerm, rhs: &ModeTerm) {
//     constrs.push(ModeConstr(lhs.clone(), rhs.clone()));
// }
//
// fn push_constr_eq(constrs: &mut Vec<ModeConstr>, lhs: &ModeTerm, rhs: &ModeTerm) {
//     push_constr_le(constrs, lhs, rhs);
//     push_constr_le(constrs, rhs, lhs);
// }
//
// fn mode_bind_ctor(
//     constrs: &mut Vec<ModeConstr>,
//     intrinsic_type: &annot::IntrinsicType<ModeTerm>,
//     ty: &annot::Type<ModeTerm>,
// ) {
//     match (intrinsic_type, ty) {
//         (annot::IntrinsicType::Bool, annot::Type::Bool) => {}
//         (annot::IntrinsicType::Num(_), annot::Type::Num(_)) => {}
//         (annot::IntrinsicType::Tuple(tys1), annot::Type::Tuple(tys2)) => {
//             assert_eq!(tys1.len(), tys2.len());
//             for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
//                 mode_bind_ctor(constrs, ty1, ty2);
//             }
//         }
//         (annot::IntrinsicType::Variants(tys1), annot::Type::Variants(tys2)) => {
//             assert_eq!(tys1.len(), tys2.len());
//             for ((_, ty1), (_, ty2)) in tys1.iter().zip(tys2.iter()) {
//                 mode_bind_ctor(constrs, ty1, ty2);
//             }
//         }
//         (annot::IntrinsicType::Custom(id1), annot::Type::Custom(id2)) => {
//             assert_eq!(id1, id2);
//         }
//         (annot::IntrinsicType::Array(ty, mode), annot::Type::Array(_, annot)) => {
//             push_constr_eq(constrs, mode, &annot.mode);
//             mode_bind_intrinsic(constrs, ty, &annot.intrinsic_type);
//         }
//         (annot::IntrinsicType::HoleArray(ty, mode), annot::Type::HoleArray(_, annot)) => {
//             push_constr_eq(constrs, mode, &annot.mode);
//             mode_bind_intrinsic(constrs, ty, &annot.intrinsic_type);
//         }
//         (annot::IntrinsicType::Boxed(ty, mode), annot::Type::Boxed(_, annot)) => {
//             push_constr_eq(constrs, mode, &annot.mode);
//             mode_bind_intrinsic(constrs, ty, &annot.intrinsic_type);
//         }
//         _ => panic!("Type mismatch"),
//     }
// }
//
// fn mode_bind(
//     constrs: &mut Vec<ModeConstr>,
//     ty1: &annot::Type<ModeTerm>,
//     ty2: &annot::Type<ModeTerm>,
// ) {
//     match (ty1, ty2) {
//         (annot::Type::Bool, annot::Type::Bool) => {}
//         (annot::Type::Num(_), annot::Type::Num(_)) => {}
//         (annot::Type::Tuple(tys1), annot::Type::Tuple(tys2)) => {
//             assert_eq!(tys1.len(), tys2.len());
//             for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
//                 mode_bind(constrs, ty1, ty2);
//             }
//         }
//         (annot::Type::Variants(tys1), annot::Type::Variants(tys2)) => {
//             assert_eq!(tys1.len(), tys2.len());
//             for ((_, ty1), (_, ty2)) in tys1.iter().zip(tys2.iter()) {
//                 mode_bind(constrs, ty1, ty2);
//             }
//         }
//         (annot::Type::Custom(id1), annot::Type::Custom(id2)) => {
//             assert_eq!(id1, id2);
//         }
//         (annot::Type::Array(ty1, annot1), annot::Type::Array(ty2, annot2)) => {
//             push_constr_eq(constrs, &annot1.mode, &annot2.mode);
//             mode_bind(constrs, ty1, ty2);
//             mode_bind_intrinsic(constrs, &annot1.intrinsic_type, &annot2.intrinsic_ty);
//         }
//         (annot::Type::HoleArray(ty1, annot1), annot::Type::HoleArray(ty2, annot2)) => {
//             push_constr_eq(constrs, &annot1.mode, &annot2.mode);
//             mode_bind(constrs, ty1, ty2);
//             mode_bind_intrinsic(constrs, &annot1.intrinsic_type, &annot2.intrinsic_ty);
//         }
//         (annot::Type::Boxed(ty1, annot1), annot::Type::Boxed(ty2, annot2)) => {
//             push_constr_eq(constrs, &annot1.mode, &annot2.mode);
//             mode_bind(constrs, ty1, ty2);
//             mode_bind_intrinsic(constrs, &annot1.intrinsic_type, &annot2.intrinsic_ty);
//         }
//         _ => panic!("Type mismatch"),
//     }
// }
//
// fn mode_bind_intrinsic(
//     constrs: &mut Vec<ModeConstr>,
//     ty1: &annot::IntrinsicType<ModeTerm>,
//     ty2: &annot::IntrinsicType<ModeTerm>,
// ) {
//     match (ty1, ty2) {
//         (annot::IntrinsicType::Bool, annot::IntrinsicType::Bool) => {}
//         (annot::IntrinsicType::Num(_), annot::IntrinsicType::Num(_)) => {}
//         (annot::IntrinsicType::Tuple(tys1), annot::IntrinsicType::Tuple(tys2)) => {
//             assert_eq!(tys1.len(), tys2.len());
//             for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
//                 mode_bind_intrinsic(constrs, ty1, ty2);
//             }
//         }
//         (annot::IntrinsicType::Variants(tys1), annot::IntrinsicType::Variants(tys2)) => {
//             assert_eq!(tys1.len(), tys2.len());
//             for ((_, ty1), (_, ty2)) in tys1.iter().zip(tys2.iter()) {
//                 mode_bind_intrinsic(constrs, ty1, ty2);
//             }
//         }
//         (annot::IntrinsicType::Custom(id1), annot::IntrinsicType::Custom(id2)) => {
//             assert_eq!(id1, id2);
//         }
//         (annot::IntrinsicType::Array(ty1, mode1), annot::IntrinsicType::Array(ty2, mode2)) => {
//             push_constr_eq(constrs, mode1, mode2);
//             mode_bind_intrinsic(constrs, ty1, ty2);
//         }
//         (
//             annot::IntrinsicType::HoleArray(ty1, mode1),
//             annot::IntrinsicType::HoleArray(ty2, mode2),
//         ) => {
//             push_constr_eq(constrs, mode1, mode2);
//             mode_bind_intrinsic(constrs, ty1, ty2);
//         }
//         (annot::IntrinsicType::Boxed(ty1, mode1), annot::IntrinsicType::Boxed(ty2, mode2)) => {
//             push_constr_eq(constrs, mode1, mode2);
//             mode_bind_intrinsic(constrs, ty1, ty2);
//         }
//         _ => panic!("Type mismatch"),
//     }
// }
