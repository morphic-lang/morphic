use crate::data::pure_ast as pure;
use crate::data::purity::{self, Purity};
use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;
use crate::intrinsic_config::intrinsic_sig;
use id_collections::id_type;

// The purity annotations in the source code are just for the user's benefit. Up through type
// checking "debug_output" is treated as pure, but in the rest of the compiler it should be treated
// as impure since it *actually* is impure. This pass infers the real purity annotations.

#[id_type]
struct PurityVar(pub usize);

pub fn purity_infer(prog: typed::Program) -> pure::Program {
    pure::Program {
        mod_symbols: prog.mod_symbols,
        custom_types: prog.custom_types,
        custom_type_symbols: prog.custom_type_symbols,
        profile_points: prog.profile_points,
        vals: prog.vals.map(|_, val| infer_val(val)),
        val_symbols: prog.val_symbols,
        main: prog.main,
    }
}

pub fn count_params(ty: &res::Type) -> usize {
    match ty {
        res::Type::Var(_) => 0,
        res::Type::App(_, args) => args.iter().map(count_params).sum(),
        res::Type::Tuple(args) => args.iter().map(count_params).sum(),
        res::Type::Func(_, arg, ret) => count_params(arg) + count_params(ret) + 1,
    }
}

fn infer_val(val: typed::ValDef) -> pure::ValDef<Purity> {
    let (body, ty, _purity) = infer_expr(val.body, val.scheme.body);
    pure::ValDef {
        scheme: res::TypeScheme {
            num_params: val.scheme.num_params,
            body: ty,
        },
        body,
    }
}

fn infer_global(id: res::GlobalId) -> (pure::GlobalId, Purity) {
    match id {
        res::GlobalId::Intrinsic(intr) => {
            (pure::GlobalId::Intrinsic(intr), intrinsic_sig(intr).purity)
        }
        res::GlobalId::ArrayOp(op) => (pure::GlobalId::ArrayOp(op), res::array_op_purity(op)),
        res::GlobalId::IoOp(op) => {
            // After this pass, we turn "debug_output" into "output" since they are effectively the
            // same. Maybe we should thread the distinction through for debuggability?
            let op = match op {
                res::IoOp::Input => pure::IoOp::Input,
                res::IoOp::Output => pure::IoOp::Output,
                res::IoOp::DebugOutput => pure::IoOp::Output,
            };
            (pure::GlobalId::IoOp(op), pure::io_op_purity(op))
        }
        res::GlobalId::Panic => (pure::GlobalId::Panic, Purity::Impure),
        res::GlobalId::Ctor(ty, variant) => (pure::GlobalId::Ctor(ty, variant), Purity::Pure),
        res::GlobalId::Custom(id) => (pure::GlobalId::Custom(id), Purity::Pure),
    }
}

fn infer_expr(expr: typed::Expr, ty: res::Type) -> (pure::Expr, res::Type, Purity) {
    todo!()
}

// fn infer_expr(expr: typed::Expr, ty: res::Type) -> (pure::Expr, res::Type, Purity) {
//     match (expr, ty) {
//         typed::Expr::Global(id, param_vars) => {
//             let (id, purity) = infer_global(id);
//             (pure::Expr::Global(id, param_vars), purity)
//         }
//         typed::Expr::Local(id) => (pure::Expr::Local(id), Purity::Pure),
//         typed::Expr::Tuple(exprs) => {
//             let (exprs, purities): (Vec<_>, Vec<_>) = exprs.into_iter().map(infer_expr).unzip();
//             (
//                 pure::Expr::Tuple(exprs),
//                 purities.into_iter().fold(Purity::Pure, purity::meet),
//             )
//         }
//         typed::Expr::Lam(_purity, arg, ret, pat, body, profile_point) => {
//             // throw away the purity annotation and reinfer it
//             let (body, purity) = infer_expr(*body);
//             (
//                 pure::Expr::Lam(purity, arg, ret, pat, Box::new(body), profile_point),
//                 purity,
//             )
//         }
//         typed::Expr::App(_purity, func, arg) => {
//             // throw away the purity annotation and reinfer it
//             let (func, func_purity) = infer_expr(*func);
//             let (arg, arg_purity) = infer_expr(*arg);
//             let purity = purity::meet(func_purity, arg_purity);
//             (
//                 pure::Expr::App(purity, Box::new(func), Box::new(arg)),
//                 purity,
//             )
//         }
//         typed::Expr::Match(discrim, cases, ty) => {
//             let (discrim, discrim_purity) = infer_expr(*discrim);
//             let (cases, case_purities): (Vec<_>, Vec<_>) = cases
//                 .into_iter()
//                 .map(|(pat, expr)| {
//                     let (expr, purity) = infer_expr(expr);
//                     ((pat, expr), purity)
//                 })
//                 .unzip();
//             (
//                 pure::Expr::Match(Box::new(discrim), cases, ty),
//                 std::iter::once(discrim_purity)
//                     .chain(case_purities.into_iter())
//                     .fold(Purity::Pure, purity::meet),
//             )
//         }
//         typed::Expr::LetMany(bindings, body) => {
//             let (bindings, binding_purities): (Vec<_>, Vec<_>) = bindings
//                 .into_iter()
//                 .map(|(pat, expr)| {
//                     let (expr, purity) = infer_expr(expr);
//                     ((pat, expr), purity)
//                 })
//                 .unzip();
//             let (body, body_purity) = infer_expr(*body);
//             (
//                 pure::Expr::LetMany(bindings, Box::new(body)),
//                 std::iter::once(body_purity)
//                     .chain(binding_purities.into_iter())
//                     .fold(Purity::Pure, purity::meet),
//             )
//         }
//         typed::Expr::ArrayLit(ty, exprs) => {
//             let (exprs, purities): (Vec<_>, Vec<_>) = exprs.into_iter().map(infer_expr).unzip();
//             (
//                 pure::Expr::ArrayLit(ty, exprs),
//                 purities.into_iter().fold(Purity::Pure, purity::meet),
//             )
//         }
//         (typed::Expr::ByteLit(x), ty) => (pure::Expr::ByteLit(x), ty, Purity::Pure),
//         (typed::Expr::IntLit(x), ty) => (pure::Expr::IntLit(x), ty, Purity::Pure),
//         (typed::Expr::FloatLit(x), ty) => (pure::Expr::FloatLit(x), ty, Purity::Pure),
//         (typed::Expr::Span(lo, hi, content), ty) => {
//             let (content, new_ty, purity) = infer_expr(*content, ty);
//             (pure::Expr::Span(lo, hi, Box::new(content)), new_ty, purity)
//         }
//     }
// }
