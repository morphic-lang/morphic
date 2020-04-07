// This is almost entirely boilerplate.  The most important logic is in the 'Ctor' cases of the
// `trans_expr` and `trans_pattern` functions.

use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::util::id_vec::IdVec;

pub fn split_custom_types(program: &first_ord::Program) -> anon::Program {
    let custom_types = program.custom_types.map(|_, typedef| {
        if typedef.variants.len() == 1 {
            trans_content_type(&typedef.variants[first_ord::VariantId(0)])
        } else {
            anon::Type::Variants(trans_variants(&typedef.variants))
        }
    });

    let funcs = program.funcs.map(|_, func_def| anon::FuncDef {
        purity: func_def.purity,
        arg_type: trans_type(&func_def.arg_type),
        ret_type: trans_type(&func_def.ret_type),
        arg: trans_pattern(&program.custom_types, &func_def.arg),
        body: trans_expr(&program.custom_types, &func_def.body),
    });

    anon::Program {
        mod_symbols: program.mod_symbols.clone(),
        custom_types,
        funcs,
        main: program.main,
    }
}

fn trans_type(type_: &first_ord::Type) -> anon::Type {
    match type_ {
        first_ord::Type::Bool => anon::Type::Bool,
        first_ord::Type::Num(num_type) => anon::Type::Num(*num_type),
        first_ord::Type::Array(item_type) => anon::Type::Array(Box::new(trans_type(item_type))),
        first_ord::Type::HoleArray(item_type) => {
            anon::Type::HoleArray(Box::new(trans_type(item_type)))
        }
        first_ord::Type::Tuple(items) => anon::Type::Tuple(items.iter().map(trans_type).collect()),
        first_ord::Type::Custom(type_id) => anon::Type::Custom(*type_id),
    }
}

fn trans_content_type(content: &Option<first_ord::Type>) -> anon::Type {
    match content {
        Some(type_) => trans_type(type_),
        None => anon::Type::Tuple(Vec::new()),
    }
}

fn trans_variants(
    variants: &IdVec<first_ord::VariantId, Option<first_ord::Type>>,
) -> IdVec<first_ord::VariantId, anon::Type> {
    assert![variants.len() != 1];
    variants.map(|_, content| trans_content_type(content))
}

fn trans_expr(
    typedefs: &IdVec<first_ord::CustomTypeId, first_ord::TypeDef>,
    expr: &first_ord::Expr,
) -> anon::Expr {
    match expr {
        first_ord::Expr::ArithOp(first_ord::ArithOp::Op(num_type, op, left, right)) => {
            anon::Expr::ArithOp(anon::ArithOp::Op(
                *num_type,
                *op,
                Box::new(trans_expr(typedefs, left)),
                Box::new(trans_expr(typedefs, right)),
            ))
        }

        first_ord::Expr::ArithOp(first_ord::ArithOp::Cmp(num_type, cmp, left, right)) => {
            anon::Expr::ArithOp(anon::ArithOp::Cmp(
                *num_type,
                *cmp,
                Box::new(trans_expr(typedefs, left)),
                Box::new(trans_expr(typedefs, right)),
            ))
        }

        first_ord::Expr::ArithOp(first_ord::ArithOp::Negate(num_type, body)) => {
            anon::Expr::ArithOp(anon::ArithOp::Negate(
                *num_type,
                Box::new(trans_expr(typedefs, body)),
            ))
        }

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Item(item_type, array, index)) => {
            anon::Expr::ArrayOp(anon::ArrayOp::Item(
                trans_type(item_type),
                Box::new(trans_expr(typedefs, array)),
                Box::new(trans_expr(typedefs, index)),
            ))
        }

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Len(item_type, array)) => anon::Expr::ArrayOp(
            anon::ArrayOp::Len(trans_type(item_type), Box::new(trans_expr(typedefs, array))),
        ),

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Push(item_type, array, item)) => {
            anon::Expr::ArrayOp(anon::ArrayOp::Push(
                trans_type(item_type),
                Box::new(trans_expr(typedefs, array)),
                Box::new(trans_expr(typedefs, item)),
            ))
        }

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Pop(item_type, array)) => anon::Expr::ArrayOp(
            anon::ArrayOp::Pop(trans_type(item_type), Box::new(trans_expr(typedefs, array))),
        ),

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Replace(item_type, hole_array, item)) => {
            anon::Expr::ArrayOp(anon::ArrayOp::Replace(
                trans_type(item_type),
                Box::new(trans_expr(typedefs, hole_array)),
                Box::new(trans_expr(typedefs, item)),
            ))
        }

        first_ord::Expr::IoOp(first_ord::IoOp::Input) => anon::Expr::IoOp(anon::IoOp::Input),

        first_ord::Expr::IoOp(first_ord::IoOp::Output(output)) => {
            anon::Expr::IoOp(anon::IoOp::Output(Box::new(trans_expr(typedefs, output))))
        }

        first_ord::Expr::Ctor(type_id, variant, content) => anon::Expr::WrapCustom(
            *type_id,
            if typedefs[type_id].variants.len() != 1 {
                Box::new(anon::Expr::WrapVariant(
                    trans_variants(&typedefs[type_id].variants),
                    *variant,
                    Box::new(match content {
                        Some(content) => trans_expr(typedefs, content),
                        None => anon::Expr::Tuple(Vec::new()),
                    }),
                ))
            } else {
                Box::new(match content {
                    Some(content) => trans_expr(typedefs, content),
                    None => anon::Expr::Tuple(Vec::new()),
                })
            },
        ),

        first_ord::Expr::Local(local_id) => anon::Expr::Local(*local_id),

        first_ord::Expr::Tuple(items) => anon::Expr::Tuple(
            items
                .iter()
                .map(|item| trans_expr(typedefs, item))
                .collect(),
        ),

        first_ord::Expr::Call(purity, func, arg) => {
            anon::Expr::Call(*purity, *func, Box::new(trans_expr(typedefs, arg)))
        }

        first_ord::Expr::Match(discrim, cases, result_type) => {
            if cases.len() != 1 {
                anon::Expr::Match(
                    Box::new(trans_expr(typedefs, discrim)),
                    cases
                        .iter()
                        .map(|(pat, body)| {
                            (trans_pattern(typedefs, pat), trans_expr(typedefs, body))
                        })
                        .collect(),
                    trans_type(result_type),
                )
            } else {
                let (pat, body) = &cases[0];
                anon::Expr::LetMany(
                    vec![(trans_pattern(typedefs, pat), trans_expr(typedefs, discrim))],
                    Box::new(trans_expr(typedefs, body)),
                )
            }
        }

        first_ord::Expr::LetMany(bindings, body) => anon::Expr::LetMany(
            bindings
                .iter()
                .map(|(lhs, rhs)| (trans_pattern(typedefs, lhs), trans_expr(typedefs, rhs)))
                .collect(),
            Box::new(trans_expr(typedefs, body)),
        ),

        first_ord::Expr::ArrayLit(item_type, items) => anon::Expr::ArrayLit(
            trans_type(item_type),
            items
                .iter()
                .map(|item| trans_expr(typedefs, item))
                .collect(),
        ),

        first_ord::Expr::BoolLit(val) => anon::Expr::BoolLit(*val),
        first_ord::Expr::ByteLit(val) => anon::Expr::ByteLit(*val),
        first_ord::Expr::IntLit(val) => anon::Expr::IntLit(*val),
        first_ord::Expr::FloatLit(val) => anon::Expr::FloatLit(*val),
    }
}

fn trans_pattern(
    typedefs: &IdVec<first_ord::CustomTypeId, first_ord::TypeDef>,
    pat: &first_ord::Pattern,
) -> anon::Pattern {
    match pat {
        first_ord::Pattern::Any(type_) => anon::Pattern::Any(trans_type(type_)),
        first_ord::Pattern::Var(type_) => anon::Pattern::Var(trans_type(type_)),
        first_ord::Pattern::Tuple(items) => anon::Pattern::Tuple(
            items
                .iter()
                .map(|item| trans_pattern(typedefs, item))
                .collect(),
        ),
        first_ord::Pattern::Ctor(type_id, variant, content) => anon::Pattern::Custom(
            *type_id,
            if typedefs[type_id].variants.len() != 1 {
                Box::new(anon::Pattern::Variant(
                    trans_variants(&typedefs[type_id].variants),
                    *variant,
                    Box::new(match content {
                        Some(content) => trans_pattern(typedefs, content),
                        None => anon::Pattern::Tuple(Vec::new()),
                    }),
                ))
            } else {
                Box::new(match content {
                    Some(content) => trans_pattern(typedefs, content),
                    None => anon::Pattern::Tuple(Vec::new()),
                })
            },
        ),
        first_ord::Pattern::BoolConst(val) => anon::Pattern::BoolConst(*val),
        first_ord::Pattern::ByteConst(val) => anon::Pattern::ByteConst(*val),
        first_ord::Pattern::IntConst(val) => anon::Pattern::IntConst(*val),
        first_ord::Pattern::FloatConst(val) => anon::Pattern::FloatConst(*val),
    }
}
