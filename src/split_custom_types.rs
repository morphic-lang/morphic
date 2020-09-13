// This is almost entirely boilerplate.  The most important logic is in the 'Ctor' cases of the
// `trans_expr` and `trans_pattern` functions.

use std::collections::BTreeSet;

use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::util::graph::{self, Graph};
use crate::util::id_vec::IdVec;

pub fn split_custom_types(program: &first_ord::Program) -> anon::Program {
    let boxed_variants = find_boxed_variants(&program.custom_types);

    let custom_types = program.custom_types.map(|custom, typedef| {
        match typedef.variants.len() {
            0 => anon::Type::Tuple(vec![]),
            1 => {
                // TODO: As an optimization, we might actually be able to eliminate boxing here in all
                // cases.
                trans_content_type(
                    boxed_variants[custom][first_ord::VariantId(0)],
                    &typedef.variants[first_ord::VariantId(0)],
                )
            }
            _ => anon::Type::Variants(trans_variants(&boxed_variants[custom], &typedef.variants)),
        }
    });

    let funcs = program.funcs.map(|_, func_def| anon::FuncDef {
        purity: func_def.purity,
        arg_type: trans_type(&func_def.arg_type),
        ret_type: trans_type(&func_def.ret_type),
        arg: trans_pattern(&program.custom_types, &boxed_variants, &func_def.arg),
        body: trans_expr(&program.custom_types, &boxed_variants, &func_def.body),
        profile_point: func_def.profile_point,
    });

    anon::Program {
        mod_symbols: program.mod_symbols.clone(),
        custom_types,
        custom_type_symbols: program.custom_type_symbols.clone(),
        funcs,
        func_symbols: program.func_symbols.clone(),
        profile_points: program.profile_points.clone(),
        main: program.main,
    }
}

fn add_size_deps(type_: &first_ord::Type, deps: &mut BTreeSet<first_ord::CustomTypeId>) {
    match type_ {
        first_ord::Type::Bool | first_ord::Type::Num(_) => {}

        first_ord::Type::Array(_) | first_ord::Type::HoleArray(_) => {}

        first_ord::Type::Tuple(items) => {
            for item in items {
                add_size_deps(item, deps)
            }
        }

        first_ord::Type::Custom(custom) => {
            deps.insert(*custom);
        }
    }
}

fn needs_boxing(scc: &BTreeSet<first_ord::CustomTypeId>, type_: &first_ord::Type) -> bool {
    match type_ {
        first_ord::Type::Bool | first_ord::Type::Num(_) => false,

        first_ord::Type::Array(_) | first_ord::Type::HoleArray(_) => false,

        first_ord::Type::Tuple(items) => items.iter().any(|item| needs_boxing(scc, item)),

        first_ord::Type::Custom(custom) => scc.contains(custom),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Ord, PartialOrd)]
enum IsBoxed {
    Unboxed,
    Boxed,
}

fn find_boxed_variants(
    typedefs: &IdVec<first_ord::CustomTypeId, first_ord::TypeDef>,
) -> IdVec<first_ord::CustomTypeId, IdVec<first_ord::VariantId, IsBoxed>> {
    let size_deps = Graph {
        edges_out: typedefs.map(|_, def| {
            let mut deps = BTreeSet::new();
            for (_, variant) in &def.variants {
                if let Some(content) = variant {
                    add_size_deps(content, &mut deps);
                }
            }
            deps.into_iter().collect()
        }),
    };

    let sccs = graph::strongly_connected(&size_deps);

    let mut boxed_variants = IdVec::from_items(vec![None; typedefs.len()]);

    for scc_vec in sccs {
        let scc: BTreeSet<_> = scc_vec.into_iter().collect();

        for custom in &scc {
            debug_assert!(boxed_variants[custom].is_none());
            boxed_variants[custom] =
                Some(typedefs[custom].variants.map(|_, variant| match variant {
                    Some(content) => {
                        if needs_boxing(&scc, content) {
                            IsBoxed::Boxed
                        } else {
                            IsBoxed::Unboxed
                        }
                    }
                    None => IsBoxed::Unboxed,
                }));
        }
    }

    boxed_variants.into_mapped(|_, variants| variants.unwrap())
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

fn trans_content_type(is_boxed: IsBoxed, content: &Option<first_ord::Type>) -> anon::Type {
    let content_trans = match content {
        Some(type_) => trans_type(type_),
        None => anon::Type::Tuple(Vec::new()),
    };

    match is_boxed {
        IsBoxed::Unboxed => content_trans,
        IsBoxed::Boxed => anon::Type::Boxed(Box::new(content_trans)),
    }
}

fn trans_variants(
    boxed: &IdVec<first_ord::VariantId, IsBoxed>,
    variants: &IdVec<first_ord::VariantId, Option<first_ord::Type>>,
) -> IdVec<first_ord::VariantId, anon::Type> {
    assert![variants.len() != 1];
    variants.map(|variant_id, content| trans_content_type(boxed[variant_id], content))
}

fn trans_expr(
    typedefs: &IdVec<first_ord::CustomTypeId, first_ord::TypeDef>,
    boxed_variants: &IdVec<first_ord::CustomTypeId, IdVec<first_ord::VariantId, IsBoxed>>,
    expr: &first_ord::Expr,
) -> anon::Expr {
    match expr {
        first_ord::Expr::Intrinsic(intr, arg) => {
            anon::Expr::Intrinsic(*intr, Box::new(trans_expr(typedefs, boxed_variants, arg)))
        }

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Item(item_type, array, index)) => {
            anon::Expr::ArrayOp(anon::ArrayOp::Item(
                trans_type(item_type),
                Box::new(trans_expr(typedefs, boxed_variants, array)),
                Box::new(trans_expr(typedefs, boxed_variants, index)),
            ))
        }

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Len(item_type, array)) => {
            anon::Expr::ArrayOp(anon::ArrayOp::Len(
                trans_type(item_type),
                Box::new(trans_expr(typedefs, boxed_variants, array)),
            ))
        }

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Push(item_type, array, item)) => {
            anon::Expr::ArrayOp(anon::ArrayOp::Push(
                trans_type(item_type),
                Box::new(trans_expr(typedefs, boxed_variants, array)),
                Box::new(trans_expr(typedefs, boxed_variants, item)),
            ))
        }

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Pop(item_type, array)) => {
            anon::Expr::ArrayOp(anon::ArrayOp::Pop(
                trans_type(item_type),
                Box::new(trans_expr(typedefs, boxed_variants, array)),
            ))
        }

        first_ord::Expr::ArrayOp(first_ord::ArrayOp::Replace(item_type, hole_array, item)) => {
            anon::Expr::ArrayOp(anon::ArrayOp::Replace(
                trans_type(item_type),
                Box::new(trans_expr(typedefs, boxed_variants, hole_array)),
                Box::new(trans_expr(typedefs, boxed_variants, item)),
            ))
        }

        first_ord::Expr::IoOp(first_ord::IoOp::Input) => anon::Expr::IoOp(anon::IoOp::Input),

        first_ord::Expr::IoOp(first_ord::IoOp::Output(output)) => anon::Expr::IoOp(
            anon::IoOp::Output(Box::new(trans_expr(typedefs, boxed_variants, output))),
        ),

        first_ord::Expr::Panic(ret_type, message) => anon::Expr::Panic(
            trans_type(ret_type),
            Box::new(trans_expr(typedefs, boxed_variants, message)),
        ),

        first_ord::Expr::Ctor(type_id, variant, content) => {
            let content_trans = match content {
                Some(content) => trans_expr(typedefs, boxed_variants, content),
                None => anon::Expr::Tuple(Vec::new()),
            };

            let content_trans_maybe_boxed = match boxed_variants[type_id][variant] {
                IsBoxed::Unboxed => content_trans,
                IsBoxed::Boxed => anon::Expr::WrapBoxed(
                    Box::new(content_trans),
                    trans_type(
                        &typedefs[type_id].variants[variant]
                            .as_ref()
                            .expect("Only nonempty variants should be boxed"),
                    ),
                ),
            };

            anon::Expr::WrapCustom(
                *type_id,
                // It's impossible to construct a variant with 0 cases, so we don't need to handle that
                // case even though it uses a different type representation in the transformed AST.
                if typedefs[type_id].variants.len() != 1 {
                    Box::new(anon::Expr::WrapVariant(
                        trans_variants(&boxed_variants[type_id], &typedefs[type_id].variants),
                        *variant,
                        Box::new(content_trans_maybe_boxed),
                    ))
                } else {
                    Box::new(content_trans_maybe_boxed)
                },
            )
        }

        first_ord::Expr::Local(local_id) => anon::Expr::Local(*local_id),

        first_ord::Expr::Tuple(items) => anon::Expr::Tuple(
            items
                .iter()
                .map(|item| trans_expr(typedefs, boxed_variants, item))
                .collect(),
        ),

        first_ord::Expr::Call(purity, func, arg) => anon::Expr::Call(
            *purity,
            *func,
            Box::new(trans_expr(typedefs, boxed_variants, arg)),
        ),

        first_ord::Expr::Match(discrim, cases, result_type) => {
            if cases.len() != 1 {
                anon::Expr::Match(
                    Box::new(trans_expr(typedefs, boxed_variants, discrim)),
                    cases
                        .iter()
                        .map(|(pat, body)| {
                            (
                                trans_pattern(typedefs, boxed_variants, pat),
                                trans_expr(typedefs, boxed_variants, body),
                            )
                        })
                        .collect(),
                    trans_type(result_type),
                )
            } else {
                let (pat, body) = &cases[0];
                anon::Expr::LetMany(
                    vec![(
                        trans_pattern(typedefs, boxed_variants, pat),
                        trans_expr(typedefs, boxed_variants, discrim),
                    )],
                    Box::new(trans_expr(typedefs, boxed_variants, body)),
                )
            }
        }

        first_ord::Expr::LetMany(bindings, body) => anon::Expr::LetMany(
            bindings
                .iter()
                .map(|(lhs, rhs)| {
                    (
                        trans_pattern(typedefs, boxed_variants, lhs),
                        trans_expr(typedefs, boxed_variants, rhs),
                    )
                })
                .collect(),
            Box::new(trans_expr(typedefs, boxed_variants, body)),
        ),

        first_ord::Expr::ArrayLit(item_type, items) => anon::Expr::ArrayLit(
            trans_type(item_type),
            items
                .iter()
                .map(|item| trans_expr(typedefs, boxed_variants, item))
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
    boxed_variants: &IdVec<first_ord::CustomTypeId, IdVec<first_ord::VariantId, IsBoxed>>,
    pat: &first_ord::Pattern,
) -> anon::Pattern {
    match pat {
        first_ord::Pattern::Any(type_) => anon::Pattern::Any(trans_type(type_)),
        first_ord::Pattern::Var(type_) => anon::Pattern::Var(trans_type(type_)),
        first_ord::Pattern::Tuple(items) => anon::Pattern::Tuple(
            items
                .iter()
                .map(|item| trans_pattern(typedefs, boxed_variants, item))
                .collect(),
        ),
        first_ord::Pattern::Ctor(type_id, variant, content) => {
            let content_trans = match content {
                Some(content) => trans_pattern(typedefs, boxed_variants, content),
                None => anon::Pattern::Tuple(Vec::new()),
            };

            let content_trans_maybe_boxed = match boxed_variants[type_id][variant] {
                IsBoxed::Unboxed => content_trans,
                IsBoxed::Boxed => anon::Pattern::Boxed(
                    Box::new(content_trans),
                    trans_type(
                        &typedefs[type_id].variants[variant]
                            .as_ref()
                            .expect("Only nonempty types should be boxed"),
                    ),
                ),
            };

            anon::Pattern::Custom(
                *type_id,
                // It's impossible to match on a variant with 0 cases, so we don't need to handle that
                // case even though it uses a different type representation in the transformed AST.
                if typedefs[type_id].variants.len() != 1 {
                    Box::new(anon::Pattern::Variant(
                        trans_variants(&boxed_variants[type_id], &typedefs[type_id].variants),
                        *variant,
                        Box::new(content_trans_maybe_boxed),
                    ))
                } else {
                    Box::new(content_trans_maybe_boxed)
                },
            )
        }
        first_ord::Pattern::BoolConst(val) => anon::Pattern::BoolConst(*val),
        first_ord::Pattern::ByteConst(val) => anon::Pattern::ByteConst(*val),
        first_ord::Pattern::IntConst(val) => anon::Pattern::IntConst(*val),
        first_ord::Pattern::FloatConst(val) => anon::Pattern::FloatConst(*val),
    }
}
