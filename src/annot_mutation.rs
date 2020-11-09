use im_rc::{vector, OrdMap, OrdSet, Vector};

use crate::data::alias_annot_ast as alias;
use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast as annot;
use crate::field_path::{get_names_in, split_at_fold, translate_callee_cond_disj};
use crate::fixed_point::{annot_all, Signature, SignatureAssumptions};
use crate::mutation_status::translate_callee_status_cond_disj;
use crate::util::disjunction::Disj;
use crate::util::id_vec::IdVec;

impl Signature for annot::FuncDef {
    type Sig = annot::MutationSig;

    fn signature(&self) -> &Self::Sig {
        &self.mutation_sig
    }
}

pub fn annot_mutation(program: alias::Program) -> annot::Program {
    let funcs = annot_all(
        program.funcs.len(),
        |sig_assumptions, func| annot_func(&program, sig_assumptions, &program.funcs[func]),
        &program.sccs,
    );

    annot::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs,
        func_symbols: program.func_symbols,
        profile_points: program.profile_points,
        main: program.main,
        sccs: program.sccs,
    }
}

#[derive(Clone, Debug)]
struct LocalInfo {
    type_: anon::Type,
    statuses: OrdMap<alias::FieldPath, annot::LocalStatus>,
}

#[derive(Clone, Debug)]
struct ExprInfo {
    mutations: Vec<(flat::LocalId, alias::FieldPath, Disj<alias::AliasCondition>)>,
    val_statuses: OrdMap<alias::FieldPath, annot::LocalStatus>,
}

fn trivial_info() -> ExprInfo {
    ExprInfo {
        mutations: Vec::new(),
        val_statuses: OrdMap::new(),
    }
}

fn empty_statuses(
    typedefs: &IdVec<first_ord::CustomTypeId, anon::Type>,
    type_: &anon::Type,
) -> OrdMap<alias::FieldPath, annot::LocalStatus> {
    get_names_in(typedefs, type_)
        .into_iter()
        .map(|(name, _)| {
            (
                name,
                annot::LocalStatus {
                    mutated_cond: Disj::new(),
                },
            )
        })
        .collect()
}

fn array_extraction_statuses(
    orig: &alias::Program,
    ctx: &OrdMap<flat::LocalId, LocalInfo>,
    item_type: &anon::Type,
    array: flat::LocalId,
    ret_array_field: alias::Field,
    ret_item_field: alias::Field,
) -> OrdMap<alias::FieldPath, annot::LocalStatus> {
    let arg_info = &ctx[&array];

    let mut ret_statuses = OrdMap::new();

    for (item_path, _) in get_names_in(&orig.custom_types, item_type) {
        let mut arg_path = item_path.clone();
        arg_path.push_front(alias::Field::ArrayMembers);

        let mut ret_array_path = item_path.clone();
        ret_array_path.push_front(alias::Field::ArrayMembers);
        ret_array_path.push_front(ret_array_field);

        let mut ret_item_path = item_path.clone();
        ret_item_path.push_front(ret_item_field);

        let arg_path_status = &arg_info.statuses[&arg_path];

        ret_statuses.insert(ret_array_path, arg_path_status.clone());
        ret_statuses.insert(ret_item_path, arg_path_status.clone());
    }

    ret_statuses.insert(
        vector![ret_array_field],
        annot::LocalStatus {
            mutated_cond: Disj::new(),
        },
    );

    ret_statuses
}

fn array_insertion_statuses(
    orig: &alias::Program,
    ctx: &OrdMap<flat::LocalId, LocalInfo>,
    item_type: &anon::Type,
    array: flat::LocalId,
    item: flat::LocalId,
) -> OrdMap<alias::FieldPath, annot::LocalStatus> {
    let array_info = &ctx[&array];
    let item_info = &ctx[&item];

    let mut ret_statuses = OrdMap::new();

    for (item_path, _) in get_names_in(&orig.custom_types, item_type) {
        let mut array_path = item_path.clone();
        array_path.push_front(alias::Field::ArrayMembers);

        let arg_array_mut_cond = array_info.statuses[&array_path].mutated_cond.clone();
        let arg_item_mut_cond = item_info.statuses[&item_path].mutated_cond.clone();

        ret_statuses.insert(
            array_path,
            annot::LocalStatus {
                mutated_cond: arg_array_mut_cond.or(arg_item_mut_cond),
            },
        );
    }

    ret_statuses.insert(
        Vector::new(),
        annot::LocalStatus {
            mutated_cond: Disj::new(),
        },
    );

    ret_statuses
}

fn propagated_mutations(
    array: flat::LocalId,
    aliases: &alias::LocalAliases,
) -> Vec<(flat::LocalId, alias::FieldPath, Disj<alias::AliasCondition>)> {
    let mut mutations = vec![(array, Vector::new(), Disj::True)];
    for ((other, other_path), alias_cond) in &aliases.aliases {
        mutations.push((*other, other_path.clone(), alias_cond.clone()));
    }
    mutations
}

fn annot_expr(
    orig: &alias::Program,
    sigs: &SignatureAssumptions<first_ord::CustomFuncId, annot::FuncDef>,
    ctx: &OrdMap<flat::LocalId, LocalInfo>,
    expr: &alias::Expr,
) -> (annot::Expr, ExprInfo) {
    match expr {
        alias::Expr::Local(local) => (
            annot::Expr::Local(*local),
            ExprInfo {
                mutations: Vec::new(),
                val_statuses: ctx[local].statuses.clone(),
            },
        ),

        alias::Expr::Call(purity, func, arg_aliases, arg_folded_aliases, arg) => {
            let arg_info = &ctx[arg];

            let annot_expr = annot::Expr::Call(
                *purity,
                *func,
                arg_aliases.clone(),
                arg_folded_aliases.clone(),
                arg_info.statuses.clone(),
                *arg,
            );

            let ret_type = &orig.funcs[func].ret_type;

            let expr_info = match sigs.sig_of(func) {
                None => {
                    // On the first iteration of fixed point analysis, we assume all recursive calls
                    // return fresh (un-mutated) values, and do not mutate their arguments.
                    ExprInfo {
                        mutations: Vec::new(),
                        val_statuses: empty_statuses(&orig.custom_types, ret_type),
                    }
                }

                Some(sig) => {
                    let mut mutations = Vec::new();
                    for (alias::ArgName(arg_path), mut_cond) in &sig.arg_mutation_conds {
                        mutations.push((
                            *arg,
                            arg_path.clone(),
                            translate_callee_cond_disj(
                                *arg,
                                arg_aliases,
                                arg_folded_aliases,
                                mut_cond,
                            ),
                        ));

                        // Propagate mutations along aliasing edges
                        if mut_cond == &Disj::True {
                            for ((other, other_path), alias_cond) in &arg_aliases[arg_path].aliases
                            {
                                if other == arg {
                                    // The consequences of this aliasing relationship have already
                                    // been accounted for in the callee's signature.
                                    continue;
                                }

                                mutations.push((*other, other_path.clone(), alias_cond.clone()));
                            }
                        }
                    }

                    let val_statuses = sig
                        .ret_statuses
                        .iter()
                        .map(|(alias::RetName(ret_path), callee_status)| {
                            (
                                ret_path.clone(),
                                annot::LocalStatus {
                                    mutated_cond: translate_callee_status_cond_disj(
                                        *arg,
                                        arg_aliases,
                                        arg_folded_aliases,
                                        &arg_info.statuses,
                                        &callee_status.mutated_cond,
                                    ),
                                },
                            )
                        })
                        .collect();

                    ExprInfo {
                        mutations,
                        val_statuses,
                    }
                }
            };

            (annot_expr, expr_info)
        }

        alias::Expr::Branch(discrim, cases, result_type) => {
            let mut annot_cases = Vec::with_capacity(cases.len());
            let mut mutations = Vec::new();
            let mut val_statuses = empty_statuses(&orig.custom_types, result_type);

            for (cond, body) in cases {
                let (annot_body, body_info) = annot_expr(orig, sigs, ctx, body);
                annot_cases.push((cond.clone(), annot_body));

                for mutation in body_info.mutations {
                    mutations.push(mutation);
                }

                for (path, status) in body_info.val_statuses {
                    val_statuses[&path].mutated_cond.or_mut(status.mutated_cond);
                }
            }

            let annot_expr = annot::Expr::Branch(*discrim, annot_cases, result_type.clone());
            let expr_info = ExprInfo {
                mutations,
                val_statuses,
            };

            (annot_expr, expr_info)
        }

        alias::Expr::LetMany(bindings, final_local) => {
            let mut new_bindings = Vec::with_capacity(bindings.len());
            let mut mutations = Vec::new();

            let mut new_ctx = ctx.clone();
            for (type_, rhs) in bindings {
                let (annot_rhs, rhs_info) = annot_expr(orig, sigs, &new_ctx, rhs);

                new_bindings.push((type_.clone(), annot_rhs));

                for (other, other_path, mut_cond) in rhs_info.mutations {
                    if other.0 < ctx.len() {
                        // This is a mutation of a variable outside the scope of this `let`.
                        mutations.push((other, other_path.clone(), mut_cond.clone()));
                    }

                    new_ctx[&other].statuses[&other_path]
                        .mutated_cond
                        .or_mut(mut_cond.into_mapped(annot::MutationCondition::AliasCondition));
                }

                let lhs = flat::LocalId(new_ctx.len());
                debug_assert!(!new_ctx.contains_key(&lhs));

                let lhs_info = LocalInfo {
                    type_: type_.clone(),
                    statuses: rhs_info.val_statuses,
                };

                new_ctx.insert(lhs, lhs_info);
            }

            debug_assert_eq!(new_bindings.len(), bindings.len());

            (
                annot::Expr::LetMany(new_bindings, *final_local),
                ExprInfo {
                    mutations,
                    val_statuses: new_ctx[final_local].statuses.clone(),
                },
            )
        }

        alias::Expr::Tuple(items) => {
            let mut tuple_statuses = OrdMap::new();

            for (idx, item) in items.iter().enumerate() {
                let item_info = &ctx[item];

                for (item_path, _) in get_names_in(&orig.custom_types, &item_info.type_) {
                    let mut tuple_path = item_path.clone();
                    tuple_path.push_front(alias::Field::Field(idx));

                    tuple_statuses.insert(tuple_path, item_info.statuses[&item_path].clone());
                }
            }

            (
                annot::Expr::Tuple(items.clone()),
                ExprInfo {
                    mutations: Vec::new(),
                    val_statuses: tuple_statuses,
                },
            )
        }

        alias::Expr::TupleField(tuple, idx) => {
            let tuple_info = &ctx[tuple];

            let item_type = if let anon::Type::Tuple(item_types) = &tuple_info.type_ {
                &item_types[*idx]
            } else {
                unreachable!()
            };

            let mut item_statuses = OrdMap::new();
            for (item_path, _) in get_names_in(&orig.custom_types, item_type) {
                let mut tuple_path = item_path.clone();
                tuple_path.push_front(alias::Field::Field(*idx));

                item_statuses.insert(item_path, tuple_info.statuses[&tuple_path].clone());
            }

            (
                annot::Expr::TupleField(*tuple, *idx),
                ExprInfo {
                    mutations: Vec::new(),
                    val_statuses: item_statuses,
                },
            )
        }

        alias::Expr::WrapVariant(variant_types, variant_id, content) => {
            let content_info = &ctx[content];

            debug_assert_eq!(variant_types[variant_id], content_info.type_);

            let mut variant_statuses = OrdMap::new();
            for (idx, variant_type) in variant_types.iter() {
                for (path, _) in get_names_in(&orig.custom_types, variant_type) {
                    let mut variant_path = path.clone();
                    variant_path.push_front(alias::Field::Variant(idx));

                    variant_statuses.insert(
                        variant_path,
                        if idx == *variant_id {
                            content_info.statuses[&path].clone()
                        } else {
                            annot::LocalStatus {
                                mutated_cond: Disj::new(),
                            }
                        },
                    );
                }
            }

            (
                annot::Expr::WrapVariant(variant_types.clone(), *variant_id, *content),
                ExprInfo {
                    mutations: Vec::new(),
                    val_statuses: variant_statuses,
                },
            )
        }

        alias::Expr::UnwrapVariant(variant_id, variant) => {
            let variant_info = &ctx[variant];

            let content_type = if let anon::Type::Variants(variant_types) = &variant_info.type_ {
                &variant_types[variant_id]
            } else {
                unreachable!()
            };

            let mut content_statuses = OrdMap::new();
            for (content_path, _) in get_names_in(&orig.custom_types, content_type) {
                let mut variant_path = content_path.clone();
                variant_path.push_front(alias::Field::Variant(*variant_id));

                content_statuses.insert(content_path, variant_info.statuses[&variant_path].clone());
            }

            (
                annot::Expr::UnwrapVariant(*variant_id, *variant),
                ExprInfo {
                    mutations: Vec::new(),
                    val_statuses: content_statuses,
                },
            )
        }

        alias::Expr::WrapBoxed(content, content_type) => {
            let content_info = &ctx[content];

            debug_assert_eq!(&content_info.type_, content_type);

            let mut boxed_statuses = OrdMap::new();
            for (content_path, _) in get_names_in(&orig.custom_types, content_type) {
                let mut boxed_path = content_path.clone();
                boxed_path.push_front(alias::Field::Boxed);

                boxed_statuses.insert(boxed_path, content_info.statuses[&content_path].clone());
            }

            (
                annot::Expr::WrapBoxed(*content, content_type.clone()),
                ExprInfo {
                    mutations: Vec::new(),
                    val_statuses: boxed_statuses,
                },
            )
        }

        alias::Expr::UnwrapBoxed(boxed, content_type) => {
            let boxed_info = &ctx[boxed];

            let mut content_statuses = OrdMap::new();
            for (content_path, _) in get_names_in(&orig.custom_types, content_type) {
                let mut boxed_path = content_path.clone();
                boxed_path.push_front(alias::Field::Boxed);

                content_statuses.insert(content_path, boxed_info.statuses[&boxed_path].clone());
            }

            (
                annot::Expr::UnwrapBoxed(*boxed, content_type.clone()),
                ExprInfo {
                    mutations: Vec::new(),
                    val_statuses: content_statuses,
                },
            )
        }

        alias::Expr::WrapCustom(custom_id, content) => {
            let content_info = &ctx[content];

            debug_assert_eq!(&content_info.type_, &orig.custom_types[custom_id]);

            let mut wrapped_statuses =
                empty_statuses(&orig.custom_types, &anon::Type::Custom(*custom_id));

            for (content_path, _) in get_names_in(&orig.custom_types, &content_info.type_) {
                let (_, sub_path) = split_at_fold(*custom_id, content_path.clone());

                let mut wrapped_path = sub_path.0.clone();
                wrapped_path.push_front(alias::Field::Custom(*custom_id));

                wrapped_statuses[&wrapped_path]
                    .mutated_cond
                    .or_mut(content_info.statuses[&content_path].mutated_cond.clone());
            }

            (
                annot::Expr::WrapCustom(*custom_id, *content),
                ExprInfo {
                    mutations: Vec::new(),
                    val_statuses: wrapped_statuses,
                },
            )
        }

        alias::Expr::UnwrapCustom(custom_id, wrapped) => {
            let wrapped_info = &ctx[wrapped];

            debug_assert_eq!(&wrapped_info.type_, &anon::Type::Custom(*custom_id));

            let content_type = &orig.custom_types[custom_id];

            let mut content_statuses = OrdMap::new();
            for (content_path, _) in get_names_in(&orig.custom_types, content_type) {
                let (_, sub_path) = split_at_fold(*custom_id, content_path.clone());

                let mut wrapped_path = sub_path.0.clone();
                wrapped_path.push_front(alias::Field::Custom(*custom_id));

                content_statuses.insert(content_path, wrapped_info.statuses[&wrapped_path].clone());
            }

            (
                annot::Expr::UnwrapCustom(*custom_id, *wrapped),
                ExprInfo {
                    mutations: Vec::new(),
                    val_statuses: content_statuses,
                },
            )
        }

        // NOTE [intrinsics]: If we add array intrinsics in the future, this will need to be
        // modified.
        alias::Expr::Intrinsic(intr, arg) => (annot::Expr::Intrinsic(*intr, *arg), trivial_info()),

        alias::Expr::ArrayOp(alias::ArrayOp::Get(item_type, array_aliases, array, index)) => {
            let array_info = &ctx[array];

            let mut item_statuses = OrdMap::new();
            for (item_path, _) in get_names_in(&orig.custom_types, item_type) {
                let mut array_path = item_path.clone();
                array_path.push_front(alias::Field::ArrayMembers);

                item_statuses.insert(item_path, array_info.statuses[&array_path].clone());
            }

            (
                annot::Expr::ArrayOp(annot::ArrayOp::Get(
                    item_type.clone(),
                    array_aliases.clone(),
                    ctx[array].statuses[&Vector::new()].clone(),
                    *array,
                    *index,
                )),
                ExprInfo {
                    mutations: Vec::new(),
                    val_statuses: item_statuses,
                },
            )
        }

        alias::Expr::ArrayOp(alias::ArrayOp::Extract(item_type, array_aliases, array, index)) => (
            annot::Expr::ArrayOp(annot::ArrayOp::Extract(
                item_type.clone(),
                array_aliases.clone(),
                ctx[array].statuses[&Vector::new()].clone(),
                *array,
                *index,
            )),
            ExprInfo {
                mutations: propagated_mutations(*array, array_aliases),
                val_statuses: array_extraction_statuses(
                    orig,
                    ctx,
                    item_type,
                    *array,
                    alias::Field::Field(1), // hole array is the second return value
                    alias::Field::Field(0), // item is the first return value
                ),
            },
        ),

        alias::Expr::ArrayOp(alias::ArrayOp::Pop(item_type, array_aliases, array)) => (
            annot::Expr::ArrayOp(annot::ArrayOp::Pop(
                item_type.clone(),
                array_aliases.clone(),
                ctx[array].statuses[&Vector::new()].clone(),
                *array,
            )),
            ExprInfo {
                mutations: propagated_mutations(*array, array_aliases),
                val_statuses: array_extraction_statuses(
                    orig,
                    ctx,
                    item_type,
                    *array,
                    alias::Field::Field(0), // new array is the first return value
                    alias::Field::Field(1), // item is the second return value
                ),
            },
        ),

        alias::Expr::ArrayOp(alias::ArrayOp::Replace(
            item_type,
            array_aliases,
            hole_array,
            item,
        )) => (
            annot::Expr::ArrayOp(annot::ArrayOp::Replace(
                item_type.clone(),
                array_aliases.clone(),
                ctx[hole_array].statuses[&Vector::new()].clone(),
                *hole_array,
                *item,
            )),
            ExprInfo {
                mutations: propagated_mutations(*hole_array, array_aliases),
                val_statuses: array_insertion_statuses(orig, ctx, item_type, *hole_array, *item),
            },
        ),

        alias::Expr::ArrayOp(alias::ArrayOp::Push(item_type, array_aliases, array, item)) => (
            annot::Expr::ArrayOp(annot::ArrayOp::Push(
                item_type.clone(),
                array_aliases.clone(),
                ctx[array].statuses[&Vector::new()].clone(),
                *array,
                *item,
            )),
            ExprInfo {
                mutations: propagated_mutations(*array, array_aliases),
                val_statuses: array_insertion_statuses(orig, ctx, item_type, *array, *item),
            },
        ),

        alias::Expr::ArrayOp(alias::ArrayOp::Len(item_type, array_aliases, array)) => (
            annot::Expr::ArrayOp(annot::ArrayOp::Len(
                item_type.clone(),
                array_aliases.clone(),
                ctx[array].statuses[&Vector::new()].clone(),
                *array,
            )),
            trivial_info(),
        ),

        alias::Expr::IoOp(alias::IoOp::Input) => (
            annot::Expr::IoOp(annot::IoOp::Input),
            ExprInfo {
                mutations: Vec::new(),
                val_statuses: OrdMap::unit(
                    Vector::new(),
                    annot::LocalStatus {
                        mutated_cond: Disj::new(),
                    },
                ),
            },
        ),

        alias::Expr::IoOp(alias::IoOp::Output(bytes_aliases, bytes)) => (
            annot::Expr::IoOp(annot::IoOp::Output(
                bytes_aliases.clone(),
                ctx[bytes].statuses[&Vector::new()].clone(),
                *bytes,
            )),
            trivial_info(),
        ),

        alias::Expr::Panic(ret_type, _bytes_aliases, bytes) => (
            annot::Expr::Panic(
                ret_type.clone(),
                ctx[bytes].statuses[&Vector::new()].clone(),
                *bytes,
            ),
            ExprInfo {
                mutations: Vec::new(),
                val_statuses: empty_statuses(&orig.custom_types, ret_type),
            },
        ),

        alias::Expr::ArrayLit(item_type, items) => {
            let mut array_statuses = empty_statuses(
                &orig.custom_types,
                &anon::Type::Array(Box::new(item_type.clone())),
            );

            let item_paths = get_names_in(&orig.custom_types, item_type);

            for item in items {
                let item_info = &ctx[item];

                debug_assert_eq!(&item_info.type_, item_type);

                for (item_path, _) in &item_paths {
                    let mut array_path = item_path.clone();
                    array_path.push_front(alias::Field::ArrayMembers);

                    array_statuses[&array_path]
                        .mutated_cond
                        .or_mut(item_info.statuses[&item_path].mutated_cond.clone());
                }
            }

            (
                annot::Expr::ArrayLit(item_type.clone(), items.clone()),
                ExprInfo {
                    mutations: Vec::new(),
                    val_statuses: array_statuses,
                },
            )
        }

        &alias::Expr::BoolLit(val) => (annot::Expr::BoolLit(val), trivial_info()),
        &alias::Expr::ByteLit(val) => (annot::Expr::ByteLit(val), trivial_info()),
        &alias::Expr::IntLit(val) => (annot::Expr::IntLit(val), trivial_info()),
        &alias::Expr::FloatLit(val) => (annot::Expr::FloatLit(val), trivial_info()),
    }
}

fn annot_func(
    orig: &alias::Program,
    sigs: &SignatureAssumptions<first_ord::CustomFuncId, annot::FuncDef>,
    func_def: &alias::FuncDef,
) -> annot::FuncDef {
    let arg_names = get_names_in(&orig.custom_types, &func_def.arg_type)
        .into_iter()
        .map(|(name, _)| alias::ArgName(name))
        .collect::<Vec<_>>();

    let mut arg_init_statuses = OrdMap::new();
    for name in &arg_names {
        arg_init_statuses.insert(
            name.0.clone(),
            annot::LocalStatus {
                mutated_cond: Disj::Any(OrdSet::unit(annot::MutationCondition::ArgMutated(
                    name.clone(),
                ))),
            },
        );
    }

    let arg_info = LocalInfo {
        type_: func_def.arg_type.clone(),
        statuses: arg_init_statuses,
    };

    let init_ctx = OrdMap::unit(flat::ARG_LOCAL, arg_info);

    let (annot_body, body_info) = annot_expr(orig, sigs, &init_ctx, &func_def.body);

    let mut arg_mutation_conds = OrdMap::new();
    for name in arg_names {
        arg_mutation_conds.insert(name, Disj::new());
    }

    for (local, name, cond) in body_info.mutations {
        debug_assert_eq!(local, flat::ARG_LOCAL);
        arg_mutation_conds[&alias::ArgName(name.clone())].or_mut(cond);
    }

    let mutation_sig = annot::MutationSig {
        arg_mutation_conds,
        ret_statuses: body_info
            .val_statuses
            .into_iter()
            .map(|(name, status)| (alias::RetName(name), status))
            .collect(),
    };

    annot::FuncDef {
        purity: func_def.purity,
        arg_type: func_def.arg_type.clone(),
        ret_type: func_def.ret_type.clone(),
        alias_sig: func_def.alias_sig.clone(),
        mutation_sig,
        body: annot_body,
        profile_point: func_def.profile_point,
    }
}
