use std::collections::{BTreeMap, BTreeSet};

use crate::data::closure_annot_ast as annot;
use crate::data::lambda_lifted_ast as lifted;
use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp, IOOp};
use crate::util::constraint_graph::{ConstraintGraph, EquivClass, EquivClasses, SolverVarId};
use crate::util::graph::{self, Graph};
use crate::util::id_gen::IdGen;
use crate::util::id_vec::IdVec;
use crate::util::local_context::LocalContext;

fn count_params(
    parameterized: &IdVec<mono::CustomTypeId, Option<annot::TypeDef>>,
    type_: &mono::Type,
) -> usize {
    match type_ {
        mono::Type::Bool => 0,
        mono::Type::Byte => 0,
        mono::Type::Int => 0,
        mono::Type::Float => 0,
        mono::Type::Array(item) => count_params(parameterized, item),
        mono::Type::Tuple(items) => items
            .iter()
            .map(|item| count_params(parameterized, item))
            .sum(),
        mono::Type::Func(_, arg, ret) => {
            1 + count_params(parameterized, arg) + count_params(parameterized, ret)
        }
        mono::Type::Custom(other) => match &parameterized[other] {
            Some(typedef) => typedef.num_params,
            // This is a typedef in the same SCC; the reference to it here contributes no additional
            // parameters to the entire SCC.
            None => 0,
        },
    }
}

fn parameterize(
    parameterized: &IdVec<mono::CustomTypeId, Option<annot::TypeDef>>,
    scc_num_params: usize,
    id_gen: &mut IdGen<annot::RepParamId>,
    type_: &mono::Type,
) -> annot::Type<annot::RepParamId> {
    match type_ {
        mono::Type::Bool => annot::Type::Bool,
        mono::Type::Byte => annot::Type::Byte,
        mono::Type::Int => annot::Type::Int,
        mono::Type::Float => annot::Type::Float,

        mono::Type::Array(item) => annot::Type::Array(Box::new(parameterize(
            parameterized,
            scc_num_params,
            id_gen,
            item,
        ))),

        mono::Type::Tuple(items) => annot::Type::Tuple(
            items
                .iter()
                .map(|item| parameterize(parameterized, scc_num_params, id_gen, item))
                .collect(),
        ),

        mono::Type::Func(purity, arg, ret) => {
            let func_param = id_gen.fresh();
            let parameterized_arg = parameterize(parameterized, scc_num_params, id_gen, arg);
            let parameterized_ret = parameterize(parameterized, scc_num_params, id_gen, ret);
            annot::Type::Func(
                *purity,
                func_param,
                Box::new(parameterized_arg),
                Box::new(parameterized_ret),
            )
        }

        mono::Type::Custom(other) => {
            match &parameterized[other] {
                Some(typedef) => annot::Type::Custom(
                    *other,
                    IdVec::from_items((0..typedef.num_params).map(|_| id_gen.fresh()).collect()),
                ),

                None => {
                    // This is a typedef in the same SCC, so we need to parameterize it by
                    // all the SCC parameters.
                    annot::Type::Custom(
                        *other,
                        IdVec::from_items((0..scc_num_params).map(annot::RepParamId).collect()),
                    )
                }
            }
        }
    }
}

fn parameterize_typedef_scc(
    typedefs: &IdVec<mono::CustomTypeId, mono::TypeDef>,
    parameterized: &mut IdVec<mono::CustomTypeId, Option<annot::TypeDef>>,
    scc: &[mono::CustomTypeId],
) {
    let num_params = scc
        .iter()
        .map(|type_id| {
            typedefs[type_id]
                .variants
                .iter()
                .map(|(_variant_id, variant)| match variant {
                    Some(content) => count_params(parameterized, content),
                    None => 0,
                })
                .sum::<usize>()
        })
        .sum::<usize>();

    let mut id_gen = IdGen::new();

    let to_populate: BTreeMap<mono::CustomTypeId, _> = scc
        .iter()
        .map(|&type_id| {
            let typedef = &typedefs[type_id];
            let parameterized_variants = typedef.variants.map(|_variant_id, variant| {
                variant
                    .as_ref()
                    .map(|content| parameterize(parameterized, num_params, &mut id_gen, content))
            });

            debug_assert!(parameterized[type_id].is_none());

            (
                type_id,
                annot::TypeDef {
                    num_params,
                    variants: parameterized_variants,
                },
            )
        })
        .collect();

    debug_assert_eq!(id_gen.count(), num_params);

    for (type_id, typedef) in to_populate {
        debug_assert!(parameterized[type_id].is_none());
        parameterized[type_id] = Some(typedef);
    }
}

fn add_dependencies(type_: &mono::Type, deps: &mut BTreeSet<mono::CustomTypeId>) {
    match type_ {
        mono::Type::Bool => {}
        mono::Type::Byte => {}
        mono::Type::Int => {}
        mono::Type::Float => {}

        mono::Type::Array(item) => {
            add_dependencies(item, deps);
        }

        mono::Type::Tuple(items) => {
            for item in items {
                add_dependencies(item, deps);
            }
        }

        mono::Type::Func(_, arg, ret) => {
            add_dependencies(arg, deps);
            add_dependencies(ret, deps);
        }

        mono::Type::Custom(other) => {
            deps.insert(*other);
        }
    }
}

fn parameterize_typedefs(
    typedefs: &IdVec<mono::CustomTypeId, mono::TypeDef>,
) -> IdVec<mono::CustomTypeId, annot::TypeDef> {
    let dep_graph = Graph {
        edges_out: typedefs.map(|_id, typedef| {
            let mut deps = BTreeSet::new();
            for (_variant_id, variant) in &typedef.variants {
                if let Some(content) = variant {
                    add_dependencies(content, &mut deps);
                }
            }
            deps.into_iter().collect()
        }),
    };

    let sccs = graph::strongly_connected(&dep_graph);

    let mut parameterized = IdVec::from_items(vec![None; typedefs.len()]);

    for scc in sccs {
        parameterize_typedef_scc(typedefs, &mut parameterized, &scc);
    }

    parameterized.into_mapped(|_id, typedef| typedef.unwrap())
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum SolverRequirement {
    Lam(lifted::LamId, IdVec<annot::RepParamId, SolverVarId>),
    PendingLam(lifted::LamId),
    Template(annot::TemplateId, IdVec<annot::RepParamId, SolverVarId>),
    ArithOp(Op),
    ArrayOp(ArrayOp, annot::Type<SolverVarId>),
    ArrayReplace(annot::Type<SolverVarId>),
    IOOp(IOOp),
    Ctor(
        mono::CustomTypeId,
        IdVec<annot::RepParamId, SolverVarId>,
        res::VariantId,
    ),
}

#[derive(Clone, Debug)]
enum SolverExpr {
    ArithOp(Op, SolverVarId),
    ArrayOp(ArrayOp, annot::Type<SolverVarId>, SolverVarId),
    IOOp(IOOp, SolverVarId),
    NullaryCtor(
        mono::CustomTypeId,
        IdVec<annot::RepParamId, SolverVarId>,
        res::VariantId,
    ),
    Ctor(
        mono::CustomTypeId,
        IdVec<annot::RepParamId, SolverVarId>,
        res::VariantId,
        SolverVarId,
    ),
    Global(mono::CustomGlobalId, IdVec<annot::RepParamId, SolverVarId>),
    PendingGlobal(mono::CustomGlobalId), // A global belonging to the current SCC
    Local(lifted::LocalId),
    Capture(lifted::CaptureId),
    Tuple(Vec<SolverExpr>),
    Lam(
        lifted::LamId,
        IdVec<annot::RepParamId, SolverVarId>, // Parameters on the lambda
        SolverVarId,                           // Representation of the lambda expression
        IdVec<lifted::CaptureId, SolverExpr>,  // Captures
    ),
    PendingLam(
        lifted::LamId,
        SolverVarId,
        IdVec<lifted::CaptureId, SolverExpr>,
    ), // A lambda belonging to the current SCC
    App(
        Purity,
        SolverVarId, // Representation being called
        Box<SolverExpr>,
        Box<SolverExpr>,
        annot::Type<SolverVarId>, // Argument type
        annot::Type<SolverVarId>, // Return type
    ),
    Match(
        Box<SolverExpr>,
        Vec<(SolverPattern, SolverExpr)>,
        annot::Type<SolverVarId>,
    ),
    Let(SolverPattern, Box<SolverExpr>, Box<SolverExpr>),

    ArrayLit(
        annot::Type<SolverVarId>, // Item type
        Vec<SolverExpr>,
    ),
    BoolLit(bool),
    ByteLit(u8),
    IntLit(i64),
    FloatLit(f64),
}

#[derive(Clone, Debug)]
enum SolverPattern {
    Any(annot::Type<SolverVarId>),
    Var(annot::Type<SolverVarId>),
    Tuple(Vec<SolverPattern>),
    Ctor(
        mono::CustomTypeId,
        IdVec<annot::RepParamId, SolverVarId>,
        res::VariantId,
        Option<Box<SolverPattern>>,
    ),
    BoolConst(bool),
    ByteConst(u8),
    IntConst(i64),
    FloatConst(f64),
}

#[derive(Clone, Debug)]
struct SolverLamSig {
    purity: Purity,
    captures: IdVec<lifted::CaptureId, annot::Type<SolverVarId>>,
    arg: annot::Type<SolverVarId>,
    ret: annot::Type<SolverVarId>,
}

fn instantiate_mono(
    typedefs: &IdVec<mono::CustomTypeId, annot::TypeDef>,
    graph: &mut ConstraintGraph<SolverRequirement>,
    type_: &mono::Type,
) -> annot::Type<SolverVarId> {
    match type_ {
        mono::Type::Bool => annot::Type::Bool,
        mono::Type::Byte => annot::Type::Byte,
        mono::Type::Int => annot::Type::Int,
        mono::Type::Float => annot::Type::Float,

        mono::Type::Array(item) => {
            annot::Type::Array(Box::new(instantiate_mono(typedefs, graph, item)))
        }

        mono::Type::Tuple(items) => annot::Type::Tuple(
            items
                .iter()
                .map(|item| instantiate_mono(typedefs, graph, item))
                .collect(),
        ),

        mono::Type::Func(purity, arg, ret) => annot::Type::Func(
            *purity,
            graph.new_var(),
            Box::new(instantiate_mono(typedefs, graph, arg)),
            Box::new(instantiate_mono(typedefs, graph, ret)),
        ),

        mono::Type::Custom(custom) => {
            let vars = IdVec::from_items(
                (0..typedefs[custom].num_params)
                    .map(|_| graph.new_var())
                    .collect(),
            );

            annot::Type::Custom(*custom, vars)
        }
    }
}

fn equate_types(
    graph: &mut ConstraintGraph<SolverRequirement>,
    type1: &annot::Type<SolverVarId>,
    type2: &annot::Type<SolverVarId>,
) {
    match (type1, type2) {
        (annot::Type::Bool, annot::Type::Bool) => {}
        (annot::Type::Byte, annot::Type::Byte) => {}
        (annot::Type::Int, annot::Type::Int) => {}
        (annot::Type::Float, annot::Type::Float) => {}

        (annot::Type::Array(item1), annot::Type::Array(item2)) => {
            equate_types(graph, item1, item2);
        }

        (annot::Type::Tuple(items1), annot::Type::Tuple(items2)) => {
            debug_assert_eq!(items1.len(), items2.len());

            for (item1, item2) in items1.iter().zip(items2.iter()) {
                equate_types(graph, item1, item2);
            }
        }

        (
            annot::Type::Func(purity1, var1, arg1, ret1),
            annot::Type::Func(purity2, var2, arg2, ret2),
        ) => {
            debug_assert_eq!(purity1, purity2);

            graph.equate(*var1, *var2);

            equate_types(graph, arg1, arg2);
            equate_types(graph, ret1, ret2);
        }

        (annot::Type::Custom(custom1, args1), annot::Type::Custom(custom2, args2)) => {
            debug_assert_eq!(custom1, custom2);

            for (_, arg1, arg2) in args1.try_zip_exact(args2).expect(
                "Arguments lists for the same type constructor should always have the same length",
            ) {
                graph.equate(*arg1, *arg2);
            }
        }

        _ => unreachable!(),
    }
}

fn instantiate_subst(
    vars: &IdVec<annot::RepParamId, SolverVarId>,
    type_: &annot::Type<annot::RepParamId>,
) -> annot::Type<SolverVarId> {
    match type_ {
        annot::Type::Bool => annot::Type::Bool,
        annot::Type::Byte => annot::Type::Byte,
        annot::Type::Int => annot::Type::Int,
        annot::Type::Float => annot::Type::Float,

        annot::Type::Array(item) => annot::Type::Array(Box::new(instantiate_subst(vars, item))),

        annot::Type::Tuple(items) => annot::Type::Tuple(
            items
                .iter()
                .map(|item| instantiate_subst(vars, item))
                .collect(),
        ),

        annot::Type::Func(purity, id, arg, ret) => annot::Type::Func(
            *purity,
            vars[id],
            Box::new(instantiate_subst(vars, arg)),
            Box::new(instantiate_subst(vars, ret)),
        ),

        annot::Type::Custom(custom, args) => {
            annot::Type::Custom(*custom, args.map(|_, id| vars[id]))
        }
    }
}

fn instantiate_pattern(
    typedefs: &IdVec<mono::CustomTypeId, annot::TypeDef>,
    locals: &mut LocalContext<lifted::LocalId, annot::Type<SolverVarId>>,
    rhs: &annot::Type<SolverVarId>,
    pat: &mono::Pattern,
) -> SolverPattern {
    match (pat, rhs) {
        (mono::Pattern::Any(_), _) => {
            // Invariant: rhs should equal the type this 'any' pattern is annotated with.
            SolverPattern::Any(rhs.clone())
        }

        (mono::Pattern::Var(_), _) => {
            // Invariant: rhs should equal the type this 'var' pattern is annotated with.
            locals.add_local(rhs.clone());
            SolverPattern::Var(rhs.clone())
        }

        (mono::Pattern::Tuple(items), annot::Type::Tuple(rhs_items)) => {
            debug_assert_eq!(items.len(), rhs_items.len());

            SolverPattern::Tuple(
                items
                    .iter()
                    .zip(rhs_items.iter())
                    .map(|(item, rhs_item)| instantiate_pattern(typedefs, locals, rhs_item, item))
                    .collect(),
            )
        }

        (
            mono::Pattern::Ctor(custom, variant, content),
            annot::Type::Custom(rhs_custom, rhs_args),
        ) => {
            debug_assert_eq!(custom, rhs_custom);

            let solver_content = match (content, &typedefs[custom].variants[variant]) {
                (Some(content_pat), Some(content_type)) => {
                    let solver_content_type = instantiate_subst(rhs_args, content_type);
                    Some(Box::new(instantiate_pattern(
                        typedefs,
                        locals,
                        &solver_content_type,
                        content_pat,
                    )))
                }

                (None, None) => None,

                _ => unreachable!(),
            };

            SolverPattern::Ctor(*custom, rhs_args.clone(), *variant, solver_content)
        }

        (&mono::Pattern::BoolConst(val), annot::Type::Bool) => SolverPattern::BoolConst(val),

        (&mono::Pattern::ByteConst(val), annot::Type::Byte) => SolverPattern::ByteConst(val),

        (&mono::Pattern::IntConst(val), annot::Type::Int) => SolverPattern::IntConst(val),

        (&mono::Pattern::FloatConst(val), annot::Type::Float) => SolverPattern::FloatConst(val),

        (_, _) => unreachable!(),
    }
}

fn arith_op_type(
    graph: &mut ConstraintGraph<SolverRequirement>,
    op: Op,
) -> (annot::Type<SolverVarId>, SolverVarId) {
    let op_var = graph.new_var();
    graph.require(op_var, SolverRequirement::ArithOp(op));

    fn byte_binop(op_var: SolverVarId) -> annot::Type<SolverVarId> {
        annot::Type::Func(
            Purity::Pure,
            op_var,
            Box::new(annot::Type::Tuple(vec![
                annot::Type::Byte,
                annot::Type::Byte,
            ])),
            Box::new(annot::Type::Byte),
        )
    }

    fn int_binop(op_var: SolverVarId) -> annot::Type<SolverVarId> {
        annot::Type::Func(
            Purity::Pure,
            op_var,
            Box::new(annot::Type::Tuple(vec![annot::Type::Int, annot::Type::Int])),
            Box::new(annot::Type::Int),
        )
    }

    fn float_binop(op_var: SolverVarId) -> annot::Type<SolverVarId> {
        annot::Type::Func(
            Purity::Pure,
            op_var,
            Box::new(annot::Type::Tuple(vec![
                annot::Type::Float,
                annot::Type::Float,
            ])),
            Box::new(annot::Type::Float),
        )
    }

    fn byte_comp(op_var: SolverVarId) -> annot::Type<SolverVarId> {
        annot::Type::Func(
            Purity::Pure,
            op_var,
            Box::new(annot::Type::Tuple(vec![
                annot::Type::Byte,
                annot::Type::Byte,
            ])),
            Box::new(annot::Type::Bool),
        )
    }

    fn int_comp(op_var: SolverVarId) -> annot::Type<SolverVarId> {
        annot::Type::Func(
            Purity::Pure,
            op_var,
            Box::new(annot::Type::Tuple(vec![annot::Type::Int, annot::Type::Int])),
            Box::new(annot::Type::Bool),
        )
    }

    fn float_comp(op_var: SolverVarId) -> annot::Type<SolverVarId> {
        annot::Type::Func(
            Purity::Pure,
            op_var,
            Box::new(annot::Type::Tuple(vec![
                annot::Type::Float,
                annot::Type::Float,
            ])),
            Box::new(annot::Type::Bool),
        )
    }

    fn byte_unop(op_var: SolverVarId) -> annot::Type<SolverVarId> {
        annot::Type::Func(
            Purity::Pure,
            op_var,
            Box::new(annot::Type::Byte),
            Box::new(annot::Type::Byte),
        )
    }

    fn int_unop(op_var: SolverVarId) -> annot::Type<SolverVarId> {
        annot::Type::Func(
            Purity::Pure,
            op_var,
            Box::new(annot::Type::Int),
            Box::new(annot::Type::Int),
        )
    }

    fn float_unop(op_var: SolverVarId) -> annot::Type<SolverVarId> {
        annot::Type::Func(
            Purity::Pure,
            op_var,
            Box::new(annot::Type::Float),
            Box::new(annot::Type::Float),
        )
    }

    let op_type = match op {
        Op::AddByte => byte_binop(op_var),
        Op::SubByte => byte_binop(op_var),
        Op::MulByte => byte_binop(op_var),
        Op::DivByte => byte_binop(op_var),
        Op::NegByte => byte_unop(op_var),

        Op::EqByte => byte_comp(op_var),
        Op::LtByte => byte_comp(op_var),
        Op::LteByte => byte_comp(op_var),

        Op::AddInt => int_binop(op_var),
        Op::SubInt => int_binop(op_var),
        Op::MulInt => int_binop(op_var),
        Op::DivInt => int_binop(op_var),
        Op::NegInt => int_unop(op_var),

        Op::EqInt => int_comp(op_var),
        Op::LtInt => int_comp(op_var),
        Op::LteInt => int_comp(op_var),

        Op::AddFloat => float_binop(op_var),
        Op::SubFloat => float_binop(op_var),
        Op::MulFloat => float_binop(op_var),
        Op::DivFloat => float_binop(op_var),
        Op::NegFloat => float_unop(op_var),

        Op::EqFloat => float_comp(op_var),
        Op::LtFloat => float_comp(op_var),
        Op::LteFloat => float_comp(op_var),
    };

    (op_type, op_var)
}

fn array_op_type(
    graph: &mut ConstraintGraph<SolverRequirement>,
    op: ArrayOp,
    solver_item_type: annot::Type<SolverVarId>,
) -> (annot::Type<SolverVarId>, SolverVarId) {
    let op_var = graph.new_var();
    graph.require(
        op_var,
        SolverRequirement::ArrayOp(op, solver_item_type.clone()),
    );

    let op_type = match op {
        ArrayOp::Item => {
            let ret_closure_var = graph.new_var();
            graph.require(
                ret_closure_var,
                SolverRequirement::ArrayReplace(solver_item_type.clone()),
            );

            annot::Type::Func(
                Purity::Pure,
                op_var,
                Box::new(annot::Type::Tuple(vec![
                    annot::Type::Array(Box::new(solver_item_type.clone())),
                    annot::Type::Int,
                ])),
                Box::new(annot::Type::Tuple(vec![
                    solver_item_type.clone(),
                    annot::Type::Func(
                        Purity::Pure,
                        ret_closure_var,
                        Box::new(solver_item_type.clone()),
                        Box::new(annot::Type::Array(Box::new(solver_item_type))),
                    ),
                ])),
            )
        }

        ArrayOp::Len => annot::Type::Func(
            Purity::Pure,
            op_var,
            Box::new(annot::Type::Array(Box::new(solver_item_type))),
            Box::new(annot::Type::Int),
        ),

        ArrayOp::Push => annot::Type::Func(
            Purity::Pure,
            op_var,
            Box::new(annot::Type::Tuple(vec![
                annot::Type::Array(Box::new(solver_item_type.clone())),
                solver_item_type.clone(),
            ])),
            Box::new(annot::Type::Array(Box::new(solver_item_type))),
        ),

        ArrayOp::Pop => annot::Type::Func(
            Purity::Pure,
            op_var,
            Box::new(annot::Type::Array(Box::new(solver_item_type.clone()))),
            Box::new(annot::Type::Tuple(vec![
                annot::Type::Array(Box::new(solver_item_type.clone())),
                solver_item_type,
            ])),
        ),

        ArrayOp::Concat => annot::Type::Func(
            Purity::Pure,
            op_var,
            Box::new(annot::Type::Tuple(vec![
                annot::Type::Array(Box::new(solver_item_type.clone())),
                annot::Type::Array(Box::new(solver_item_type.clone())),
            ])),
            Box::new(annot::Type::Array(Box::new(solver_item_type))),
        ),
    };

    (op_type, op_var)
}

fn io_op_type(
    graph: &mut ConstraintGraph<SolverRequirement>,
    op: IOOp,
) -> (annot::Type<SolverVarId>, SolverVarId) {
    let op_var = graph.new_var();
    graph.require(op_var, SolverRequirement::IOOp(op));

    let op_type = match op {
        IOOp::Input => annot::Type::Func(
            Purity::Impure,
            op_var,
            Box::new(annot::Type::Tuple(vec![])),
            Box::new(annot::Type::Array(Box::new(annot::Type::Byte))),
        ),
        IOOp::Output => annot::Type::Func(
            Purity::Impure,
            op_var,
            Box::new(annot::Type::Array(Box::new(annot::Type::Byte))),
            Box::new(annot::Type::Tuple(vec![])),
        ),
    };

    (op_type, op_var)
}

#[derive(Clone, Copy, Debug)]
struct GlobalContext<'a> {
    annot_vals: &'a IdVec<mono::CustomGlobalId, Option<annot::ValDef>>,
    annot_lams: &'a IdVec<lifted::LamId, Option<annot::LamDef>>,
    curr_vals: &'a BTreeMap<mono::CustomGlobalId, annot::Type<SolverVarId>>,
    curr_lams: &'a BTreeMap<lifted::LamId, SolverLamSig>,
}

fn instantiate_params(
    graph: &mut ConstraintGraph<SolverRequirement>,
    params: &annot::Params,
) -> IdVec<annot::RepParamId, SolverVarId> {
    let param_vars = IdVec::from_items((0..params.num_params()).map(|_| graph.new_var()).collect());

    for (_, param_var, (req_template, req_params)) in param_vars
        .try_zip_exact(&params.requirements)
        .expect("params.num_params() should equal params.requirements.len()")
    {
        graph.require(
            *param_var,
            SolverRequirement::Template(
                *req_template,
                req_params.map(|_, other_param| param_vars[other_param]),
            ),
        );
    }

    param_vars
}

fn instantiate_expr(
    typedefs: &IdVec<mono::CustomTypeId, annot::TypeDef>,
    globals: GlobalContext,
    graph: &mut ConstraintGraph<SolverRequirement>,
    captures: &IdVec<lifted::CaptureId, annot::Type<SolverVarId>>,
    locals: &mut LocalContext<lifted::LocalId, annot::Type<SolverVarId>>,
    expr: &lifted::Expr,
) -> (SolverExpr, annot::Type<SolverVarId>) {
    match expr {
        &lifted::Expr::ArithOp(op) => {
            let (solver_type, op_var) = arith_op_type(graph, op);
            (SolverExpr::ArithOp(op, op_var), solver_type)
        }

        lifted::Expr::ArrayOp(op, item_type) => {
            let solver_item_type = instantiate_mono(typedefs, graph, item_type);
            let (solver_type, op_var) = array_op_type(graph, *op, solver_item_type.clone());
            (
                SolverExpr::ArrayOp(*op, solver_item_type, op_var),
                solver_type,
            )
        }

        &lifted::Expr::IOOp(op) => {
            let (solver_type, op_var) = io_op_type(graph, op);
            (SolverExpr::IOOp(op, op_var), solver_type)
        }

        &lifted::Expr::Ctor(custom, variant) => {
            let typedef = &typedefs[custom];

            let params =
                IdVec::from_items((0..typedef.num_params).map(|_| graph.new_var()).collect());

            match &typedef.variants[variant] {
                Some(content_type) => {
                    let op_closure_var = graph.new_var();
                    graph.require(
                        op_closure_var,
                        SolverRequirement::Ctor(custom, params.clone(), variant),
                    );

                    let solver_content_type = instantiate_subst(&params, content_type);

                    let solver_type = annot::Type::Func(
                        Purity::Pure,
                        op_closure_var,
                        Box::new(solver_content_type),
                        Box::new(annot::Type::Custom(custom, params.clone())),
                    );

                    let solver_expr = SolverExpr::Ctor(custom, params, variant, op_closure_var);

                    (solver_expr, solver_type)
                }

                None => {
                    let solver_type = annot::Type::Custom(custom, params.clone());

                    let solver_expr = SolverExpr::NullaryCtor(custom, params, variant);

                    (solver_expr, solver_type)
                }
            }
        }

        &lifted::Expr::Global(global) => match &globals.annot_vals[global] {
            Some(global_def) => {
                let scheme_params = instantiate_params(graph, &global_def.params);

                let solver_type = instantiate_subst(&scheme_params, &global_def.type_);

                (SolverExpr::Global(global, scheme_params), solver_type)
            }

            None => (
                SolverExpr::PendingGlobal(global),
                globals.curr_vals[&global].clone(),
            ),
        },

        &lifted::Expr::Local(local) => (SolverExpr::Local(local), locals.local_type(local).clone()),

        &lifted::Expr::Capture(capture) => {
            (SolverExpr::Capture(capture), captures[capture].clone())
        }

        lifted::Expr::Tuple(items) => {
            let mut solver_items = Vec::new();
            let mut solver_types = Vec::new();

            for item in items {
                let (solver_item, solver_type) =
                    instantiate_expr(typedefs, globals, graph, captures, locals, item);

                solver_items.push(solver_item);
                solver_types.push(solver_type);
            }

            (
                SolverExpr::Tuple(solver_items),
                annot::Type::Tuple(solver_types),
            )
        }

        lifted::Expr::Lam(lam, lam_captures) => {
            let mut solver_captures = IdVec::new();
            let mut solver_capture_types = IdVec::new();

            for (capture_id, capture) in lam_captures {
                let (solver_capture, solver_type) =
                    instantiate_expr(typedefs, globals, graph, captures, locals, capture);

                {
                    let pushed_id = solver_captures.push(solver_capture);
                    debug_assert_eq!(pushed_id, capture_id);
                }

                {
                    let pushed_id = solver_capture_types.push(solver_type);
                    debug_assert_eq!(pushed_id, capture_id)
                }
            }

            match &globals.annot_lams[lam] {
                Some(lam_def) => {
                    let scheme_params = instantiate_params(graph, &lam_def.params);

                    for (_capture_id, expected, actual) in lam_def
                        .captures
                        .try_zip_exact(&solver_capture_types)
                        .expect(
                            "A lambda should always be instantiated with the same number of \
                             captures",
                        )
                    {
                        let solver_expected = instantiate_subst(&scheme_params, expected);
                        equate_types(graph, &solver_expected, actual);
                    }

                    let solver_arg = instantiate_subst(&scheme_params, &lam_def.arg);
                    let solver_ret = instantiate_subst(&scheme_params, &lam_def.ret);

                    let lam_var = graph.new_var();
                    graph.require(lam_var, SolverRequirement::Lam(*lam, scheme_params.clone()));

                    let solver_expr =
                        SolverExpr::Lam(*lam, scheme_params, lam_var, solver_captures);

                    let solver_type = annot::Type::Func(
                        lam_def.purity,
                        lam_var,
                        Box::new(solver_arg),
                        Box::new(solver_ret),
                    );

                    (solver_expr, solver_type)
                }

                None => {
                    let solver_sig = &globals.curr_lams[lam];

                    debug_assert_eq!(solver_sig.captures.len(), lam_captures.len());

                    for (_capture_id, expected, actual) in solver_sig
                        .captures
                        .try_zip_exact(&solver_capture_types)
                        .expect(
                            "A lambda should always be instantiated with the same number of \
                             captures",
                        )
                    {
                        equate_types(graph, expected, actual);
                    }

                    let lam_var = graph.new_var();
                    graph.require(lam_var, SolverRequirement::PendingLam(*lam));

                    let solver_expr = SolverExpr::PendingLam(*lam, lam_var, solver_captures);

                    let solver_type = annot::Type::Func(
                        solver_sig.purity,
                        lam_var,
                        Box::new(solver_sig.arg.clone()),
                        Box::new(solver_sig.ret.clone()),
                    );

                    (solver_expr, solver_type)
                }
            }
        }

        lifted::Expr::App(purity, func, arg) => {
            let (solver_func, solver_func_type) =
                instantiate_expr(typedefs, globals, graph, captures, locals, func);

            let (solver_arg, solver_arg_type) =
                instantiate_expr(typedefs, globals, graph, captures, locals, arg);

            if let annot::Type::Func(func_purity, func_var, func_arg, func_ret) = solver_func_type {
                debug_assert_eq!(func_purity, *purity);

                equate_types(graph, &func_arg, &solver_arg_type);

                let solver_expr = SolverExpr::App(
                    *purity,
                    func_var,
                    Box::new(solver_func),
                    Box::new(solver_arg.clone()),
                    *func_arg,
                    (&*func_ret).clone(),
                );

                (solver_expr, *func_ret)
            } else {
                unreachable!()
            }
        }

        lifted::Expr::Match(discrim, cases, result_type) => {
            let (solver_discrim, solver_discrim_type) =
                instantiate_expr(typedefs, globals, graph, captures, locals, discrim);

            let solver_result_type = instantiate_mono(typedefs, graph, result_type);

            let solver_cases = cases
                .iter()
                .map(|(pat, body)| {
                    locals.with_scope(|sub_locals| {
                        let solver_pat =
                            instantiate_pattern(typedefs, sub_locals, &solver_discrim_type, pat);

                        let (solver_body, solver_body_type) =
                            instantiate_expr(typedefs, globals, graph, captures, sub_locals, body);

                        equate_types(graph, &solver_body_type, &solver_result_type);

                        (solver_pat, solver_body)
                    })
                })
                .collect();

            let solver_expr = SolverExpr::Match(
                Box::new(solver_discrim),
                solver_cases,
                solver_result_type.clone(),
            );

            (solver_expr, solver_result_type)
        }

        lifted::Expr::Let(lhs, rhs, body) => {
            let (solver_rhs, solver_rhs_type) =
                instantiate_expr(typedefs, globals, graph, captures, locals, rhs);

            let (solver_lhs, solver_body, solver_body_type) = locals.with_scope(|sub_locals| {
                let solver_lhs = instantiate_pattern(typedefs, sub_locals, &solver_rhs_type, lhs);

                let (solver_body, solver_body_type) =
                    instantiate_expr(typedefs, globals, graph, captures, sub_locals, body);

                (solver_lhs, solver_body, solver_body_type)
            });

            let solver_expr =
                SolverExpr::Let(solver_lhs, Box::new(solver_rhs), Box::new(solver_body));

            (solver_expr, solver_body_type)
        }

        lifted::Expr::ArrayLit(item_type, items) => {
            let solver_item_type = instantiate_mono(typedefs, graph, item_type);

            let solver_items = items
                .iter()
                .map(|item| {
                    let (solver_item, solver_this_item_type) =
                        instantiate_expr(typedefs, globals, graph, captures, locals, item);

                    equate_types(graph, &solver_this_item_type, &solver_item_type);

                    solver_item
                })
                .collect();

            (
                SolverExpr::ArrayLit(solver_item_type.clone(), solver_items),
                annot::Type::Array(Box::new(solver_item_type)),
            )
        }

        &lifted::Expr::BoolLit(val) => (SolverExpr::BoolLit(val), annot::Type::Bool),

        &lifted::Expr::ByteLit(val) => (SolverExpr::ByteLit(val), annot::Type::Byte),

        &lifted::Expr::IntLit(val) => (SolverExpr::IntLit(val), annot::Type::Int),

        &lifted::Expr::FloatLit(val) => (SolverExpr::FloatLit(val), annot::Type::Float),
    }
}

fn instantiate_lam_sig(
    typedefs: &IdVec<mono::CustomTypeId, annot::TypeDef>,
    graph: &mut ConstraintGraph<SolverRequirement>,
    lam_def: &lifted::LamDef,
) -> SolverLamSig {
    let solver_captures = lam_def
        .captures
        .map(|_capture_id, capture| instantiate_mono(typedefs, graph, capture));

    let solver_arg = instantiate_mono(typedefs, graph, &lam_def.arg_type);
    let solver_ret = instantiate_mono(typedefs, graph, &lam_def.ret_type);

    SolverLamSig {
        purity: lam_def.purity,
        captures: solver_captures,
        arg: solver_arg,
        ret: solver_ret,
    }
}

#[derive(Clone, Debug)]
struct SolverScc {
    val_sigs: BTreeMap<mono::CustomGlobalId, annot::Type<SolverVarId>>,
    lam_sigs: BTreeMap<lifted::LamId, SolverLamSig>,

    solver_vals: BTreeMap<mono::CustomGlobalId, SolverExpr>,
    solver_lams: BTreeMap<lifted::LamId, (SolverPattern, SolverExpr)>,

    constraints: ConstraintGraph<SolverRequirement>,
}

fn instantiate_scc(
    typedefs: &IdVec<mono::CustomTypeId, annot::TypeDef>,
    annot_vals: &IdVec<mono::CustomGlobalId, Option<annot::ValDef>>,
    annot_lams: &IdVec<lifted::LamId, Option<annot::LamDef>>,
    vals: &IdVec<mono::CustomGlobalId, lifted::ValDef>,
    lams: &IdVec<lifted::LamId, lifted::LamDef>,
    scc_vals: &[mono::CustomGlobalId],
    scc_lams: &[lifted::LamId],
) -> SolverScc {
    let mut graph = ConstraintGraph::new();

    let curr_val_sigs: BTreeMap<_, _> = scc_vals
        .iter()
        .map(|&val_id| {
            (
                val_id,
                instantiate_mono(typedefs, &mut graph, &vals[val_id].type_),
            )
        })
        .collect();

    let curr_lam_sigs: BTreeMap<_, _> = scc_lams
        .iter()
        .map(|&lam_id| {
            (
                lam_id,
                instantiate_lam_sig(typedefs, &mut graph, &lams[lam_id]),
            )
        })
        .collect();

    let global_ctx = GlobalContext {
        annot_vals,
        annot_lams,

        curr_vals: &curr_val_sigs,
        curr_lams: &curr_lam_sigs,
    };

    let solver_vals: BTreeMap<_, _> = scc_vals
        .iter()
        .map(|&val_id| {
            let mut local_ctx = LocalContext::new();

            let (solver_val, solver_val_type) = instantiate_expr(
                typedefs,
                global_ctx,
                &mut graph,
                &IdVec::new(),
                &mut local_ctx,
                &vals[val_id].body,
            );

            debug_assert_eq!(local_ctx.len(), 0);

            equate_types(&mut graph, &global_ctx.curr_vals[&val_id], &solver_val_type);

            (val_id, solver_val)
        })
        .collect();

    let solver_lams: BTreeMap<_, _> = scc_lams
        .iter()
        .map(|&lam_id| {
            let solver_sig = &global_ctx.curr_lams[&lam_id];
            let lam_def = &lams[lam_id];

            let mut local_ctx = LocalContext::new();

            let (solver_arg, solver_body) = local_ctx.with_scope(|sub_locals| {
                let solver_arg =
                    instantiate_pattern(typedefs, sub_locals, &solver_sig.arg, &lam_def.arg);

                let (solver_body, solver_body_type) = instantiate_expr(
                    typedefs,
                    global_ctx,
                    &mut graph,
                    &solver_sig.captures,
                    sub_locals,
                    &lam_def.body,
                );

                equate_types(&mut graph, &solver_sig.ret, &solver_body_type);

                (solver_arg, solver_body)
            });

            debug_assert_eq!(local_ctx.len(), 0);

            (lam_id, (solver_arg, solver_body))
        })
        .collect();

    SolverScc {
        val_sigs: curr_val_sigs,
        lam_sigs: curr_lam_sigs,

        solver_vals,
        solver_lams,

        constraints: graph,
    }
}

fn add_mentioned_classes(
    equiv_classes: &EquivClasses,
    type_: &annot::Type<SolverVarId>,
    mentioned: &mut BTreeSet<EquivClass>,
) {
    match type_ {
        annot::Type::Bool => {}
        annot::Type::Byte => {}
        annot::Type::Int => {}
        annot::Type::Float => {}

        annot::Type::Array(item) => add_mentioned_classes(equiv_classes, item, mentioned),

        annot::Type::Tuple(items) => {
            for item in items {
                add_mentioned_classes(equiv_classes, item, mentioned);
            }
        }

        annot::Type::Func(_, var, arg, ret) => {
            mentioned.insert(equiv_classes.class(*var));

            add_mentioned_classes(equiv_classes, arg, mentioned);
            add_mentioned_classes(equiv_classes, ret, mentioned);
        }

        annot::Type::Custom(_, args) => {
            for (_, &var) in args {
                mentioned.insert(equiv_classes.class(var));
            }
        }
    }
}

#[derive(Clone, Debug)]
struct Params(IdVec<annot::RepParamId, EquivClass>);

fn find_params(scc: &SolverScc, equiv_classes: &EquivClasses) -> Params {
    let mut mentioned = BTreeSet::new();

    for sig in scc.val_sigs.values() {
        add_mentioned_classes(equiv_classes, sig, &mut mentioned);
    }

    for sig in scc.lam_sigs.values() {
        for (_, capture) in &sig.captures {
            add_mentioned_classes(equiv_classes, capture, &mut mentioned);
        }

        add_mentioned_classes(equiv_classes, &sig.arg, &mut mentioned);
        add_mentioned_classes(equiv_classes, &sig.ret, &mut mentioned);
    }

    // This is where we *define* the mapping between representation parameters and equivalence
    // classes for this SCC.  We record our choice of mapping in the returned `Params` structure.
    // The choice of mapping at this point is arbitrary, but after we commit to it we must be
    // consistent going forward.
    Params(IdVec::from_items(mentioned.into_iter().collect()))
}

fn add_req_mentioned_classes(
    equiv_classes: &EquivClasses,
    params: &Params,
    req: &SolverRequirement,
    mentioned: &mut BTreeSet<EquivClass>,
) {
    match req {
        SolverRequirement::Lam(_, lam_params) => {
            mentioned.extend(lam_params.iter().map(|(_, &var)| equiv_classes.class(var)));
        }

        SolverRequirement::PendingLam(_) => {
            mentioned.extend(params.0.iter().map(|(_, &var)| var));
        }

        SolverRequirement::Template(_, template_params) => {
            mentioned.extend(
                template_params
                    .iter()
                    .map(|(_, &var)| equiv_classes.class(var)),
            );
        }

        SolverRequirement::ArithOp(_) => {}

        SolverRequirement::ArrayOp(_, item_type) | SolverRequirement::ArrayReplace(item_type) => {
            add_mentioned_classes(equiv_classes, item_type, mentioned);
        }

        SolverRequirement::IOOp(_) => {}

        SolverRequirement::Ctor(_, custom_params, _) => {
            mentioned.extend(
                custom_params
                    .iter()
                    .map(|(_, &var)| equiv_classes.class(var)),
            );
        }
    }
}

#[derive(Clone, Debug)]
struct RequirementDeps(IdVec<EquivClass, BTreeSet<EquivClass>>);

fn requirement_deps(
    equiv_classes: &EquivClasses,
    params: &Params,
    graph: &ConstraintGraph<SolverRequirement>,
) -> RequirementDeps {
    let mut deps = IdVec::from_items(vec![BTreeSet::new(); equiv_classes.count()]);

    for (var_id, var_constraints) in &graph.var_constraints {
        let class = equiv_classes.class(var_id);

        let class_deps = &mut deps[class];

        for req in &var_constraints.requirements {
            add_req_mentioned_classes(equiv_classes, params, req, class_deps);
        }
    }

    RequirementDeps(deps)
}

#[derive(Clone, Debug)]
struct ClassRequirements(IdVec<EquivClass, Vec<SolverRequirement>>);

fn consolidate_class_requirements(
    equiv_classes: &EquivClasses,
    graph: ConstraintGraph<SolverRequirement>,
) -> ClassRequirements {
    let mut reqs = IdVec::from_items(vec![Vec::new(); equiv_classes.count()]);

    for (var_id, var_constraints) in graph.var_constraints.into_iter() {
        let class = equiv_classes.class(var_id);

        reqs[class].extend(var_constraints.requirements);
    }

    ClassRequirements(reqs)
}

#[derive(Clone, Debug)]
struct Solutions {
    class_solutions: IdVec<EquivClass, annot::Solution>,
    param_reqs: IdVec<
        annot::RepParamId,
        (
            annot::TemplateId,
            IdVec<annot::RepParamId, annot::RepParamId>,
        ),
    >,
}

fn translate_solution_for_template(
    solver_to_template: &BTreeMap<annot::RepParamId, annot::RepParamId>,
    solution: &annot::Solution,
) -> annot::Solution {
    match solution {
        annot::Solution::Param(param) => annot::Solution::Param(solver_to_template[param]),

        annot::Solution::MinSolutionTo(id, args) => {
            annot::Solution::MinSolutionTo(*id, args.map(|_, arg| solver_to_template[arg]))
        }
    }
}

fn translate_var_for_template(
    equiv_classes: &EquivClasses,
    class_solutions: &IdVec<EquivClass, Option<annot::Solution>>,
    solver_to_template: &BTreeMap<annot::RepParamId, annot::RepParamId>,
    var: SolverVarId,
) -> annot::Solution {
    translate_solution_for_template(
        solver_to_template,
        class_solutions[equiv_classes.class(var)].as_ref().unwrap(),
    )
}

fn translate_type_for_template(
    equiv_classes: &EquivClasses,
    class_solutions: &IdVec<EquivClass, Option<annot::Solution>>,
    solver_to_template: &BTreeMap<annot::RepParamId, annot::RepParamId>,
    type_: &annot::Type<SolverVarId>,
) -> annot::Type<annot::Solution> {
    match type_ {
        annot::Type::Bool => annot::Type::Bool,
        annot::Type::Byte => annot::Type::Byte,
        annot::Type::Int => annot::Type::Int,
        annot::Type::Float => annot::Type::Float,

        annot::Type::Array(item_type) => annot::Type::Array(Box::new(translate_type_for_template(
            equiv_classes,
            class_solutions,
            solver_to_template,
            item_type,
        ))),

        annot::Type::Tuple(items) => annot::Type::Tuple(
            items
                .iter()
                .map(|item| {
                    translate_type_for_template(
                        equiv_classes,
                        class_solutions,
                        solver_to_template,
                        item,
                    )
                })
                .collect(),
        ),

        annot::Type::Func(purity, var, arg, ret) => annot::Type::Func(
            *purity,
            translate_var_for_template(equiv_classes, class_solutions, solver_to_template, *var),
            Box::new(translate_type_for_template(
                equiv_classes,
                class_solutions,
                solver_to_template,
                arg,
            )),
            Box::new(translate_type_for_template(
                equiv_classes,
                class_solutions,
                solver_to_template,
                ret,
            )),
        ),

        annot::Type::Custom(custom, vars) => annot::Type::Custom(
            *custom,
            vars.map(|_, &var| {
                translate_var_for_template(equiv_classes, class_solutions, solver_to_template, var)
            }),
        ),
    }
}

fn translate_req_for_template(
    equiv_classes: &EquivClasses,
    params: &Params,
    class_solutions: &IdVec<EquivClass, Option<annot::Solution>>,
    solver_to_template: &BTreeMap<annot::RepParamId, annot::RepParamId>,
    req: &SolverRequirement,
) -> annot::Requirement {
    match req {
        SolverRequirement::Lam(lam_id, vars) => annot::Requirement::Lam(
            *lam_id,
            vars.map(|_, &var| {
                translate_var_for_template(equiv_classes, class_solutions, solver_to_template, var)
            }),
        ),

        SolverRequirement::PendingLam(lam_id) => annot::Requirement::Lam(
            *lam_id,
            params.0.map(|_, &class| {
                translate_solution_for_template(
                    solver_to_template,
                    class_solutions[class].as_ref().unwrap(),
                )
            }),
        ),

        SolverRequirement::Template(template_id, vars) => annot::Requirement::Template(
            *template_id,
            vars.map(|_, &var| {
                translate_var_for_template(equiv_classes, class_solutions, solver_to_template, var)
            }),
        ),

        SolverRequirement::ArithOp(op) => annot::Requirement::ArithOp(*op),

        SolverRequirement::ArrayOp(op, item_type) => annot::Requirement::ArrayOp(
            *op,
            translate_type_for_template(
                equiv_classes,
                class_solutions,
                solver_to_template,
                item_type,
            ),
        ),

        SolverRequirement::ArrayReplace(item_type) => {
            annot::Requirement::ArrayReplace(translate_type_for_template(
                equiv_classes,
                class_solutions,
                solver_to_template,
                item_type,
            ))
        }

        SolverRequirement::IOOp(op) => annot::Requirement::IOOp(*op),

        SolverRequirement::Ctor(custom, vars, variant) => annot::Requirement::Ctor(
            *custom,
            vars.map(|_, &var| {
                translate_var_for_template(equiv_classes, class_solutions, solver_to_template, var)
            }),
            *variant,
        ),
    }
}

fn solve_requirements(
    equiv_classes: &EquivClasses,
    params: &Params,
    req_deps: &RequirementDeps,
    reqs: &ClassRequirements,
    templates: &mut IdVec<annot::TemplateId, annot::Template>,
) -> Solutions {
    let mut class_solutions: IdVec<EquivClass, _> =
        IdVec::from_items(vec![None; equiv_classes.count()]);

    let mut param_reqs: IdVec<annot::RepParamId, _> = IdVec::from_items(vec![None; params.0.len()]);

    for (param_id, param_class) in &params.0 {
        debug_assert!(class_solutions[param_class].is_none());
        class_solutions[param_class] = Some(annot::Solution::Param(param_id));
    }

    let dep_graph = Graph {
        edges_out: req_deps
            .0
            .map(|_, class_deps| class_deps.iter().cloned().collect()),
    };

    let class_sccs = graph::strongly_connected(&dep_graph);

    for scc in class_sccs {
        let is_cycle = if scc.len() == 1 {
            // We have an SCC with a single node, but we still need to check if it has a self-loop.
            let singleton = scc[0];

            if req_deps.0[singleton].contains(&singleton) {
                annot::InCycle::Cycle
            } else {
                annot::InCycle::NoCycle
            }
        } else {
            annot::InCycle::Cycle
        };

        // Find parameters mentioned

        let mut params_mentioned = BTreeSet::new();

        for &class_id in &scc {
            for dep in &req_deps.0[class_id] {
                match &class_solutions[dep] {
                    &Some(annot::Solution::Param(param)) => {
                        params_mentioned.insert(param);
                    }

                    Some(annot::Solution::MinSolutionTo(_, dep_mentioned_params)) => {
                        params_mentioned
                            .extend(dep_mentioned_params.iter().map(|(_, &param)| param));
                    }

                    None => {
                        // Dependency is a non-parameter class in the current SCC
                    }
                }
            }
        }

        // Fix an order
        let params_mentioned: IdVec<annot::RepParamId, _> =
            IdVec::from_items(params_mentioned.into_iter().collect());

        // Forward-declare templates for all non-parameter classes

        for &class_id in &scc {
            match &mut class_solutions[class_id] {
                Some(annot::Solution::Param(_param)) => {
                    // The template representing the requirements for this variable should go into
                    // param_reqs rather than class_solutions.  As such, we won't need to know it's
                    // ID until we actually populate it, so we do nothing for now.
                }

                Some(annot::Solution::MinSolutionTo(_, _)) => unreachable!(),

                solution @ None => {
                    // Create a dummy template whose requirements we'll fill in during the next loop
                    let template_id = templates.push(annot::Template {
                        in_cycle: is_cycle,
                        num_params: params_mentioned.len(),
                        requirements: Vec::new(), // To be populated
                    });

                    *solution = Some(annot::Solution::MinSolutionTo(
                        template_id,
                        params_mentioned.clone(),
                    ));
                }
            }
        }

        // Build map from solver params (for this scc of valdefs) to template-internal params (for
        // this scc of equiv classes)

        let solver_to_template: BTreeMap<annot::RepParamId, annot::RepParamId> = params_mentioned
            .iter()
            .map(|(internal_idx, &solver_param)| (solver_param, internal_idx))
            .collect();

        // Fill in template and parameters with the appropriate requirements

        for &class_id in &scc {
            let template_internal_requirements: Vec<_> = reqs.0[class_id]
                .iter()
                .map(|req| {
                    translate_req_for_template(
                        equiv_classes,
                        params,
                        &class_solutions,
                        &solver_to_template,
                        req,
                    )
                })
                .collect();

            match &class_solutions[class_id] {
                Some(annot::Solution::Param(param)) => {
                    // Add parameter requirements

                    let param_req_template = annot::Template {
                        in_cycle: is_cycle,
                        num_params: params_mentioned.len(),
                        requirements: template_internal_requirements,
                    };

                    let template_id = templates.push(param_req_template);

                    debug_assert!(param_reqs[param].is_none());
                    param_reqs[param] = Some((template_id, params_mentioned.clone()));
                }

                Some(annot::Solution::MinSolutionTo(template_id, template_params)) => {
                    debug_assert_eq!(template_params, &params_mentioned);
                    debug_assert!(templates[template_id].requirements.is_empty());

                    templates[template_id].requirements = template_internal_requirements;
                }

                None => unreachable!(),
            }
        }
    }

    Solutions {
        class_solutions: class_solutions.into_mapped(|_, solution| solution.unwrap()),
        param_reqs: param_reqs.into_mapped(|_, req| req.unwrap()),
    }
}

fn extract_type(
    equiv_classes: &EquivClasses,
    class_solutions: &IdVec<EquivClass, annot::Solution>,
    type_: &annot::Type<SolverVarId>,
) -> annot::Type<annot::Solution> {
    match type_ {
        annot::Type::Bool => annot::Type::Bool,
        annot::Type::Byte => annot::Type::Byte,
        annot::Type::Int => annot::Type::Int,
        annot::Type::Float => annot::Type::Float,

        annot::Type::Array(item_type) => annot::Type::Array(Box::new(extract_type(
            equiv_classes,
            class_solutions,
            item_type,
        ))),

        annot::Type::Tuple(items) => annot::Type::Tuple(
            items
                .iter()
                .map(|item| extract_type(equiv_classes, class_solutions, item))
                .collect(),
        ),

        annot::Type::Func(purity, var, arg, ret) => annot::Type::Func(
            *purity,
            class_solutions[equiv_classes.class(*var)].clone(),
            Box::new(extract_type(equiv_classes, class_solutions, arg)),
            Box::new(extract_type(equiv_classes, class_solutions, ret)),
        ),

        annot::Type::Custom(custom, vars) => annot::Type::Custom(
            *custom,
            vars.map(|_, &var| class_solutions[equiv_classes.class(var)].clone()),
        ),
    }
}

fn extract_pattern(
    equiv_classes: &EquivClasses,
    class_solutions: &IdVec<EquivClass, annot::Solution>,
    pat: &SolverPattern,
) -> annot::Pattern {
    match pat {
        SolverPattern::Any(type_) => {
            annot::Pattern::Any(extract_type(equiv_classes, class_solutions, type_))
        }

        SolverPattern::Var(type_) => {
            annot::Pattern::Var(extract_type(equiv_classes, class_solutions, type_))
        }

        SolverPattern::Tuple(items) => annot::Pattern::Tuple(
            items
                .iter()
                .map(|item| extract_pattern(equiv_classes, class_solutions, item))
                .collect(),
        ),

        SolverPattern::Ctor(custom, vars, variant, content) => annot::Pattern::Ctor(
            *custom,
            vars.map(|_, &var| class_solutions[equiv_classes.class(var)].clone()),
            *variant,
            content
                .as_ref()
                .map(|content| Box::new(extract_pattern(equiv_classes, class_solutions, content))),
        ),

        &SolverPattern::BoolConst(val) => annot::Pattern::BoolConst(val),
        &SolverPattern::ByteConst(val) => annot::Pattern::ByteConst(val),
        &SolverPattern::IntConst(val) => annot::Pattern::IntConst(val),
        &SolverPattern::FloatConst(val) => annot::Pattern::FloatConst(val),
    }
}

fn extract_expr(
    equiv_classes: &EquivClasses,
    params: &Params,
    class_solutions: &IdVec<EquivClass, annot::Solution>,
    expr: &SolverExpr,
) -> annot::Expr {
    match expr {
        &SolverExpr::ArithOp(op, var) => {
            annot::Expr::ArithOp(op, class_solutions[equiv_classes.class(var)].clone())
        }

        SolverExpr::ArrayOp(op, item_type, var) => annot::Expr::ArrayOp(
            *op,
            extract_type(equiv_classes, class_solutions, item_type),
            class_solutions[equiv_classes.class(*var)].clone(),
        ),

        &SolverExpr::IOOp(op, var) => {
            annot::Expr::IOOp(op, class_solutions[equiv_classes.class(var)].clone())
        }

        SolverExpr::NullaryCtor(custom, vars, variant) => annot::Expr::NullaryCtor(
            *custom,
            vars.map(|_, &var| class_solutions[equiv_classes.class(var)].clone()),
            *variant,
        ),

        SolverExpr::Ctor(custom, vars, variant, var) => annot::Expr::Ctor(
            *custom,
            vars.map(|_, &var| class_solutions[equiv_classes.class(var)].clone()),
            *variant,
            class_solutions[equiv_classes.class(*var)].clone(),
        ),

        SolverExpr::Global(global, vars) => annot::Expr::Global(
            *global,
            vars.map(|_, &var| class_solutions[equiv_classes.class(var)].clone()),
        ),

        SolverExpr::PendingGlobal(global) => annot::Expr::Global(
            *global,
            params.0.map(|_, param| class_solutions[param].clone()),
        ),

        &SolverExpr::Local(local) => annot::Expr::Local(local),

        &SolverExpr::Capture(capture) => annot::Expr::Capture(capture),

        SolverExpr::Tuple(items) => annot::Expr::Tuple(
            items
                .iter()
                .map(|item| extract_expr(equiv_classes, params, class_solutions, item))
                .collect(),
        ),

        SolverExpr::Lam(lam, rep_params, lam_rep_var, captures) => annot::Expr::Lam(
            *lam,
            rep_params.map(|_, &var| class_solutions[equiv_classes.class(var)].clone()),
            class_solutions[equiv_classes.class(*lam_rep_var)].clone(),
            captures
                .map(|_, capture| extract_expr(equiv_classes, params, class_solutions, capture)),
        ),

        SolverExpr::PendingLam(lam, lam_rep_var, captures) => annot::Expr::Lam(
            *lam,
            params.0.map(|_, param| class_solutions[param].clone()),
            class_solutions[equiv_classes.class(*lam_rep_var)].clone(),
            captures
                .map(|_, capture| extract_expr(equiv_classes, params, class_solutions, capture)),
        ),

        SolverExpr::App(purity, func_rep_var, func, arg, arg_type, ret_type) => annot::Expr::App(
            *purity,
            class_solutions[equiv_classes.class(*func_rep_var)].clone(),
            Box::new(extract_expr(equiv_classes, params, class_solutions, func)),
            Box::new(extract_expr(equiv_classes, params, class_solutions, arg)),
            extract_type(equiv_classes, class_solutions, arg_type),
            extract_type(equiv_classes, class_solutions, ret_type),
        ),

        SolverExpr::Match(discrim, cases, result_type) => annot::Expr::Match(
            Box::new(extract_expr(
                equiv_classes,
                params,
                class_solutions,
                discrim,
            )),
            cases
                .iter()
                .map(|(pat, body)| {
                    (
                        extract_pattern(equiv_classes, class_solutions, pat),
                        extract_expr(equiv_classes, params, class_solutions, body),
                    )
                })
                .collect(),
            extract_type(equiv_classes, class_solutions, result_type),
        ),

        SolverExpr::Let(lhs, rhs, body) => annot::Expr::Let(
            extract_pattern(equiv_classes, class_solutions, lhs),
            Box::new(extract_expr(equiv_classes, params, class_solutions, rhs)),
            Box::new(extract_expr(equiv_classes, params, class_solutions, body)),
        ),

        SolverExpr::ArrayLit(item_type, items) => annot::Expr::ArrayLit(
            extract_type(equiv_classes, class_solutions, item_type),
            items
                .iter()
                .map(|item| extract_expr(equiv_classes, params, class_solutions, item))
                .collect(),
        ),

        &SolverExpr::BoolLit(val) => annot::Expr::BoolLit(val),
        &SolverExpr::ByteLit(val) => annot::Expr::ByteLit(val),
        &SolverExpr::IntLit(val) => annot::Expr::IntLit(val),
        &SolverExpr::FloatLit(val) => annot::Expr::FloatLit(val),
    }
}

fn extract_param(
    equiv_classes: &EquivClasses,
    class_solutions: &IdVec<EquivClass, annot::Solution>,
    var: SolverVarId,
) -> annot::RepParamId {
    match &class_solutions[equiv_classes.class(var)] {
        &annot::Solution::Param(param) => param,
        _ => unreachable!(),
    }
}

fn extract_sig_type(
    equiv_classes: &EquivClasses,
    class_solutions: &IdVec<EquivClass, annot::Solution>,
    type_: &annot::Type<SolverVarId>,
) -> annot::Type<annot::RepParamId> {
    match type_ {
        annot::Type::Bool => annot::Type::Bool,
        annot::Type::Byte => annot::Type::Byte,
        annot::Type::Int => annot::Type::Int,
        annot::Type::Float => annot::Type::Float,

        annot::Type::Array(item_type) => annot::Type::Array(Box::new(extract_sig_type(
            equiv_classes,
            class_solutions,
            item_type,
        ))),

        annot::Type::Tuple(items) => annot::Type::Tuple(
            items
                .iter()
                .map(|item| extract_sig_type(equiv_classes, class_solutions, item))
                .collect(),
        ),

        annot::Type::Func(purity, var, arg, ret) => annot::Type::Func(
            *purity,
            extract_param(equiv_classes, class_solutions, *var),
            Box::new(extract_sig_type(equiv_classes, class_solutions, arg)),
            Box::new(extract_sig_type(equiv_classes, class_solutions, ret)),
        ),

        annot::Type::Custom(custom, vars) => annot::Type::Custom(
            *custom,
            vars.map(|_, &var| extract_param(equiv_classes, class_solutions, var)),
        ),
    }
}

fn solve_scc(
    typedefs: &IdVec<mono::CustomTypeId, annot::TypeDef>,
    vals: &IdVec<mono::CustomGlobalId, lifted::ValDef>,
    lams: &IdVec<lifted::LamId, lifted::LamDef>,
    annot_vals: &mut IdVec<mono::CustomGlobalId, Option<annot::ValDef>>,
    annot_lams: &mut IdVec<lifted::LamId, Option<annot::LamDef>>,
    templates: &mut IdVec<annot::TemplateId, annot::Template>,
    scc_vals: &[mono::CustomGlobalId],
    scc_lams: &[lifted::LamId],
) {
    let instantiated = instantiate_scc(
        typedefs,
        &annot_vals,
        &annot_lams,
        vals,
        lams,
        scc_vals,
        scc_lams,
    );

    let equiv_classes = instantiated.constraints.find_equiv_classes();

    let params = find_params(&instantiated, &equiv_classes);

    let req_deps = requirement_deps(&equiv_classes, &params, &instantiated.constraints);

    let reqs = consolidate_class_requirements(&equiv_classes, instantiated.constraints);

    let solutions = solve_requirements(&equiv_classes, &params, &req_deps, &reqs, templates);

    for val_id in scc_vals {
        let annot_val = annot::ValDef {
            params: annot::Params {
                requirements: solutions.param_reqs.clone(),
            },
            type_: extract_sig_type(
                &equiv_classes,
                &solutions.class_solutions,
                &instantiated.val_sigs[val_id],
            ),
            body: extract_expr(
                &equiv_classes,
                &params,
                &solutions.class_solutions,
                &instantiated.solver_vals[val_id],
            ),
        };

        debug_assert!(annot_vals[val_id].is_none());
        annot_vals[val_id] = Some(annot_val);
    }

    for lam_id in scc_lams {
        let solver_sig = &instantiated.lam_sigs[lam_id];

        let (solver_pat, solver_body) = &instantiated.solver_lams[lam_id];

        let annot_lam = annot::LamDef {
            purity: solver_sig.purity,
            params: annot::Params {
                requirements: solutions.param_reqs.clone(),
            },
            captures: solver_sig.captures.map(|_, capture_type| {
                extract_sig_type(&equiv_classes, &solutions.class_solutions, capture_type)
            }),
            arg: extract_sig_type(&equiv_classes, &solutions.class_solutions, &solver_sig.arg),
            ret: extract_sig_type(&equiv_classes, &solutions.class_solutions, &solver_sig.ret),
            arg_pat: extract_pattern(&equiv_classes, &solutions.class_solutions, solver_pat),
            body: extract_expr(
                &equiv_classes,
                &params,
                &solutions.class_solutions,
                solver_body,
            ),
        };

        debug_assert!(annot_lams[lam_id].is_none());
        annot_lams[lam_id] = Some(annot_lam);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Item {
    Val(mono::CustomGlobalId),
    Lam(lifted::LamId),
}

fn add_expr_deps(deps: &mut BTreeSet<Item>, expr: &lifted::Expr) {
    match expr {
        lifted::Expr::ArithOp(_) => {}

        lifted::Expr::ArrayOp(_, _) => {}

        lifted::Expr::IOOp(_) => {}

        lifted::Expr::Ctor(_, _) => {}

        &lifted::Expr::Global(dep) => {
            deps.insert(Item::Val(dep));
        }

        lifted::Expr::Local(_) => {}

        lifted::Expr::Capture(_) => {}

        lifted::Expr::Tuple(items) => {
            for item in items {
                add_expr_deps(deps, item);
            }
        }

        lifted::Expr::Lam(dep, captures) => {
            deps.insert(Item::Lam(*dep));

            for (_capture_id, capture) in captures {
                add_expr_deps(deps, capture);
            }
        }

        lifted::Expr::App(_purity, func, arg) => {
            add_expr_deps(deps, func);
            add_expr_deps(deps, arg);
        }

        lifted::Expr::Match(discrim, cases, _result_type) => {
            add_expr_deps(deps, discrim);

            for (_pat, body) in cases {
                add_expr_deps(deps, body);
            }
        }

        lifted::Expr::Let(_lhs, rhs, body) => {
            add_expr_deps(deps, rhs);
            add_expr_deps(deps, body);
        }

        lifted::Expr::ArrayLit(_item_type, items) => {
            for item in items {
                add_expr_deps(deps, item);
            }
        }

        lifted::Expr::BoolLit(_) => {}
        lifted::Expr::ByteLit(_) => {}
        lifted::Expr::IntLit(_) => {}
        lifted::Expr::FloatLit(_) => {}
    }
}

#[derive(Clone, Debug)]
struct ItemScc {
    vals: Vec<mono::CustomGlobalId>,
    lams: Vec<lifted::LamId>,
}

fn item_sccs(program: &lifted::Program) -> Vec<ItemScc> {
    id_type!(ItemId);

    fn item_to_id(program: &lifted::Program, item: Item) -> ItemId {
        match item {
            Item::Val(mono::CustomGlobalId(id)) => ItemId(id),
            Item::Lam(lifted::LamId(id)) => ItemId(program.vals.len() + id),
        }
    }

    fn id_to_item(program: &lifted::Program, node: ItemId) -> Item {
        if node.0 < program.vals.len() {
            Item::Val(mono::CustomGlobalId(node.0))
        } else {
            Item::Lam(lifted::LamId(node.0 - program.vals.len()))
        }
    }

    let val_deps = program.vals.iter().map(|(_val_def_id, val_def)| {
        let mut deps = BTreeSet::new();
        add_expr_deps(&mut deps, &val_def.body);
        deps
    });

    let lam_deps = program.lams.iter().map(|(_lam_def_id, lam_def)| {
        let mut deps = BTreeSet::new();
        add_expr_deps(&mut deps, &lam_def.body);
        deps
    });

    let dep_graph = Graph {
        edges_out: IdVec::from_items(
            (val_deps.chain(lam_deps))
                .map(|deps| {
                    deps.into_iter()
                        .map(|item| item_to_id(program, item))
                        .collect()
                })
                .collect(),
        ),
    };

    let sccs = graph::strongly_connected(&dep_graph);

    sccs.into_iter()
        .map(|scc| {
            let mut scc_vals = Vec::new();
            let mut scc_lams = Vec::new();

            for node in scc {
                match id_to_item(program, node) {
                    Item::Val(val_id) => scc_vals.push(val_id),
                    Item::Lam(lam_id) => scc_lams.push(lam_id),
                }
            }

            ItemScc {
                vals: scc_vals,
                lams: scc_lams,
            }
        })
        .collect()
}

pub fn annot_closures(program: lifted::Program) -> annot::Program {
    let typedefs = parameterize_typedefs(&program.custom_types);

    let mut annot_vals = IdVec::from_items(vec![None; program.vals.len()]);
    let mut annot_lams = IdVec::from_items(vec![None; program.lams.len()]);

    let mut templates = IdVec::new();

    let sccs = item_sccs(&program);

    for scc in sccs {
        solve_scc(
            &typedefs,
            &program.vals,
            &program.lams,
            &mut annot_vals,
            &mut annot_lams,
            &mut templates,
            &scc.vals,
            &scc.lams,
        );
    }

    annot::Program {
        custom_types: typedefs,
        templates,
        vals: annot_vals.into_mapped(|_id, val| val.unwrap()),
        lams: annot_lams.into_mapped(|_id, lam| lam.unwrap()),
        main: program.main,
    }
}
