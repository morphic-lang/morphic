use std::collections::{BTreeMap, BTreeSet};

use crate::data::closure_annot_ast as annot;
use crate::data::lambda_lifted_ast as lifted;
use crate::data::mono_ast as mono;
use crate::data::purity::Purity;
use crate::data::raw_ast::Op;
use crate::data::resolved_ast::{self as res, ArrayOp};
use crate::graph::{self, Graph};

fn count_params(parameterized: &[Option<annot::TypeDef>], type_: &mono::Type) -> usize {
    match type_ {
        mono::Type::Bool => 0,
        mono::Type::Int => 0,
        mono::Type::Float => 0,
        mono::Type::Text => 0,
        mono::Type::Array(item) => count_params(parameterized, item),
        mono::Type::Tuple(items) => items
            .iter()
            .map(|item| count_params(parameterized, item))
            .sum(),
        mono::Type::Func(_, arg, ret) => {
            1 + count_params(parameterized, arg) + count_params(parameterized, ret)
        }
        mono::Type::Custom(other) => match &parameterized[other.0] {
            Some(typedef) => typedef.num_params,
            // This is a typedef in the same SCC; the reference to it here contributes no additional
            // parameters to the entire SCC.
            None => 0,
        },
    }
}

#[derive(Clone, Debug)]
struct ParamIdGen(usize);

impl ParamIdGen {
    fn fresh(&mut self) -> annot::RepParamId {
        let result = annot::RepParamId(self.0);
        self.0 += 1;
        result
    }
}

fn parameterize(
    parameterized: &[Option<annot::TypeDef>],
    scc_num_params: usize,
    id_gen: &mut ParamIdGen,
    type_: &mono::Type,
) -> annot::Type<annot::RepParamId> {
    match type_ {
        mono::Type::Bool => annot::Type::Bool,
        mono::Type::Int => annot::Type::Int,
        mono::Type::Float => annot::Type::Float,
        mono::Type::Text => annot::Type::Text,

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
            match &parameterized[other.0] {
                Some(typedef) => annot::Type::Custom(
                    *other,
                    (0..typedef.num_params).map(|_| id_gen.fresh()).collect(),
                ),

                None => {
                    // This is a typedef in the same SCC, so we need to parameterize it by
                    // all the SCC parameters.
                    annot::Type::Custom(
                        *other,
                        (0..scc_num_params).map(annot::RepParamId).collect(),
                    )
                }
            }
        }
    }
}

fn parameterize_typedef_scc(
    typedefs: &[mono::TypeDef],
    parameterized: &mut [Option<annot::TypeDef>],
    scc: &[mono::CustomTypeId],
) {
    let num_params = scc
        .iter()
        .map(|type_id| {
            typedefs[type_id.0]
                .variants
                .iter()
                .map(|variant| match variant {
                    Some(content) => count_params(parameterized, content),
                    None => 0,
                })
                .sum::<usize>()
        })
        .sum::<usize>();

    let mut id_gen = ParamIdGen(0);

    for type_id in scc {
        let typedef = &typedefs[type_id.0];
        let parameterized_variants = typedef
            .variants
            .iter()
            .map(|variant| {
                variant
                    .as_ref()
                    .map(|content| parameterize(parameterized, num_params, &mut id_gen, content))
            })
            .collect();

        debug_assert!(parameterized[type_id.0].is_none());

        parameterized[type_id.0] = Some(annot::TypeDef {
            num_params,
            variants: parameterized_variants,
        });
    }
}

fn add_dependencies(type_: &mono::Type, deps: &mut BTreeSet<mono::CustomTypeId>) {
    match type_ {
        mono::Type::Bool => {}
        mono::Type::Int => {}
        mono::Type::Float => {}
        mono::Type::Text => {}

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

fn parameterize_typedefs(typedefs: &[mono::TypeDef]) -> Vec<annot::TypeDef> {
    let dep_graph = Graph {
        edges_out: typedefs
            .iter()
            .map(|typedef| {
                let mut deps = BTreeSet::new();
                for variant in &typedef.variants {
                    if let Some(content) = variant {
                        add_dependencies(content, &mut deps);
                    }
                }
                deps.iter()
                    .map(|&mono::CustomTypeId(id)| graph::NodeId(id))
                    .collect()
            })
            .collect(),
    };

    let sccs = graph::strongly_connected(&dep_graph);

    let mut parameterized = vec![None; typedefs.len()];

    for scc in sccs {
        let type_ids: Vec<_> = scc
            .iter()
            .map(|&graph::NodeId(id)| mono::CustomTypeId(id))
            .collect();

        parameterize_typedef_scc(typedefs, &mut parameterized, &type_ids);
    }

    parameterized
        .into_iter()
        .map(|typedef| typedef.unwrap())
        .collect()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct SolverVarId(usize);

#[derive(Clone, Debug)]
enum SolverRequirement {
    Lam(lifted::LamId, Vec<SolverVarId>),
    PendingLam(lifted::LamId),
    Template(annot::TemplateId, Vec<SolverVarId>),
    ArithOp(Op),
    ArrayOp(ArrayOp, annot::Type<SolverVarId>),
    ArrayReplace(annot::Type<SolverVarId>),
    Ctor(mono::CustomTypeId, Vec<SolverVarId>, res::VariantId),
}

#[derive(Clone, Debug)]
enum SolverExpr {
    ArithOp(Op),
    ArrayOp(ArrayOp, annot::Type<SolverVarId>),
    Ctor(mono::CustomTypeId, Vec<SolverVarId>, res::VariantId),
    Global(mono::CustomGlobalId, Vec<SolverVarId>),
    PendingGlobal(mono::CustomGlobalId), // A global belonging to the current SCC
    Local(lifted::LocalId),
    Capture(lifted::CaptureId),
    Tuple(Vec<SolverExpr>),
    Lam(
        lifted::LamId,
        Vec<SolverVarId>, // Parameters on the lambda
        SolverVarId,      // Representation of the lambda expression
        Vec<SolverExpr>,  // Captures
    ),
    PendingLam(lifted::LamId, SolverVarId, Vec<SolverExpr>), // A lambda belonging to the current SCC
    App(
        Purity,
        SolverVarId, // Representation being called
        Box<SolverExpr>,
        Box<SolverExpr>,
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
    IntLit(i64),
    FloatLit(f64),
    TextLit(String),
}

#[derive(Clone, Debug)]
enum SolverPattern {
    Any(annot::Type<SolverVarId>),
    Var(annot::Type<SolverVarId>),
    Tuple(Vec<SolverPattern>),
    Ctor(
        mono::CustomTypeId,
        Vec<SolverVarId>,
        res::VariantId,
        Option<Box<SolverPattern>>,
    ),
    BoolConst(bool),
    IntConst(i64),
    FloatConst(f64),
    TextConst(String),
}

#[derive(Clone, Debug)]
struct SolverLamSig {
    purity: Purity,
    captures: Vec<annot::Type<SolverVarId>>,
    arg: annot::Type<SolverVarId>,
    ret: annot::Type<SolverVarId>,
}

#[derive(Clone, Debug)]
struct VarConstraints {
    equalities: BTreeSet<SolverVarId>,
    requirements: Vec<SolverRequirement>,
}

#[derive(Clone, Debug)]
struct ConstraintGraph {
    // Indexed by SolverVarId
    // Number of variables is implicit in the length of the vector
    var_constraints: Vec<VarConstraints>,
}

impl ConstraintGraph {
    fn new() -> Self {
        ConstraintGraph {
            var_constraints: Vec::new(),
        }
    }

    fn new_var(&mut self) -> SolverVarId {
        let id = SolverVarId(self.var_constraints.len());
        self.var_constraints.push(VarConstraints {
            equalities: BTreeSet::new(),
            requirements: Vec::new(),
        });
        id
    }

    fn equate(&mut self, fst: SolverVarId, snd: SolverVarId) {
        self.var_constraints[fst.0].equalities.insert(snd);
        self.var_constraints[snd.0].equalities.insert(fst);
    }

    fn require(&mut self, var: SolverVarId, req: SolverRequirement) {
        self.var_constraints[var.0].requirements.push(req);
    }
}

fn instantiate_mono(
    typedefs: &[annot::TypeDef],
    graph: &mut ConstraintGraph,
    type_: &mono::Type,
) -> annot::Type<SolverVarId> {
    match type_ {
        mono::Type::Bool => annot::Type::Bool,
        mono::Type::Int => annot::Type::Int,
        mono::Type::Float => annot::Type::Float,
        mono::Type::Text => annot::Type::Text,

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
            let vars = (0..typedefs[custom.0].num_params)
                .map(|_| graph.new_var())
                .collect();

            annot::Type::Custom(*custom, vars)
        }
    }
}

fn equate_types(
    graph: &mut ConstraintGraph,
    type1: &annot::Type<SolverVarId>,
    type2: &annot::Type<SolverVarId>,
) {
    match (type1, type2) {
        (annot::Type::Bool, annot::Type::Bool) => {}
        (annot::Type::Int, annot::Type::Int) => {}
        (annot::Type::Float, annot::Type::Float) => {}
        (annot::Type::Text, annot::Type::Text) => {}

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
            debug_assert_eq!(args1.len(), args2.len());

            for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                graph.equate(*arg1, *arg2);
            }
        }

        _ => unreachable!(),
    }
}

// TODO: Determine if this should be merged with similar structures in other passes
#[derive(Clone, Debug)]
struct LocalContext {
    types: Vec<annot::Type<SolverVarId>>,
}

impl LocalContext {
    fn new() -> Self {
        LocalContext { types: Vec::new() }
    }

    fn add_local(&mut self, type_: annot::Type<SolverVarId>) {
        self.types.push(type_);
    }

    fn local_type(&mut self, local: lifted::LocalId) -> annot::Type<SolverVarId> {
        self.types[local.0].clone()
    }

    fn with_scope<R, F: for<'a> FnOnce(&'a mut LocalContext) -> R>(&mut self, body: F) -> R {
        let old_len = self.types.len();
        let result = body(self);
        self.types.truncate(old_len);
        result
    }
}

fn instantiate_subst(
    vars: &[SolverVarId],
    type_: &annot::Type<annot::RepParamId>,
) -> annot::Type<SolverVarId> {
    match type_ {
        annot::Type::Bool => annot::Type::Bool,
        annot::Type::Int => annot::Type::Int,
        annot::Type::Float => annot::Type::Float,
        annot::Type::Text => annot::Type::Text,

        annot::Type::Array(item) => annot::Type::Array(Box::new(instantiate_subst(vars, item))),

        annot::Type::Tuple(items) => annot::Type::Tuple(
            items
                .iter()
                .map(|item| instantiate_subst(vars, item))
                .collect(),
        ),

        annot::Type::Func(purity, annot::RepParamId(id), arg, ret) => annot::Type::Func(
            *purity,
            vars[*id],
            Box::new(instantiate_subst(vars, arg)),
            Box::new(instantiate_subst(vars, ret)),
        ),

        annot::Type::Custom(custom, args) => annot::Type::Custom(
            *custom,
            args.iter().map(|&annot::RepParamId(id)| vars[id]).collect(),
        ),
    }
}

fn instantiate_pattern(
    typedefs: &[annot::TypeDef],
    locals: &mut LocalContext,
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

            let solver_content = match (content, &typedefs[custom.0].variants[variant.0]) {
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

        (&mono::Pattern::IntConst(val), annot::Type::Int) => SolverPattern::IntConst(val),

        (&mono::Pattern::FloatConst(val), annot::Type::Float) => SolverPattern::FloatConst(val),

        (mono::Pattern::TextConst(text), annot::Type::Text) => {
            SolverPattern::TextConst(text.clone())
        }

        (_, _) => unreachable!(),
    }
}

fn arith_op_type(graph: &mut ConstraintGraph, op: Op) -> annot::Type<SolverVarId> {
    let op_var = graph.new_var();
    graph.require(op_var, SolverRequirement::ArithOp(op));

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
            Box::new(annot::Type::Int),
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
            Box::new(annot::Type::Tuple(vec![annot::Type::Int, annot::Type::Int])),
            Box::new(annot::Type::Float),
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

    match op {
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
    }
}

fn array_op_type(
    graph: &mut ConstraintGraph,
    op: ArrayOp,
    solver_item_type: annot::Type<SolverVarId>,
) -> annot::Type<SolverVarId> {
    let op_var = graph.new_var();
    graph.require(
        op_var,
        SolverRequirement::ArrayOp(op, solver_item_type.clone()),
    );

    match op {
        ArrayOp::Item => {
            let ret_closure_var = graph.new_var();
            graph.require(
                op_var,
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
    }
}

#[derive(Clone, Copy, Debug)]
struct GlobalContext<'a> {
    annot_vals: &'a [Option<annot::ValDef>], // Indexed by mono::CustomGlobalId
    annot_lams: &'a [Option<annot::LamDef>], // Indexed by lifted::LamId
    curr_vals: &'a BTreeMap<mono::CustomGlobalId, annot::Type<SolverVarId>>,
    curr_lams: &'a BTreeMap<lifted::LamId, SolverLamSig>,
}

fn instantiate_params(graph: &mut ConstraintGraph, params: &annot::Params) -> Vec<SolverVarId> {
    let param_vars: Vec<_> = (0..params.num_params()).map(|_| graph.new_var()).collect();

    for (param_var, (req_template, req_params)) in param_vars.iter().zip(params.requirements.iter())
    {
        graph.require(
            *param_var,
            SolverRequirement::Template(
                *req_template,
                req_params
                    .iter()
                    .map(|other_param| param_vars[other_param.0])
                    .collect(),
            ),
        );
    }

    param_vars
}

fn instantiate_expr(
    typedefs: &[annot::TypeDef],
    globals: GlobalContext,
    graph: &mut ConstraintGraph,
    captures: &[annot::Type<SolverVarId>],
    locals: &mut LocalContext,
    expr: &lifted::Expr,
) -> (SolverExpr, annot::Type<SolverVarId>) {
    match expr {
        &lifted::Expr::ArithOp(op) => {
            let solver_type = arith_op_type(graph, op);
            (SolverExpr::ArithOp(op), solver_type)
        }

        lifted::Expr::ArrayOp(op, item_type) => {
            let solver_item_type = instantiate_mono(typedefs, graph, item_type);
            let solver_type = array_op_type(graph, *op, solver_item_type.clone());
            (SolverExpr::ArrayOp(*op, solver_item_type), solver_type)
        }

        &lifted::Expr::Ctor(custom, variant) => {
            let typedef = &typedefs[custom.0];

            let params: Vec<_> = (0..typedef.num_params).map(|_| graph.new_var()).collect();

            let solver_type = match &typedef.variants[variant.0] {
                Some(content_type) => {
                    let op_closure_var = graph.new_var();
                    graph.require(
                        op_closure_var,
                        SolverRequirement::Ctor(custom, params.clone(), variant),
                    );

                    let solver_content_type = instantiate_subst(&params, content_type);

                    annot::Type::Func(
                        Purity::Pure,
                        op_closure_var,
                        Box::new(solver_content_type),
                        Box::new(annot::Type::Custom(custom, params.clone())),
                    )
                }

                None => annot::Type::Custom(custom, params.clone()),
            };

            let solver_expr = SolverExpr::Ctor(custom, params, variant);

            (solver_expr, solver_type)
        }

        &lifted::Expr::Global(global) => match &globals.annot_vals[global.0] {
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

        &lifted::Expr::Local(local) => (SolverExpr::Local(local), locals.local_type(local)),

        &lifted::Expr::Capture(capture) => {
            (SolverExpr::Capture(capture), captures[capture.0].clone())
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
            let mut solver_captures = Vec::new();
            let mut solver_capture_types = Vec::new();

            for capture in lam_captures {
                let (solver_capture, solver_type) =
                    instantiate_expr(typedefs, globals, graph, captures, locals, capture);
                solver_captures.push(solver_capture);
                solver_capture_types.push(solver_type);
            }

            match &globals.annot_lams[lam.0] {
                Some(lam_def) => {
                    let scheme_params = instantiate_params(graph, &lam_def.params);

                    debug_assert_eq!(lam_def.captures.len(), lam_captures.len());

                    for (expected, actual) in
                        lam_def.captures.iter().zip(solver_capture_types.iter())
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

                    for (expected, actual) in
                        solver_sig.captures.iter().zip(solver_capture_types.iter())
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
                    Box::new(solver_arg),
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

        &lifted::Expr::IntLit(val) => (SolverExpr::IntLit(val), annot::Type::Int),

        &lifted::Expr::FloatLit(val) => (SolverExpr::FloatLit(val), annot::Type::Float),

        lifted::Expr::TextLit(text) => (SolverExpr::TextLit(text.clone()), annot::Type::Text),
    }
}

fn instantiate_lam_sig(
    typedefs: &[annot::TypeDef],
    graph: &mut ConstraintGraph,
    lam_def: &lifted::LamDef,
) -> SolverLamSig {
    let solver_captures = lam_def
        .captures
        .iter()
        .map(|capture| instantiate_mono(typedefs, graph, capture))
        .collect();

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

    constraints: ConstraintGraph,
}

fn instantiate_scc(
    typedefs: &[annot::TypeDef],
    annot_vals: &[Option<annot::ValDef>],
    annot_lams: &[Option<annot::LamDef>],
    vals: &[lifted::ValDef],
    lams: &[lifted::LamDef],
    scc_vals: &[mono::CustomGlobalId],
    scc_lams: &[lifted::LamId],
) -> SolverScc {
    let mut graph = ConstraintGraph::new();

    let curr_val_sigs: BTreeMap<_, _> = scc_vals
        .iter()
        .map(|&val_id| {
            (
                val_id,
                instantiate_mono(typedefs, &mut graph, &vals[val_id.0].type_),
            )
        })
        .collect();

    let curr_lam_sigs: BTreeMap<_, _> = scc_lams
        .iter()
        .map(|&lam_id| {
            (
                lam_id,
                instantiate_lam_sig(typedefs, &mut graph, &lams[lam_id.0]),
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
                &[],
                &mut local_ctx,
                &vals[val_id.0].body,
            );

            debug_assert!(local_ctx.types.is_empty());

            equate_types(&mut graph, &global_ctx.curr_vals[&val_id], &solver_val_type);

            (val_id, solver_val)
        })
        .collect();

    let solver_lams: BTreeMap<_, _> = scc_lams
        .iter()
        .map(|&lam_id| {
            let solver_sig = &global_ctx.curr_lams[&lam_id];
            let lam_def = &lams[lam_id.0];

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

            debug_assert!(local_ctx.types.is_empty());

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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct EquivClass(usize);

#[derive(Clone, Debug)]
struct EquivClasses(Vec<EquivClass>); // Indexed by SolverVarId

impl EquivClasses {
    fn class(&self, var: SolverVarId) -> EquivClass {
        self.0[var.0]
    }
}

fn solve_equiv_classes(constraints: &ConstraintGraph) -> EquivClasses {
    let equality_graph = graph::Undirected::from_directed_unchecked(Graph {
        edges_out: constraints
            .var_constraints
            .iter()
            .map(|var_constraints| {
                var_constraints
                    .equalities
                    .iter()
                    .map(|&SolverVarId(other)| graph::NodeId(other))
                    .collect()
            })
            .collect(),
    });

    let components = graph::connected_components(&equality_graph);

    let equiv_classes: Vec<_> = {
        let mut equiv_classes = vec![None; constraints.var_constraints.len()];

        for (equiv_class, solver_vars) in components.iter().enumerate() {
            for &graph::NodeId(solver_var) in solver_vars {
                debug_assert!(equiv_classes[solver_var].is_none());
                equiv_classes[solver_var] = Some(EquivClass(equiv_class));
            }
        }

        equiv_classes.into_iter().map(Option::unwrap).collect()
    };

    EquivClasses(equiv_classes)
}

fn add_mentioned_classes(
    equiv_classes: &EquivClasses,
    type_: &annot::Type<SolverVarId>,
    mentioned: &mut BTreeSet<EquivClass>,
) {
    match type_ {
        annot::Type::Bool => {}
        annot::Type::Int => {}
        annot::Type::Float => {}
        annot::Type::Text => {}

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
            for &var in args {
                mentioned.insert(equiv_classes.class(var));
            }
        }
    }
}

#[derive(Clone, Debug)]
struct Params(Vec<EquivClass>); // Indexed by annot::RepParamId

fn find_params(scc: &SolverScc, equiv_classes: &EquivClasses) -> Params {
    let mut mentioned = BTreeSet::new();

    for sig in scc.val_sigs.values() {
        add_mentioned_classes(equiv_classes, sig, &mut mentioned);
    }

    for sig in scc.lam_sigs.values() {
        for capture in &sig.captures {
            add_mentioned_classes(equiv_classes, capture, &mut mentioned);
        }

        add_mentioned_classes(equiv_classes, &sig.arg, &mut mentioned);
        add_mentioned_classes(equiv_classes, &sig.ret, &mut mentioned);
    }

    Params(mentioned.into_iter().collect())
}

fn add_req_mentioned_classes(
    equiv_classes: &EquivClasses,
    params: &Params,
    req: &SolverRequirement,
    mentioned: &mut BTreeSet<EquivClass>,
) {
    match req {
        SolverRequirement::Lam(_, lam_params) => {
            mentioned.extend(lam_params.iter().map(|&var| equiv_classes.class(var)));
        }

        SolverRequirement::PendingLam(_) => {
            mentioned.extend(params.0.iter().cloned());
        }

        SolverRequirement::Template(_, template_params) => {
            mentioned.extend(template_params.iter().map(|&var| equiv_classes.class(var)));
        }

        SolverRequirement::ArithOp(_) => {}

        SolverRequirement::ArrayOp(_, item_type) | SolverRequirement::ArrayReplace(item_type) => {
            add_mentioned_classes(equiv_classes, item_type, mentioned);
        }

        SolverRequirement::Ctor(_, custom_params, _) => {
            mentioned.extend(custom_params.iter().map(|&var| equiv_classes.class(var)));
        }
    }
}

#[derive(Clone, Debug)]
struct RequirementDeps(Vec<BTreeSet<EquivClass>>); // Indexed by EquivClass

fn requirement_deps(
    equiv_classes: &EquivClasses,
    params: &Params,
    graph: &ConstraintGraph,
) -> RequirementDeps {
    let mut deps = vec![BTreeSet::new(); equiv_classes.0.len()];

    for (var_idx, var_constraints) in graph.var_constraints.iter().enumerate() {
        let class = equiv_classes.class(SolverVarId(var_idx));

        let class_deps = &mut deps[class.0];

        for req in &var_constraints.requirements {
            add_req_mentioned_classes(equiv_classes, params, req, class_deps);
        }
    }

    RequirementDeps(deps)
}

#[derive(Clone, Debug)]
struct ClassRequirements(Vec<Vec<SolverRequirement>>); // Outer Vec indexed by EquivClass

fn consolidate_class_requirements(
    equiv_classes: &EquivClasses,
    graph: ConstraintGraph,
) -> ClassRequirements {
    let mut reqs = vec![Vec::new(); equiv_classes.0.len()];

    for (var_idx, var_constraints) in graph.var_constraints.into_iter().enumerate() {
        let class = equiv_classes.class(SolverVarId(var_idx));

        reqs[class.0].extend(var_constraints.requirements);
    }

    ClassRequirements(reqs)
}

#[derive(Clone, Debug)]
struct Solutions {
    class_solutions: Vec<annot::Solution>, // Indexed by EquivClass
    param_reqs: Vec<(annot::TemplateId, Vec<annot::RepParamId>)>, // Indexed by annot::RepParamId
}

fn translate_solution_for_template(
    solver_to_template: &BTreeMap<annot::RepParamId, annot::RepParamId>,
    solution: &annot::Solution,
) -> annot::Solution {
    match solution {
        annot::Solution::Param(param) => annot::Solution::Param(solver_to_template[param]),

        annot::Solution::MinSolutionTo(id, args) => annot::Solution::MinSolutionTo(
            *id,
            args.iter().map(|arg| solver_to_template[arg]).collect(),
        ),
    }
}

fn translate_var_for_template(
    equiv_classes: &EquivClasses,
    class_solutions: &[Option<annot::Solution>],
    solver_to_template: &BTreeMap<annot::RepParamId, annot::RepParamId>,
    var: SolverVarId,
) -> annot::Solution {
    translate_solution_for_template(
        solver_to_template,
        class_solutions[equiv_classes.class(var).0]
            .as_ref()
            .unwrap(),
    )
}

fn translate_type_for_template(
    equiv_classes: &EquivClasses,
    class_solutions: &[Option<annot::Solution>],
    solver_to_template: &BTreeMap<annot::RepParamId, annot::RepParamId>,
    type_: &annot::Type<SolverVarId>,
) -> annot::Type<annot::Solution> {
    match type_ {
        annot::Type::Bool => annot::Type::Bool,
        annot::Type::Int => annot::Type::Int,
        annot::Type::Float => annot::Type::Float,
        annot::Type::Text => annot::Type::Text,

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
            vars.iter()
                .map(|&var| {
                    translate_var_for_template(
                        equiv_classes,
                        class_solutions,
                        solver_to_template,
                        var,
                    )
                })
                .collect(),
        ),
    }
}

fn translate_req_for_template(
    equiv_classes: &EquivClasses,
    params: &Params,
    class_solutions: &[Option<annot::Solution>], // Indexed by EquivClass
    solver_to_template: &BTreeMap<annot::RepParamId, annot::RepParamId>,
    req: &SolverRequirement,
) -> annot::Requirement {
    match req {
        SolverRequirement::Lam(lam_id, vars) => annot::Requirement::Lam(
            *lam_id,
            vars.iter()
                .map(|&var| {
                    translate_var_for_template(
                        equiv_classes,
                        class_solutions,
                        solver_to_template,
                        var,
                    )
                })
                .collect(),
        ),

        SolverRequirement::PendingLam(lam_id) => annot::Requirement::Lam(
            *lam_id,
            params
                .0
                .iter()
                .map(|&class| {
                    translate_solution_for_template(
                        solver_to_template,
                        class_solutions[class.0].as_ref().unwrap(),
                    )
                })
                .collect(),
        ),

        SolverRequirement::Template(template_id, vars) => annot::Requirement::Template(
            *template_id,
            vars.iter()
                .map(|&var| {
                    translate_var_for_template(
                        equiv_classes,
                        class_solutions,
                        solver_to_template,
                        var,
                    )
                })
                .collect(),
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

        SolverRequirement::Ctor(custom, vars, variant) => annot::Requirement::Ctor(
            *custom,
            vars.iter()
                .map(|&var| {
                    translate_var_for_template(
                        equiv_classes,
                        class_solutions,
                        solver_to_template,
                        var,
                    )
                })
                .collect(),
            *variant,
        ),
    }
}

fn solve_requirements(
    equiv_classes: &EquivClasses,
    params: &Params,
    req_deps: &RequirementDeps,
    reqs: &ClassRequirements,
    templates: &mut Vec<annot::Template>,
) -> Solutions {
    let mut class_solutions = vec![None; equiv_classes.0.len()];
    let mut param_reqs = vec![None; params.0.len()];

    for (param_id, param_class) in params.0.iter().enumerate() {
        debug_assert!(class_solutions[param_class.0].is_none());
        class_solutions[param_class.0] = Some(annot::Solution::Param(annot::RepParamId(param_id)));
    }

    let dep_graph = Graph {
        edges_out: req_deps
            .0
            .iter()
            .map(|class_deps| {
                class_deps
                    .iter()
                    .map(|&EquivClass(dep)| graph::NodeId(dep))
                    .collect()
            })
            .collect(),
    };

    let class_sccs = graph::strongly_connected(&dep_graph);

    for scc in class_sccs {
        let is_cycle = if scc.len() == 1 {
            // We have an SCC with a single node, but we still need to check if it has a self-loop.
            let graph::NodeId(singleton) = scc[0];

            if req_deps.0[singleton].contains(&EquivClass(singleton)) {
                annot::InCycle::Cycle
            } else {
                annot::InCycle::NoCycle
            }
        } else {
            annot::InCycle::Cycle
        };

        // Find parameters mentioned

        let mut params_mentioned = BTreeSet::new();

        for &graph::NodeId(class_idx) in &scc {
            for dep in &req_deps.0[class_idx] {
                match &class_solutions[dep.0] {
                    &Some(annot::Solution::Param(param)) => {
                        params_mentioned.insert(param);
                    }

                    Some(annot::Solution::MinSolutionTo(_, dep_mentioned_params)) => {
                        params_mentioned.extend(dep_mentioned_params.iter().cloned());
                    }

                    None => {
                        // Dependency is a non-parameter class in the current SCC
                    }
                }
            }
        }

        // Fix an order
        let params_mentioned: Vec<_> = params_mentioned.into_iter().collect();

        // Forward-declare templates for all non-parameter classes

        for &graph::NodeId(class_idx) in &scc {
            match &mut class_solutions[class_idx] {
                Some(annot::Solution::Param(_param)) => {
                    // The template representing the requirements for this variable should go into
                    // param_reqs rather than class_solutions.  As such, we won't need to know it's
                    // ID until we actually populate it, so we do nothing for now.
                }

                Some(annot::Solution::MinSolutionTo(_, _)) => unreachable!(),

                solution @ None => {
                    let template_id = annot::TemplateId(templates.len());

                    // Create a dummy template whose requirements we'll fill in during the next loop
                    templates.push(annot::Template {
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
            .enumerate()
            .map(|(internal_idx, &solver_param)| (solver_param, annot::RepParamId(internal_idx)))
            .collect();

        // Fill in template and parameters with the appropriate requirements

        for &graph::NodeId(class_idx) in &scc {
            let template_internal_requirements: Vec<_> = reqs.0[class_idx]
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

            match &class_solutions[class_idx] {
                Some(annot::Solution::Param(param)) => {
                    // Add parameter requirements

                    let param_req_template = annot::Template {
                        in_cycle: is_cycle,
                        num_params: params_mentioned.len(),
                        requirements: template_internal_requirements,
                    };

                    let template_id = annot::TemplateId(templates.len());
                    templates.push(param_req_template);

                    debug_assert!(param_reqs[param.0].is_none());
                    param_reqs[param.0] = Some((template_id, params_mentioned.clone()));
                }

                Some(annot::Solution::MinSolutionTo(template_id, template_params)) => {
                    debug_assert_eq!(template_params, &params_mentioned);
                    debug_assert!(templates[template_id.0].requirements.is_empty());

                    templates[template_id.0].requirements = template_internal_requirements;
                }

                None => unreachable!(),
            }
        }
    }

    Solutions {
        class_solutions: class_solutions.into_iter().map(Option::unwrap).collect(),
        param_reqs: param_reqs.into_iter().map(Option::unwrap).collect(),
    }
}
