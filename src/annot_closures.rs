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
enum SolverConstraint {
    Lam(SolverVarId, lifted::LamId, Vec<SolverVarId>),
    PendingLam(SolverVarId, lifted::LamId),
    Template(annot::TemplateId, Vec<SolverVarId>),
    ArithOp(SolverVarId, Op),
    ArrayOp(SolverVarId, ArrayOp, annot::Type<SolverVarId>),
    ArrayReplace(SolverVarId, annot::Type<SolverVarId>),
    Ctor(
        SolverVarId,
        mono::CustomTypeId,
        Vec<SolverVarId>,
        res::VariantId,
    ),
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
struct ConstraintGraph {
    var_equalities: Vec<BTreeSet<SolverVarId>>, // Indexed by SolverVarId
    constraints: Vec<SolverConstraint>,
}

impl ConstraintGraph {
    fn new() -> Self {
        ConstraintGraph {
            var_equalities: Vec::new(),
            constraints: Vec::new(),
        }
    }

    fn new_var(&mut self) -> SolverVarId {
        let id = SolverVarId(self.var_equalities.len());
        self.var_equalities.push(BTreeSet::new());
        id
    }

    fn equate(&mut self, fst: SolverVarId, snd: SolverVarId) {
        self.var_equalities[fst.0].insert(snd);
        self.var_equalities[snd.0].insert(fst);
    }

    fn constrain(&mut self, constraint: SolverConstraint) {
        self.constraints.push(constraint);
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
    graph.constrain(SolverConstraint::ArithOp(op_var, op));

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
    graph.constrain(SolverConstraint::ArrayOp(
        op_var,
        op,
        solver_item_type.clone(),
    ));

    match op {
        ArrayOp::Item => {
            let ret_closure_var = graph.new_var();
            graph.constrain(SolverConstraint::ArrayReplace(
                ret_closure_var,
                solver_item_type.clone(),
            ));

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
    templates: &'a [annot::Template],
    annot_vals: &'a [Option<annot::ValDef>], // Indexed by mono::CustomGlobalId
    annot_lams: &'a [Option<annot::LamDef>], // Indexed by lifted::LamId
    curr_vals: &'a BTreeMap<mono::CustomGlobalId, annot::Type<SolverVarId>>,
    curr_lams: &'a BTreeMap<lifted::LamId, SolverLamSig>,
}

fn instantiate_template(
    graph: &mut ConstraintGraph,
    templates: &[annot::Template],
    template_id: annot::TemplateId,
) -> Vec<SolverVarId> {
    let template = &templates[template_id.0];

    let param_vars: Vec<_> = (0..template.params.len())
        .map(|_| graph.new_var())
        .collect();

    graph.constrain(SolverConstraint::Template(template_id, param_vars.clone()));

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
                    graph.constrain(SolverConstraint::Ctor(
                        op_closure_var,
                        custom,
                        params.clone(),
                        variant,
                    ));

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
                let scheme_params =
                    instantiate_template(graph, &globals.templates, global_def.template);

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
                    let scheme_params =
                        instantiate_template(graph, &globals.templates, lam_def.template);

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
                    graph.constrain(SolverConstraint::Lam(lam_var, *lam, scheme_params.clone()));

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
                    graph.constrain(SolverConstraint::PendingLam(lam_var, *lam));

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
    templates: &[annot::Template],
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
        templates,
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

#[derive(Clone, Debug)]
struct EquivClasses(Vec<annot::TemplateVarId>); // Indexed by SolverVarId

impl EquivClasses {
    fn class(&self, var: SolverVarId) -> annot::TemplateVarId {
        self.0[var.0]
    }
}

fn solve_equiv_classes(constraints: &ConstraintGraph) -> EquivClasses {
    let equality_graph = graph::Undirected::from_directed_unchecked(Graph {
        edges_out: constraints
            .var_equalities
            .iter()
            .map(|others_equal| {
                others_equal
                    .iter()
                    .map(|&SolverVarId(other)| graph::NodeId(other))
                    .collect()
            })
            .collect(),
    });

    let components = graph::connected_components(&equality_graph);

    let equiv_classes: Vec<_> = {
        let mut equiv_classes = vec![None; constraints.var_equalities.len()];

        for (equiv_class, solver_vars) in components.iter().enumerate() {
            for &graph::NodeId(solver_var) in solver_vars {
                debug_assert!(equiv_classes[solver_var].is_none());
                equiv_classes[solver_var] = Some(annot::TemplateVarId(equiv_class));
            }
        }

        equiv_classes.into_iter().map(Option::unwrap).collect()
    };

    EquivClasses(equiv_classes)
}

fn add_mentioned_classes(
    equiv_classes: &EquivClasses,
    type_: &annot::Type<SolverVarId>,
    mentioned: &mut BTreeSet<annot::TemplateVarId>,
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
struct Params(Vec<annot::TemplateVarId>); // Indexed by annot::RepParamId

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

fn extract_type(
    equiv_classes: &EquivClasses,
    type_: &annot::Type<SolverVarId>,
) -> annot::Type<annot::TemplateVarId> {
    match type_ {
        annot::Type::Bool => annot::Type::Bool,
        annot::Type::Int => annot::Type::Int,
        annot::Type::Float => annot::Type::Float,
        annot::Type::Text => annot::Type::Text,

        annot::Type::Array(item) => annot::Type::Array(Box::new(extract_type(equiv_classes, item))),

        annot::Type::Tuple(items) => annot::Type::Tuple(
            items
                .iter()
                .map(|item| extract_type(equiv_classes, item))
                .collect(),
        ),

        annot::Type::Func(purity, var, arg, ret) => annot::Type::Func(
            *purity,
            equiv_classes.class(*var),
            Box::new(extract_type(equiv_classes, arg)),
            Box::new(extract_type(equiv_classes, ret)),
        ),

        annot::Type::Custom(custom, vars) => annot::Type::Custom(
            *custom,
            vars.iter().map(|&var| equiv_classes.class(var)).collect(),
        ),
    }
}

fn extract_constraint(
    equiv_classes: &EquivClasses,
    params: &Params,
    constraint: &SolverConstraint,
) -> annot::Constraint {
    match constraint {
        SolverConstraint::Lam(var, lam_id, params) => annot::Constraint::Lam(
            equiv_classes.class(*var),
            *lam_id,
            params
                .iter()
                .map(|param| equiv_classes.class(*param))
                .collect(),
        ),

        SolverConstraint::PendingLam(var, lam_id) => {
            annot::Constraint::Lam(equiv_classes.class(*var), *lam_id, params.0.clone())
        }

        SolverConstraint::Template(template_id, params) => annot::Constraint::Template(
            *template_id,
            params.iter().map(|&var| equiv_classes.class(var)).collect(),
        ),

        SolverConstraint::ArithOp(var, op) => {
            annot::Constraint::ArithOp(equiv_classes.class(*var), *op)
        }

        SolverConstraint::ArrayOp(var, op, item_type) => annot::Constraint::ArrayOp(
            equiv_classes.class(*var),
            *op,
            extract_type(equiv_classes, item_type),
        ),

        SolverConstraint::ArrayReplace(var, item_type) => annot::Constraint::ArrayReplace(
            equiv_classes.class(*var),
            extract_type(equiv_classes, item_type),
        ),

        SolverConstraint::Ctor(var, custom, params, variant) => annot::Constraint::Ctor(
            equiv_classes.class(*var),
            *custom,
            params
                .iter()
                .map(|&param| equiv_classes.class(param))
                .collect(),
            *variant,
        ),
    }
}

fn extract_expr(equiv_classes: &EquivClasses, params: &Params, expr: &SolverExpr) -> annot::Expr {
    match expr {
        // TODO: Add fields to primitive opeations (ArithOp, ArrayOp, Ctor) to track what
        // representation they should be coerced to upon construction.
        SolverExpr::ArithOp(op) => annot::Expr::ArithOp(*op),

        SolverExpr::ArrayOp(op, item_type) => {
            annot::Expr::ArrayOp(*op, extract_type(equiv_classes, item_type))
        }

        SolverExpr::Ctor(custom, type_params, variant) => annot::Expr::Ctor(
            *custom,
            type_params
                .iter()
                .map(|&param| equiv_classes.class(param))
                .collect(),
            *variant,
        ),

        SolverExpr::Global(global_id, global_params) => annot::Expr::Global(
            *global_id,
            global_params
                .iter()
                .map(|&param| equiv_classes.class(param))
                .collect(),
        ),

        SolverExpr::PendingGlobal(global_id) => annot::Expr::Global(*global_id, params.0.clone()),

        SolverExpr::Local(local_id) => annot::Expr::Local(*local_id),

        SolverExpr::Capture(capture_id) => annot::Expr::Capture(*capture_id),

        SolverExpr::Tuple(items) => annot::Expr::Tuple(
            items
                .iter()
                .map(|item| extract_expr(equiv_classes, params, item))
                .collect(),
        ),

        SolverExpr::Lam(lam_id, lam_params, rep_var, captures) => annot::Expr::Lam(
            *lam_id,
            lam_params
                .iter()
                .map(|&param| equiv_classes.class(param))
                .collect(),
            equiv_classes.class(*rep_var),
            captures
                .iter()
                .map(|capture| extract_expr(equiv_classes, params, capture))
                .collect(),
        ),

        SolverExpr::PendingLam(lam_id, rep_var, captures) => annot::Expr::Lam(
            *lam_id,
            params.0.clone(),
            equiv_classes.class(*rep_var),
            captures
                .iter()
                .map(|capture| extract_expr(equiv_classes, params, capture))
                .collect(),
        ),

        SolverExpr::App(purity, func_rep_var, func, arg) => annot::Expr::App(
            *purity,
            equiv_classes.class(*func_rep_var),
            Box::new(extract_expr(equiv_classes, params, func)),
            Box::new(extract_expr(equiv_classes, params, arg)),
        ),

        SolverExpr::Match(discrim, cases, result_type) => annot::Expr::Match(
            Box::new(extract_expr(equiv_classes, params, discrim)),
            cases
                .iter()
                .map(|(pat, body)| {
                    (
                        extract_pattern(equiv_classes, pat),
                        extract_expr(equiv_classes, params, body),
                    )
                })
                .collect(),
            extract_type(equiv_classes, result_type),
        ),

        SolverExpr::Let(lhs, rhs, body) => annot::Expr::Let(
            extract_pattern(equiv_classes, lhs),
            Box::new(extract_expr(equiv_classes, params, rhs)),
            Box::new(extract_expr(equiv_classes, params, body)),
        ),

        SolverExpr::ArrayLit(item_type, items) => annot::Expr::ArrayLit(
            extract_type(equiv_classes, item_type),
            items
                .iter()
                .map(|item| extract_expr(equiv_classes, params, item))
                .collect(),
        ),

        &SolverExpr::BoolLit(val) => annot::Expr::BoolLit(val),

        &SolverExpr::IntLit(val) => annot::Expr::IntLit(val),

        &SolverExpr::FloatLit(val) => annot::Expr::FloatLit(val),

        SolverExpr::TextLit(text) => annot::Expr::TextLit(text.clone()),
    }
}

fn extract_pattern(equiv_classes: &EquivClasses, pat: &SolverPattern) -> annot::Pattern {
    match pat {
        SolverPattern::Any(type_) => annot::Pattern::Any(extract_type(equiv_classes, type_)),

        SolverPattern::Var(type_) => annot::Pattern::Var(extract_type(equiv_classes, type_)),

        SolverPattern::Tuple(items) => annot::Pattern::Tuple(
            items
                .iter()
                .map(|item| extract_pattern(equiv_classes, item))
                .collect(),
        ),

        SolverPattern::Ctor(custom, params, variant, content) => annot::Pattern::Ctor(
            *custom,
            params
                .iter()
                .map(|&param| equiv_classes.class(param))
                .collect(),
            *variant,
            content
                .as_ref()
                .map(|content| Box::new(extract_pattern(equiv_classes, content))),
        ),

        &SolverPattern::BoolConst(val) => annot::Pattern::BoolConst(val),

        &SolverPattern::IntConst(val) => annot::Pattern::IntConst(val),

        &SolverPattern::FloatConst(val) => annot::Pattern::FloatConst(val),

        SolverPattern::TextConst(text) => annot::Pattern::TextConst(text.clone()),
    }
}
