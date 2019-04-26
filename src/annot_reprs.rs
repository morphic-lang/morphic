use crate::data::first_order_ast as in_ast;
use crate::data::repr_annot_ast as out_ast;

mod mid_ast {
    pub use super::out_ast::{Constraint, ExprId, LocalId, Pattern, RepParamId, Type, TypeDef};
    use crate::annot_aliases;
    pub use crate::data::first_order_ast::{self, BinOp, CustomFuncId, CustomTypeId, VariantId};
    use crate::data::purity::Purity;
    use crate::util::constraint_graph::SolverVarId;
    use im_rc::{vector, Vector};

    #[derive(Clone, Debug)]
    pub enum ArithOp {
        IntOp(BinOp, Term, Term),
        FloatOp(BinOp, Term, Term),
        IntCmp(std::cmp::Ordering, Term, Term),
        FloatCmp(std::cmp::Ordering, Term, Term),
        NegateInt(Term),
        NegateFloat(Term),
    }

    // Terms do not have to be assigned to temps before being used.
    // Thus they can have no operational side-effects.
    #[derive(Clone, Debug)]
    pub enum Term {
        Access(
            LocalId,
            annot_aliases::FieldPath,         // actual accessed path
            Option<annot_aliases::FieldPath>, // type-folded (pruned) path for alias analysis
        ),
        BoolLit(bool),
        IntLit(i64),
        FloatLit(f64),
    }

    #[derive(Clone, Debug)]
    pub enum ArrayOp {
        // Construct(..) effectively contains an array type (i.e. Type::Array variant)
        Construct(Box<Type<SolverVarId>>, SolverVarId, Vec<Term>),
        Item(
            Term,                              // Array
            Term,                              // Index
            Option<(CustomTypeId, VariantId)>, // Constructor to wrap returned HoleArray in
        ), // Returns tuple of (item, (potentially wrapped) hole array)
        Len(Term),
        Push(
            Term, // Array
            Term, // Item
        ), // Returns new array
        Pop(Term), // Returns tuple of (array, item)
        Replace(
            Term, // Hole array
            Term, // Item
        ), // Returns new array
    }

    #[derive(Clone, Debug)]
    pub enum ReprParams<ReprVar> {
        Determined(Vec<ReprVar>),
        Pending, // for calls to the same SCC
    }

    #[derive(Clone, Debug)]
    pub enum Expr<ExprType> {
        Term(Term),
        ArithOp(ArithOp),
        ArrayOp(ArrayOp),
        Ctor(CustomTypeId, VariantId, Option<Term>),
        Tuple(Vec<Term>),
        Local(LocalId),
        Call(Purity, CustomFuncId, Term, Option<ReprParams<SolverVarId>>),
        Match(
            LocalId,
            Vec<(Pattern, Block<ExprType>)>,
            Box<Type<SolverVarId>>,
        ),
    }

    #[derive(Clone, Debug)]
    pub struct Block<ExprType> {
        pub initial_idx: usize, // for LocalId, not ExprId
        // `terms` and `types` are indexed by LocalId *offset by `initial_idx`
        pub terms: Vec<Expr<ExprType>>,
        pub types: Vec<ExprType>,
        pub expr_ids: Vector<ExprId>, // indexed by LocalId
    }

    pub type TypedExpr = Expr<Type<SolverVarId>>;
    pub type TypedBlock = Block<Type<SolverVarId>>;

    // TODO: move out of data module?
    impl<T> Block<T> {
        pub fn function_body() -> Block<T> {
            Block {
                // LocalId(0) is arg, so first term index is 1
                initial_idx: 1,
                terms: vec![],
                types: vec![],
                expr_ids: vector![ExprId::ARG],
            }
        }

        pub fn branch_from(block: &Block<T>) -> Block<T> {
            Block {
                initial_idx: block.initial_idx + block.terms.len(),
                terms: vec![],
                types: vec![],
                expr_ids: block.expr_ids.clone(),
            }
        }

        // Adds an expression to the block and returns a Term referring to that expression
        pub fn add(&mut self, e: Expr<T>) -> Term {
            Term::Access(self.add_local(e), vector![], None)
        }

        pub fn add_local(&mut self, e: Expr<T>) -> LocalId {
            let idx = self.initial_idx + self.terms.len();
            self.terms.push(e);
            LocalId(idx)
        }

        pub fn expr_id_of(&self, l: LocalId) -> ExprId {
            self.expr_ids[l.0]
        }
    }

    #[derive(Clone, Debug)]
    pub struct FuncDef<ExprType> {
        pub purity: Purity,
        pub arg_type: Type<SolverVarId>,
        pub ret_type: Type<SolverVarId>,
        pub constraints: Vec<Vec<Constraint>>,
        pub body: Block<ExprType>,
    }

    type TypedFuncDef = FuncDef<Type<SolverVarId>>;
}

mod parameterize {
    use super::{in_ast, mid_ast};
    use crate::graph::{self, Graph};
    use std::collections::{BTreeMap, BTreeSet};

    fn count_params(
        parameterized: &[Option<mid_ast::TypeDef<mid_ast::RepParamId>>],
        type_: &in_ast::Type,
    ) -> usize {
        match type_ {
            in_ast::Type::Bool | in_ast::Type::Int | in_ast::Type::Float | in_ast::Type::Text => 0,
            in_ast::Type::Array(item) | in_ast::Type::HoleArray(item) => {
                1 + count_params(parameterized, item)
            }
            in_ast::Type::Tuple(items) => items
                .iter()
                .map(|item| count_params(parameterized, item))
                .sum(),
            in_ast::Type::Custom(other) => match &parameterized[other.0] {
                Some(typedef) => typedef.num_params,
                // This is a typedef in the same SCC; the reference to it here contributes no additional
                // parameters to the entire SCC.
                None => 0,
            },
        }
    }

    #[derive(Clone, Debug)]
    struct ReprVarIdGen(usize);

    impl ReprVarIdGen {
        fn fresh(&mut self) -> mid_ast::RepParamId {
            let result = mid_ast::RepParamId(self.0);
            self.0 += 1;
            result
        }
    }

    fn parameterize(
        parameterized: &[Option<mid_ast::TypeDef<mid_ast::RepParamId>>],
        scc_num_params: usize,
        id_gen: &mut ReprVarIdGen,
        type_: &in_ast::Type,
    ) -> mid_ast::Type<mid_ast::RepParamId> {
        match type_ {
            in_ast::Type::Bool => mid_ast::Type::Bool,
            in_ast::Type::Int => mid_ast::Type::Int,
            in_ast::Type::Float => mid_ast::Type::Float,
            in_ast::Type::Text => mid_ast::Type::Text,

            in_ast::Type::Array(item) | in_ast::Type::HoleArray(item) => {
                let repr_param = id_gen.fresh();
                mid_ast::Type::Array(
                    Box::new(parameterize(parameterized, scc_num_params, id_gen, item)),
                    repr_param,
                )
            }

            in_ast::Type::Tuple(items) => mid_ast::Type::Tuple(
                items
                    .iter()
                    .map(|item| parameterize(parameterized, scc_num_params, id_gen, item))
                    .collect(),
            ),

            in_ast::Type::Custom(other) => {
                match &parameterized[other.0] {
                    Some(typedef) => mid_ast::Type::Custom(
                        *other,
                        (0..typedef.num_params).map(|_| id_gen.fresh()).collect(),
                    ),

                    None => {
                        // This is a typedef in the same SCC, so we need to parameterize it by
                        // all the SCC parameters.
                        mid_ast::Type::Custom(
                            *other,
                            (0..scc_num_params).map(mid_ast::RepParamId).collect(),
                        )
                    }
                }
            }
        }
    }

    fn parameterize_typedef_scc(
        typedefs: &[in_ast::TypeDef],
        parameterized: &mut [Option<mid_ast::TypeDef<mid_ast::RepParamId>>],
        scc: &[in_ast::CustomTypeId],
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

        let mut id_gen = ReprVarIdGen(0);

        let to_populate: BTreeMap<in_ast::CustomTypeId, _> = scc
            .iter()
            .map(|&type_id| {
                let typedef = &typedefs[type_id.0];
                let parameterized_variants = typedef
                    .variants
                    .iter()
                    .map(|variant| {
                        variant.as_ref().map(|content| {
                            parameterize(parameterized, num_params, &mut id_gen, content)
                        })
                    })
                    .collect();

                debug_assert!(parameterized[type_id.0].is_none());

                (
                    type_id,
                    mid_ast::TypeDef {
                        num_params,
                        variants: parameterized_variants,
                    },
                )
            })
            .collect();

        for (type_id, typedef) in to_populate {
            debug_assert!(parameterized[type_id.0].is_none());
            parameterized[type_id.0] = Some(typedef);
        }
    }

    fn add_dependencies(type_: &in_ast::Type, deps: &mut BTreeSet<in_ast::CustomTypeId>) {
        match type_ {
            in_ast::Type::Bool | in_ast::Type::Int | in_ast::Type::Float | in_ast::Type::Text => {}
            in_ast::Type::Array(item) | in_ast::Type::HoleArray(item) => {
                add_dependencies(item, deps);
            }
            in_ast::Type::Tuple(items) => {
                for item in items {
                    add_dependencies(item, deps);
                }
            }
            in_ast::Type::Custom(other) => {
                deps.insert(*other);
            }
        }
    }

    pub fn parameterize_typedefs(
        typedefs: &[in_ast::TypeDef],
    ) -> Vec<mid_ast::TypeDef<mid_ast::RepParamId>> {
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
                        .map(|&in_ast::CustomTypeId(id)| graph::NodeId(id))
                        .collect()
                })
                .collect(),
        };

        let sccs = graph::strongly_connected(&dep_graph);

        let mut parameterized = vec![None; typedefs.len()];

        for scc in sccs {
            let type_ids: Vec<_> = scc
                .iter()
                .map(|&graph::NodeId(id)| in_ast::CustomTypeId(id))
                .collect();

            parameterize_typedef_scc(typedefs, &mut parameterized, &type_ids);
        }

        parameterized
            .into_iter()
            .map(|typedef| typedef.unwrap())
            .collect()
    }
}

fn with_scope<T, R, F: for<'a> FnOnce(&'a mut Vec<T>) -> R>(vec: &mut Vec<T>, func: F) -> R {
    let old_len = vec.len();
    let result = func(vec);
    assert!(vec.len() >= old_len);
    vec.truncate(old_len);
    result
}

mod flatten {
    use super::{in_ast, mid_ast, with_scope};
    use crate::annot_aliases::{FieldId, FieldPath};
    use crate::util::constraint_graph::{ConstraintGraph, SolverVarId};
    use im_rc::vector;

    pub fn flatten_func(
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        typedefs: &[mid_ast::TypeDef<mid_ast::RepParamId>],
        func: &in_ast::FuncDef,
    ) -> mid_ast::FuncDef<()> {
        let mut locals = Vec::new();
        let mut body = mid_ast::Block::function_body();
        bind_pattern(
            graph,
            typedefs,
            &func.arg,
            mid_ast::LocalId(0),
            vector![],
            &mut locals,
        );
        flatten_expr_into(graph, typedefs, &func.body, &mut body, &mut locals);
        mid_ast::FuncDef {
            purity: func.purity,
            arg_type: instantiate_type(graph, typedefs, &func.arg_type),
            ret_type: instantiate_type(graph, typedefs, &func.ret_type),
            constraints: Vec::new(), // none for now
            body,
        }
    }

    // Basic conversion, initializing unique solver vars for each array, holearray, or parameterized custom type
    pub fn instantiate_type(
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        typedefs: &[mid_ast::TypeDef<mid_ast::RepParamId>],
        type_: &in_ast::Type,
    ) -> mid_ast::Type<SolverVarId> {
        match type_ {
            in_ast::Type::Bool => mid_ast::Type::Bool,
            in_ast::Type::Int => mid_ast::Type::Int,
            in_ast::Type::Float => mid_ast::Type::Float,
            in_ast::Type::Text => mid_ast::Type::Text,
            in_ast::Type::Array(item_type) => mid_ast::Type::Array(
                Box::new(instantiate_type(graph, typedefs, item_type)),
                graph.new_var(),
            ),
            in_ast::Type::HoleArray(item_type) => mid_ast::Type::HoleArray(
                Box::new(instantiate_type(graph, typedefs, item_type)),
                graph.new_var(),
            ),
            in_ast::Type::Tuple(items) => mid_ast::Type::Tuple(
                items
                    .iter()
                    .map(|t| instantiate_type(graph, typedefs, t))
                    .collect(),
            ),
            in_ast::Type::Custom(id) => mid_ast::Type::Custom(
                *id,
                (0..typedefs[id.0].num_params)
                    .map(|_| graph.new_var())
                    .collect(),
            ),
        }
    }

    fn flatten_expr_into(
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        typedefs: &[mid_ast::TypeDef<mid_ast::RepParamId>],
        expr: &in_ast::Expr,
        // Block to append terms *into* for intermediate expressions:
        block: &mut mid_ast::Block<()>,
        // Stack of terms indexed by ins_ast::LocalId, left in its original state after return:
        locals: &mut Vec<mid_ast::Term>,
    ) -> mid_ast::Term {
        match expr {
            in_ast::Expr::ArithOp(in_arith_op) => {
                let out_arith_op = match in_arith_op {
                    in_ast::ArithOp::IntOp(op, left, right) => {
                        let lterm = flatten_expr_into(graph, typedefs, left, block, locals);
                        let rterm = flatten_expr_into(graph, typedefs, right, block, locals);
                        mid_ast::ArithOp::IntOp(*op, lterm, rterm)
                    }
                    in_ast::ArithOp::FloatOp(op, left, right) => {
                        let lterm = flatten_expr_into(graph, typedefs, left, block, locals);
                        let rterm = flatten_expr_into(graph, typedefs, right, block, locals);
                        mid_ast::ArithOp::FloatOp(*op, lterm, rterm)
                    }
                    in_ast::ArithOp::IntCmp(op, left, right) => {
                        let lterm = flatten_expr_into(graph, typedefs, left, block, locals);
                        let rterm = flatten_expr_into(graph, typedefs, right, block, locals);
                        mid_ast::ArithOp::IntCmp(*op, lterm, rterm)
                    }
                    in_ast::ArithOp::FloatCmp(op, left, right) => {
                        let lterm = flatten_expr_into(graph, typedefs, left, block, locals);
                        let rterm = flatten_expr_into(graph, typedefs, right, block, locals);
                        mid_ast::ArithOp::FloatCmp(*op, lterm, rterm)
                    }
                    in_ast::ArithOp::NegateInt(arg) => mid_ast::ArithOp::NegateInt(
                        flatten_expr_into(graph, typedefs, arg, block, locals),
                    ),
                    in_ast::ArithOp::NegateFloat(arg) => mid_ast::ArithOp::NegateFloat(
                        flatten_expr_into(graph, typedefs, arg, block, locals),
                    ),
                };
                block.add(mid_ast::Expr::ArithOp(out_arith_op))
            }
            in_ast::Expr::ArrayOp(in_array_op) => {
                let out_array_op = match in_array_op {
                    in_ast::ArrayOp::Item(_item_type, array, index, ctr) => mid_ast::ArrayOp::Item(
                        flatten_expr_into(graph, typedefs, array, block, locals),
                        flatten_expr_into(graph, typedefs, index, block, locals),
                        *ctr,
                    ),
                    in_ast::ArrayOp::Len(_item_type, array) => mid_ast::ArrayOp::Len(
                        flatten_expr_into(graph, typedefs, array, block, locals),
                    ),
                    in_ast::ArrayOp::Push(_item_type, array, item) => mid_ast::ArrayOp::Push(
                        flatten_expr_into(graph, typedefs, array, block, locals),
                        flatten_expr_into(graph, typedefs, item, block, locals),
                    ),
                    in_ast::ArrayOp::Pop(_item_type, array) => mid_ast::ArrayOp::Pop(
                        flatten_expr_into(graph, typedefs, array, block, locals),
                    ),
                    in_ast::ArrayOp::Replace(_item_type, hole_array, item) => {
                        mid_ast::ArrayOp::Replace(
                            flatten_expr_into(graph, typedefs, hole_array, block, locals),
                            flatten_expr_into(graph, typedefs, item, block, locals),
                        )
                    }
                };
                block.add(mid_ast::Expr::ArrayOp(out_array_op))
            }
            in_ast::Expr::Ctor(id, variant, Some(arg)) => {
                let arg_term = flatten_expr_into(graph, typedefs, arg, block, locals);
                block.add(mid_ast::Expr::Ctor(*id, *variant, Some(arg_term)))
            }
            in_ast::Expr::Ctor(id, variant, None) => {
                block.add(mid_ast::Expr::Ctor(*id, *variant, None))
            }
            in_ast::Expr::Local(in_ast::LocalId(id)) => locals[*id].clone(),
            in_ast::Expr::Tuple(exprs) => {
                let item_terms = exprs
                    .iter()
                    .map(|e| flatten_expr_into(graph, typedefs, e, block, locals))
                    .collect();
                block.add(mid_ast::Expr::Tuple(item_terms))
            }
            in_ast::Expr::Call(purity, func, arg) => {
                let arg_term = flatten_expr_into(graph, typedefs, arg, block, locals);
                block.add(mid_ast::Expr::Call(*purity, *func, arg_term, None))
            }
            in_ast::Expr::Match(matched_expr, patterns, type_) => {
                // Add the matched term to the block immediately so we can refer to
                // it as a LocalId (in case it's a literal)
                let matched_term = flatten_expr_into(graph, typedefs, matched_expr, block, locals);
                let matched_term_local = block.add_local(mid_ast::Expr::Term(matched_term));

                let mut cases = vec![];
                for (pat, rhs_expr) in patterns {
                    let mut branch_block = mid_ast::Block::branch_from(block);
                    let initial_locals = locals.len();
                    let out_pattern =
                        bind_pattern(graph, typedefs, pat, matched_term_local, vector![], locals);
                    flatten_expr_into(graph, typedefs, rhs_expr, &mut branch_block, locals);
                    cases.push((out_pattern, branch_block));
                    locals.truncate(initial_locals);
                }

                block.add(mid_ast::Expr::Match(
                    matched_term_local,
                    cases,
                    Box::new(instantiate_type(graph, typedefs, type_)),
                ))
            }
            in_ast::Expr::Let(pattern, rhs, body) => {
                let rhs_term = flatten_expr_into(graph, typedefs, rhs, block, locals);
                let rhs_term_local = block.add_local(mid_ast::Expr::Term(rhs_term));

                with_scope(locals, |sub_locals| {
                    bind_pattern(
                        graph,
                        typedefs,
                        pattern,
                        rhs_term_local,
                        vector![],
                        sub_locals,
                    );
                    flatten_expr_into(graph, typedefs, body, block, sub_locals)
                })
            }
            in_ast::Expr::ArrayLit(item_type, exprs) => {
                let mut elements = Vec::new();
                for e in exprs {
                    elements.push(flatten_expr_into(graph, typedefs, e, block, locals));
                }
                block.add(mid_ast::Expr::ArrayOp(mid_ast::ArrayOp::Construct(
                    Box::new(instantiate_type(graph, typedefs, item_type)),
                    graph.new_var(),
                    elements,
                )))
            }
            in_ast::Expr::BoolLit(constant) => mid_ast::Term::BoolLit(*constant),
            in_ast::Expr::IntLit(constant) => mid_ast::Term::IntLit(*constant),
            in_ast::Expr::FloatLit(constant) => mid_ast::Term::FloatLit(*constant),
            in_ast::Expr::TextLit(_) => unreachable!(),
        }
    }

    fn bind_pattern(
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        typedefs: &[mid_ast::TypeDef<mid_ast::RepParamId>],
        pattern: &in_ast::Pattern,
        matched_local: mid_ast::LocalId,
        field_path: FieldPath,
        locals: &mut Vec<mid_ast::Term>,
    ) -> mid_ast::Pattern {
        match pattern {
            in_ast::Pattern::Any(_) => mid_ast::Pattern::Any,
            in_ast::Pattern::Var(_) => {
                locals.push(mid_ast::Term::Access(matched_local, field_path, None));
                mid_ast::Pattern::Any
            }
            in_ast::Pattern::Tuple(patterns) => {
                let mut field_patterns = Vec::new();
                for (i, pat) in patterns.iter().enumerate() {
                    let mut new_field_path = field_path.clone();
                    new_field_path.push_back(FieldId::Field(i));
                    field_patterns.push(bind_pattern(
                        graph,
                        typedefs,
                        pat,
                        matched_local,
                        new_field_path,
                        locals,
                    ));
                }
                mid_ast::Pattern::Tuple(field_patterns)
            }
            in_ast::Pattern::Ctor(id, variant_id, None) => {
                mid_ast::Pattern::Ctor(*id, *variant_id, None)
            }
            in_ast::Pattern::Ctor(id, variant_id, Some(pattern)) => {
                let new_field_path = field_path + vector![FieldId::Variant(*variant_id)];
                mid_ast::Pattern::Ctor(
                    *id,
                    *variant_id,
                    Some(Box::new(bind_pattern(
                        graph,
                        typedefs,
                        pattern,
                        matched_local,
                        new_field_path,
                        locals,
                    ))),
                )
            }
            in_ast::Pattern::BoolConst(c) => mid_ast::Pattern::BoolConst(*c),
            in_ast::Pattern::IntConst(c) => mid_ast::Pattern::IntConst(*c),
            in_ast::Pattern::FloatConst(c) => mid_ast::Pattern::FloatConst(*c),
            in_ast::Pattern::TextConst(_) => unreachable!(),
        }
    }
}

// Constructs the typed AST and runs Hindley-Milner on representation variables
mod unify {
    use super::{in_ast, mid_ast, with_scope};
    use crate::annot_aliases::{FieldId, FieldPath, UniqueInfo};
    use crate::util::constraint_graph::{ConstraintGraph, SolverVarId};
    use im_rc::{vector, Vector};
    pub use mid_ast::ExprId;
    use std::collections::BTreeMap;

    #[derive(Clone, Copy, Debug)]
    pub struct Context<'a> {
        pub first_order_typedefs: &'a [in_ast::TypeDef],
        pub typedefs: &'a [mid_ast::TypeDef<mid_ast::RepParamId>],
        pub func_sigs: &'a [Option<Signature>],
        pub scc_funcdefs: &'a BTreeMap<mid_ast::CustomFuncId, mid_ast::FuncDef<()>>,
        pub unique_infos: &'a [UniqueInfo],
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Signature {
        pub num_params: usize,
        pub arg_type: mid_ast::Type<mid_ast::RepParamId>,
        pub ret_type: mid_ast::Type<mid_ast::RepParamId>,
    }

    struct ExprIdGen {
        next: usize,                    // ExprId of the next local
        local_expr_ids: Vector<ExprId>, // indexed by `mid_ast::LocalId`
    }
    impl ExprIdGen {
        fn with_scope<R, F: FnOnce(&mut ExprIdGen) -> R>(&mut self, f: F) -> R {
            let initial_len = self.local_expr_ids.len();
            let result = f(self);
            self.local_expr_ids.truncate(initial_len);
            result
        }

        fn locals_len(&self) -> usize {
            self.local_expr_ids.len()
        }

        fn get_local_mapping(&self) -> Vector<ExprId> {
            self.local_expr_ids.clone()
        }

        fn bind_fresh(&mut self) -> ExprId {
            let ret = ExprId(self.next);
            self.next += 1;
            ret
        }
    }

    pub fn unify_func(
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        context: Context,
        func: &mid_ast::FuncDef<()>,
    ) -> mid_ast::TypedBlock {
        unify_block(
            graph,
            context,
            &mut vec![func.arg_type.clone()],
            &mut ExprIdGen {
                next: 1,
                local_expr_ids: vector![ExprId::ARG],
            },
            func.body.clone(),
        )
    }

    fn unify_block(
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        context: Context,
        locals: &mut Vec<mid_ast::Type<SolverVarId>>, // indexed by `mid_ast::LocalId`
        expr_id_gen: &mut ExprIdGen,
        block: mid_ast::Block<()>,
    ) -> mid_ast::TypedBlock {
        assert_eq!(locals.len(), expr_id_gen.locals_len());
        assert_eq!(block.initial_idx, locals.len());
        assert_eq!(block.terms.len(), block.types.len());
        assert!(block.terms.len() > 0); // empty blocks are invalid
        with_scope(locals, |sub_locals| {
            expr_id_gen.with_scope(|sub_expr_id_gen| {
                let mut exprs = Vec::new();
                for expr in block.terms {
                    let (expr, type_) =
                        unify_expr(graph, context, sub_locals, sub_expr_id_gen, expr);
                    exprs.push(expr);
                    sub_locals.push(type_);
                    // Generating the new expr_id *after* calling unify_expr means that the ExprId of
                    // a match expression is *greater* than that of all expressions in its branches.
                    sub_expr_id_gen.bind_fresh();
                }
                mid_ast::Block {
                    initial_idx: block.initial_idx,
                    terms: exprs,
                    types: sub_locals.split_off(block.initial_idx),
                    expr_ids: sub_expr_id_gen.get_local_mapping(),
                }
            })
        })
    }

    fn type_fold<T, E>(
        typedefs: &[mid_ast::TypeDef<T>], // indexed by LocalId
        type_: &mid_ast::Type<E>,
        path: &FieldPath,
    ) -> FieldPath {
        use crate::annot_aliases;
        use std::borrow::Cow;
        annot_aliases::prune_field_path_with(
            |type_id, variant_id| {
                typedefs[type_id.0].variants[variant_id.0]
                    .as_ref()
                    .map(|t| Cow::Owned(t.into()))
            },
            &type_.into(),
            path,
        )
    }

    fn unify_expr(
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        ctx: Context,
        locals: &mut Vec<mid_ast::Type<SolverVarId>>, // indexed by `mid_ast::LocalId`
        expr_id_gen: &mut ExprIdGen,
        expr: mid_ast::Expr<()>,
    ) -> (mid_ast::TypedExpr, mid_ast::Type<SolverVarId>) {
        match expr {
            mid_ast::Expr::Term(term) => {
                let t = type_of_term(ctx.typedefs, locals, &term);
                // Add the type-folded field path
                let filled_term = match term {
                    mid_ast::Term::Access(local, path, None) => {
                        let type_folded_path = type_fold(ctx.typedefs, &t, &path);
                        mid_ast::Term::Access(local, path, Some(type_folded_path))
                    }
                    mid_ast::Term::Access(_, _, Some(_)) => {
                        // The typefolded path should not have yet been initialized
                        unreachable!()
                    }
                    mid_ast::Term::BoolLit(_)
                    | mid_ast::Term::IntLit(_)
                    | mid_ast::Term::FloatLit(_) => term,
                };
                (mid_ast::Expr::Term(filled_term), t)
            }
            mid_ast::Expr::Tuple(items) => {
                let t = mid_ast::Type::Tuple(
                    items
                        .iter()
                        .map(|item| type_of_term(ctx.typedefs, locals, item))
                        .collect(),
                );
                (mid_ast::Expr::Tuple(items), t)
            }
            mid_ast::Expr::ArithOp(arith_op) => {
                let type_ = match arith_op {
                    mid_ast::ArithOp::IntOp(..) => mid_ast::Type::Int,
                    mid_ast::ArithOp::NegateInt(..) => mid_ast::Type::Int,
                    mid_ast::ArithOp::FloatOp(..) => mid_ast::Type::Float,
                    mid_ast::ArithOp::NegateFloat(..) => mid_ast::Type::Float,
                    mid_ast::ArithOp::IntCmp(..) => mid_ast::Type::Bool,
                    mid_ast::ArithOp::FloatCmp(..) => mid_ast::Type::Bool,
                };
                (mid_ast::Expr::ArithOp(arith_op), type_)
            }
            mid_ast::Expr::ArrayOp(array_op) => {
                let type_ = match &array_op {
                    mid_ast::ArrayOp::Construct(item_type, repr_var, items) => {
                        for term in items {
                            equate_types(
                                graph,
                                &type_of_term(ctx.typedefs, locals, term),
                                item_type,
                            );
                        }
                        mid_ast::Type::Array(item_type.clone(), *repr_var)
                    }
                    mid_ast::ArrayOp::Item(array, _idx, wrapper) => {
                        let array_type = type_of_term(ctx.typedefs, locals, array);
                        if let Some((_type_id, _variant_id)) = wrapper {
                            // TODO: remove this case after merging code
                            unimplemented!()
                        } else if let mid_ast::Type::Array(ref item_type, _) = array_type {
                            mid_ast::Type::Tuple(vec![*item_type.clone(), array_type])
                        } else {
                            // Any other term is a type error
                            unreachable!();
                        }
                    }
                    mid_ast::ArrayOp::Len(_) => mid_ast::Type::Int,
                    mid_ast::ArrayOp::Push(array_term, pushed_item_term) => {
                        let array_type = type_of_term(ctx.typedefs, locals, array_term);
                        if let mid_ast::Type::Array(ref item_type, _) = array_type {
                            let pushed_item_type =
                                type_of_term(ctx.typedefs, locals, pushed_item_term);
                            equate_types(graph, item_type, &pushed_item_type);
                        } else {
                            // Type error
                            unreachable!();
                        }
                        array_type
                    }
                    mid_ast::ArrayOp::Pop(array_term) => {
                        let array_type = type_of_term(ctx.typedefs, locals, array_term);
                        if let mid_ast::Type::Array(ref item_type, _) = array_type {
                            let item_type = *item_type.clone();
                            mid_ast::Type::Tuple(vec![array_type, item_type])
                        } else {
                            // Type error
                            unreachable!();
                        }
                    }
                    mid_ast::ArrayOp::Replace(hole_array_term, item_term) => {
                        let array_type = type_of_term(ctx.typedefs, locals, hole_array_term);
                        if let mid_ast::Type::HoleArray(ref item_type, _) = array_type {
                            let param_type = type_of_term(ctx.typedefs, locals, item_term);
                            equate_types(graph, &item_type, &param_type);
                        } else {
                            // Type error
                            unreachable!();
                        }
                        array_type
                    }
                };
                (mid_ast::Expr::ArrayOp(array_op), type_)
            }
            mid_ast::Expr::Ctor(type_id, variant, None) => {
                let vars = (0..ctx.typedefs[type_id.0].num_params)
                    .map(|_| graph.new_var())
                    .collect();
                (
                    mid_ast::Expr::Ctor(type_id, variant, None),
                    mid_ast::Type::Custom(type_id, vars),
                )
            }
            mid_ast::Expr::Ctor(type_id, variant_id, Some(param)) => {
                let (vars, typedef) = instantiate(graph, &ctx.typedefs[type_id.0]);
                if let Some(ref variant_type) = typedef.variants[variant_id.0] {
                    let param_type = type_of_term(ctx.typedefs, locals, &param);
                    equate_types(graph, variant_type, &param_type);
                    (
                        mid_ast::Expr::Ctor(type_id, variant_id, Some(param)),
                        mid_ast::Type::Custom(type_id, vars),
                    )
                } else {
                    // Constructor doesn't take a param, but one was provided
                    unreachable!()
                }
            }
            mid_ast::Expr::Local(local_id) => {
                (mid_ast::Expr::Local(local_id), locals[local_id.0].clone())
            }
            mid_ast::Expr::Call(purity, func_id, arg_term, None) => {
                let arg_type = type_of_term(ctx.typedefs, locals, &arg_term);
                let (vars, result_type) = if let Some(funcdef) = ctx.scc_funcdefs.get(&func_id) {
                    // If its in the same SCC, just unify the types
                    equate_types(graph, &arg_type, &funcdef.arg_type);
                    (mid_ast::ReprParams::Pending, funcdef.ret_type.clone())
                } else if let Some(signature) = &ctx.func_sigs[func_id.0] {
                    // Othwerise, it's already been processed, so instantiate params
                    unify_external_function_call(
                        graph,
                        ctx.typedefs,
                        signature,
                        ctx.unique_infos[func_id.0].clone(),
                        &arg_type,
                    )
                } else {
                    unreachable!()
                };
                (
                    mid_ast::Expr::Call(purity, func_id, arg_term, Some(vars)),
                    result_type,
                )
            }
            mid_ast::Expr::Call(_, _, _, Some(_)) => unreachable!(),
            mid_ast::Expr::Match(matched_local, branches, result_type) => {
                let mut typed_branches = Vec::new();
                for (pat, branch) in branches {
                    let block = unify_block(graph, ctx, locals, expr_id_gen, branch);
                    equate_types(graph, &result_type, &block.types[block.types.len() - 1]);
                    typed_branches.push((pat, block));
                }
                (
                    mid_ast::Expr::Match(matched_local, typed_branches, result_type.clone()),
                    *result_type,
                )
            }
        }
    }

    fn unify_external_function_call(
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        typedefs: &[mid_ast::TypeDef<mid_ast::RepParamId>],
        func_sig: &Signature,
        ui: UniqueInfo,
        arg_type: &mid_ast::Type<SolverVarId>,
    ) -> (mid_ast::ReprParams<SolverVarId>, mid_ast::Type<SolverVarId>) {
        // Unify actual argument's type with parameter type
        let vars = (0..func_sig.num_params)
            .map(|_| graph.new_var())
            .collect::<Vec<_>>();
        let param_type = substitute_vars(typedefs, &func_sig.arg_type, &vars);
        equate_types(graph, &param_type, arg_type);
        let ret_type = substitute_vars(typedefs, &func_sig.ret_type, &vars);
        // Unify those pairs of names in the argument and return types that may alias
        for p in ui.edges {
            equate_types(
                graph,
                &lookup_type_field(typedefs, arg_type, p.arg_field),
                &lookup_type_field(typedefs, &ret_type, p.ret_field),
            );
        }
        (mid_ast::ReprParams::Determined(vars), ret_type)
    }

    pub fn substitute_vars(
        typedefs: &[mid_ast::TypeDef<mid_ast::RepParamId>],
        t: &mid_ast::Type<mid_ast::RepParamId>,
        vars: &[SolverVarId],
    ) -> mid_ast::Type<SolverVarId> {
        use mid_ast::Type as T;
        match t {
            T::Bool => T::Bool,
            T::Int => T::Int,
            T::Float => T::Float,
            T::Text => unimplemented!(),
            T::Array(item, var) => T::Array(
                Box::new(substitute_vars(typedefs, &*item, vars)),
                vars[var.0],
            ),
            T::HoleArray(item, var) => T::HoleArray(
                Box::new(substitute_vars(typedefs, &*item, vars)),
                vars[var.0],
            ),
            T::Tuple(items) => T::Tuple(
                items
                    .iter()
                    .map(|t| substitute_vars(typedefs, t, vars))
                    .collect(),
            ),
            T::Custom(id, repr_args) => T::Custom(
                *id,
                repr_args
                    .iter()
                    .map(|&mid_ast::RepParamId(rpid)| vars[rpid])
                    .collect(),
            ),
        }
    }

    fn type_of_term(
        typedefs: &[mid_ast::TypeDef<mid_ast::RepParamId>],
        locals: &mut Vec<mid_ast::Type<SolverVarId>>,
        term: &mid_ast::Term,
    ) -> mid_ast::Type<SolverVarId> {
        match term {
            mid_ast::Term::Access(mid_ast::LocalId(id), field_path, _) => {
                lookup_type_field(typedefs, &locals[*id], field_path.clone())
            }
            mid_ast::Term::BoolLit(_) => mid_ast::Type::Bool,
            mid_ast::Term::IntLit(_) => mid_ast::Type::Int,
            mid_ast::Term::FloatLit(_) => mid_ast::Type::Float,
        }
    }

    // It is not allowed to lookup the type of a field which is an unparameterized variant;
    // e.g. looking up the type of b.(True), getting the True variant of a boolean. Such
    // a lookup never occurs.
    fn lookup_type_field(
        typedefs: &[mid_ast::TypeDef<mid_ast::RepParamId>],
        type_: &mid_ast::Type<SolverVarId>,
        field_path: FieldPath,
    ) -> mid_ast::Type<SolverVarId> {
        if field_path.len() == 0 {
            type_.clone()
        } else {
            let (subscript, remaining_path) = (field_path[0], field_path.skip(1));
            match (type_, subscript) {
                (mid_ast::Type::Array(item_t, _repr_var), FieldId::ArrayMembers) => {
                    lookup_type_field(typedefs, item_t, remaining_path)
                }
                (mid_ast::Type::HoleArray(item_t, _repr_var), FieldId::ArrayMembers) => {
                    lookup_type_field(typedefs, item_t, remaining_path)
                }
                (mid_ast::Type::Tuple(item_types), FieldId::Field(i)) => {
                    lookup_type_field(typedefs, &item_types[i], remaining_path)
                }
                (
                    mid_ast::Type::Custom(mid_ast::CustomTypeId(type_id), repr_var_params),
                    FieldId::Variant(mid_ast::VariantId(variant_id)),
                ) => {
                    let instantiated =
                        instantiate_with(&typedefs[*type_id], repr_var_params.clone());
                    if let Some(variant_type) = &instantiated.variants[variant_id] {
                        lookup_type_field(typedefs, variant_type, remaining_path)
                    } else {
                        // The described variant is an unparameterized variant, like True or False.
                        unreachable!()
                    }
                }
                _ => unreachable!(),
            }
        }
    }

    fn instantiate(
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        typedef: &mid_ast::TypeDef<mid_ast::RepParamId>,
    ) -> (Vec<SolverVarId>, mid_ast::TypeDef<SolverVarId>) {
        let vars = (0..typedef.num_params)
            .map(|_| graph.new_var())
            .collect::<Vec<_>>();
        let variants = typedef
            .variants
            .iter()
            .map(|variant| variant.as_ref().map(|t| substitute_params(&vars, &t)))
            .collect();
        (
            vars,
            mid_ast::TypeDef {
                num_params: typedef.num_params,
                variants,
            },
        )
    }

    fn instantiate_with(
        typedef: &mid_ast::TypeDef<mid_ast::RepParamId>,
        vars: Vec<SolverVarId>,
    ) -> mid_ast::TypeDef<SolverVarId> {
        mid_ast::TypeDef {
            num_params: typedef.num_params,
            variants: typedef
                .variants
                .iter()
                .map(|variant| variant.as_ref().map(|t| substitute_params(&vars, &t)))
                .collect(),
        }
    }

    fn substitute_params(
        vars: &[SolverVarId], // indexed by mid_ast::RepParamId
        type_: &mid_ast::Type<mid_ast::RepParamId>,
    ) -> mid_ast::Type<SolverVarId> {
        match type_ {
            mid_ast::Type::Bool => mid_ast::Type::Bool,
            mid_ast::Type::Int => mid_ast::Type::Int,
            mid_ast::Type::Float => mid_ast::Type::Float,
            mid_ast::Type::Text => mid_ast::Type::Text,

            mid_ast::Type::Array(item, mid_ast::RepParamId(id)) => {
                mid_ast::Type::Array(Box::new(substitute_params(vars, item)), vars[*id])
            }
            mid_ast::Type::HoleArray(item, mid_ast::RepParamId(id)) => {
                mid_ast::Type::HoleArray(Box::new(substitute_params(vars, item)), vars[*id])
            }

            mid_ast::Type::Tuple(items) => mid_ast::Type::Tuple(
                items
                    .iter()
                    .map(|item| substitute_params(vars, item))
                    .collect(),
            ),

            mid_ast::Type::Custom(custom, args) => mid_ast::Type::Custom(
                *custom,
                args.iter()
                    .map(|&mid_ast::RepParamId(id)| vars[id])
                    .collect(),
            ),
        }
    }

    fn equate_types(
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        type_a: &mid_ast::Type<SolverVarId>,
        type_b: &mid_ast::Type<SolverVarId>,
    ) {
        use mid_ast::Type as T;
        match (type_a, type_b) {
            (T::Bool, T::Bool) => {}
            (T::Int, T::Int) => {}
            (T::Float, T::Float) => {}
            (T::Text, T::Text) => {}
            (T::Array(item_a, repr_var_a), T::Array(item_b, repr_var_b)) => {
                graph.equate(*repr_var_a, *repr_var_b);
                equate_types(graph, item_a, item_b);
            }
            (T::HoleArray(item_a, repr_var_a), T::HoleArray(item_b, repr_var_b)) => {
                graph.equate(*repr_var_a, *repr_var_b);
                equate_types(graph, item_a, item_b);
            }
            (T::Tuple(items_a), T::Tuple(items_b)) => {
                debug_assert_eq!(items_a.len(), items_b.len());
                for (a, b) in items_a.iter().zip(items_b) {
                    equate_types(graph, a, b);
                }
            }
            (T::Custom(id_a, params_a), T::Custom(id_b, params_b)) => {
                debug_assert_eq!(id_a, id_b);
                debug_assert_eq!(params_a.len(), params_b.len());
                for (a, b) in params_a.iter().zip(params_b) {
                    graph.equate(*a, *b);
                }
            }
            (_, _) => debug_assert!(false, "mismatched types"),
        }
    }
}

mod aliasing {
    use super::constrain;
    use super::mid_ast;
    use super::unify::{self, ExprId};
    use crate::annot_aliases::{FieldId, FieldPath, UniqueInfo};
    use crate::util::constraint_graph::SolverVarId;
    use im_rc::{vector, Vector};
    use std::collections::{BTreeMap, BTreeSet};

    pub type Name = (ExprId, FieldPath);

    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub struct LastAccessTree {
        expr_id: ExprId,
        rest: BTreeMap<
            usize, // index into branch list of Match
            LastAccessTree,
        >,
    }
    impl LastAccessTree {
        fn singleton(ctx: &[(ExprId, usize)], final_expr_id: ExprId) -> Self {
            if ctx.len() == 0 {
                LastAccessTree {
                    expr_id: final_expr_id,
                    rest: BTreeMap::new(),
                }
            } else if ctx.len() == 1 {
                let mut rest = BTreeMap::new();
                rest.insert(
                    ctx[0].1,
                    LastAccessTree {
                        expr_id: final_expr_id,
                        rest: BTreeMap::new(),
                    },
                );
                LastAccessTree {
                    expr_id: ctx[0].0,
                    rest,
                }
            } else {
                let mut rest = BTreeMap::new();
                rest.insert(
                    ctx[0].1,
                    LastAccessTree::singleton(&ctx[1..], final_expr_id),
                );
                LastAccessTree {
                    expr_id: ctx[0].0,
                    rest,
                }
            }
        }

        fn consider_access(&mut self, ctx: &[(ExprId, usize)], final_expr_id: ExprId) {
            let mut tree_node = self;
            for (i, &(expr_id, branch)) in ctx.iter().enumerate() {
                if tree_node.expr_id == expr_id {
                    if let Some(tree_from_branch) = tree_node.rest.get_mut(&branch) {
                        tree_node = tree_from_branch;
                    } else {
                        // The arguments provided to consider_access do not agree with self
                        // on whether expr_id is a Match statement.
                        unreachable!();
                    }
                } else if tree_node.expr_id < expr_id {
                    *tree_node = LastAccessTree::singleton(&ctx[i..], final_expr_id);
                    return;
                }
            }
            if tree_node.expr_id < final_expr_id {
                *tree_node = LastAccessTree {
                    expr_id: final_expr_id,
                    rest: BTreeMap::new(),
                };
            }
        }

        pub fn is_last_use(&self, mut ctx: &[(ExprId, usize)], final_expr_id: ExprId) -> bool {
            let mut tree_node = self;
            while let Some((expr_id, branch)) = ctx.first() {
                if *expr_id < tree_node.expr_id {
                    return false;
                }
                if *expr_id > tree_node.expr_id {
                    panic!("expression used after its recorded last point of use")
                }
                if let Some(rest) = tree_node.rest.get(branch) {
                    tree_node = rest;
                    ctx = &ctx[1..];
                } else {
                    // The given path disagrees with `self` about whether the
                    // current location is a match statement
                    unreachable!();
                }
            }
            assert!(tree_node.expr_id >= final_expr_id); // because there should be no use after the recorded last-use
            tree_node.expr_id == final_expr_id
        }

        // TODO: remove code repetition w/ above function
        pub fn is_after(&self, mut ctx: &[(ExprId, usize)], final_expr_id: ExprId) -> bool {
            let mut tree_node = self;
            while let Some((expr_id, branch)) = ctx.first() {
                if *expr_id < tree_node.expr_id {
                    return false;
                }
                if *expr_id > tree_node.expr_id {
                    return true;
                }
                if let Some(rest) = tree_node.rest.get(branch) {
                    tree_node = rest;
                    ctx = &ctx[1..];
                } else {
                    // The given path disagrees with `self` about whether the
                    // current location is a match statement
                    unreachable!();
                }
            }
            tree_node.expr_id > final_expr_id
        }
    }

    struct LastAccessesCursor {
        accesses: Vec<BTreeMap<FieldPath, LastAccessTree>>,
        // The following pairs are (ExprID of match statement, branch index)
        by_expr_id: Vec<Vec<(ExprId, usize)>>, // indexed by ExprId, describes which block that expr id is in
        ctx: Vec<(ExprId, usize)>,
    }
    impl LastAccessesCursor {
        fn with_arg_type(arg_type: &mid_ast::Type<SolverVarId>) -> Self {
            LastAccessesCursor {
                accesses: vec![],
                by_expr_id: vec![vec![]],
                ctx: Vec::new(),
            }
        }

        fn in_branch_scope<F, R>(&mut self, match_expr_id: ExprId, branch_idx: usize, f: F) -> R
        where
            F: FnOnce(&mut LastAccessesCursor) -> R,
        {
            let original_len = self.ctx.len();
            self.ctx.push((match_expr_id, branch_idx));
            let result = f(self);
            self.ctx.truncate(original_len);
            result
        }

        fn consider_access(&mut self, (accessed_expr, accessed_path): &Name, at: ExprId) {
            if let Some(accesses) = self.accesses[accessed_expr.0].get_mut(accessed_path) {
                accesses.consider_access(&self.ctx, at);
            }
        }

        fn append_expr(&mut self, info: BTreeMap<FieldPath, LastAccessTree>) {
            self.accesses.push(info);
            self.by_expr_id.push(self.ctx.clone());
        }

        fn len(&self) -> usize {
            self.accesses.len()
        }

        fn last_expr_id(&self) -> ExprId {
            ExprId(self.len() - 1)
        }
    }

    pub fn alias_track_func(
        typedefs: &[mid_ast::TypeDef<mid_ast::RepParamId>], // indexed by CustomTypeId
        unique_infos: &[UniqueInfo],                        // indexed by CustomFuncId
        block: mid_ast::TypedBlock,
        id: mid_ast::CustomFuncId,
    ) -> constrain::FuncInfo {
        let mut name_adjacencies = Vec::new();
        let mut name_vars = Vec::new();
        let mut accesses_cursor = LastAccessesCursor {
            accesses: Vec::new(),
            by_expr_id: Vec::new(),
            ctx: Vec::new(),
        };
        // The function argument is expression zero
        initialize_expr(
            typedefs,
            &mut accesses_cursor,
            &mut name_adjacencies,
            &mut name_vars,
            ExprId::ARG,
            &block.types[0],
        );
        alias_track_block(
            typedefs,
            unique_infos,
            &mut accesses_cursor,
            &mut name_adjacencies,
            &mut name_vars,
            &block,
        );
        // FIXME: consider aliasing to return type in same way as to arg type
        // FIXME: "unify" last accesses -- set each last access to max across all names it aliases
        constrain::FuncInfo {
            id: id,
            body: block,
            last_accesses: accesses_cursor.accesses,
            aliases: name_adjacencies,
            name_vars: name_vars,
            paths_to_exprs: accesses_cursor.by_expr_id,
        }
    }
    // Track aliases in block. Appends all exprs to name_adjacencies without truncating
    fn alias_track_block(
        typedefs: &[mid_ast::TypeDef<mid_ast::RepParamId>], // indexed by CustomTypeId
        unique_infos: &[UniqueInfo],                        // indexed by CustomFuncId
        name_last_accesses: &mut LastAccessesCursor,
        name_adjacencies: &mut Vec<BTreeMap<FieldPath, BTreeSet<Name>>>, // indexed by ExprId
        name_vars: &mut Vec<BTreeMap<FieldPath, SolverVarId>>,           // indexed by ExprId
        block: &mid_ast::TypedBlock,
    ) {
        assert_eq!(name_last_accesses.len(), name_adjacencies.len());
        assert_eq!(name_last_accesses.len(), name_vars.len());
        for (i, (expr, type_)) in block.terms.iter().zip(&block.types).enumerate() {
            let cur_local_id = mid_ast::LocalId(block.initial_idx + i);
            let cur_expr_id = ExprId(name_adjacencies.len());
            assert_eq!(block.expr_id_of(cur_local_id), cur_expr_id);
            alias_track_expr(
                typedefs,
                unique_infos,
                name_last_accesses,
                name_adjacencies,
                name_vars,
                &block.expr_ids,
                expr,
                cur_expr_id,
                &type_,
            );
        }
    }

    // Initializes last-accesses (for each name, one access at the point of creation),
    // aliasing-edges (for each name, no aliases), and repr vars for names of a new
    // expression of type `type_`.
    fn initialize_expr(
        typedefs: &[mid_ast::TypeDef<mid_ast::RepParamId>], // indexed by CustomTypeId
        accesses: &mut LastAccessesCursor,
        name_adjacencies: &mut Vec<BTreeMap<FieldPath, BTreeSet<Name>>>, // indexed by ExprId
        name_vars: &mut Vec<BTreeMap<FieldPath, SolverVarId>>,           // indexed by ExprId
        cur_expr_id: ExprId,
        type_: &mid_ast::Type<SolverVarId>,
    ) {
        // Initialize the node for cur_expr_id in accesses and name_adjacencies
        let mut expr_name_vars = BTreeMap::new();
        let (name_paths, internal_edges) = get_names_in(typedefs, &mut expr_name_vars, type_);
        let mut expr_edges = BTreeMap::new();
        let mut expr_accesses = BTreeMap::new();
        for name in name_paths {
            expr_edges.insert(name.clone(), BTreeSet::new());
            expr_accesses.insert(
                name.clone(),
                LastAccessTree::singleton(&accesses.ctx, cur_expr_id),
            );
        }
        // Add internal edges to account for one level of type-folding-unrolling:
        for (a, b) in internal_edges {
            expr_edges
                .get_mut(&a)
                .unwrap()
                .insert((cur_expr_id, b.clone()));
            expr_edges
                .get_mut(&b)
                .unwrap()
                .insert((cur_expr_id, a.clone()));
        }
        name_adjacencies.push(expr_edges);
        accesses.append_expr(expr_accesses);
        name_vars.push(expr_name_vars);
    }

    // Appends data for `expr` to `accesses` and `name_adjacencies`, and updates
    // each with accessing and aliasing information arising from `expr`.
    fn alias_track_expr(
        typedefs: &[mid_ast::TypeDef<mid_ast::RepParamId>], // indexed by CustomTypeId
        unique_infos: &[UniqueInfo],                        // indexed by CustomFuncId
        accesses: &mut LastAccessesCursor,
        name_adjacencies: &mut Vec<BTreeMap<FieldPath, BTreeSet<Name>>>, // indexed by ExprId
        name_vars: &mut Vec<BTreeMap<FieldPath, SolverVarId>>,           // indexed by ExprId
        locals: &Vector<ExprId>,                                         // indexed by LocalId
        expr: &mid_ast::TypedExpr,
        cur_expr_id: ExprId,                // id of `expr`
        type_: &mid_ast::Type<SolverVarId>, // type of `expr`
    ) {
        initialize_expr(
            typedefs,
            accesses,
            name_adjacencies,
            name_vars,
            cur_expr_id,
            type_,
        );

        match expr {
            mid_ast::Expr::Term(term) => {
                add_term_aliases(name_adjacencies, locals, &vector![], term, cur_expr_id);
                update_term_accesses(accesses, locals, term);
            }
            mid_ast::Expr::ArithOp(arith_op) => match arith_op {
                mid_ast::ArithOp::IntOp(_, term1, term2)
                | mid_ast::ArithOp::FloatOp(_, term1, term2)
                | mid_ast::ArithOp::IntCmp(_, term1, term2)
                | mid_ast::ArithOp::FloatCmp(_, term1, term2) => {
                    update_term_accesses(accesses, locals, term1);
                    update_term_accesses(accesses, locals, term2);
                }
                mid_ast::ArithOp::NegateInt(term) | mid_ast::ArithOp::NegateFloat(term) => {
                    update_term_accesses(accesses, locals, term);
                }
            },
            mid_ast::Expr::ArrayOp(array_op) => match array_op {
                mid_ast::ArrayOp::Construct(_type, _var, item_terms) => {
                    let path_prefix = vector![FieldId::ArrayMembers];
                    for term in item_terms {
                        add_term_aliases(name_adjacencies, locals, &path_prefix, term, cur_expr_id);
                        update_term_accesses(accesses, locals, term);
                    }
                }
                mid_ast::ArrayOp::Item(array_term, idx_term, None) => {
                    update_term_accesses(accesses, locals, array_term);
                    update_term_accesses(accesses, locals, idx_term);
                    // The item (in first tuple position) aliases array_term's contents
                    if let mid_ast::Term::Access(local_id, _actual, Some(array_field)) = array_term
                    {
                        let mut array_elements = array_field.clone();
                        array_elements.push_back(FieldId::ArrayMembers);
                        alias_fields(
                            name_adjacencies,
                            (locals[local_id.0], &array_elements),
                            (cur_expr_id, &vector![FieldId::Field(0)]),
                        );
                    } else {
                        // Any other Term is a compiler error
                        unreachable!()
                    }
                    // The HoleArray (in second tuple position) aliases array_term
                    add_term_aliases(
                        name_adjacencies,
                        locals,
                        &vector![FieldId::Field(1)],
                        array_term,
                        cur_expr_id,
                    );
                    // FIXME: the HoleArray's elements do not alias item, unless there is a self-loop
                }
                mid_ast::ArrayOp::Item(_, _, Some(_)) => {
                    // TOOD: merge to remove this case
                    unimplemented!()
                }
                mid_ast::ArrayOp::Len(array_term) => {
                    update_term_accesses(accesses, locals, array_term);
                }
                mid_ast::ArrayOp::Push(array_term, item_term) => {
                    update_term_accesses(accesses, locals, array_term);
                    update_term_accesses(accesses, locals, item_term);
                    // The result's members alias the original array's members
                    if let mid_ast::Term::Access(local_id, _, Some(array_path)) = array_term {
                        let mut array_members_path = array_path.clone();
                        array_members_path.push_back(FieldId::ArrayMembers);
                        alias_fields(
                            name_adjacencies,
                            (locals[local_id.0], &array_members_path),
                            (cur_expr_id, &vector![FieldId::ArrayMembers]),
                        );
                    } else {
                        unreachable!();
                    }
                    // The result's members alias item_term
                    add_term_aliases(
                        name_adjacencies,
                        locals,
                        &vector![FieldId::ArrayMembers],
                        item_term,
                        cur_expr_id,
                    );
                    // FIXME: the original array's elements do not alias item, unless they already did (ie. self-loop)
                }
                mid_ast::ArrayOp::Pop(array_term) => {
                    update_term_accesses(accesses, locals, array_term);
                    // The result's members alias the members of array_term
                    if let mid_ast::Term::Access(local_id, _, Some(array_field_path)) = array_term {
                        let mut members = array_field_path.clone();
                        members.push_back(FieldId::ArrayMembers);
                        alias_fields(
                            name_adjacencies,
                            (locals[local_id.0], &members),
                            (cur_expr_id, &vector![FieldId::ArrayMembers]),
                        );
                    } else {
                        unreachable!();
                    }
                }
                mid_ast::ArrayOp::Replace(hole_array_term, item_term) => {
                    update_term_accesses(accesses, locals, hole_array_term);
                    update_term_accesses(accesses, locals, item_term);
                    // The result's members alias the members of hole_array_term
                    if let mid_ast::Term::Access(local_id, _, Some(array_field_path)) =
                        hole_array_term
                    {
                        let mut members = array_field_path.clone();
                        members.push_back(FieldId::ArrayMembers);
                        alias_fields(
                            name_adjacencies,
                            (locals[local_id.0], &members),
                            (cur_expr_id, &vector![FieldId::ArrayMembers]),
                        );
                    } else {
                        // Type error
                        unreachable!();
                    }

                    // The result's members alias item_term
                    add_term_aliases(
                        name_adjacencies,
                        locals,
                        &vector![FieldId::ArrayMembers],
                        item_term,
                        cur_expr_id,
                    );
                    // FIXME: the HoleArray's elements do not alias item, unless they already did (ie. self-loop)
                }
            },
            mid_ast::Expr::Ctor(_type_id, _variant_id, None) => {
                // Nothing aliased or accessed
            }
            mid_ast::Expr::Ctor(_type_id, variant_id, Some(arg_term)) => {
                update_term_accesses(accesses, locals, arg_term);
                add_term_aliases(
                    name_adjacencies,
                    locals,
                    &vector![FieldId::Variant(*variant_id)],
                    &arg_term,
                    cur_expr_id,
                );
            }
            mid_ast::Expr::Tuple(item_terms) => {
                for (idx, item) in item_terms.iter().enumerate() {
                    update_term_accesses(accesses, locals, &item);
                    let prefix = vector![FieldId::Field(idx)];
                    add_term_aliases(name_adjacencies, locals, &prefix, &item, cur_expr_id);
                }
            }
            mid_ast::Expr::Local(local_id) => {
                alias_fields(
                    name_adjacencies,
                    (locals[local_id.0], &vector![]),
                    (cur_expr_id, &vector![]),
                );
            }
            mid_ast::Expr::Call(_purity, func_id, arg_term, _) => {
                // FIXME: emit that information from functions in UniqueInfos.
                update_term_accesses(accesses, locals, arg_term);
                // Identify where parts of arg_term are aliased in the result
                apply_unique_info(
                    name_adjacencies,
                    accesses,
                    locals,
                    &unique_infos[func_id.0],
                    arg_term,
                    cur_expr_id,
                );
            }
            mid_ast::Expr::Match(_matched, branches, _result_type) => {
                let mut new_edges = BTreeMap::new();
                for (branch_idx, (_pat, block)) in branches.iter().enumerate() {
                    accesses.in_branch_scope(cur_expr_id, branch_idx, |sub_accesses| {
                        alias_track_block(
                            typedefs,
                            unique_infos,
                            sub_accesses,
                            name_adjacencies,
                            name_vars,
                            block,
                        );
                        let branch_result = ExprId(name_adjacencies.len() - 1);
                        compute_edges_from_aliasing(
                            name_adjacencies,
                            (branch_result, &vector![]),
                            (cur_expr_id, &vector![]),
                            &mut new_edges,
                        );
                    });
                }
                add_computed_edges(name_adjacencies, new_edges);
            }
        };
    }

    // Computes the fields in `type_` at which there is a name. Differs from annot_aliases::get_names_in
    // by including, for every recursive type in `type_`, one full layer of recursion, in order to
    // facilitate alias graph construction (effectively, "unrolling" the type-folded name one step).
    //
    // Returns the names in `type_` and the edges between those that are aliased.
    pub fn get_names_in(
        type_defs: &[mid_ast::TypeDef<mid_ast::RepParamId>],
        name_vars: &mut BTreeMap<FieldPath, SolverVarId>, // indexed by ExprId
        type_: &mid_ast::Type<SolverVarId>,
    ) -> (Vec<FieldPath>, Vec<(FieldPath, FieldPath)>) {
        use im_rc::Vector;
        let mut names = Vec::new();
        let mut edges = Vec::new();
        add_names_from_type(
            type_defs,
            name_vars,
            &mut names,
            &mut edges,
            &mut BTreeMap::new(),
            &mut BTreeSet::new(),
            type_,
            Vector::new(),
        );
        return (names, edges);

        // Recursively appends paths to names in `type_` to `names`
        fn add_names_from_type(
            type_defs: &[mid_ast::TypeDef<mid_ast::RepParamId>],
            name_vars: &mut BTreeMap<FieldPath, SolverVarId>, // indexed by ExprId
            names: &mut Vec<FieldPath>,
            edges: &mut Vec<(FieldPath, FieldPath)>,
            // `typedefs_on_path` maps types to the path at which they are found in the type
            typedefs_on_path: &mut BTreeMap<mid_ast::CustomTypeId, FieldPath>,
            typedefs_on_path_twice: &mut BTreeSet<mid_ast::CustomTypeId>,
            type_: &mid_ast::Type<SolverVarId>,
            prefix: FieldPath,
        ) {
            match type_ {
                mid_ast::Type::Bool | mid_ast::Type::Int | mid_ast::Type::Float => {}
                mid_ast::Type::Text => unimplemented!(),
                mid_ast::Type::Array(item_type, var) | mid_ast::Type::HoleArray(item_type, var) => {
                    // The array itself:
                    names.push(prefix.clone());
                    name_vars.insert(prefix.clone(), *var);
                    // The names in elements of the array:
                    let mut new_prefix = prefix.clone();
                    new_prefix.push_back(FieldId::ArrayMembers);
                    add_names_from_type(
                        type_defs,
                        name_vars,
                        names,
                        edges,
                        typedefs_on_path,
                        typedefs_on_path_twice,
                        item_type,
                        new_prefix,
                    );
                }
                mid_ast::Type::Tuple(item_types) => {
                    for (i, item_type) in item_types.iter().enumerate() {
                        let mut new_prefix = prefix.clone();
                        new_prefix.push_back(FieldId::Field(i));
                        add_names_from_type(
                            type_defs,
                            name_vars,
                            names,
                            edges,
                            typedefs_on_path,
                            typedefs_on_path_twice,
                            item_type,
                            new_prefix,
                        );
                    }
                }
                mid_ast::Type::Custom(id, vars) => {
                    let naming_nonrecursively = !typedefs_on_path.contains_key(id);
                    let naming_second_layer =
                        typedefs_on_path.contains_key(id) && !typedefs_on_path_twice.contains(id);
                    if naming_nonrecursively || naming_second_layer {
                        if naming_second_layer {
                            // Mark that we should not recursively traverse this type any deeper
                            typedefs_on_path_twice.insert(*id);
                            // Record that the current field aliases the ancestor of the same type
                            edges.push((typedefs_on_path.get(id).unwrap().clone(), prefix.clone()));
                        } else {
                            // Mark the path at which this type appears, for reference if it appears recursively
                            typedefs_on_path.insert(*id, prefix.clone());
                        }
                        for (i, variant) in type_defs[id.0].variants.iter().enumerate() {
                            if let Some(variant_type) = variant {
                                let mut variant_prefix = prefix.clone();
                                variant_prefix.push_back(FieldId::Variant(mid_ast::VariantId(i)));
                                add_names_from_type(
                                    type_defs,
                                    name_vars,
                                    names,
                                    edges,
                                    typedefs_on_path,
                                    typedefs_on_path_twice,
                                    &unify::substitute_vars(type_defs, variant_type, vars),
                                    variant_prefix,
                                );
                            }
                        }
                        if naming_second_layer {
                            typedefs_on_path_twice.remove(id);
                        } else {
                            // Remove if we added it
                            typedefs_on_path.remove(id);
                        }
                    }
                }
            }
        }
    }

    fn apply_unique_info(
        name_adjacencies: &mut Vec<BTreeMap<FieldPath, BTreeSet<Name>>>, // indexed by ExprId
        name_last_accesses: &mut LastAccessesCursor,
        locals: &Vector<ExprId>, // indexed by LocalId
        ui: &UniqueInfo,
        arg: &mid_ast::Term,
        cur_expr_id: ExprId,
    ) {
        match arg {
            mid_ast::Term::Access(local_id, _, Some(field)) => {
                for alias in &ui.edges {
                    alias_fields(
                        name_adjacencies,
                        (locals[local_id.0], &(field + &alias.arg_field)),
                        (cur_expr_id, &alias.ret_field),
                    );
                }
                for name in &ui.new_names {
                    assert!(name_last_accesses.accesses[cur_expr_id.0].contains_key(&name));
                }
            }
            mid_ast::Term::Access(_, _, None) => {
                unreachable!();
            }
            mid_ast::Term::BoolLit(_) | mid_ast::Term::IntLit(_) | mid_ast::Term::FloatLit(_) => {
                // Literals have no aliasing
            }
        }
    }

    fn update_term_accesses(
        accesses: &mut LastAccessesCursor, // indexed by ExprId
        locals: &Vector<ExprId>,           // indexed by LocalId
        term: &mid_ast::Term,
    ) {
        let cur_expr_id = accesses.last_expr_id();
        match term {
            mid_ast::Term::Access(local_id, _, Some(pruned_field_path)) => {
                let referenced_expr = &mut accesses.accesses[locals[local_id.0].0];
                // Update last-accessed of all names accessed in the field_path
                for i in 0..pruned_field_path.len() {
                    if let Some(last_access) = referenced_expr.get_mut(&pruned_field_path.take(i)) {
                        last_access.consider_access(&accesses.ctx, cur_expr_id);
                    }
                }
            }
            mid_ast::Term::Access(_, _, None) => unreachable!(),
            mid_ast::Term::BoolLit(_) | mid_ast::Term::IntLit(_) | mid_ast::Term::FloatLit(_) => {}
        }
    }

    /// Adds the necessary additional edges (in the aliasing graph in name_adjacencies)
    /// when using a term in an expression.
    /// Use means: the term `term` is going to occur in the position `prefix` in
    /// the expression identified by `cur_expr_id`. `add_term_aliases` generates
    /// the edges to add to `name_adjacencies` to represent this.
    ///
    /// Note that this assumes that all field which are names in a given expression
    /// have at least an empty set assigned in name_adjacencies.
    fn add_term_aliases(
        // TODO: reorder this heinous argument list
        name_adjacencies: &mut [BTreeMap<FieldPath, BTreeSet<Name>>],
        locals: &Vector<ExprId>, // indexed by LocalId
        prefix: &FieldPath,
        term: &mid_ast::Term,
        cur_expr_id: ExprId,
    ) {
        match term {
            mid_ast::Term::Access(referenced_local_id, _, Some(referenced_name_path)) => {
                alias_fields(
                    name_adjacencies,
                    (locals[referenced_local_id.0], referenced_name_path),
                    (cur_expr_id, prefix),
                );
            }
            mid_ast::Term::BoolLit(_) | mid_ast::Term::IntLit(_) | mid_ast::Term::FloatLit(_) => {}
            _ => unreachable!(),
        }
    }

    fn alias_fields(
        name_adjacencies: &mut [BTreeMap<FieldPath, BTreeSet<Name>>],
        prior: (ExprId, &FieldPath),
        new: (ExprId, &FieldPath),
    ) {
        let mut new_edges = BTreeMap::new();
        compute_edges_from_aliasing(name_adjacencies, prior, new, &mut new_edges);
        add_computed_edges(name_adjacencies, new_edges);
    }

    fn add_computed_edges(
        name_adjacencies: &mut [BTreeMap<FieldPath, BTreeSet<Name>>],
        edges_to_add: BTreeMap<ExprId, BTreeMap<FieldPath, BTreeSet<Name>>>,
    ) {
        // Dump new edges from added_edges into name_adjacencies
        for (expr_id, edges_by_path) in edges_to_add.into_iter() {
            for (field_path, mut adjacent_names) in edges_by_path.into_iter() {
                name_adjacencies[expr_id.0]
                    .get_mut(&field_path)
                    .expect("found alias edge to name at uninitialized field path")
                    .append(&mut adjacent_names);
            }
        }
    }

    // Compute the edges to add to the graph to alias the two expressions, and add
    // those to `edges`.
    // `compute_edges_from_aliasing` crucially does *not* consider aliasing relationships described
    // in `edges` when adding transitive aliases. This enables calling
    // `compute_edges_from_aliasing` repeatedly, between each branch result of a match and the
    // match result, without creating erroneous edges between the branch results.
    fn compute_edges_from_aliasing(
        name_adjacencies: &[BTreeMap<FieldPath, BTreeSet<Name>>],
        prior: (ExprId, &FieldPath),
        new: (ExprId, &FieldPath),
        edges: &mut BTreeMap<ExprId, BTreeMap<FieldPath, BTreeSet<Name>>>,
    ) {
        let (prior_expr, prior_path) = prior;
        let (new_expr, new_path) = new;

        for (ref_path, ref_edges) in name_adjacencies[prior_expr.0].iter() {
            // Look at all sub-paths of the path being accessed
            // NOTE: there is some redundant work being done here. As name_adjacencies
            // includes names in recursive types one level deep, fields in recursive
            // types will be handled twice each by this loop. It should be harmless.
            if ref_path.take(prior_path.len()) == *prior_path {
                // ref_path is the full path into the referenced expression of some name
                // that is being copied. sub_path is that path *relative* to the path at
                // which `prior` and `new` are being aliased.
                let sub_path = ref_path.skip(prior_path.len());
                // Note: ref_path == prior_path + sub_path

                // Mark here that the name aliases there, and everything aliased by there
                let here_path = new_path + &sub_path;
                let mut here_edges = ref_edges.clone();
                here_edges.insert((prior_expr, ref_path.clone()));
                edges
                    .entry(new_expr)
                    .or_insert_with(BTreeMap::new)
                    .entry(here_path.clone())
                    .or_insert_with(BTreeSet::new)
                    .append(&mut here_edges);
                drop(here_edges); // emptied by previous statement

                // For every alias in ref_edges, mark that it is aliased
                // here (to make the edges undirected/bidirectional)
                for (other_expr, other_path) in ref_edges {
                    edges
                        .entry(*other_expr)
                        .or_insert_with(BTreeMap::new)
                        .entry(other_path.clone())
                        .or_insert_with(BTreeSet::new)
                        .insert((new_expr, here_path.clone()));
                }

                // Mark there that the name is aliased here
                edges
                    .entry(prior_expr)
                    .or_insert_with(BTreeMap::new)
                    .entry(ref_path.clone())
                    .or_insert_with(BTreeSet::new)
                    .insert((new_expr, new_path + ref_path));
            }
        }
    }
}

mod constrain {
    use super::aliasing;
    use super::mid_ast::{self, ExprId};
    use crate::annot_aliases::FieldPath;
    use crate::util::constraint_graph::{ConstraintGraph, EquivClass, EquivClasses, SolverVarId};
    use im_rc::vector;
    use std::collections::{BTreeMap, BTreeSet};

    pub struct FuncInfo {
        pub id: mid_ast::CustomFuncId,
        // arg (and its type) are first in the body, ret (and its type) are last
        pub body: mid_ast::TypedBlock,
        pub aliases: Vec<BTreeMap<FieldPath, BTreeSet<aliasing::Name>>>, // indexed by ExprId
        pub last_accesses: Vec<BTreeMap<FieldPath, aliasing::LastAccessTree>>, // indexed by ExprId
        pub name_vars: Vec<BTreeMap<FieldPath, SolverVarId>>,            // indexed by ExprId
        pub paths_to_exprs: Vec<Vec<(ExprId, usize)>>,                   // indexed by ExprId
    }

    impl FuncInfo {
        /// Returns the variable which describes the representation of the given name
        fn repr_var_for(&self, (expr_id, path): &aliasing::Name) -> SolverVarId {
            *self.name_vars[expr_id.0].get(path).unwrap()
        }

        /// Determines whether `at` is the last use of the given name.
        fn is_last_use(&self, (expr_id, path): &aliasing::Name, at: ExprId) -> bool {
            self.last_accesses[expr_id.0]
                .get(path)
                .expect("got access to non-existent or non-recorded name")
                .is_last_use(&self.paths_to_exprs[at.0], at)
        }

        /// Checks whether the given names are aliased
        fn are_aliased(
            &self,
            (name_expr_a, name_path_a): &aliasing::Name,
            (name_expr_b, name_path_b): &aliasing::Name,
        ) -> bool {
            if let Some(aliases_a) = self.aliases[name_expr_a.0].get(name_path_a) {
                for (other_expr, other_path) in aliases_a {
                    if other_expr == name_expr_b && other_path == name_path_b {
                        return true;
                    }
                }
                false
            } else {
                panic!("name does not exist")
            }
        }

        /// If the given name is aliased to a field in the function argument, `aliases_arg` returns
        /// the path in the argument to which it is aliased. Otherwise, it returns None.
        fn aliases_arg(&self, (name_expr, name_path): &aliasing::Name) -> Option<FieldPath> {
            if let Some(aliases) = self.aliases[name_expr.0].get(name_path) {
                for (other_expr, other_path) in aliases {
                    if *other_expr == ExprId::ARG {
                        return Some(other_path.clone());
                    }
                }
                None
            } else {
                panic!("name does not exist")
            }
        }
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Context<'a> {
        pub constraint_sigs: &'a [Option<Signature>], // indexed by CustomFuncId
        pub equiv_classes: &'a EquivClasses,
        pub scc_sigs: &'a BTreeMap<
            mid_ast::CustomFuncId,
            BTreeMap<EquivClass, BTreeSet<mid_ast::Constraint>>,
        >,
    }

    #[derive(Clone, Debug)]
    pub struct Signature {
        params: Vec<BTreeSet<mid_ast::Constraint>>, // indexed by RepParamId
    }

    impl Signature {
        pub fn new(params: Vec<BTreeSet<mid_ast::Constraint>>) -> Self {
            Signature { params }
        }

        pub fn num_params(&self) -> usize {
            self.params.len()
        }

        fn is_empty(&self) -> bool {
            for constraints in &self.params {
                if !constraints.is_empty() {
                    return false;
                }
            }
            true
        }
    }

    pub fn constrain_func(
        ctx: Context,
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        func: &FuncInfo,
    ) -> BTreeMap<EquivClass, BTreeSet<mid_ast::Constraint>> {
        let mut mutation_points = Vec::new();
        let _ = constrain_block(
            ctx,
            func,
            graph,
            &mut mutation_points,
            ExprId(1),
            &func.body,
        );

        for (arg_path, arg_path_last_access) in &func.last_accesses[0] {
            for (mutated_arg_path, mutation_loc) in &mutation_points {
                if arg_path_last_access
                    .is_after(&func.paths_to_exprs[mutation_loc.0], *mutation_loc)
                {
                    graph.require(
                        func.repr_var_for(&(ExprId::ARG, mutated_arg_path.clone())),
                        mid_ast::Constraint::SharedIfAliased(
                            arg_path.clone(),
                            mutated_arg_path.clone(),
                        ),
                    );
                }
            }
        }
        let mut func_sig = BTreeMap::new();
        for equiv_class_param in ctx.scc_sigs[&func.id].keys() {
            func_sig.insert(*equiv_class_param, BTreeSet::new());
        }
        for (var_idx, var_constraints) in graph.var_constraints.iter().enumerate() {
            let equiv_class = ctx.equiv_classes.class(SolverVarId(var_idx));
            if let Some(constraints) = func_sig.get_mut(&equiv_class) {
                constraints.extend(var_constraints.requirements.iter().cloned());
            }
        }
        func_sig
    }

    /// Returns the next ExprId after the expressions in the given block
    #[must_use]
    fn constrain_block(
        ctx: Context,
        func: &FuncInfo,
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        arg_mutations: &mut Vec<(FieldPath, ExprId)>,
        initial_expr_id: ExprId,
        block: &mid_ast::TypedBlock,
    ) -> ExprId {
        let mut next_expr_id = initial_expr_id;
        for (expr, type_) in block.terms.iter().zip(block.types.iter()) {
            next_expr_id = constrain_expr(
                ctx,
                func,
                graph,
                arg_mutations,
                block,
                next_expr_id,
                expr,
                type_,
            );
        }
        next_expr_id
    }

    // Returns the `ExprId` of the next expression to be processed after the given `expr`.
    #[must_use]
    fn constrain_expr(
        ctx: Context,
        func: &FuncInfo,
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        arg_mutations: &mut Vec<(FieldPath, ExprId)>,
        block: &mid_ast::TypedBlock,
        expr_id: ExprId,
        expr: &mid_ast::TypedExpr,
        type_: &mid_ast::Type<SolverVarId>,
    ) -> ExprId {
        return match expr {
            mid_ast::Expr::ArrayOp(array_op) => {
                match array_op {
                    mid_ast::ArrayOp::Construct(..) => {}
                    mid_ast::ArrayOp::Item(..) => {}
                    mid_ast::ArrayOp::Len(_) => {}
                    mid_ast::ArrayOp::Push(array_term, _item_term) => {
                        handle_array_mutated(
                            func,
                            graph,
                            arg_mutations,
                            block,
                            expr_id,
                            type_,
                            array_term,
                        );
                    }
                    mid_ast::ArrayOp::Pop(array_term) => {
                        handle_array_mutated(
                            func,
                            graph,
                            arg_mutations,
                            block,
                            expr_id,
                            type_,
                            array_term,
                        );
                    }
                    mid_ast::ArrayOp::Replace(hole_array_term, _item_term) => {
                        handle_array_mutated(
                            func,
                            graph,
                            arg_mutations,
                            block,
                            expr_id,
                            type_,
                            hole_array_term,
                        );
                    }
                }
                expr_id.next()
            }
            // Call to a function outside the SCC
            mid_ast::Expr::Call(
                _purity,
                func_id,
                arg,
                Some(mid_ast::ReprParams::Determined(repr_vars)),
            ) => {
                if let Some(arg_name) = get_accessed_name(block, arg) {
                    let sig = ctx.constraint_sigs[func_id.0].as_ref().unwrap();
                    for (repr_var, constraint_set) in repr_vars.iter().zip(sig.params.iter()) {
                        for constraint in constraint_set {
                            apply_constraint_from_call(
                                func,
                                graph,
                                arg_mutations,
                                *repr_var,
                                constraint,
                                expr_id,
                                &arg_name,
                            );
                        }
                    }
                } else {
                    assert!(ctx.constraint_sigs[func_id.0].as_ref().unwrap().is_empty())
                }
                expr_id.next()
            }
            // Call to a function in the SCC
            mid_ast::Expr::Call(_purity, func_id, arg, Some(mid_ast::ReprParams::Pending)) => {
                let callee_sig = ctx
                    .scc_sigs
                    .get(&func_id)
                    .expect("function not present in SCC map");
                if let Some(arg_name) = get_accessed_name(block, arg) {
                    for (equiv_class, constraints) in callee_sig {
                        let repr_var = ctx.equiv_classes.one_repr_var_of(*equiv_class);
                        for constraint in constraints {
                            apply_constraint_from_call(
                                func,
                                graph,
                                arg_mutations,
                                repr_var,
                                constraint,
                                expr_id,
                                &arg_name,
                            );
                        }
                    }
                } else {
                    assert!(ctx.constraint_sigs[func_id.0].as_ref().unwrap().is_empty());
                }
                expr_id.next()
            }
            mid_ast::Expr::Call(_, _, _, None) => unreachable!(),
            mid_ast::Expr::Match(_matched_local, branches, _result_type) => {
                let mut next_expr_id = expr_id;
                for (_pat, branch) in branches {
                    next_expr_id =
                        constrain_block(ctx, func, graph, arg_mutations, next_expr_id, branch);
                }
                next_expr_id
            }
            mid_ast::Expr::Term(_)
            | mid_ast::Expr::ArithOp(_)
            | mid_ast::Expr::Ctor(..)
            | mid_ast::Expr::Tuple(_)
            | mid_ast::Expr::Local(_) => expr_id.next(),
        };

        fn get_accessed_name(
            block: &mid_ast::TypedBlock,
            term: &mid_ast::Term,
        ) -> Option<(mid_ast::ExprId, FieldPath)> {
            if let mid_ast::Term::Access(local_id, _, Some(field)) = term {
                Some((block.expr_id_of(*local_id), field.clone()))
            } else if let mid_ast::Term::Access(_, _, None) = term {
                unreachable!()
            } else {
                None
            }
        }

        fn handle_array_mutated(
            func: &FuncInfo,
            graph: &mut ConstraintGraph<mid_ast::Constraint>,
            arg_mutations: &mut Vec<(FieldPath, ExprId)>,
            block: &mid_ast::TypedBlock,
            expr_id: ExprId,
            type_: &mid_ast::Type<SolverVarId>,
            array: &mid_ast::Term,
        ) {
            let original_array = get_accessed_name(block, array).expect("unexpected literal");
            let repr_var = match type_ {
                mid_ast::Type::Array(_, repr_var) => *repr_var,
                mid_ast::Type::HoleArray(_, repr_var) => *repr_var,
                _ => unreachable!(), // Type error
            };
            apply_constraint_from_call(
                func,
                graph,
                arg_mutations,
                repr_var,
                &mid_ast::Constraint::SharedIfOutlivesCall(vector![]),
                expr_id,
                &original_array,
            );
        }

        // When a function or builtin is called, generating `constraint` on `repr_var`,
        // `apply_constraint_from_call` generates the constraint(s) to apply to `repr_var`
        // in the scope of the calling function.
        // For every SharedIfOutlivesCall(Name) in which the Name aliases an argument,
        // the named argument and the expression ID that generated that constriant are
        // pushed to `arg_mutations` (for creating SharedIfAliased(...) constraints later).
        fn apply_constraint_from_call(
            func: &FuncInfo,
            graph: &mut ConstraintGraph<mid_ast::Constraint>,
            arg_mutations: &mut Vec<(FieldPath, ExprId)>,
            repr_var: SolverVarId,
            constraint: &mid_ast::Constraint,
            expr_id: ExprId, // id of expression that made the call
            arg_name: &aliasing::Name,
        ) {
            match constraint {
                mid_ast::Constraint::Shared => {
                    graph.require(repr_var, mid_ast::Constraint::Shared);
                }
                mid_ast::Constraint::SharedIfOutlivesCall(sub_arg_path) => {
                    let constrained_name = {
                        let (arg_expr, arg_path) = arg_name;
                        (*arg_expr, arg_path + sub_arg_path)
                    };
                    if let Some(outer_arg_path) = func.aliases_arg(&constrained_name) {
                        arg_mutations.push((outer_arg_path, expr_id));
                    }
                    if func.is_last_use(&constrained_name, expr_id) {
                        if let Some(outer_arg_path) = func.aliases_arg(&constrained_name) {
                            graph.require(
                                repr_var,
                                mid_ast::Constraint::SharedIfOutlivesCall(outer_arg_path),
                            );
                        } else {
                            // Apply no constraint
                        }
                    } else {
                        graph.require(repr_var, mid_ast::Constraint::Shared);
                    }
                }
                mid_ast::Constraint::SharedIfAliased(sub_arg_path_a, sub_arg_path_b) => {
                    let (name_a, name_b) = {
                        let (arg_expr, arg_path) = arg_name;
                        (
                            (*arg_expr, arg_path + sub_arg_path_a),
                            (*arg_expr, arg_path + sub_arg_path_b),
                        )
                    };
                    if func.are_aliased(&name_a, &name_b) {
                        graph.require(repr_var, mid_ast::Constraint::Shared);
                    } else if let (Some(outer_arg_path_a), Some(outer_arg_path_b)) =
                        (func.aliases_arg(&name_a), func.aliases_arg(&name_b))
                    {
                        // If both names are aliased to arguments (and not necessarily
                        // aliased locally), pass the buck
                        graph.require(
                            repr_var,
                            mid_ast::Constraint::SharedIfAliased(
                                outer_arg_path_a,
                                outer_arg_path_b,
                            ),
                        );
                    }
                }
            }
        }
    }
}

mod extract {
    use super::{constrain, unify};
    use super::{mid_ast, out_ast};
    use crate::util::constraint_graph::{EquivClass, EquivClasses, SolverVarId};
    use std::collections::{BTreeMap, BTreeSet};
    pub struct SignatureGen<'a> {
        equiv_classes: &'a EquivClasses,
        params: Vec<EquivClass>, // indexed by out_ast::RepParamId
        params_reverse: BTreeMap<EquivClass, out_ast::RepParamId>,
    }
    impl<'a> SignatureGen<'a> {
        fn new(equiv_classes: &'a EquivClasses) -> Self {
            SignatureGen {
                equiv_classes,
                params: Vec::new(),
                params_reverse: BTreeMap::new(),
            }
        }

        fn soln_for(&mut self, var: SolverVarId) -> out_ast::RepParamId {
            let class = self.equiv_classes.class(var);
            if let Some(rep_param) = self.params_reverse.get(&class) {
                *rep_param
            } else {
                let rep_param = out_ast::RepParamId(self.params.len());
                self.params.push(class);
                self.params_reverse.insert(class, rep_param);
                rep_param
            }
        }
    }

    pub struct SolutionExtractor<'a> {
        equiv_classes: &'a EquivClasses,
        class_constraints: Vec<BTreeSet<out_ast::Constraint>>, // indexed by EquivClass
        solutions: Vec<Option<out_ast::Solution>>,             // indexed by EquivClass
        params: Vec<EquivClass>,                               // indexed by out_ast::RepParamId
    }
    impl<'a> SolutionExtractor<'a> {
        pub fn from_sig_gen(
            siggen: &SignatureGen<'a>,
            class_constraints: Vec<BTreeSet<out_ast::Constraint>>,
        ) -> Self {
            let mut solutions = vec![None; siggen.equiv_classes.count()];
            for (equiv_class, rep_param) in &siggen.params_reverse {
                solutions[equiv_class.0] = Some(out_ast::Solution::Var(*rep_param));
            }
            SolutionExtractor {
                equiv_classes: siggen.equiv_classes,
                class_constraints,
                solutions,
                params: siggen.params.clone(),
            }
        }
        fn fresh_for(&mut self, class: EquivClass) -> out_ast::RepParamId {
            let param = out_ast::RepParamId(self.params.len());
            self.params.push(class);
            param
        }

        fn soln_in_body_for(&mut self, var: SolverVarId) -> out_ast::Solution {
            let class = self.equiv_classes.class(var);
            if let Some(soln) = self.solutions[class.0] {
                soln
            } else {
                let var_constraints = &self.class_constraints[class.0];
                let soln = if var_constraints.is_empty() {
                    out_ast::Solution::Unique
                } else if var_constraints.contains(&out_ast::Constraint::Shared) {
                    out_ast::Solution::Shared
                } else {
                    unreachable!() // Other constraints are only applied to equiv classes that appear in the arg or return
                };
                self.solutions[class.0] = Some(soln);
                soln
            }
        }

        pub fn drain_constraints(self) -> Vec<BTreeSet<out_ast::Constraint>> {
            self.params
                .iter()
                .map(|class| self.class_constraints[class.0].clone()) // TODO: heinous clone of constraints
                .collect()
        }
    }

    pub fn gen_sigs<'a, 'b>(
        equiv_classes: &'a EquivClasses,
        funcs: &'b [constrain::FuncInfo],
        signatures: &'b mut [Option<unify::Signature>],
    ) -> SignatureGen<'a> {
        let mut param_gen = SignatureGen::new(equiv_classes);
        let mut type_sigs = Vec::new();
        for func in funcs {
            // Generate types in signature first so they have the first `RepParamId`s
            type_sigs.push((
                func.id,
                gen_sig_type(&mut param_gen, &func.body.types[0]),
                gen_sig_type(&mut param_gen, &func.body.types.last().unwrap()),
            ));
        }
        for (id, arg_type, ret_type) in type_sigs {
            assert!(signatures[id.0].is_none());
            signatures[id.0] = Some(unify::Signature {
                num_params: param_gen.params.len(),
                arg_type,
                ret_type,
            });
        }
        param_gen
    }

    pub fn gen_block(
        param_gen: &mut SolutionExtractor,
        block: &mid_ast::TypedBlock,
    ) -> out_ast::Block {
        let mut out_block = out_ast::Block {
            initial_idx: block.initial_idx,
            exprs: Vec::new(),
            types: Vec::new(),
            expr_ids: block.expr_ids.clone(),
        };
        for (expr, type_) in block.terms.iter().zip(block.types.iter()) {
            out_block.exprs.push(gen_expr(param_gen, expr));
            out_block.types.push(gen_type(param_gen, type_));
        }
        out_block
    }

    fn gen_expr(param_gen: &mut SolutionExtractor, expr: &mid_ast::TypedExpr) -> out_ast::Expr {
        return match expr {
            mid_ast::Expr::Term(term) => out_ast::Expr::Term(gen_term(term)),
            mid_ast::Expr::ArithOp(arith_op) => {
                let a = match arith_op {
                    mid_ast::ArithOp::IntOp(binop, left, right) => {
                        out_ast::ArithOp::IntOp(*binop, gen_term(left), gen_term(right))
                    }
                    mid_ast::ArithOp::FloatOp(binop, left, right) => {
                        out_ast::ArithOp::FloatOp(*binop, gen_term(left), gen_term(right))
                    }
                    mid_ast::ArithOp::IntCmp(cmp, left, right) => {
                        out_ast::ArithOp::IntCmp(*cmp, gen_term(left), gen_term(right))
                    }
                    mid_ast::ArithOp::FloatCmp(cmp, left, right) => {
                        out_ast::ArithOp::FloatCmp(*cmp, gen_term(left), gen_term(right))
                    }
                    mid_ast::ArithOp::NegateInt(term) => {
                        out_ast::ArithOp::NegateInt(gen_term(term))
                    }
                    mid_ast::ArithOp::NegateFloat(term) => {
                        out_ast::ArithOp::NegateFloat(gen_term(term))
                    }
                };
                out_ast::Expr::ArithOp(a)
            }
            mid_ast::Expr::ArrayOp(array_op) => {
                let a = match array_op {
                    mid_ast::ArrayOp::Construct(item_type, repr_var, items) => {
                        out_ast::ArrayOp::Construct(
                            Box::new(gen_type(param_gen, item_type)),
                            param_gen.soln_in_body_for(*repr_var),
                            items.iter().map(gen_term).collect(),
                        )
                    }
                    mid_ast::ArrayOp::Item(array, idx, _) => {
                        out_ast::ArrayOp::Item(gen_term(array), gen_term(idx))
                    }
                    mid_ast::ArrayOp::Len(array) => out_ast::ArrayOp::Len(gen_term(array)),
                    mid_ast::ArrayOp::Push(array, item) => {
                        out_ast::ArrayOp::Push(gen_term(array), gen_term(item))
                    }
                    mid_ast::ArrayOp::Pop(array) => out_ast::ArrayOp::Pop(gen_term(array)),
                    mid_ast::ArrayOp::Replace(hole_array, item) => {
                        out_ast::ArrayOp::Replace(gen_term(hole_array), gen_term(item))
                    }
                };
                out_ast::Expr::ArrayOp(a)
            }
            mid_ast::Expr::Ctor(type_id, variant_id, arg) => {
                out_ast::Expr::Ctor(*type_id, *variant_id, arg.as_ref().map(gen_term))
            }
            mid_ast::Expr::Tuple(items) => {
                out_ast::Expr::Tuple(items.iter().map(gen_term).collect())
            }
            mid_ast::Expr::Local(local_id) => out_ast::Expr::Local(*local_id),
            mid_ast::Expr::Call(
                purity,
                func_id,
                arg,
                Some(mid_ast::ReprParams::Determined(repr_params)),
            ) => out_ast::Expr::Call(
                *purity,
                *func_id,
                gen_term(arg),
                repr_params
                    .iter()
                    .map(|p| param_gen.soln_in_body_for(*p))
                    .collect(),
            ),
            mid_ast::Expr::Call(purity, func_id, arg, Some(mid_ast::ReprParams::Pending)) => {
                out_ast::Expr::Call(
                    *purity,
                    *func_id,
                    gen_term(arg),
                    (0..param_gen.params.len())
                        .into_iter()
                        .map(|rep_id| out_ast::Solution::Var(out_ast::RepParamId(rep_id)))
                        .collect(),
                )
            }
            mid_ast::Expr::Call(_, _, _, None) => unreachable!(),
            mid_ast::Expr::Match(matched_local, branches, result_t) => out_ast::Expr::Match(
                *matched_local,
                branches
                    .iter()
                    .map(|(pat, branch)| (pat.clone(), gen_block(param_gen, branch)))
                    .collect(),
                Box::new(gen_type(param_gen, result_t)),
            ),
        };

        fn gen_term(term: &mid_ast::Term) -> out_ast::Term {
            match term {
                mid_ast::Term::Access(expr, field, typefolded_field) => {
                    out_ast::Term::Access(*expr, field.clone(), typefolded_field.clone().unwrap())
                }
                &mid_ast::Term::BoolLit(v) => out_ast::Term::BoolLit(v),
                &mid_ast::Term::IntLit(v) => out_ast::Term::IntLit(v),
                &mid_ast::Term::FloatLit(v) => out_ast::Term::FloatLit(v),
            }
        }
    }

    fn gen_type(
        param_gen: &mut SolutionExtractor,
        type_: &mid_ast::Type<SolverVarId>,
    ) -> out_ast::Type {
        use out_ast::Type as T;
        match type_ {
            T::Bool => T::Bool,
            T::Int => T::Int,
            T::Float => T::Float,
            T::Text => T::Text,
            T::Array(item_t, var) => T::Array(
                Box::new(gen_type(param_gen, item_t)),
                param_gen.soln_in_body_for(*var),
            ),
            T::HoleArray(item_t, var) => T::HoleArray(
                Box::new(gen_type(param_gen, item_t)),
                param_gen.soln_in_body_for(*var),
            ),
            T::Tuple(item_types) => {
                T::Tuple(item_types.iter().map(|t| gen_type(param_gen, t)).collect())
            }
            T::Custom(type_id, vars) => T::Custom(
                *type_id,
                vars.iter()
                    .map(|v| param_gen.soln_in_body_for(*v))
                    .collect(),
            ),
        }
    }

    fn gen_sig_type(
        sig_gen: &mut SignatureGen,
        type_: &mid_ast::Type<SolverVarId>,
    ) -> out_ast::Type<out_ast::RepParamId> {
        use out_ast::Type as T;
        match type_ {
            T::Bool => T::Bool,
            T::Int => T::Int,
            T::Float => T::Float,
            T::Text => T::Text,
            T::Array(item_t, var) => T::Array(
                Box::new(gen_sig_type(sig_gen, item_t)),
                sig_gen.soln_for(*var),
            ),
            T::HoleArray(item_t, var) => T::HoleArray(
                Box::new(gen_sig_type(sig_gen, item_t)),
                sig_gen.soln_for(*var),
            ),
            T::Tuple(item_types) => T::Tuple(
                item_types
                    .iter()
                    .map(|t| gen_sig_type(sig_gen, t))
                    .collect(),
            ),
            T::Custom(type_id, vars) => T::Custom(
                *type_id,
                vars.iter().map(|v| sig_gen.soln_for(*v)).collect(),
            ),
        }
    }
}

mod integrate {
    use super::{aliasing, constrain, extract, flatten, parameterize, unify};
    use super::{in_ast, mid_ast, out_ast};
    use crate::annot_aliases::{self, UniqueInfo};
    use crate::graph;
    use crate::util::constraint_graph::{ConstraintGraph, EquivClass, EquivClasses, SolverVarId};
    use std::collections::{BTreeMap, BTreeSet};

    fn analyze_scc_func(
        context: unify::Context,
        graph: &mut ConstraintGraph<mid_ast::Constraint>,
        func: &mid_ast::FuncDef<()>,
        id: mid_ast::CustomFuncId,
    ) -> constrain::FuncInfo {
        let typed_body = unify::unify_func(graph, context, func);
        let func_info =
            aliasing::alias_track_func(context.typedefs, context.unique_infos, typed_body, id);

        assert_eq!(func_info.last_accesses.len(), func_info.aliases.len());
        assert_eq!(func_info.aliases.len(), func_info.name_vars.len());
        func_info
    }

    fn add_equiv_class_params(
        equiv_classes: &EquivClasses,
        params: &mut BTreeMap<EquivClass, BTreeSet<mid_ast::Constraint>>,
        type_: &mid_ast::Type<SolverVarId>,
    ) {
        use mid_ast::Type as T;
        match type_ {
            T::Bool | T::Int | T::Float | T::Text => {}
            T::Array(item_t, var) | T::HoleArray(item_t, var) => {
                params.insert(equiv_classes.class(*var), BTreeSet::new());
                add_equiv_class_params(equiv_classes, params, item_t);
            }
            T::Tuple(item_types) => {
                for t in item_types {
                    add_equiv_class_params(equiv_classes, params, t);
                }
            }
            T::Custom(_id, vars) => {
                for v in vars {
                    params.insert(equiv_classes.class(*v), BTreeSet::new());
                }
            }
        }
    }

    pub fn annot_reprs(program: &in_ast::Program, unique_infos: &[UniqueInfo]) -> out_ast::Program {
        let typedefs = parameterize::parameterize_typedefs(&program.custom_types);
        let func_graph = annot_aliases::func_dependency_graph(program);

        let mut signatures = vec![None; program.funcs.len()];
        let mut constraint_signatures = vec![None; program.funcs.len()];
        let mut out_func_bodies = vec![None; program.funcs.len()];

        for scc_nodes in graph::strongly_connected(&func_graph) {
            let scc_func_ids = scc_nodes
                .iter()
                .map(|&graph::NodeId(id)| in_ast::CustomFuncId(id));
            let mut graph = ConstraintGraph::new();
            let scc_funcs = scc_func_ids
                .map(|func_id| {
                    (
                        func_id,
                        flatten::flatten_func(&mut graph, &typedefs, &program.funcs[func_id.0]),
                    )
                })
                .collect::<BTreeMap<_, _>>();
            let context = unify::Context {
                first_order_typedefs: &program.custom_types,
                typedefs: &typedefs,
                func_sigs: &signatures,
                scc_funcdefs: &scc_funcs,
                unique_infos,
            };
            let equiv_classes = graph.find_equiv_classes();
            // take union of equiv classes for each func in scc_funcs, these are params to each func in the SCC
            let mut scc_sigs = BTreeMap::new();
            {
                let mut scc_equiv_class_params = BTreeMap::new();
                for func in scc_funcs.values() {
                    add_equiv_class_params(
                        &equiv_classes,
                        &mut scc_equiv_class_params,
                        &func.arg_type,
                    );
                    add_equiv_class_params(
                        &equiv_classes,
                        &mut scc_equiv_class_params,
                        &func.ret_type,
                    );
                }
                for func_id in scc_funcs.keys() {
                    scc_sigs.insert(*func_id, scc_equiv_class_params.clone());
                }
            }
            let scc_funcinfos = scc_funcs
                .iter()
                .map(|(id, func)| analyze_scc_func(context, &mut graph, func, *id))
                .collect::<Vec<_>>();
            loop {
                let mut new_scc_sigs = BTreeMap::new();
                for func in &scc_funcinfos {
                    let sig = constrain::constrain_func(
                        constrain::Context {
                            constraint_sigs: &constraint_signatures,
                            equiv_classes: &equiv_classes,
                            scc_sigs: &scc_sigs,
                        },
                        &mut graph,
                        func,
                    );
                    new_scc_sigs.insert(func.id, sig);
                    graph.clear_requirements();
                }
                if new_scc_sigs == scc_sigs {
                    break;
                }
                scc_sigs = new_scc_sigs;
            }
            // Extract `unify::Signature`s for this SCC
            let sig_gen = extract::gen_sigs(&equiv_classes, &scc_funcinfos, &mut signatures);

            for func in &scc_funcinfos {
                // Compute constraints one more time to extract solutions for internal variables,
                // and assert that we are at a fixed point
                assert_eq!(
                    &scc_sigs[&func.id],
                    &constrain::constrain_func(
                        constrain::Context {
                            constraint_sigs: &constraint_signatures,
                            equiv_classes: &equiv_classes,
                            scc_sigs: &scc_sigs,
                        },
                        &mut graph,
                        func,
                    )
                );

                // Extract constraints on each equivalence class
                let mut class_constraints = (0..equiv_classes.count())
                    .map(|_| BTreeSet::new())
                    .collect::<Vec<_>>();
                for (var_idx, graph_constraints) in graph.var_constraints.iter_mut().enumerate() {
                    // Empty the constraint list in the graph to avoid clone (resetting
                    // constraints is necessary for next iteration anyway)
                    let mut var_constraints = Vec::new();
                    std::mem::swap(&mut graph_constraints.requirements, &mut var_constraints);
                    let equiv_class = equiv_classes.class(SolverVarId(var_idx));
                    class_constraints[equiv_class.0].extend(var_constraints);
                }

                let mut extractor =
                    extract::SolutionExtractor::from_sig_gen(&sig_gen, class_constraints);

                out_func_bodies[func.id.0] = Some(extract::gen_block(&mut extractor, &func.body));

                assert!(constraint_signatures[func.id.0].is_none());
                constraint_signatures[func.id.0] =
                    Some(constrain::Signature::new(extractor.drain_constraints()));
            }
        }

        let mut out_funcs = Vec::new();
        for (constraint_sig, body) in constraint_signatures.into_iter().zip(out_func_bodies) {
            out_funcs.push(out_ast::FuncDef {
                num_params: constraint_sig.unwrap().num_params(),
                body: body.unwrap(),
            })
        }

        out_ast::Program {
            custom_types: typedefs,
            funcs: out_funcs,
            main: program.main,
        }
    }
}
