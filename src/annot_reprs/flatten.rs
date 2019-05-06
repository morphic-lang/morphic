use super::{in_ast, mid_ast};
use crate::annot_aliases::{FieldId, FieldPath};
use crate::util::constraint_graph::{ConstraintGraph, SolverVarId};
use crate::util::with_scope;
use im_rc::vector;

pub fn flatten_func(
    graph: &mut ConstraintGraph<mid_ast::Constraint>,
    typedefs: &[mid_ast::TypeDef<mid_ast::RepParamId>],
    func: &in_ast::FuncDef,
) -> mid_ast::FuncDef<()> {
    let mut locals = Vec::new();
    let mut body = mid_ast::Block {
        // LocalId(0) is arg, so first term index is 1
        initial_idx: 1,
        terms: vec![],
        types: vec![],
        expr_ids: None,
    };
    bind_pattern(
        graph,
        typedefs,
        &func.arg,
        mid_ast::LocalId(0),
        vector![],
        &mut locals,
    );
    let return_expr = mid_ast::Expr::Term(flatten_expr_into(
        graph,
        typedefs,
        &func.body,
        &mut body,
        &mut locals,
    ));
    let _ = body.add(return_expr);
    body.assert_valid();
    mid_ast::FuncDef {
        purity: func.purity,
        arg_type: instantiate_type(graph, typedefs, &func.arg_type),
        ret_type: instantiate_type(graph, typedefs, &func.ret_type),
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
        in_ast::Type::Byte => mid_ast::Type::Byte,
        in_ast::Type::Float => mid_ast::Type::Float,
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

#[must_use]
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
                in_ast::ArithOp::ByteOp(op, left, right) => {
                    let lterm = flatten_expr_into(graph, typedefs, left, block, locals);
                    let rterm = flatten_expr_into(graph, typedefs, right, block, locals);
                    mid_ast::ArithOp::ByteOp(*op, lterm, rterm)
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
                in_ast::ArithOp::ByteCmp(op, left, right) => {
                    let lterm = flatten_expr_into(graph, typedefs, left, block, locals);
                    let rterm = flatten_expr_into(graph, typedefs, right, block, locals);
                    mid_ast::ArithOp::ByteCmp(*op, lterm, rterm)
                }
                in_ast::ArithOp::NegateInt(arg) => mid_ast::ArithOp::NegateInt(flatten_expr_into(
                    graph, typedefs, arg, block, locals,
                )),
                in_ast::ArithOp::NegateByte(arg) => mid_ast::ArithOp::NegateByte(
                    flatten_expr_into(graph, typedefs, arg, block, locals),
                ),
                in_ast::ArithOp::NegateFloat(arg) => mid_ast::ArithOp::NegateFloat(
                    flatten_expr_into(graph, typedefs, arg, block, locals),
                ),
            };
            block.add(mid_ast::Expr::ArithOp(out_arith_op))
        }
        in_ast::Expr::IOOp(in_ast::IOOp::Input) => {
            block.add(mid_ast::Expr::IOOp(mid_ast::IOOp::Input(graph.new_var())))
        }
        in_ast::Expr::IOOp(in_ast::IOOp::Output(output_expr)) => {
            let output_term = flatten_expr_into(graph, typedefs, output_expr, block, locals);
            block.add(mid_ast::Expr::IOOp(mid_ast::IOOp::Output(output_term)))
        }
        in_ast::Expr::ArrayOp(in_array_op) => {
            let out_array_op = match in_array_op {
                in_ast::ArrayOp::Item(_item_type, array, index) => mid_ast::ArrayOp::Item(
                    flatten_expr_into(graph, typedefs, array, block, locals),
                    flatten_expr_into(graph, typedefs, index, block, locals),
                ),
                in_ast::ArrayOp::Len(_item_type, array) => {
                    mid_ast::ArrayOp::Len(flatten_expr_into(graph, typedefs, array, block, locals))
                }
                in_ast::ArrayOp::Push(_item_type, array, item) => mid_ast::ArrayOp::Push(
                    flatten_expr_into(graph, typedefs, array, block, locals),
                    flatten_expr_into(graph, typedefs, item, block, locals),
                ),
                in_ast::ArrayOp::Concat(..) => {
                    // Concat will be removed
                    unimplemented!()
                }
                in_ast::ArrayOp::Pop(_item_type, array) => {
                    mid_ast::ArrayOp::Pop(flatten_expr_into(graph, typedefs, array, block, locals))
                }
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
        in_ast::Expr::Local(in_ast::LocalId(id)) => {
            // TODO: consider rearchitecting, so that locals are declared
            // at first use and referred back to rather than cloned here
            locals[*id].clone()
        }
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
                let mut branch_block = mid_ast::Block {
                    initial_idx: block.initial_idx + block.terms.len(),
                    terms: vec![],
                    types: vec![],
                    expr_ids: None,
                };
                with_scope(locals, |sub_locals| {
                    let out_pattern = bind_pattern(
                        graph,
                        typedefs,
                        pat,
                        matched_term_local,
                        vector![],
                        sub_locals,
                    );
                    let block_result = mid_ast::Expr::Term(flatten_expr_into(
                        graph,
                        typedefs,
                        rhs_expr,
                        &mut branch_block,
                        sub_locals,
                    ));
                    let _ = branch_block.add(block_result);
                    branch_block.assert_valid();
                    cases.push((out_pattern, branch_block));
                });
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
        in_ast::Expr::ByteLit(constant) => mid_ast::Term::ByteLit(*constant),
        in_ast::Expr::FloatLit(constant) => mid_ast::Term::FloatLit(*constant),
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
        in_ast::Pattern::ByteConst(c) => mid_ast::Pattern::ByteConst(*c),
        in_ast::Pattern::FloatConst(c) => mid_ast::Pattern::FloatConst(*c),
    }
}
