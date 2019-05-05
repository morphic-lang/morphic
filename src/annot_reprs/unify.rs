use super::{in_ast, mid_ast};
use crate::annot_aliases::{FieldId, FieldPath};
use crate::util::constraint_graph::{ConstraintGraph, SolverVarId};
use crate::util::with_scope;
use im_rc::{vector, Vector};
pub use mid_ast::ExprId;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug)]
pub struct Context<'a> {
    pub first_order_typedefs: &'a [in_ast::TypeDef],
    pub typedefs: &'a [mid_ast::TypeDef<mid_ast::RepParamId>],
    pub func_sigs: &'a [Option<Signature>],
    pub scc_funcdefs: &'a BTreeMap<mid_ast::CustomFuncId, mid_ast::FuncDef<()>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    pub num_params: usize,
    pub arg_type: mid_ast::Type<mid_ast::RepParamId>,
    pub ret_type: mid_ast::Type<mid_ast::RepParamId>,
}

#[derive(Clone, Debug)]
struct ExprIdGen {
    next: usize,                    // ExprId of the next local
    local_expr_ids: Vector<ExprId>, // indexed by `mid_ast::LocalId`
    reserved: BTreeSet<ExprId>,
}
impl ExprIdGen {
    fn with_scope<R, F: FnOnce(&mut ExprIdGen) -> R>(&mut self, f: F) -> R {
        let initial = self.clone();
        let result = f(self);

        // Never go backwards:
        assert!(self.locals_len() >= initial.locals_len());
        assert!(self.next >= initial.next);
        // `next` was never reset:
        assert!(self.locals_len() == initial.locals_len() || self.next > initial.next);

        self.local_expr_ids.truncate(initial.locals_len());
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
        self.local_expr_ids.push_back(ret);
        self.next += 1;
        ret
    }

    fn reserve_fresh(&mut self) -> ExprId {
        let ret = ExprId(self.next);
        self.reserved.insert(ret);
        self.next += 1;
        ret
    }

    fn bind_reserved(&mut self, reserved: ExprId) {
        assert!(self.reserved.remove(&reserved));
        self.local_expr_ids.push_back(reserved);
    }
}

pub fn unify_func(
    graph: &mut ConstraintGraph<mid_ast::Constraint>,
    context: Context,
    func: &mid_ast::FuncDef<()>,
) -> (mid_ast::Type<SolverVarId>, mid_ast::TypedBlock) {
    (
        func.arg_type.clone(),
        unify_block(
            graph,
            context,
            &mut vec![func.arg_type.clone()],
            &mut ExprIdGen {
                next: 1,
                local_expr_ids: vector![ExprId::ARG],
                reserved: BTreeSet::new(),
            },
            func.body.clone(),
        ),
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
    block.assert_valid();
    with_scope(locals, |sub_locals| {
        expr_id_gen.with_scope(|sub_expr_id_gen| {
            let mut exprs = Vec::new();
            for expr in block.terms {
                // FIXME // Generating the new expr_id *after* calling unify_expr means that the ExprId of
                // FIXME // a match expression is *greater* than that of all expressions in its branches.
                let expr_id = sub_expr_id_gen.reserve_fresh();
                let (expr, type_) = unify_expr(graph, context, sub_locals, sub_expr_id_gen, expr);
                sub_expr_id_gen.bind_reserved(expr_id);
                expr.assert_typefolded();
                if sub_locals.len() == 3 {
                    println!("ADDING THIRD LOCAL");
                    println!("=expr: {:#?}", &expr);
                    println!("=type: {:#?}", &type_);
                }
                exprs.push(expr);
                sub_locals.push(type_);
            }
            mid_ast::Block {
                initial_idx: block.initial_idx,
                terms: exprs,
                types: sub_locals.split_off(block.initial_idx),
                expr_ids: Some(sub_expr_id_gen.get_local_mapping()),
            }
        })
    })
}

fn unify_expr(
    graph: &mut ConstraintGraph<mid_ast::Constraint>,
    ctx: Context,
    locals: &mut Vec<mid_ast::Type<SolverVarId>>, // indexed by `mid_ast::LocalId`
    expr_id_gen: &mut ExprIdGen,
    expr: mid_ast::Expr<()>,
) -> (mid_ast::TypedExpr, mid_ast::Type<SolverVarId>) {
    let typefold = |t| typefold_term(ctx.typedefs, locals, t);
    match expr {
        mid_ast::Expr::Term(term) => {
            let type_ = type_of_term(ctx.typedefs, locals, &term);
            (
                mid_ast::Expr::Term(typefold_term(ctx.typedefs, locals, &term)),
                type_,
            )
        }
        mid_ast::Expr::Tuple(items) => {
            let types = mid_ast::Type::Tuple(
                items
                    .iter()
                    .map(|item| type_of_term(ctx.typedefs, locals, item))
                    .collect(),
            );
            (
                mid_ast::Expr::Tuple(
                    items
                        .into_iter()
                        .map(|item| typefold_term(ctx.typedefs, locals, &item))
                        .collect(),
                ),
                types,
            )
        }
        mid_ast::Expr::IOOp(mid_ast::IOOp::Input(var)) => (
            mid_ast::Expr::IOOp(mid_ast::IOOp::Input(var)),
            mid_ast::Type::Array(Box::new(mid_ast::Type::Byte), var),
        ),
        mid_ast::Expr::IOOp(mid_ast::IOOp::Output(output)) => (
            mid_ast::Expr::IOOp(mid_ast::IOOp::Output(typefold_term(
                ctx.typedefs,
                locals,
                &output,
            ))),
            mid_ast::Type::Tuple(vec![]),
        ),
        mid_ast::Expr::ArithOp(arith_op) => {
            use mid_ast::ArithOp as A;
            let type_ = match arith_op {
                A::IntOp(..) => mid_ast::Type::Int,
                A::NegateInt(..) => mid_ast::Type::Int,

                A::ByteOp(..) => mid_ast::Type::Byte,
                A::NegateByte(..) => mid_ast::Type::Byte,

                A::FloatOp(..) => mid_ast::Type::Float,
                A::NegateFloat(..) => mid_ast::Type::Float,

                A::IntCmp(..) => mid_ast::Type::Bool,
                A::FloatCmp(..) => mid_ast::Type::Bool,
                A::ByteCmp(..) => mid_ast::Type::Bool,
            };
            let typefolded = match arith_op {
                A::IntOp(binop, a, b) => A::IntOp(binop, typefold(&a), typefold(&b)),
                A::NegateInt(a) => A::NegateInt(typefold(&a)),

                A::ByteOp(binop, a, b) => A::ByteOp(binop, typefold(&a), typefold(&b)),
                A::NegateByte(a) => A::NegateByte(typefold(&a)),

                A::FloatOp(binop, a, b) => A::FloatOp(binop, typefold(&a), typefold(&b)),
                A::NegateFloat(a) => A::NegateFloat(typefold(&a)),

                A::IntCmp(cmp, a, b) => A::IntCmp(cmp, typefold(&a), typefold(&b)),
                A::FloatCmp(cmp, a, b) => A::FloatCmp(cmp, typefold(&a), typefold(&b)),
                A::ByteCmp(cmp, a, b) => A::ByteCmp(cmp, typefold(&a), typefold(&b)),
            };
            (mid_ast::Expr::ArithOp(typefolded), type_)
        }
        mid_ast::Expr::ArrayOp(array_op) => {
            use mid_ast::ArrayOp as A;
            let type_ = match &array_op {
                A::Construct(item_type, repr_var, items) => {
                    for term in items {
                        equate_types(graph, &type_of_term(ctx.typedefs, locals, term), item_type);
                    }
                    mid_ast::Type::Array(item_type.clone(), *repr_var)
                }
                A::Item(array, _idx) => {
                    let array_type = type_of_term(ctx.typedefs, locals, array);
                    if let mid_ast::Type::Array(ref item_type, v) = array_type {
                        mid_ast::Type::Tuple(vec![
                            *item_type.clone(),
                            mid_ast::Type::HoleArray(item_type.clone(), v),
                        ])
                    } else {
                        panic!("internal type error");
                    }
                }
                A::Len(_) => mid_ast::Type::Int,
                A::Push(array_term, pushed_item_term) => {
                    let array_type = type_of_term(ctx.typedefs, locals, array_term);
                    if let mid_ast::Type::Array(ref item_type, _) = array_type {
                        let pushed_item_type = type_of_term(ctx.typedefs, locals, pushed_item_term);
                        equate_types(graph, item_type, &pushed_item_type);
                        array_type
                    } else {
                        panic!("internal type error")
                    }
                }
                A::Pop(array_term) => {
                    let array_type = type_of_term(ctx.typedefs, locals, array_term);
                    if let mid_ast::Type::Array(ref item_type, _) = array_type {
                        let item_type = *item_type.clone();
                        mid_ast::Type::Tuple(vec![array_type, item_type])
                    } else {
                        panic!("internal type error");
                    }
                }
                A::Replace(hole_array_term, item_term) => {
                    let array_type = type_of_term(ctx.typedefs, locals, hole_array_term);
                    if let mid_ast::Type::HoleArray(ref item_type, var) = array_type {
                        let param_type = type_of_term(ctx.typedefs, locals, item_term);
                        equate_types(graph, &item_type, &param_type);
                        mid_ast::Type::Array(item_type.clone(), var)
                    } else {
                        panic!(
                            "internal type error: expected HoleArray, got {:?}",
                            &array_type
                        )
                    }
                }
            };
            let typefolded = match array_op {
                A::Construct(t, v, items) => {
                    A::Construct(t.clone(), v.clone(), items.iter().map(typefold).collect())
                }
                A::Item(array, idx) => A::Item(typefold(&array), typefold(&idx)),
                A::Len(array) => A::Len(typefold(&array)),
                A::Push(array, item) => A::Push(typefold(&array), typefold(&item)),
                A::Pop(array) => A::Pop(typefold(&array)),
                A::Replace(array, item) => A::Replace(typefold(&array), typefold(&item)),
            };
            (mid_ast::Expr::ArrayOp(typefolded), type_)
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
                let param_folded = typefold_term(ctx.typedefs, locals, &param);
                equate_types(graph, variant_type, &param_type);
                (
                    mid_ast::Expr::Ctor(type_id, variant_id, Some(param_folded)),
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
            let arg_folded = typefold_term(ctx.typedefs, locals, &arg_term);
            let (vars, result_type) = if let Some(funcdef) = ctx.scc_funcdefs.get(&func_id) {
                // If its in the same SCC, just unify the types
                equate_types(graph, &arg_type, &funcdef.arg_type);
                (mid_ast::ReprParams::Pending, funcdef.ret_type.clone())
            } else if let Some(signature) = &ctx.func_sigs[func_id.0] {
                // Othwerise, it's already been processed, so instantiate params
                unify_external_function_call(graph, ctx.typedefs, func_id, signature, &arg_type)
            } else {
                unreachable!()
            };
            (
                mid_ast::Expr::Call(purity, func_id, arg_folded, Some(vars)),
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

/// Computes type-folded names for Access terms
fn typefold_term<T>(
    typedefs: &[mid_ast::TypeDef<T>],
    locals: &[mid_ast::Type<SolverVarId>],
    term: &mid_ast::Term,
) -> mid_ast::Term {
    println!("Typefolding term {:?}", term);
    match term {
        mid_ast::Term::Access(local, path, None) => {
            let type_folded_path = type_fold(typedefs, &locals[local.0], &path);
            mid_ast::Term::Access(*local, path.clone(), Some(type_folded_path))
        }
        mid_ast::Term::Access(_, _, Some(_)) => {
            // The typefolded path should not have yet been initialized
            unreachable!()
        }
        mid_ast::Term::BoolLit(v) => mid_ast::Term::BoolLit(*v),
        mid_ast::Term::IntLit(v) => mid_ast::Term::IntLit(*v),
        mid_ast::Term::ByteLit(v) => mid_ast::Term::ByteLit(*v),
        mid_ast::Term::FloatLit(v) => mid_ast::Term::FloatLit(*v),
    }
}

fn type_fold<T, E>(
    typedefs: &[mid_ast::TypeDef<T>],
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

fn unify_external_function_call(
    graph: &mut ConstraintGraph<mid_ast::Constraint>,
    typedefs: &[mid_ast::TypeDef<mid_ast::RepParamId>],
    func_id: mid_ast::CustomFuncId, // FIXME rm
    func_sig: &Signature,
    arg_type: &mid_ast::Type<SolverVarId>,
) -> (mid_ast::ReprParams<SolverVarId>, mid_ast::Type<SolverVarId>) {
    // Unify actual argument's type with parameter type
    let vars = (0..func_sig.num_params)
        .map(|_| graph.new_var())
        .collect::<Vec<_>>();
    let param_type = substitute_vars(typedefs, &func_sig.arg_type, &vars);
    equate_types(graph, &param_type, arg_type);
    let ret_type = substitute_vars(typedefs, &func_sig.ret_type, &vars);
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
        T::Byte => T::Byte,
        T::Float => T::Float,
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
    locals: &[mid_ast::Type<SolverVarId>],
    term: &mid_ast::Term,
) -> mid_ast::Type<SolverVarId> {
    match term {
        mid_ast::Term::Access(mid_ast::LocalId(id), field_path, _) => {
            lookup_type_field(typedefs, &locals[*id], field_path.clone())
        }
        mid_ast::Term::BoolLit(_) => mid_ast::Type::Bool,
        mid_ast::Term::IntLit(_) => mid_ast::Type::Int,
        mid_ast::Term::ByteLit(_) => mid_ast::Type::Byte,
        mid_ast::Term::FloatLit(_) => mid_ast::Type::Float,
    }
}

// It is not allowed to lookup the type of a field which is an unparameterized variant;
// e.g. looking up the type of b.(True), getting the True variant of a boolean. Such
// a lookup never occurs.
pub fn lookup_type_field(
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
                let instantiated = instantiate_with(&typedefs[*type_id], repr_var_params.clone());
                if let Some(variant_type) = &instantiated.variants[variant_id] {
                    lookup_type_field(typedefs, variant_type, remaining_path)
                } else {
                    // The described variant is an unparameterized variant, like True or False.
                    unreachable!()
                }
            }
            _ => panic!(
                "internal error: field {:?} does not exist in type {:?}",
                &field_path, type_
            ),
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
        mid_ast::Type::Byte => mid_ast::Type::Byte,
        mid_ast::Type::Float => mid_ast::Type::Float,

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
        (T::Byte, T::Byte) => {}
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
        (_, _) => panic!("mismatched types: {:?} and {:?}", type_a, type_b),
    }
}
