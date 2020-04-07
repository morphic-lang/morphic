use crate::data::first_order_ast as ast;
use crate::util::with_scope;

pub fn typecheck(program: &ast::Program) {
    for (_, func) in &program.funcs {
        typecheck_func(&program, func);
    }
}

fn typecheck_func(program: &ast::Program, func: &ast::FuncDef) {
    let mut locals = Vec::new();
    bind_pattern(program, &func.arg, &mut locals, &func.arg_type);
    assert_eq!(
        typecheck_expr(program, &mut locals, &func.body),
        func.ret_type
    );
}

fn typecheck_expr(
    program: &ast::Program,
    locals: &mut Vec<ast::Type>,
    expr: &ast::Expr,
) -> ast::Type {
    use ast::Expr as E;
    use ast::Type as T;

    match expr {
        E::ArithOp(ast::ArithOp::Op(num_type, _, v, w)) => {
            assert_eq!(typecheck_expr(program, locals, &**v), T::Num(*num_type));
            assert_eq!(typecheck_expr(program, locals, &**w), T::Num(*num_type));
            T::Num(*num_type)
        }
        E::ArithOp(ast::ArithOp::Cmp(num_type, _, v, w)) => {
            assert_eq!(typecheck_expr(program, locals, &**v), T::Num(*num_type));
            assert_eq!(typecheck_expr(program, locals, &**w), T::Num(*num_type));
            T::Bool
        }
        E::ArithOp(ast::ArithOp::Negate(num_type, v)) => {
            assert_eq!(typecheck_expr(program, locals, &**v), T::Num(*num_type));
            T::Num(*num_type)
        }
        E::ArrayOp(ast::ArrayOp::Item(item_type, array, index)) => {
            assert_eq!(
                typecheck_expr(program, locals, &**index),
                T::Num(ast::NumType::Int)
            );
            assert_eq!(
                typecheck_expr(program, locals, &**array),
                T::Array(Box::new(item_type.clone()))
            );
            T::Tuple(vec![
                item_type.clone(),
                T::HoleArray(Box::new(item_type.clone())),
            ])
        }
        E::ArrayOp(ast::ArrayOp::Len(item_type, array)) => {
            assert_eq!(
                typecheck_expr(program, locals, &**array),
                T::Array(Box::new(item_type.clone()))
            );
            T::Num(ast::NumType::Int)
        }
        E::ArrayOp(ast::ArrayOp::Push(item_type, array, item)) => {
            assert_eq!(&typecheck_expr(program, locals, &**item), item_type);
            let array_type = T::Array(Box::new(item_type.clone()));
            assert_eq!(&typecheck_expr(program, locals, &**array), &array_type);
            array_type
        }
        E::ArrayOp(ast::ArrayOp::Pop(item_type, array)) => {
            let array_type = T::Array(Box::new(item_type.clone()));
            assert_eq!(&typecheck_expr(program, locals, &**array), &array_type);
            T::Tuple(vec![array_type, item_type.clone()])
        }
        E::ArrayOp(ast::ArrayOp::Replace(item_type, hole_array, item)) => {
            let hole_array_t = T::HoleArray(Box::new(item_type.clone()));
            assert_eq!(
                &typecheck_expr(program, locals, &**hole_array),
                &hole_array_t
            );
            assert_eq!(&typecheck_expr(program, locals, &**item), item_type);
            T::Array(Box::new(item_type.clone()))
        }
        E::IoOp(ast::IoOp::Input) => T::Array(Box::new(T::Num(ast::NumType::Byte))),
        E::IoOp(ast::IoOp::Output(output)) => {
            assert_eq!(
                typecheck_expr(program, locals, &**output),
                T::Array(Box::new(T::Num(ast::NumType::Byte)))
            );
            T::Tuple(vec![])
        }
        E::Ctor(type_id, variant_id, expr) => {
            assert_eq!(
                program.custom_types[type_id].variants[variant_id],
                expr.as_ref().map(|e| typecheck_expr(program, locals, &**e)),
            );
            T::Custom(*type_id)
        }
        E::Local(local_id) => locals[local_id.0].clone(),
        E::Tuple(items) => {
            let item_types = items
                .iter()
                .map(|item| typecheck_expr(program, locals, item))
                .collect();
            T::Tuple(item_types)
        }
        E::Call(_purity, func_id, arg) => {
            assert_eq!(
                program.funcs[func_id].arg_type,
                typecheck_expr(program, locals, &**arg)
            );
            program.funcs[func_id].ret_type.clone()
        }
        E::Match(matched, branches, result_type) => {
            let matched_type = typecheck_expr(program, locals, matched);
            for (pattern, body) in branches {
                with_scope(locals, |sub_locals| {
                    bind_pattern(program, pattern, sub_locals, &matched_type);
                    assert_eq!(&typecheck_expr(program, sub_locals, body), result_type);
                });
            }
            result_type.clone()
        }
        E::LetMany(bindings, body) => with_scope(locals, |sub_locals| {
            for (lhs, rhs) in bindings {
                let rhs_type = typecheck_expr(program, sub_locals, rhs);
                bind_pattern(program, lhs, sub_locals, &rhs_type);
            }
            typecheck_expr(program, sub_locals, body)
        }),
        E::ArrayLit(item_type, items) => {
            for item in items {
                assert_eq!(&typecheck_expr(program, locals, item), item_type);
            }
            T::Array(Box::new(item_type.clone()))
        }
        E::BoolLit(_) => T::Bool,
        E::ByteLit(_) => T::Num(ast::NumType::Byte),
        E::IntLit(_) => T::Num(ast::NumType::Int),
        E::FloatLit(_) => T::Num(ast::NumType::Float),
    }
}

fn bind_pattern(
    program: &ast::Program,
    pattern: &ast::Pattern,
    locals: &mut Vec<ast::Type>,
    expected_type: &ast::Type,
) {
    use ast::Pattern as P;
    use ast::Type as T;
    match (pattern, expected_type) {
        (P::Any(_), _) => {}
        (P::Var(t), expected_t) => {
            assert_eq!(t, expected_t);
            locals.push(t.clone())
        }
        (P::Tuple(pats), T::Tuple(item_types)) => {
            assert_eq!(pats.len(), item_types.len());
            for (pat, expected_t) in pats.iter().zip(item_types) {
                bind_pattern(program, pat, locals, expected_t);
            }
        }
        (P::Ctor(type_id, variant_id, Some(arg_pat)), T::Custom(expected)) => {
            assert_eq!(type_id, expected);
            bind_pattern(
                program,
                arg_pat,
                locals,
                program.custom_types[type_id].variants[variant_id]
                    .as_ref()
                    .expect("pattern matched on params to nullary constructor"),
            );
        }
        (P::Ctor(type_id, variant_id, None), T::Custom(expected)) => {
            assert_eq!(type_id, expected);
            assert!(program.custom_types[type_id].variants[variant_id].is_none());
        }
        (P::BoolConst(_), T::Bool)
        | (P::ByteConst(_), T::Num(ast::NumType::Byte))
        | (P::IntConst(_), T::Num(ast::NumType::Int))
        | (P::FloatConst(_), T::Num(ast::NumType::Float)) => {}
        _ => {
            panic!("Pattern {:?} invalid for type {:?}", pattern, expected_type);
        }
    }
}
