use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast as mutation;
use crate::data::repr_constrained_ast as constrain;
use crate::data::repr_specialized_ast as special;
use crate::data::repr_unified_ast as unif;
use crate::util::id_vec::IdVec;
use crate::util::instance_queue::InstanceQueue;

type ValInstances = InstanceQueue<
    (
        first_ord::CustomFuncId,
        IdVec<unif::RepParamId, constrain::RepChoice>,
    ),
    special::CustomFuncId,
>;

type TypeInstances = InstanceQueue<
    (
        first_ord::CustomTypeId,
        IdVec<unif::RepParamId, constrain::RepChoice>,
    ),
    special::CustomTypeId,
>;

fn resolve_type<Rep>(
    type_insts: &mut TypeInstances,
    resolve_var: &impl for<'a> Fn(&'a Rep) -> constrain::RepChoice,
    type_: &unif::Type<Rep>,
) -> special::Type {
    match type_ {
        unif::Type::Bool => special::Type::Bool,
        unif::Type::Num(num_type) => special::Type::Num(*num_type),

        unif::Type::Array(rep_var, item_type) => special::Type::Array(
            resolve_var(rep_var),
            Box::new(resolve_type(type_insts, resolve_var, item_type)),
        ),

        unif::Type::HoleArray(rep_var, item_type) => special::Type::HoleArray(
            resolve_var(rep_var),
            Box::new(resolve_type(type_insts, resolve_var, item_type)),
        ),

        unif::Type::Tuple(items) => special::Type::Tuple(
            items
                .iter()
                .map(|item| resolve_type(type_insts, resolve_var, item))
                .collect(),
        ),

        unif::Type::Variants(variants) => special::Type::Variants(
            variants.map(|_, variant| resolve_type(type_insts, resolve_var, variant)),
        ),

        unif::Type::Custom(custom, rep_vars) => special::Type::Custom(
            type_insts.resolve((*custom, rep_vars.map(|_, var| resolve_var(var)))),
        ),
    }
}

fn resolve_body_type(
    type_insts: &mut TypeInstances,
    params: &IdVec<unif::RepParamId, constrain::RepChoice>,
    internal: &IdVec<unif::InternalRepVarId, constrain::RepChoice>,
    type_: &unif::Type<unif::RepSolution>,
) -> special::Type {
    resolve_type(
        type_insts,
        &|rep_var| resolve_solution(params, internal, *rep_var),
        type_,
    )
}

fn resolve_sig_type(
    type_insts: &mut TypeInstances,
    params: &IdVec<unif::RepParamId, constrain::RepChoice>,
    type_: &unif::Type<unif::RepParamId>,
) -> special::Type {
    resolve_type(type_insts, &|param| params[param], type_)
}

fn resolve_solution(
    params: &IdVec<unif::RepParamId, constrain::RepChoice>,
    internal: &IdVec<unif::InternalRepVarId, constrain::RepChoice>,
    solution: unif::RepSolution,
) -> constrain::RepChoice {
    match solution {
        unif::RepSolution::Internal(var) => internal[var],
        unif::RepSolution::Param(param) => params[param],
    }
}

fn resolve_condition(
    type_insts: &mut TypeInstances,
    params: &IdVec<unif::RepParamId, constrain::RepChoice>,
    internal: &IdVec<unif::InternalRepVarId, constrain::RepChoice>,
    cond: &unif::Condition<unif::RepSolution>,
) -> special::Condition {
    match cond {
        unif::Condition::Any => special::Condition::Any,

        unif::Condition::Tuple(items) => special::Condition::Tuple(
            items
                .iter()
                .map(|item| resolve_condition(type_insts, params, internal, item))
                .collect(),
        ),

        unif::Condition::Variant(variant, content_cond) => special::Condition::Variant(
            *variant,
            Box::new(resolve_condition(
                type_insts,
                params,
                internal,
                content_cond,
            )),
        ),

        unif::Condition::Custom(custom, rep_vars, content_cond) => special::Condition::Custom(
            type_insts.resolve((
                *custom,
                rep_vars.map(|_, rep_var| resolve_solution(params, internal, *rep_var)),
            )),
            Box::new(resolve_condition(
                type_insts,
                params,
                internal,
                content_cond,
            )),
        ),

        &unif::Condition::BoolConst(val) => special::Condition::BoolConst(val),
        &unif::Condition::ByteConst(val) => special::Condition::ByteConst(val),
        &unif::Condition::IntConst(val) => special::Condition::IntConst(val),
        &unif::Condition::FloatConst(val) => special::Condition::FloatConst(val),
    }
}

fn resolve_expr(
    func_insts: &mut ValInstances,
    type_insts: &mut TypeInstances,
    params: &IdVec<unif::RepParamId, constrain::RepChoice>,
    internal: &IdVec<unif::InternalRepVarId, constrain::RepChoice>,
    expr: &unif::Expr<unif::SolvedCall<unif::RepSolution>, unif::RepSolution>,
) -> special::Expr {
    match expr {
        unif::Expr::Local(local) => special::Expr::Local(*local),

        unif::Expr::Call(unif::SolvedCall(
            purity,
            func,
            rep_vars,
            _arg_aliases,
            _arg_folded_aliases,
            _arg_statuses,
            arg,
        )) => special::Expr::Call(
            *purity,
            func_insts.resolve((
                *func,
                rep_vars.map(|_, rep_var| resolve_solution(params, internal, *rep_var)),
            )),
            *arg,
        ),

        unif::Expr::Branch(discrim, cases, result_type) => special::Expr::Branch(
            *discrim,
            cases
                .iter()
                .map(|(cond, body)| {
                    (
                        resolve_condition(type_insts, params, internal, cond),
                        resolve_expr(func_insts, type_insts, params, internal, body),
                    )
                })
                .collect(),
            resolve_body_type(type_insts, params, internal, result_type),
        ),

        unif::Expr::LetMany(bindings, final_local) => special::Expr::LetMany(
            bindings
                .iter()
                .map(|(type_, binding)| {
                    (
                        resolve_body_type(type_insts, params, internal, type_),
                        resolve_expr(func_insts, type_insts, params, internal, binding),
                    )
                })
                .collect(),
            *final_local,
        ),

        unif::Expr::Tuple(items) => special::Expr::Tuple(items.clone()),
        unif::Expr::TupleField(tuple, idx) => special::Expr::TupleField(*tuple, *idx),

        unif::Expr::WrapVariant(variant_types, variant, content) => special::Expr::WrapVariant(
            variant_types.map(|_, type_| resolve_body_type(type_insts, params, internal, type_)),
            *variant,
            *content,
        ),

        unif::Expr::UnwrapVariant(variant, wrapped) => {
            special::Expr::UnwrapVariant(*variant, *wrapped)
        }

        unif::Expr::WrapCustom(custom, rep_vars, content) => special::Expr::WrapCustom(
            type_insts.resolve((
                *custom,
                rep_vars.map(|_, rep_var| resolve_solution(params, internal, *rep_var)),
            )),
            *content,
        ),

        unif::Expr::UnwrapCustom(custom, rep_vars, wrapped) => special::Expr::UnwrapCustom(
            type_insts.resolve((
                *custom,
                rep_vars.map(|_, rep_var| resolve_solution(params, internal, *rep_var)),
            )),
            *wrapped,
        ),

        &unif::Expr::ArithOp(op) => special::Expr::ArithOp(op),

        unif::Expr::ArrayOp(rep_var, item_type, _array_status, op) => special::Expr::ArrayOp(
            resolve_solution(params, internal, *rep_var),
            resolve_body_type(type_insts, params, internal, item_type),
            *op,
        ),

        unif::Expr::IOOp(rep_var, op) => {
            let resolved_var = resolve_solution(params, internal, *rep_var);
            let resolved_op = match op {
                mutation::IOOp::Input => flat::IOOp::Input,
                mutation::IOOp::Output(_, array) => flat::IOOp::Output(*array),
            };
            special::Expr::IoOp(resolved_var, resolved_op)
        }

        unif::Expr::ArrayLit(rep_var, item_type, items) => special::Expr::ArrayLit(
            resolve_solution(params, internal, *rep_var),
            resolve_body_type(type_insts, params, internal, item_type),
            items.clone(),
        ),

        &unif::Expr::BoolLit(val) => special::Expr::BoolLit(val),
        &unif::Expr::ByteLit(val) => special::Expr::ByteLit(val),
        &unif::Expr::IntLit(val) => special::Expr::IntLit(val),
        &unif::Expr::FloatLit(val) => special::Expr::FloatLit(val),
    }
}

pub fn specialize_reprs(program: constrain::Program) -> special::Program {
    let mut func_insts = InstanceQueue::new();
    let mut type_insts = InstanceQueue::new();

    debug_assert_eq!(program.funcs[program.main].num_params, 0);

    let main_new_id = func_insts.resolve((program.main, IdVec::new()));

    let mut funcs_resolved = IdVec::new();
    while let Some((new_id, (orig_id, inst_args))) = func_insts.pop_pending() {
        let orig_def = &program.funcs[orig_id];

        debug_assert_eq!(inst_args.len(), orig_def.num_params);

        let arg_resolved = resolve_sig_type(&mut type_insts, &inst_args, &orig_def.arg_type);
        let ret_resolved = resolve_sig_type(&mut type_insts, &inst_args, &orig_def.ret_type);
        let body_resolved = resolve_expr(
            &mut func_insts,
            &mut type_insts,
            &inst_args,
            &program.rep_constraints[orig_id].internal_vars,
            &orig_def.body,
        );

        let def_resolved = special::FuncDef {
            purity: orig_def.purity,
            arg_type: arg_resolved,
            ret_type: ret_resolved,
            body: body_resolved,
        };

        let pushed_func_id = funcs_resolved.push(def_resolved);

        // We enqueue pending function defs to resolve in the order in which their ids are
        // generated, so this should always hold.  This allows us to insert resolved val defs at the
        // appropriate index simply by pushing them onto the end of the vector.
        assert_eq!(new_id, pushed_func_id);
    }

    let mut types_resolved = IdVec::new();
    while let Some((new_id, (orig_id, inst_args))) = type_insts.pop_pending() {
        let orig_typedef = &program.custom_types[orig_id];

        let type_resolved = resolve_sig_type(&mut type_insts, &inst_args, &orig_typedef.content);

        let pushed_type_id = types_resolved.push(type_resolved);

        // See above comment in the function instance queue loop
        assert_eq!(new_id, pushed_type_id);
    }

    special::Program {
        custom_types: types_resolved,
        funcs: funcs_resolved,
        main: main_new_id,
    }
}
