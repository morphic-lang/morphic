use im_rc::{OrdMap, OrdSet};

use crate::data::alias_annot_ast as alias;
use crate::data::anon_sum_ast as anon;
use crate::data::first_order_ast as first_ord;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast as annot;
use crate::field_path::get_names_in;
use crate::fixed_point::{annot_all, Signature, SignatureAssumptions};
use crate::util::disjunction::Disj;

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
        custom_types: program.custom_types,
        funcs,
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
    val_statuses: OrdMap<alias::FieldPath, annot::LocalStatus>,
    mutations: Vec<(flat::LocalId, alias::FieldPath, Disj<alias::AliasCondition>)>,
}

#[allow(unused_variables)]
fn annot_expr(
    orig: &alias::Program,
    sigs: &SignatureAssumptions<first_ord::CustomFuncId, annot::FuncDef>,
    ctx: &OrdMap<flat::LocalId, LocalInfo>,
    expr: &alias::Expr,
) -> (annot::Expr, ExprInfo) {
    match expr {
        _ => unimplemented!(),
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
        mutation_sig,
        body: annot_body,
    }
}
