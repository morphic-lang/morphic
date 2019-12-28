use crate::data::first_order_ast as first_ord;
use crate::data::repr_constrained_ast as constrain;
use crate::data::repr_unified_ast as unif;
use crate::fixed_point::{annot_all, Signature, SignatureAssumptions};
use crate::util::id_vec::IdVec;

impl Signature for constrain::FuncRepConstraints {
    type Sig = IdVec<unif::RepParamId, constrain::ParamConstraints>;

    fn signature(&self) -> &Self::Sig {
        &self.param_constraints
    }
}

#[allow(unused_variables)]
fn constrain_func(
    sigs: &SignatureAssumptions<first_ord::CustomFuncId, constrain::FuncRepConstraints>,
    func_def: &unif::FuncDef,
) -> constrain::FuncRepConstraints {
    unimplemented!()
}

pub fn constrain_reprs(program: unif::Program) -> constrain::Program {
    let rep_constraints = annot_all(
        program.funcs.len(),
        |sigs, func| constrain_func(sigs, &program.funcs[func]),
        &program.sccs,
    );

    constrain::Program {
        custom_types: program.custom_types,
        funcs: program.funcs,
        rep_constraints,
        main: program.main,
    }
}
