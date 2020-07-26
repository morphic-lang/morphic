use im_rc::{vector, OrdMap, OrdSet, Vector};

use crate::data::fate_annot_ast as fate;
use crate::data::first_order_ast as first_ord;
use crate::data::mutation_annot_ast as mutation;
use crate::fixed_point::{annot_all, Signature, SignatureAssumptions};

impl Signature for fate::FuncDef {
    type Sig = fate::Fate;

    fn signature(&self) -> &Self::Sig {
        &self.arg_fate
    }
}

fn annot_func(
    orig: &mutation::Program,
    sigs: &SignatureAssumptions<first_ord::CustomFuncId, fate::FuncDef>,
    func_def: &mutation::FuncDef,
) -> fate::FuncDef {
    todo!()
}

fn annot_fates(program: mutation::Program) -> fate::Program {
    let funcs = annot_all(
        program.funcs.len(),
        |sig_assumptions, func| annot_func(&program, sig_assumptions, &program.funcs[func]),
        &program.sccs,
    );

    fate::Program {
        mod_symbols: program.mod_symbols,
        custom_types: program.custom_types,
        custom_type_symbols: program.custom_type_symbols,
        funcs,
        func_symbols: program.func_symbols,
        profile_points: program.profile_points,
        main: program.main,

        sccs: program.sccs,
    }
}
