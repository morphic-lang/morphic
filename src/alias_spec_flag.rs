use std::collections::BTreeMap;

use crate::data::alias_annot_ast as alias;
use crate::data::alias_specialized_ast as spec;
use crate::util::disjunction::Disj;

pub fn lookup_concrete_cond(
    aliases: &BTreeMap<alias::AliasCondition, spec::ConcreteAlias>,
    symbolic: &Disj<alias::AliasCondition>,
) -> bool {
    match symbolic {
        Disj::True => true,
        Disj::Any(conds) => conds
            .iter()
            .any(|cond| aliases[cond] == spec::ConcreteAlias::MayAlias),
    }
}
