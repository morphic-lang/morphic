use im_rc::OrdMap;

use crate::data::alias_annot_ast as alias;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast as annot;
use crate::field_path::translate_callee_cond;
use crate::util::disjunction::Disj;

pub fn translate_callee_status_cond(
    arg_id: flat::LocalId,
    arg_aliases: &OrdMap<alias::FieldPath, alias::LocalAliases>,
    arg_folded_aliases: &OrdMap<alias::FieldPath, alias::FoldedAliases>,
    arg_statuses: &OrdMap<alias::FieldPath, annot::LocalStatus>,
    callee_cond: &annot::MutationCondition,
) -> Disj<annot::MutationCondition> {
    match callee_cond {
        annot::MutationCondition::AliasCondition(alias_cond) => {
            translate_callee_cond(arg_id, arg_aliases, arg_folded_aliases, alias_cond)
                .into_mapped(annot::MutationCondition::AliasCondition)
        }

        annot::MutationCondition::ArgMutated(alias::ArgName(arg_path)) => {
            arg_statuses[arg_path].mutated_cond.clone()
        }
    }
}

pub fn translate_callee_status_cond_disj(
    arg_id: flat::LocalId,
    arg_aliases: &OrdMap<alias::FieldPath, alias::LocalAliases>,
    arg_folded_aliases: &OrdMap<alias::FieldPath, alias::FoldedAliases>,
    arg_statuses: &OrdMap<alias::FieldPath, annot::LocalStatus>,
    callee_cond: &Disj<annot::MutationCondition>,
) -> Disj<annot::MutationCondition> {
    callee_cond.flat_map(|cond| {
        translate_callee_status_cond(arg_id, arg_aliases, arg_folded_aliases, arg_statuses, cond)
    })
}
