use im_rc::OrdMap;

use crate::data::alias_annot_ast as alias;
use crate::data::flat_ast as flat;
use crate::data::mutation_annot_ast as annot;
use crate::data::rc_specialized_ast as rc;
use crate::field_path::translate_callee_cond;
use crate::util::disjunction::Disj;
use crate::util::norm_pair::NormPair;

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

// TODO: Can we find a better name for this function?
pub fn translate_callee_status_cond_post_rc(
    arg_aliases: &rc::ArgAliases,
    arg_statuses: &OrdMap<alias::FieldPath, annot::LocalStatus>,
    callee_cond: &annot::MutationCondition,
) -> Disj<annot::MutationCondition> {
    match callee_cond {
        annot::MutationCondition::AliasCondition(alias_cond) => {
            let opt_cond = match alias_cond {
                alias::AliasCondition::AliasInArg(arg_pair) => {
                    let alias::ArgName(arg_pair_fst) = arg_pair.fst();
                    let alias::ArgName(arg_pair_snd) = arg_pair.snd();

                    arg_aliases
                        .aliases
                        .get(&NormPair::new(arg_pair_fst.clone(), arg_pair_snd.clone()))
                }

                alias::AliasCondition::FoldedAliasInArg(
                    alias::ArgName(fold_point),
                    sub_path_pair,
                ) => arg_aliases.folded_aliases[fold_point]
                    .inter_elem_aliases
                    .get(sub_path_pair),
            };

            opt_cond
                .cloned()
                .unwrap_or_default()
                .into_mapped(annot::MutationCondition::AliasCondition)
        }

        annot::MutationCondition::ArgMutated(alias::ArgName(arg_path)) => {
            arg_statuses[arg_path].mutated_cond.clone()
        }
    }
}

// TODO: Can we find a better name for this function?
pub fn translate_callee_status_cond_disj_post_rc(
    arg_aliases: &rc::ArgAliases,
    arg_statuses: &OrdMap<alias::FieldPath, annot::LocalStatus>,
    callee_cond: &Disj<annot::MutationCondition>,
) -> Disj<annot::MutationCondition> {
    callee_cond
        .flat_map(|cond| translate_callee_status_cond_post_rc(arg_aliases, arg_statuses, cond))
}
