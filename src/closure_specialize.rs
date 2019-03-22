use std::collections::{BTreeMap, BTreeSet};

use crate::data::closure_annot_ast as annot;
use crate::data::closure_specialized_ast as special;
use crate::data::lambda_lifted_ast as lifted;
use crate::data::mono_ast as mono;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Request<T> {
    head: T,
    params: Vec<special::FuncRep>,
}

#[derive(Clone, Debug)]
struct Context<'a> {
    orig: &'a annot::Program,

    template_instances: BTreeMap<Request<annot::TemplateId>, special::FuncRep>,
    type_instances: BTreeMap<Request<mono::CustomTypeId>, special::CustomTypeId>,
    lam_instances: BTreeMap<Request<lifted::LamId>, special::LamId>,
    val_instances: BTreeMap<Request<mono::CustomGlobalId>, special::CustomGlobalId>,

    custom_types: Vec<Option<special::TypeDef>>,
    opaque_reps: Vec<Option<special::FuncRep>>,
    vals: Vec<Option<special::ValDef>>,
    lams: Vec<Option<special::LamDef>>,
}

fn fresh_id<T>(items: &mut Vec<Option<T>>) -> usize {
    let result = items.len();
    items.push(None);
    result
}

fn populate<T>(opt: &mut Option<T>, val: T) {
    debug_assert!(opt.is_none());
    *opt = Some(val);
}

impl<'a> Context<'a> {
    fn new(orig: &'a annot::Program) -> Self {
        Context {
            orig,

            template_instances: BTreeMap::new(),
            type_instances: BTreeMap::new(),
            lam_instances: BTreeMap::new(),
            val_instances: BTreeMap::new(),

            custom_types: Vec::new(),
            opaque_reps: Vec::new(),
            vals: Vec::new(),
            lams: Vec::new(),
        }
    }

    fn resolve_template(&mut self, request: Request<annot::TemplateId>) -> special::FuncRep {
        if let Some(existing) = self.template_instances.get(&request) {
            return existing.clone();
        }

        let template = &self.orig.templates[request.head.0];

        match template.in_cycle {
            annot::InCycle::NoCycle => {
                let mut rep = special::FuncRep(BTreeSet::new());

                for requirement in &template.requirements {
                    self.resolve_requirement(requirement, &request.params, &mut rep);
                }

                self.template_instances.insert(request, rep.clone());

                rep
            }

            annot::InCycle::Cycle => {
                let opaque_id = special::OpaqueFuncRepId(fresh_id(&mut self.opaque_reps));

                let external_rep = {
                    let mut external_rep = special::FuncRep(BTreeSet::new());
                    external_rep.0.insert(special::FuncCase::Opaque(opaque_id));
                    external_rep
                };

                self.template_instances
                    .insert(request.clone(), external_rep.clone());

                let mut internal_rep = special::FuncRep(BTreeSet::new());

                for requirement in &template.requirements {
                    self.resolve_requirement(requirement, &request.params, &mut internal_rep);
                }

                populate(&mut self.opaque_reps[opaque_id.0], internal_rep);

                external_rep
            }
        }
    }

    fn resolve_requirement(
        &mut self,
        requirement: &annot::Requirement,
        params: &[special::FuncRep],
        target_cases: &mut special::FuncRep,
    ) {
        match requirement {
            annot::Requirement::Lam(lam_id, lam_params) => {
                let resolved_lam_params = lam_params
                    .iter()
                    .map(|solution| self.resolve_solution(solution, params))
                    .collect();

                let resolved_lam = self.resolve_lam(Request {
                    head: *lam_id,
                    params: resolved_lam_params,
                });

                target_cases.0.insert(special::FuncCase::Lam(resolved_lam));
            }

            annot::Requirement::Template(template_id, template_params) => {
                let resolved_template_params = template_params
                    .iter()
                    .map(|solution| self.resolve_solution(solution, params))
                    .collect();

                let resolved_template = self.resolve_template(Request {
                    head: *template_id,
                    params: resolved_template_params,
                });

                target_cases.0.extend(resolved_template.0);
            }

            annot::Requirement::ArithOp(op) => {
                target_cases.0.insert(special::FuncCase::ArithOp(*op));
            }

            annot::Requirement::ArrayOp(op, item_type) => {
                let resolved_item_type = self.resolve_type(item_type, params);

                target_cases
                    .0
                    .insert(special::FuncCase::ArrayOp(*op, resolved_item_type));
            }

            annot::Requirement::ArrayReplace(item_type) => {
                let resolved_item_type = self.resolve_type(item_type, params);

                target_cases
                    .0
                    .insert(special::FuncCase::ArrayReplace(resolved_item_type));
            }

            annot::Requirement::Ctor(custom, type_params, variant) => {
                let resolved_type_params = type_params
                    .iter()
                    .map(|solution| self.resolve_solution(solution, params))
                    .collect();

                let resolved_custom = self.resolve_custom_type(Request {
                    head: *custom,
                    params: resolved_type_params,
                });

                target_cases
                    .0
                    .insert(special::FuncCase::Ctor(resolved_custom, *variant));
            }
        }
    }

    fn resolve_solution(
        &mut self,
        solution: &annot::Solution,
        params: &[special::FuncRep],
    ) -> special::FuncRep {
        match solution {
            annot::Solution::Param(param) => params[param.0].clone(),

            annot::Solution::MinSolutionTo(template_id, template_params) => {
                self.resolve_template(Request {
                    head: *template_id,
                    params: template_params
                        .iter()
                        .map(|param| params[param.0].clone())
                        .collect(),
                })
            }
        }
    }

    fn resolve_lam(&mut self, request: Request<lifted::LamId>) -> special::LamId {
        if let Some(existing) = self.lam_instances.get(&request) {
            return existing.clone();
        }

        let lam_id = special::LamId(fresh_id(&mut self.lams));
        self.lam_instances.insert(request.clone(), lam_id);

        let lam = &self.orig.lams[request.head.0];

        debug_assert_eq!(lam.params.num_params(), request.params.len());

        let resolved_captures = lam
            .captures
            .iter()
            .map(|capture| self.resolve_sig_type(capture, &request.params))
            .collect();

        let resolved_arg = self.resolve_sig_type(&lam.arg, &request.params);

        let resolved_ret = self.resolve_sig_type(&lam.ret, &request.params);

        let resolved_arg_pat = self.resolve_pattern(&lam.arg_pat, &request.params);

        let resolved_body = self.resolve_expr(&lam.body, &request.params);

        let resolved_lam = special::LamDef {
            purity: lam.purity,
            captures: resolved_captures,
            arg: resolved_arg,
            ret: resolved_ret,
            arg_pat: resolved_arg_pat,
            body: resolved_body,
        };

        populate(&mut self.lams[lam_id.0], resolved_lam);

        lam_id
    }

    fn resolve_type_generic<Rep, F>(
        &mut self,
        type_: &annot::Type<Rep>,
        resolve_rep: &mut F,
    ) -> special::Type
    where
        F: for<'b> FnMut(&'b mut Self, &'b Rep) -> special::FuncRep,
    {
        match type_ {
            annot::Type::Bool => special::Type::Bool,
            annot::Type::Int => special::Type::Int,
            annot::Type::Float => special::Type::Float,
            annot::Type::Text => special::Type::Text,

            annot::Type::Array(item_type) => {
                special::Type::Array(Box::new(self.resolve_type_generic(item_type, resolve_rep)))
            }

            annot::Type::Tuple(items) => special::Type::Tuple(
                items
                    .iter()
                    .map(|item| self.resolve_type_generic(item, resolve_rep))
                    .collect(),
            ),

            annot::Type::Func(_purity, rep, _arg, _ret) => {
                special::Type::Func(resolve_rep(self, rep))
            }

            annot::Type::Custom(custom, custom_params) => {
                let resolved_reps = custom_params
                    .iter()
                    .map(|rep| resolve_rep(self, rep))
                    .collect();

                let resolved_custom = self.resolve_custom_type(Request {
                    head: *custom,
                    params: resolved_reps,
                });

                special::Type::Custom(resolved_custom)
            }
        }
    }

    fn resolve_type(
        &mut self,
        type_: &annot::Type<annot::Solution>,
        params: &[special::FuncRep],
    ) -> special::Type {
        self.resolve_type_generic(type_, &mut |ctx, solution| {
            ctx.resolve_solution(solution, params)
        })
    }

    fn resolve_sig_type(
        &mut self,
        type_: &annot::Type<annot::RepParamId>,
        params: &[special::FuncRep],
    ) -> special::Type {
        self.resolve_type_generic(type_, &mut |_, param| params[param.0].clone())
    }

    fn resolve_custom_type(
        &mut self,
        request: Request<mono::CustomTypeId>,
    ) -> special::CustomTypeId {
        if let Some(&existing) = self.type_instances.get(&request) {
            return existing;
        }

        let custom_id = special::CustomTypeId(fresh_id(&mut self.custom_types));
        self.type_instances.insert(request.clone(), custom_id);

        let typedef = &self.orig.custom_types[request.head.0];

        debug_assert_eq!(typedef.num_params, request.params.len());

        let resolved_variants = typedef
            .variants
            .iter()
            .map(|content| {
                content
                    .as_ref()
                    .map(|content| self.resolve_sig_type(content, &request.params))
            })
            .collect();

        let resolved_typedef = special::TypeDef {
            variants: resolved_variants,
        };

        populate(&mut self.custom_types[custom_id.0], resolved_typedef);

        custom_id
    }

    fn resolve_pattern(
        &mut self,
        pat: &annot::Pattern,
        params: &[special::FuncRep],
    ) -> special::Pattern {
        match pat {
            annot::Pattern::Any(type_) => special::Pattern::Any(self.resolve_type(type_, params)),

            annot::Pattern::Var(type_) => special::Pattern::Var(self.resolve_type(type_, params)),

            annot::Pattern::Tuple(items) => special::Pattern::Tuple(
                items
                    .iter()
                    .map(|item| self.resolve_pattern(item, params))
                    .collect(),
            ),

            annot::Pattern::Ctor(custom, custom_params, variant, content) => {
                let resolved_custom_params = custom_params
                    .iter()
                    .map(|solution| self.resolve_solution(solution, params))
                    .collect();

                let resolved_custom = self.resolve_custom_type(Request {
                    head: *custom,
                    params: resolved_custom_params,
                });

                let resolved_content = content
                    .as_ref()
                    .map(|content| Box::new(self.resolve_pattern(content, params)));

                special::Pattern::Ctor(resolved_custom, *variant, resolved_content)
            }

            &annot::Pattern::BoolConst(val) => special::Pattern::BoolConst(val),

            &annot::Pattern::IntConst(val) => special::Pattern::IntConst(val),

            &annot::Pattern::FloatConst(val) => special::Pattern::FloatConst(val),

            annot::Pattern::TextConst(text) => special::Pattern::TextConst(text.clone()),
        }
    }

    fn resolve_expr(&mut self, expr: &annot::Expr, params: &[special::FuncRep]) -> special::Expr {
        match expr {
            annot::Expr::ArithOp(op, solution) => {
                special::Expr::ArithOp(*op, self.resolve_solution(solution, params))
            }

            annot::Expr::ArrayOp(op, item_type, solution) => special::Expr::ArrayOp(
                *op,
                self.resolve_type(item_type, params),
                self.resolve_solution(solution, params),
            ),

            annot::Expr::NullaryCtor(custom, custom_params, variant) => {
                let resolved_custom_params = custom_params
                    .iter()
                    .map(|solution| self.resolve_solution(solution, params))
                    .collect();

                let resolved_custom = self.resolve_custom_type(Request {
                    head: *custom,
                    params: resolved_custom_params,
                });

                special::Expr::NullaryCtor(resolved_custom, *variant)
            }

            annot::Expr::Ctor(custom, custom_params, variant, solution) => {
                let resolved_custom_params = custom_params
                    .iter()
                    .map(|solution| self.resolve_solution(solution, params))
                    .collect();

                let resolved_custom = self.resolve_custom_type(Request {
                    head: *custom,
                    params: resolved_custom_params,
                });

                let resolved_rep = self.resolve_solution(solution, params);

                special::Expr::Ctor(resolved_custom, *variant, resolved_rep)
            }

            annot::Expr::Global(val_id, val_params) => {
                let resolved_val_params = val_params
                    .iter()
                    .map(|solution| self.resolve_solution(solution, params))
                    .collect();

                let resolved_val_id = self.resolve_val(Request {
                    head: *val_id,
                    params: resolved_val_params,
                });

                special::Expr::Global(resolved_val_id)
            }

            &annot::Expr::Local(local) => special::Expr::Local(local),

            &annot::Expr::Capture(capture) => special::Expr::Capture(capture),

            annot::Expr::Tuple(items) => special::Expr::Tuple(
                items
                    .iter()
                    .map(|item| self.resolve_expr(item, params))
                    .collect(),
            ),

            annot::Expr::Lam(lam_id, lam_params, rep, captures) => {
                let resolved_lam_params = lam_params
                    .iter()
                    .map(|solution| self.resolve_solution(solution, params))
                    .collect();

                let resolved_lam_id = self.resolve_lam(Request {
                    head: *lam_id,
                    params: resolved_lam_params,
                });

                let resolved_rep = self.resolve_solution(rep, params);

                let resolved_captures = captures
                    .iter()
                    .map(|capture| self.resolve_expr(capture, params))
                    .collect();

                special::Expr::Lam(resolved_lam_id, resolved_rep, resolved_captures)
            }

            annot::Expr::App(purity, func_rep, func, arg) => {
                let resolved_func_rep = self.resolve_solution(func_rep, params);

                let resolved_func = self.resolve_expr(func, params);

                let resolved_arg = self.resolve_expr(arg, params);

                special::Expr::App(
                    *purity,
                    resolved_func_rep,
                    Box::new(resolved_func),
                    Box::new(resolved_arg),
                )
            }

            annot::Expr::Match(discrim, cases, result_type) => {
                let resolved_discrim = self.resolve_expr(discrim, params);

                let resolved_cases = cases
                    .iter()
                    .map(|(pat, body)| {
                        let resolved_pat = self.resolve_pattern(pat, params);
                        let resolved_body = self.resolve_expr(body, params);
                        (resolved_pat, resolved_body)
                    })
                    .collect();

                let resolved_result_type = self.resolve_type(result_type, params);

                special::Expr::Match(
                    Box::new(resolved_discrim),
                    resolved_cases,
                    resolved_result_type,
                )
            }

            annot::Expr::Let(lhs, rhs, body) => {
                let resolved_lhs = self.resolve_pattern(lhs, params);

                let resolved_rhs = self.resolve_expr(rhs, params);

                let resolved_body = self.resolve_expr(body, params);

                special::Expr::Let(
                    resolved_lhs,
                    Box::new(resolved_rhs),
                    Box::new(resolved_body),
                )
            }

            annot::Expr::ArrayLit(item_type, items) => {
                let resolved_item_type = self.resolve_type(item_type, params);

                let resolved_items = items
                    .iter()
                    .map(|item| self.resolve_expr(item, params))
                    .collect();

                special::Expr::ArrayLit(resolved_item_type, resolved_items)
            }

            &annot::Expr::BoolLit(val) => special::Expr::BoolLit(val),

            &annot::Expr::IntLit(val) => special::Expr::IntLit(val),

            &annot::Expr::FloatLit(val) => special::Expr::FloatLit(val),

            annot::Expr::TextLit(text) => special::Expr::TextLit(text.clone()),
        }
    }

    fn resolve_val(&mut self, request: Request<mono::CustomGlobalId>) -> special::CustomGlobalId {
        if let Some(&existing) = self.val_instances.get(&request) {
            return existing;
        }

        let val_id = special::CustomGlobalId(fresh_id(&mut self.vals));
        self.val_instances.insert(request.clone(), val_id);

        let val_def = &self.orig.vals[request.head.0];

        debug_assert_eq!(val_def.params.num_params(), request.params.len());

        let resolved_type = self.resolve_sig_type(&val_def.type_, &request.params);

        let resolved_body = self.resolve_expr(&val_def.body, &request.params);

        let resolved_val_def = special::ValDef {
            type_: resolved_type,
            body: resolved_body,
        };

        populate(&mut self.vals[val_id.0], resolved_val_def);

        val_id
    }
}

pub fn closure_specialize(program: annot::Program) -> special::Program {
    let mut ctx = Context::new(&program);

    let main_def = &program.vals[program.main.0];

    // TODO: Using an opaque representation to monomorphize every representation parameter in main's
    // SCC is a hack to avoid doing proper analysis of the dependencies among these representation
    // variables.  There should be some way to do this dependency analysis during the prior closure
    // annotation pass.

    let main_param_opaque_ids: Vec<_> = (0..main_def.params.num_params())
        .map(|_| special::OpaqueFuncRepId(fresh_id(&mut ctx.opaque_reps)))
        .collect();

    let main_param_opaque_reps: Vec<_> = main_param_opaque_ids
        .iter()
        .map(|&opaque_id| {
            let mut param_rep = special::FuncRep(BTreeSet::new());
            param_rep.0.insert(special::FuncCase::Opaque(opaque_id));
            param_rep
        })
        .collect();

    for (opaque_id, (template_id, template_params)) in main_param_opaque_ids
        .iter()
        .zip(main_def.params.requirements.iter())
    {
        let resolved_template_params = template_params
            .iter()
            .map(|param| main_param_opaque_reps[param.0].clone())
            .collect();

        let rep = ctx.resolve_template(Request {
            head: *template_id,
            params: resolved_template_params,
        });

        populate(&mut ctx.opaque_reps[opaque_id.0], rep);
    }

    let resolved_main_id = ctx.resolve_val(Request {
        head: program.main,
        params: main_param_opaque_reps,
    });

    special::Program {
        custom_types: ctx.custom_types.into_iter().map(Option::unwrap).collect(),
        opaque_reps: ctx.opaque_reps.into_iter().map(Option::unwrap).collect(),
        vals: ctx.vals.into_iter().map(Option::unwrap).collect(),
        lams: ctx.lams.into_iter().map(Option::unwrap).collect(),
        main: resolved_main_id,
    }
}
