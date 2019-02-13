// TODO: Should this be changed to HashSet?
use std::collections::{BTreeMap, VecDeque};

use crate::data::mono_ast as mono;
use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;

// TODO: Should we unify `ValInstances` and `TypeInstances` under a common abstraction?

#[derive(Clone, Debug)]
struct ValInstances {
    ids: BTreeMap<(res::CustomGlobalId, Vec<mono::Type>), mono::CustomGlobalId>,
    pending: VecDeque<(mono::CustomGlobalId, res::CustomGlobalId, Vec<mono::Type>)>,
}

#[derive(Clone, Debug)]
struct TypeInstances {
    ids: BTreeMap<(res::CustomTypeId, Vec<mono::Type>), mono::CustomTypeId>,
    pending: VecDeque<(mono::CustomTypeId, res::CustomTypeId, Vec<mono::Type>)>,
}

impl ValInstances {
    fn new() -> Self {
        ValInstances {
            ids: BTreeMap::new(),
            pending: VecDeque::new(),
        }
    }

    fn resolve(&mut self, id: res::CustomGlobalId, args: Vec<mono::Type>) -> mono::CustomGlobalId {
        let new_id_if_needed = mono::CustomGlobalId(self.ids.len());
        let pending = &mut self.pending; // Appease the borrow checker
        *self.ids.entry((id, args.clone())).or_insert_with(|| {
            pending.push_back((new_id_if_needed, id, args));
            new_id_if_needed
        })
    }

    fn pop_pending(
        &mut self,
    ) -> Option<(mono::CustomGlobalId, res::CustomGlobalId, Vec<mono::Type>)> {
        self.pending.pop_front()
    }
}

impl TypeInstances {
    fn new() -> Self {
        TypeInstances {
            ids: BTreeMap::new(),
            pending: VecDeque::new(),
        }
    }

    fn resolve(&mut self, id: res::CustomTypeId, args: Vec<mono::Type>) -> mono::CustomTypeId {
        let new_id_if_needed = mono::CustomTypeId(self.ids.len());
        let pending = &mut self.pending; // Appease the borrow checker
        *self.ids.entry((id, args.clone())).or_insert_with(|| {
            pending.push_back((new_id_if_needed, id, args));
            new_id_if_needed
        })
    }

    fn pop_pending(&mut self) -> Option<(mono::CustomTypeId, res::CustomTypeId, Vec<mono::Type>)> {
        self.pending.pop_front()
    }
}

fn resolve_expr(
    val_insts: &mut ValInstances,
    type_insts: &mut TypeInstances,
    inst_args: &[mono::Type],
    expr: &typed::Expr,
) -> mono::Expr {
    match expr {
        typed::Expr::Global(res::GlobalId::ArithOp(op), args) => {
            debug_assert!(args.is_empty());
            mono::Expr::ArithOp(*op)
        }

        typed::Expr::Global(res::GlobalId::ArrayOp(op), args) => {
            debug_assert_eq!(args.len(), 1);
            mono::Expr::ArrayOp(*op, resolve_type(type_insts, inst_args, &args[0]))
        }

        typed::Expr::Global(res::GlobalId::Ctor(res::TypeId::Bool, variant), args) => {
            debug_assert!(args.is_empty());

            let val = match variant {
                res::VariantId(0) => false,
                res::VariantId(1) => true,
                res::VariantId(_) => unreachable!(),
            };

            mono::Expr::BoolLit(val)
        }

        typed::Expr::Global(res::GlobalId::Ctor(res::TypeId::Custom(id), variant), args) => {
            let args_resolved = args
                .iter()
                .map(|arg| resolve_type(type_insts, inst_args, arg))
                .collect();

            let new_id = type_insts.resolve(*id, args_resolved);
            mono::Expr::Ctor(new_id, *variant)
        }

        typed::Expr::Global(res::GlobalId::Ctor(_, _), _) => unreachable!(),

        typed::Expr::Global(res::GlobalId::Custom(id), args) => {
            let args_resolved = args
                .iter()
                .map(|arg| resolve_type(type_insts, inst_args, arg))
                .collect();

            let new_id = val_insts.resolve(*id, args_resolved);
            mono::Expr::Global(new_id)
        }

        &typed::Expr::Local(id) => mono::Expr::Local(id),

        typed::Expr::Tuple(items) => mono::Expr::Tuple(
            items
                .iter()
                .map(|item| resolve_expr(val_insts, type_insts, inst_args, item))
                .collect(),
        ),

        typed::Expr::Lam(purity, pat, ret, body) => {
            let pat_resolved = resolve_pattern(type_insts, inst_args, pat);
            let ret_resolved = resolve_type(type_insts, inst_args, ret);
            let body_resolved = resolve_expr(val_insts, type_insts, inst_args, body);
            mono::Expr::Lam(*purity, pat_resolved, ret_resolved, Box::new(body_resolved))
        }

        typed::Expr::App(purity, func, arg) => {
            let func_resolved = resolve_expr(val_insts, type_insts, inst_args, func);
            let arg_resolved = resolve_expr(val_insts, type_insts, inst_args, arg);
            mono::Expr::App(*purity, Box::new(func_resolved), Box::new(arg_resolved))
        }

        typed::Expr::Match(discrim, cases) => {
            let discrim_resolved = resolve_expr(val_insts, type_insts, inst_args, discrim);

            let cases_resolved = cases
                .iter()
                .map(|(pat, body)| {
                    let pat_resolved = resolve_pattern(type_insts, inst_args, pat);
                    let body_resolved = resolve_expr(val_insts, type_insts, inst_args, body);
                    (pat_resolved, body_resolved)
                })
                .collect();

            mono::Expr::Match(Box::new(discrim_resolved), cases_resolved)
        }

        typed::Expr::Let(lhs, rhs, body) => {
            let lhs_resolved = resolve_pattern(type_insts, inst_args, lhs);
            let rhs_resolved = resolve_expr(val_insts, type_insts, inst_args, rhs);
            let body_resolved = resolve_expr(val_insts, type_insts, inst_args, body);

            mono::Expr::Let(
                lhs_resolved,
                Box::new(rhs_resolved),
                Box::new(body_resolved),
            )
        }

        typed::Expr::ArrayLit(type_, items) => {
            let type_resolved = resolve_type(type_insts, inst_args, type_);
            let item_resolved = items
                .iter()
                .map(|item| resolve_expr(val_insts, type_insts, inst_args, item))
                .collect();

            mono::Expr::ArrayLit(type_resolved, item_resolved)
        }

        &typed::Expr::IntLit(val) => mono::Expr::IntLit(val),
        &typed::Expr::FloatLit(val) => mono::Expr::FloatLit(val),
        typed::Expr::TextLit(val) => mono::Expr::TextLit(val.clone()),
    }
}

fn resolve_type(
    type_insts: &mut TypeInstances,
    inst_args: &[mono::Type],
    type_: &res::Type,
) -> mono::Type {
    // TODO: Make sure that sane argument count invariants are actually enforced during typechecking.
    match type_ {
        res::Type::Var(arg) => inst_args[arg.0].clone(),

        res::Type::App(res::TypeId::Bool, args) => {
            debug_assert!(args.is_empty());
            mono::Type::Bool
        }

        res::Type::App(res::TypeId::Int, args) => {
            debug_assert!(args.is_empty());
            mono::Type::Int
        }

        res::Type::App(res::TypeId::Float, args) => {
            debug_assert!(args.is_empty());
            mono::Type::Float
        }

        res::Type::App(res::TypeId::Text, args) => {
            debug_assert!(args.is_empty());
            mono::Type::Text
        }

        res::Type::App(res::TypeId::Array, args) => {
            debug_assert_eq!(args.len(), 1);
            mono::Type::Array(Box::new(resolve_type(type_insts, inst_args, &args[0])))
        }

        res::Type::App(res::TypeId::Custom(id), args) => {
            let args_resolved = args
                .iter()
                .map(|arg| resolve_type(type_insts, inst_args, arg))
                .collect();

            let new_id = type_insts.resolve(*id, args_resolved);

            mono::Type::Custom(new_id)
        }

        res::Type::Tuple(items) => {
            let items_resolved = items
                .iter()
                .map(|item| resolve_type(type_insts, inst_args, item))
                .collect();

            mono::Type::Tuple(items_resolved)
        }

        res::Type::Func(purity, arg, ret) => {
            let arg_resolved = resolve_type(type_insts, inst_args, arg);
            let ret_resolved = resolve_type(type_insts, inst_args, ret);
            mono::Type::Func(*purity, Box::new(arg_resolved), Box::new(ret_resolved))
        }
    }
}

fn resolve_pattern(
    type_insts: &mut TypeInstances,
    inst_args: &[mono::Type],
    pat: &typed::Pattern,
) -> mono::Pattern {
    match pat {
        typed::Pattern::Any(type_) => {
            mono::Pattern::Any(resolve_type(type_insts, inst_args, type_))
        }

        typed::Pattern::Var(type_) => {
            mono::Pattern::Var(resolve_type(type_insts, inst_args, type_))
        }

        typed::Pattern::Tuple(items) => {
            let items_resolved = items
                .iter()
                .map(|item| resolve_pattern(type_insts, inst_args, item))
                .collect();

            mono::Pattern::Tuple(items_resolved)
        }

        typed::Pattern::Ctor(res::TypeId::Bool, args, variant, None) => {
            debug_assert!(args.is_empty());

            let val = match variant {
                res::VariantId(0) => false,
                res::VariantId(1) => true,
                _ => unreachable!(),
            };

            mono::Pattern::BoolConst(val)
        }

        typed::Pattern::Ctor(res::TypeId::Custom(id), args, variant, content) => {
            let args_resolved = args
                .iter()
                .map(|arg| resolve_type(type_insts, inst_args, arg))
                .collect();

            let content_resolved = if let Some(content) = content {
                Some(Box::new(resolve_pattern(type_insts, inst_args, content)))
            } else {
                None
            };

            let new_id = type_insts.resolve(*id, args_resolved);

            mono::Pattern::Ctor(new_id, *variant, content_resolved)
        }

        typed::Pattern::Ctor(_, _, _, _) => unreachable!(),

        &typed::Pattern::IntConst(val) => mono::Pattern::IntConst(val),
        &typed::Pattern::FloatConst(val) => mono::Pattern::FloatConst(val),
        typed::Pattern::TextConst(text) => mono::Pattern::TextConst(text.clone()),
    }
}

fn resolve_val_def(
    val_insts: &mut ValInstances,
    type_insts: &mut TypeInstances,
    inst_args: &[mono::Type],
    def: &typed::ValDef,
) -> mono::ValDef {
    debug_assert_eq!(inst_args.len(), def.scheme.num_params);

    let type_resolved = resolve_type(type_insts, inst_args, &def.scheme.body);

    let body_resolved = resolve_expr(val_insts, type_insts, inst_args, &def.body);

    mono::ValDef {
        type_: type_resolved,
        body: body_resolved,
    }
}

fn resolve_typedef(
    type_insts: &mut TypeInstances,
    inst_args: &[mono::Type],
    typedef: &res::TypeDef,
) -> mono::TypeDef {
    debug_assert_eq!(inst_args.len(), typedef.num_params);

    let variants_resolved = typedef
        .variants
        .iter()
        .map(|variant| {
            if let Some(variant) = variant {
                Some(resolve_type(type_insts, inst_args, variant))
            } else {
                None
            }
        })
        .collect();

    mono::TypeDef {
        variants: variants_resolved,
    }
}

// TODO: Handle polymorphic recursion with a graceful error.  Currently, we enter an infinite loop
// and consume all available memory.

pub fn monomorphize(program: typed::Program) -> mono::Program {
    let mut val_insts = ValInstances::new();
    let mut type_insts = TypeInstances::new();

    let main_new_id = val_insts.resolve(program.main, vec![]);

    let mut val_defs_resolved = Vec::new();

    while let Some((mono::CustomGlobalId(new_idx), res::CustomGlobalId(orig_idx), inst_args)) =
        val_insts.pop_pending()
    {
        // We enqueue pending val defs to resolve in the order in which their ids are generated, so
        // this should always hold.  This allows us to insert resolved val defs at the appropriate
        // index simply by pushing them onto the end of the vector.
        assert_eq!(new_idx, val_defs_resolved.len());

        let def = &program.vals[orig_idx];

        let def_resolved = resolve_val_def(&mut val_insts, &mut type_insts, &inst_args, def);

        val_defs_resolved.push(def_resolved);
    }

    let mut typedefs_resolved = Vec::new();

    while let Some((mono::CustomTypeId(new_idx), res::CustomTypeId(orig_idx), inst_args)) =
        type_insts.pop_pending()
    {
        // Same as above
        assert_eq!(new_idx, typedefs_resolved.len());

        let typedef = &program.custom_types[orig_idx];

        let typedef_resolved = resolve_typedef(&mut type_insts, &inst_args, typedef);

        typedefs_resolved.push(typedef_resolved);
    }

    mono::Program {
        custom_types: typedefs_resolved,
        vals: val_defs_resolved,
        main: main_new_id,
    }
}
