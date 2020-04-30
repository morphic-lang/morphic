use crate::data::mono_ast as mono;
use crate::data::resolved_ast as res;
use crate::data::typed_ast as typed;
use crate::util::id_vec::IdVec;
use crate::util::instance_queue::InstanceQueue;

type ValInstances =
    InstanceQueue<(res::CustomGlobalId, IdVec<res::TypeParamId, mono::Type>), mono::CustomGlobalId>;

type TypeInstances =
    InstanceQueue<(res::CustomTypeId, IdVec<res::TypeParamId, mono::Type>), mono::CustomTypeId>;

fn resolve_expr(
    val_insts: &mut ValInstances,
    type_insts: &mut TypeInstances,
    inst_args: &IdVec<res::TypeParamId, mono::Type>,
    expr: &typed::Expr,
) -> mono::Expr {
    match expr {
        typed::Expr::Global(res::GlobalId::ArithOp(op), args) => {
            debug_assert!(args.is_empty());
            mono::Expr::ArithOp(*op)
        }

        typed::Expr::Global(res::GlobalId::ArrayOp(op), args) => {
            debug_assert_eq!(args.len(), 1);
            mono::Expr::ArrayOp(
                *op,
                resolve_type(type_insts, inst_args, &args[res::TypeParamId(0)]),
            )
        }

        typed::Expr::Global(res::GlobalId::IoOp(op), args) => {
            debug_assert!(args.is_empty());
            mono::Expr::IoOp(*op)
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
            let args_resolved = args.map(|_param_id, arg| resolve_type(type_insts, inst_args, arg));

            let new_id = type_insts.resolve((*id, args_resolved));
            mono::Expr::Ctor(new_id, *variant)
        }

        typed::Expr::Global(res::GlobalId::Ctor(_, _), _) => unreachable!(),

        typed::Expr::Global(res::GlobalId::Custom(id), args) => {
            let args_resolved = args.map(|_param_id, arg| resolve_type(type_insts, inst_args, arg));
            let new_id = val_insts.resolve((*id, args_resolved));
            mono::Expr::Global(new_id)
        }

        &typed::Expr::Local(id) => mono::Expr::Local(id),

        typed::Expr::Tuple(items) => mono::Expr::Tuple(
            items
                .iter()
                .map(|item| resolve_expr(val_insts, type_insts, inst_args, item))
                .collect(),
        ),

        typed::Expr::Lam(purity, arg_type, ret_type, pat, body) => {
            let pat_resolved = resolve_pattern(type_insts, inst_args, pat);
            let arg_type_resolved = resolve_type(type_insts, inst_args, arg_type);
            let ret_type_resolved = resolve_type(type_insts, inst_args, ret_type);
            let body_resolved = resolve_expr(val_insts, type_insts, inst_args, body);
            mono::Expr::Lam(
                *purity,
                arg_type_resolved,
                ret_type_resolved,
                pat_resolved,
                Box::new(body_resolved),
            )
        }

        typed::Expr::App(purity, func, arg) => {
            let func_resolved = resolve_expr(val_insts, type_insts, inst_args, func);
            let arg_resolved = resolve_expr(val_insts, type_insts, inst_args, arg);
            mono::Expr::App(*purity, Box::new(func_resolved), Box::new(arg_resolved))
        }

        typed::Expr::Match(discrim, cases, result_type) => {
            let discrim_resolved = resolve_expr(val_insts, type_insts, inst_args, discrim);

            let cases_resolved = cases
                .iter()
                .map(|(pat, body)| {
                    let pat_resolved = resolve_pattern(type_insts, inst_args, pat);
                    let body_resolved = resolve_expr(val_insts, type_insts, inst_args, body);
                    (pat_resolved, body_resolved)
                })
                .collect();

            let result_resolved = resolve_type(type_insts, inst_args, result_type);

            mono::Expr::Match(Box::new(discrim_resolved), cases_resolved, result_resolved)
        }

        typed::Expr::LetMany(bindings, body) => {
            let mut new_bindings = Vec::new();

            for (lhs, rhs) in bindings {
                let lhs_resolved = resolve_pattern(type_insts, inst_args, lhs);
                let rhs_resolved = resolve_expr(val_insts, type_insts, inst_args, rhs);

                new_bindings.push((lhs_resolved, rhs_resolved));
            }

            let body_resolved = resolve_expr(val_insts, type_insts, inst_args, body);

            mono::Expr::LetMany(new_bindings, Box::new(body_resolved))
        }

        typed::Expr::ArrayLit(type_, items) => {
            let type_resolved = resolve_type(type_insts, inst_args, type_);
            let item_resolved = items
                .iter()
                .map(|item| resolve_expr(val_insts, type_insts, inst_args, item))
                .collect();

            mono::Expr::ArrayLit(type_resolved, item_resolved)
        }

        &typed::Expr::ByteLit(val) => mono::Expr::ByteLit(val),
        &typed::Expr::IntLit(val) => mono::Expr::IntLit(val),
        &typed::Expr::FloatLit(val) => mono::Expr::FloatLit(val),

        typed::Expr::Span(_, _, content) => resolve_expr(val_insts, type_insts, inst_args, content),
    }
}

fn resolve_type(
    type_insts: &mut TypeInstances,
    inst_args: &IdVec<res::TypeParamId, mono::Type>,
    type_: &res::Type,
) -> mono::Type {
    // TODO: Make sure that sane argument count invariants are actually enforced during typechecking.
    match type_ {
        res::Type::Var(arg) => inst_args[arg].clone(),

        res::Type::App(res::TypeId::Bool, args) => {
            debug_assert!(args.is_empty());
            mono::Type::Bool
        }

        res::Type::App(res::TypeId::Byte, args) => {
            debug_assert!(args.is_empty());
            mono::Type::Byte
        }

        res::Type::App(res::TypeId::Int, args) => {
            debug_assert!(args.is_empty());
            mono::Type::Int
        }

        res::Type::App(res::TypeId::Float, args) => {
            debug_assert!(args.is_empty());
            mono::Type::Float
        }

        res::Type::App(res::TypeId::Array, args) => {
            debug_assert_eq!(args.len(), 1);
            mono::Type::Array(Box::new(resolve_type(type_insts, inst_args, &args[0])))
        }

        res::Type::App(res::TypeId::Custom(id), args) => {
            let args_resolved = IdVec::from_items(
                args.iter()
                    .map(|arg| resolve_type(type_insts, inst_args, arg))
                    .collect(),
            );

            let new_id = type_insts.resolve((*id, args_resolved));

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
    inst_args: &IdVec<res::TypeParamId, mono::Type>,
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
            let args_resolved = IdVec::from_items(
                args.iter()
                    .map(|arg| resolve_type(type_insts, inst_args, arg))
                    .collect(),
            );

            let content_resolved = if let Some(content) = content {
                Some(Box::new(resolve_pattern(type_insts, inst_args, content)))
            } else {
                None
            };

            let new_id = type_insts.resolve((*id, args_resolved));

            mono::Pattern::Ctor(new_id, *variant, content_resolved)
        }

        typed::Pattern::Ctor(_, _, _, _) => unreachable!(),

        &typed::Pattern::ByteConst(val) => mono::Pattern::ByteConst(val),
        &typed::Pattern::IntConst(val) => mono::Pattern::IntConst(val),
        &typed::Pattern::FloatConst(val) => mono::Pattern::FloatConst(val),

        typed::Pattern::Span(_, _, content) => resolve_pattern(type_insts, inst_args, content),
    }
}

fn resolve_val_def(
    val_insts: &mut ValInstances,
    type_insts: &mut TypeInstances,
    inst_args: &IdVec<res::TypeParamId, mono::Type>,
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
    inst_args: &IdVec<res::TypeParamId, mono::Type>,
    typedef: &res::TypeDef,
) -> mono::TypeDef {
    debug_assert_eq!(inst_args.len(), typedef.num_params);

    let variants_resolved = typedef.variants.map(|_id, variant| {
        if let Some(variant) = variant {
            Some(resolve_type(type_insts, inst_args, variant))
        } else {
            None
        }
    });

    mono::TypeDef {
        variants: variants_resolved,
    }
}

// TODO: Handle polymorphic recursion with a graceful error.  Currently, we enter an infinite loop
// and consume all available memory.

pub fn monomorphize(program: typed::Program) -> mono::Program {
    let mut val_insts = ValInstances::new();
    let mut type_insts = TypeInstances::new();

    let main_new_id = val_insts.resolve((program.main, IdVec::new()));

    let mut val_defs_resolved = IdVec::new();
    let mut val_defs_resolved_symbols = IdVec::new();

    while let Some((new_id, (orig_id, inst_args))) = val_insts.pop_pending() {
        let def = &program.vals[orig_id];

        let def_resolved = resolve_val_def(&mut val_insts, &mut type_insts, &inst_args, def);
        let def_resolved_symbols = mono::ValSymbols::Normal(mono::ValSymbolsInner {
            val_name: program.val_symbols[orig_id].val_name.clone(),
        });

        let pushed_val_id = val_defs_resolved.push(def_resolved);
        let pushed_val_symbols_id = val_defs_resolved_symbols.push(def_resolved_symbols);

        // We enqueue pending val defs to resolve in the order in which their ids are generated, so
        // this should always hold.  This allows us to insert resolved val defs at the appropriate
        // index simply by pushing them onto the end of the vector.
        assert_eq!(new_id, pushed_val_id);
        assert_eq!(new_id, pushed_val_symbols_id);
    }

    let mut typedefs_resolved = IdVec::new();
    let mut typedefs_resolved_symbols = IdVec::new();

    while let Some((new_id, (orig_id, inst_args))) = type_insts.pop_pending() {
        let typedef = &program.custom_types[orig_id];

        let typedef_resolved = resolve_typedef(&mut type_insts, &inst_args, typedef);

        let typedef_resolved_symbols = mono::TypeSymbols {
            type_name: program.custom_type_symbols[orig_id].type_name.clone(),
            variant_symbols: program.custom_type_symbols[orig_id].variant_symbols.clone(),
        };

        let pushed_type_id = typedefs_resolved.push(typedef_resolved);
        let pushed_type_symbols_id = typedefs_resolved_symbols.push(typedef_resolved_symbols);

        // These assertions are analogous to those in the val def case, described above
        assert_eq!(new_id, pushed_type_id);
        assert_eq!(new_id, pushed_type_symbols_id);
    }

    mono::Program {
        mod_symbols: program.mod_symbols.clone(),
        custom_types: typedefs_resolved,
        custom_type_symbols: typedefs_resolved_symbols,
        vals: val_defs_resolved,
        val_symbols: val_defs_resolved_symbols,
        main: main_new_id,
    }
}
