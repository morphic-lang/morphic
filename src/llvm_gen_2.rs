use crate::{
    builtins::{flat_array, persistent_array, zero_sized_array},
    data::{
        first_order_ast as first_ord,
        low_ast_2::{FuncDef, FuncId, IsZeroSized, Program, Type, TypeDef, TypeId},
        repr_constrained_ast::RepChoice,
    },
    util::{id_type::Id, id_vec::IdVec},
};
use inkwell::{
    context::Context,
    module::Module,
    targets::TargetMachine,
    types::{BasicTypeEnum, StructType},
    values::FunctionValue,
};
use std::collections::BTreeMap;

fn collect_ids<K: Id, V>(map: BTreeMap<K, V>) -> IdVec<K, V> {
    let expected = map
        .iter()
        .next_back()
        .map(|(id, _)| id.to_index() + 1)
        .unwrap_or(0);
    assert!(
        expected == map.len(),
        "non-contiguous identifiers declared during LLVM generation"
    );
    IdVec::from_items(map.into_iter().map(|(_, v)| v).collect())
}

fn decl_type<'ctx>(
    def: &TypeDef,
    context: &'ctx Context,
    decls: &mut BTreeMap<TypeId, StructType<'ctx>>,
) {
    let mut declare = |type_id| {
        decls.insert(
            type_id,
            context.opaque_struct_type(&format!("type_{}", type_id.0)),
        );
    };

    match def {
        TypeDef::ArrayTypeDef(t) => {
            declare(t.array_type.0);
            declare(t.hole_array_type.0);
        }
        TypeDef::BoxedTypeDef(t) => {
            declare(t.boxed_type.0);
        }
        TypeDef::CustomTypeDef(t) => {
            declare(t.custom_type.0);
        }
        TypeDef::VariantTypeDef(t) => {
            declare(t.variant_type.0);
        }
    }
}

fn get_llvm_type<'ctx>(
    context: &'ctx Context,
    custom_types: &IdVec<TypeId, StructType<'ctx>>,
    type_: &Type,
) -> BasicTypeEnum<'ctx> {
    match type_ {
        Type::Bool => context.bool_type().into(),
        Type::Num(first_ord::NumType::Byte) => context.i8_type().into(),
        Type::Num(first_ord::NumType::Int) => context.i64_type().into(),
        Type::Num(first_ord::NumType::Float) => context.f64_type().into(),
        Type::Tuple(fields) => {
            let fields = fields
                .iter()
                .map(|type_| get_llvm_type(context, custom_types, type_))
                .collect::<Vec<_>>();
            context.struct_type(&fields, false).into()
        }
        Type::Opaque(id) => custom_types[id].into(),
    }
}

fn def_type<'ctx>(def: &TypeDef, context: &'ctx Context, decls: &IdVec<TypeId, StructType<'ctx>>) {
    match def {
        TypeDef::ArrayTypeDef(t) => {
            let array_id = t.array_type.0;
            let hole_id = t.hole_array_type.0;
            let item_type = &t.item_type;
            match t.item_zero_sized {
                IsZeroSized::ZeroSized => {
                    zero_sized_array::def_types(&decls[array_id], &decls[hole_id])
                }
                IsZeroSized::NonZeroSized => match t.rep {
                    RepChoice::OptimizedMut => {
                        flat_array::def_types(&decls[array_id], &decls[hole_id], item_type)
                    }
                    RepChoice::FallbackImmut => {
                        persistent_array::def_types(&decls[array_id], &decls[hole_id], item_type)
                    }
                },
            }
        }
        TypeDef::BoxedTypeDef(t) => decls[t.array_type.0].set_body(&[]),
        TypeDef::CustomTypeDef(t) => {
            todo!()
        }
        TypeDef::VariantTypeDef(t) => {
            todo!()
        }
    }
}

fn decl_func<'ctx>(
    def: &FuncDef,
    module: &Module<'ctx>,
    decls: &mut BTreeMap<FuncId, FunctionValue<'ctx>>,
) {
}

fn def_func<'ctx>(def: &FuncDef, decls: &IdVec<FuncId, FunctionValue<'ctx>>) {}

fn gen_program<'ctx>(
    prog: Program,
    context: &'ctx Context,
    machine: &TargetMachine,
) -> Module<'ctx> {
    let module = context.create_module("module");
    module.set_triple(&machine.get_triple());
    module.set_data_layout(&machine.get_target_data().get_data_layout());

    let mut types = BTreeMap::new();
    for def in &prog.type_defs {
        decl_type(def, context, &mut types);
    }

    let types = collect_ids(types);
    for def in &prog.type_defs {
        def_type(def, context, &types);
    }

    let mut funcs = BTreeMap::new();
    for def in &prog.func_defs {
        decl_func(def, &module, &mut funcs);
    }

    let funcs = collect_ids(funcs);
    for def in &prog.func_defs {
        def_func(def, &funcs);
    }

    module
}
