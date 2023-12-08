use crate::data::first_order_ast::NumType;
use crate::data::rc_specialized_ast::LocalId;
use crate::data::rc_specialized_ast::RcOp;
use crate::data::repr_constrained_ast::RepChoice;
use crate::data::repr_specialized_ast::Condition;
use crate::data::repr_specialized_ast::CustomFuncId;
use crate::data::repr_specialized_ast::CustomTypeId;
use crate::data::repr_specialized_ast::Expr;
use crate::data::repr_specialized_ast::FuncDef;
use crate::data::repr_specialized_ast::IoOp;
use crate::data::repr_specialized_ast::Program;
use crate::data::repr_specialized_ast::Type;
use crate::data::repr_unified_ast::ArrayOp;
use crate::intrinsic_config::intrinsic_to_name;
use crate::pretty_print::utils::{CustomTypeRenderer, FuncRenderer};
use std::io;
use std::io::Write;

const TAB_SIZE: usize = 2;

#[derive(Clone, Debug, Copy)]
struct Context<'a> {
    type_renderer: &'a CustomTypeRenderer,
    func_renderer: &'a FuncRenderer<CustomFuncId>,
    indentation: usize,
    num_locals: usize,
}

impl<'a> Context<'a> {
    fn add_indent(&self) -> Context {
        Context {
            indentation: self.indentation + TAB_SIZE,
            ..*self
        }
    }

    fn writeln(&self, w: &mut dyn Write) -> io::Result<()> {
        writeln![w]?;
        write![w, "{}", " ".repeat(self.indentation)]
    }
}

fn write_condition(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer,
    condition: &Condition,
) -> io::Result<()> {
    match condition {
        Condition::Any => write![w, "_",],
        Condition::Tuple(conditions) => {
            if conditions.len() == 0 {
                write![w, "()"]?;
            } else if conditions.len() == 1 {
                write![w, "("]?;
                write_condition(w, type_renderer, &conditions[0])?;
                write![w, ",)"]?
            } else {
                write![w, "("]?;
                for condition in &conditions[..conditions.len() - 1] {
                    write_condition(w, type_renderer, condition)?;
                    write![w, ", "]?;
                }
                write_condition(w, type_renderer, &conditions[conditions.len() - 1])?;
                write![w, ")"]?;
            }
            Ok(())
        }
        Condition::Variant(variant_id, subcondition) => {
            write![w, "variant {} (", variant_id.0]?;
            write_condition(w, type_renderer, subcondition)?;
            write![w, ")"]?;
            Ok(())
        }
        Condition::Boxed(subcondition, _content_type) => {
            write![w, "boxed ("]?;
            write_condition(w, type_renderer, subcondition)?;
            write![w, ")"]?;
            Ok(())
        }
        Condition::Custom(type_id, subcondition) => {
            write![w, "custom {} (", type_renderer.render(type_id)]?;
            write_condition(w, type_renderer, subcondition)?;
            write![w, ")"]?;
            Ok(())
        }
        Condition::BoolConst(val) => write![w, "{}", if *val { "True" } else { "False" }],
        Condition::ByteConst(val) => write![w, "{:?}", *val as char],
        Condition::IntConst(val) => write![w, "{}", val],
        Condition::FloatConst(val) => write![w, "{}", val],
    }
}

fn write_repchoice(w: &mut dyn Write, rep: &RepChoice) -> io::Result<()> {
    let s = match &rep {
        RepChoice::FallbackImmut => "immut",
        RepChoice::OptimizedMut => "mut",
    };
    write![w, "{}", s]
}

fn write_type(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer,
    type_: &Type,
) -> io::Result<()> {
    match type_ {
        Type::Bool => write![w, "Bool"],
        Type::Num(NumType::Byte) => write![w, "Byte"],
        Type::Num(NumType::Int) => write![w, "Int"],
        Type::Num(NumType::Float) => write![w, "Float"],
        Type::Array(rep, item_type) => {
            write_repchoice(w, rep)?;
            write![w, " Array ("]?;
            write_type(w, type_renderer, item_type)?;
            write![w, ")"]
        }
        Type::HoleArray(rep, item_type) => {
            write_repchoice(w, rep)?;
            write![w, " HoleArray ("]?;
            write_type(w, type_renderer, item_type)?;
            write![w, ")"]
        }
        Type::Tuple(types) => {
            if types.len() == 0 {
                write![w, "()"]?;
            } else if types.len() == 1 {
                write![w, "("]?;
                write_type(w, type_renderer, &types[0])?;
                write![w, ",)"]?
            } else {
                write![w, "("]?;
                for item_type in &types[..types.len() - 1] {
                    write_type(w, type_renderer, item_type)?;
                    write![w, ", "]?;
                }
                write_type(w, type_renderer, &types[types.len() - 1])?;
                write![w, ")"]?;
            }
            Ok(())
        }
        Type::Boxed(content_type) => {
            write![w, "Box ("]?;
            write_type(w, type_renderer, content_type)?;
            write![w, ")"]?;
            Ok(())
        }
        Type::Variants(types) => {
            let types = types.as_slice();
            if types.len() == 0 {
                write![w, "{{}}"]?
            } else if types.len() == 1 {
                write![w, "{{"]?;
                write_type(w, type_renderer, &types[0])?;
                write![w, ",}}"]?
            } else {
                write![w, "{{"]?;
                for item_type in &types[..types.len() - 1] {
                    write_type(w, type_renderer, item_type)?;
                    write![w, ", "]?;
                }
                write_type(w, type_renderer, &types[types.len() - 1])?;
                write![w, "}}"]?;
            }
            Ok(())
        }
        Type::Custom(type_id) => write![w, "{}", type_renderer.render(type_id)],
    }
}

fn write_single(w: &mut dyn Write, name: &str, local_id: &LocalId) -> io::Result<()> {
    write![w, "{}(%{})", name, local_id.0]
}

fn write_double(
    w: &mut dyn Write,
    name: &str,
    local_id1: &LocalId,
    local_id2: &LocalId,
) -> io::Result<()> {
    write![w, "{}(%{}, %{})", name, local_id1.0, local_id2.0]
}

fn match_string_bytes(bindings: &[(Type, Expr)]) -> Option<String> {
    let mut result_bytes = Vec::new();
    for binding in bindings {
        if let (_, Expr::ByteLit(byte)) = binding {
            result_bytes.push(*byte);
        } else {
            break;
        }
    }
    if result_bytes.len() < 2 {
        return None;
    }
    String::from_utf8(result_bytes).ok()
}

fn write_expr(w: &mut dyn Write, expr: &Expr, context: Context) -> io::Result<()> {
    match expr {
        Expr::Local(local_id) => write![w, "%{}", local_id.0],
        Expr::Call(_purity, func_id, local_id) => write![
            w,
            "call {} (%{})",
            context.func_renderer.render(func_id),
            local_id.0
        ],
        Expr::Branch(local_id, conditions, _return_type) => {
            write![w, "branch %{} {{", local_id.0]?;
            let new_context = context.add_indent();
            for (condition, sub_expr) in conditions {
                let newer_context = new_context.add_indent();
                new_context.writeln(w)?;
                write_condition(w, context.type_renderer, condition)?;
                write![w, " ->"]?;
                newer_context.writeln(w)?;
                write_expr(w, sub_expr, newer_context)?;
            }
            context.writeln(w)?;
            write![w, "}}"]?;
            Ok(())
        }
        Expr::LetMany(bindings, final_local) => {
            write![w, "let"]?;
            let new_context = context.add_indent();
            let mut index = 0;
            while index < bindings.len() {
                if let Some(string) = match_string_bytes(&bindings[index..]) {
                    new_context.writeln(w)?;
                    write![
                        w,
                        "%{}...%{}: Byte = {:?}",
                        context.num_locals + index,
                        context.num_locals + index + string.len() - 1,
                        string,
                    ]?;
                    index += string.len();
                } else {
                    let (binding_type, binding_expr) = &bindings[index];
                    new_context.writeln(w)?;
                    write![w, "%{}: ", context.num_locals + index]?;
                    write_type(w, context.type_renderer, binding_type)?;
                    write![w, " = "]?;
                    write_expr(
                        w,
                        binding_expr,
                        Context {
                            num_locals: context.num_locals + index,
                            ..new_context
                        },
                    )?;
                    index += 1;
                }
            }
            context.writeln(w)?;
            write![w, "in %{}", final_local.0]?;
            Ok(())
        }
        Expr::Tuple(elem_ids) => {
            if elem_ids.len() == 0 {
                write![w, "()"]?
            } else if elem_ids.len() == 1 {
                write![w, "(%{},)", elem_ids[0].0]?;
            } else {
                write![w, "("]?;
                for elem_id in &elem_ids[..elem_ids.len() - 1] {
                    write![w, "%{}, ", elem_id.0]?;
                }
                write![w, "%{})", elem_ids[elem_ids.len() - 1].0]?;
            }
            Ok(())
        }
        Expr::TupleField(local_id, index) => write![w, "tuple field {} %{}", index, local_id.0],
        Expr::WrapVariant(_variants, variant_id, local_id) => {
            write![w, "wrap variant {} %{}", variant_id.0, local_id.0]
        }
        Expr::UnwrapVariant(variant_id, local_id) => {
            write![w, "unwrap variant {} %{}", variant_id.0, local_id.0]
        }
        Expr::WrapBoxed(content_id, _content_type) => write![w, "wrap boxed %{}", content_id.0],
        Expr::UnwrapBoxed(content_id, _content_type) => write![w, "unwrap boxed %{}", content_id.0],
        Expr::WrapCustom(type_id, local_id) => write![
            w,
            "wrap custom {} %{}",
            context.type_renderer.render(type_id),
            local_id.0
        ],
        Expr::UnwrapCustom(type_id, local_id) => write![
            w,
            "unwrap custom {} %{}",
            context.type_renderer.render(type_id),
            local_id.0
        ],

        Expr::RcOp(RcOp::Retain, _container, _inner_type, local_id) => {
            write![w, "retain %{}", local_id.0]
        }

        Expr::RcOp(RcOp::Release, _container, _inner_type, local_id) => {
            write![w, "release %{}", local_id.0]
        }

        Expr::Intrinsic(intr, local_id) => write![
            w,
            "{} %{}",
            intrinsic_to_name(*intr).debug_name(),
            local_id.0
        ],

        Expr::ArrayOp(rep, _item_type, array_op) => {
            write_repchoice(w, rep)?;
            write![w, " "]?;
            match array_op {
                ArrayOp::Get(local_id1, local_id2) => write_double(w, "get", local_id1, local_id2),
                ArrayOp::Extract(local_id1, local_id2) => {
                    write_double(w, "extract", local_id1, local_id2)
                }
                ArrayOp::Len(local_id) => write_single(w, "len", local_id),
                ArrayOp::Push(local_id1, local_id2) => {
                    write_double(w, "push", local_id1, local_id2)
                }
                ArrayOp::Pop(local_id) => write_single(w, "pop", local_id),
                ArrayOp::Replace(local_id1, local_id2) => {
                    write_double(w, "replace", local_id1, local_id2)
                }
                ArrayOp::Reserve(local_id1, local_id2) => {
                    write_double(w, "reserve", local_id1, local_id2)
                }
            }
        }

        Expr::IoOp(rep, ioop) => {
            write_repchoice(w, rep)?;
            write![w, " "]?;
            match ioop {
                IoOp::Input => write![w, "input"],
                IoOp::Output(local_id) => write_single(w, "output", local_id),
            }
        }

        Expr::Panic(_ret_type, rep, local_id) => {
            write_repchoice(w, rep)?;
            write![w, " "]?;
            write_single(w, "panic", local_id)
        }

        Expr::ArrayLit(rep, _type, elem_ids) => {
            let elems_are_contiguous = elem_ids.len() > 1
                && (0..elem_ids.len() - 1).all(|i| elem_ids[i].0 + 1 == elem_ids[i + 1].0);

            write_repchoice(w, rep)?;
            write![w, " "]?;
            if elem_ids.len() == 0 {
                write![w, "[]"]?
            } else if elems_are_contiguous {
                write![
                    w,
                    "[%{}...%{}]",
                    elem_ids.first().unwrap().0,
                    elem_ids.last().unwrap().0
                ]?;
            } else {
                write![w, "["]?;
                for elem_id in &elem_ids[..elem_ids.len() - 1] {
                    write![w, "%{}, ", elem_id.0]?;
                }
                write![w, "%{}]", elem_ids[elem_ids.len() - 1].0]?;
            }
            Ok(())
        }

        Expr::BoolLit(val) => write![w, "{}", if *val { "True" } else { "False" }],
        Expr::ByteLit(val) => write![w, "{:?}", (*val as char)],
        Expr::IntLit(val) => write![w, "{}", val],
        Expr::FloatLit(val) => write![w, "{}", val],
    }
}

fn write_func(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer,
    func_renderer: &FuncRenderer<CustomFuncId>,
    func: &FuncDef,
    func_id: CustomFuncId,
) -> io::Result<()> {
    let context = Context {
        type_renderer,
        func_renderer,
        indentation: 0,
        num_locals: 1,
    };

    let context = context.add_indent();

    write![w, "func {} (%0: ", func_renderer.render(func_id)]?;
    write_type(w, type_renderer, &func.arg_type)?;
    write![w, "): "]?;
    write_type(w, type_renderer, &func.ret_type)?;
    write![w, " ="]?;
    context.writeln(w)?;

    write_expr(w, &func.body, context)?;
    writeln![w]?;
    writeln![w]?;
    Ok(())
}

fn write_custom_type(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer,
    type_: &Type,
    type_id: CustomTypeId,
) -> io::Result<()> {
    write![w, "custom type {} = ", type_renderer.render(type_id)]?;
    write_type(w, type_renderer, type_)?;
    writeln![w]?;
    Ok(())
}

pub fn write_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    let type_renderer = CustomTypeRenderer::from_symbols(&program.custom_type_symbols);
    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);

    for (i, type_) in &program.custom_types {
        write_custom_type(w, &type_renderer, type_, i)?;
    }
    writeln![w]?;
    for (i, func) in &program.funcs {
        write_func(w, &type_renderer, &func_renderer, func, i)?;
    }
    Ok(())
}
