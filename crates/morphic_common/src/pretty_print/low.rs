use crate::data::first_order_ast::NumType;
use crate::data::low_ast::{ArrayOp, CustomFuncId, Expr, FuncDef, IoOp, LocalId, Program, Type};
use crate::data::obligation_annot_ast::CustomTypeId;
use crate::data::rc_specialized_ast::RcOp;
use crate::data::tail_rec_ast::TailFuncId;
use crate::intrinsic_config::intrinsic_to_name;
use crate::pretty_print::utils::{
    write_metadata, CustomTypeRenderer, FuncRenderer, TailFuncRenderer,
};
use std::io;
use std::io::Write;

const TAB_SIZE: usize = 2;

#[derive(Clone, Debug, Copy)]
struct Context {
    indentation: usize,
    num_locals: usize,
}

impl Context {
    fn add_indent(&self) -> Context {
        Context {
            indentation: self.indentation + TAB_SIZE,
            num_locals: self.num_locals,
        }
    }

    fn writeln(&self, w: &mut dyn Write) -> io::Result<()> {
        writeln![w]?;
        write![w, "{}", " ".repeat(self.indentation)]
    }
}

fn write_type(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    type_: &Type,
) -> io::Result<()> {
    match type_ {
        Type::Bool => write![w, "Bool"],
        Type::Num(NumType::Byte) => write![w, "Byte"],
        Type::Num(NumType::Int) => write![w, "Int"],
        Type::Num(NumType::Float) => write![w, "Float"],
        Type::Array(item_type) => {
            write![w, "Array ("]?;
            write_type(w, type_renderer, item_type)?;
            write![w, ")"]
        }
        Type::HoleArray(item_type) => {
            write![w, "HoleArray ("]?;
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
        Type::Boxed(box_type) => {
            write![w, "Box ("]?;
            write_type(w, type_renderer, box_type)?;
            write![w, ")"]
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

fn write_expr(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    tail_renderer: &TailFuncRenderer<CustomFuncId>,
    func_renderer: &FuncRenderer<TailFuncId>,
    expr: &Expr,
    context: Context,
) -> io::Result<()> {
    match expr {
        Expr::Local(local_id) => write![w, "%{}", local_id.0],
        Expr::Call(func_id, local_id) => write![
            w,
            "call #{} (%{})",
            tail_renderer.render(func_id),
            local_id.0
        ],
        Expr::TailCall(tail_func_id, local_id) => {
            write![
                w,
                "tail call @{} (%{})",
                func_renderer.render(tail_func_id),
                local_id.0
            ]
        }
        Expr::If(local_id, then_branch, else_branch) => {
            write![w, "if %{} {{", local_id.0]?;
            let new_context = context.add_indent();
            new_context.writeln(w)?;
            write_expr(
                w,
                type_renderer,
                tail_renderer,
                func_renderer,
                then_branch,
                new_context,
            )?;
            context.writeln(w)?;
            write![w, "}} else {{"]?;
            new_context.writeln(w)?;
            write_expr(
                w,
                type_renderer,
                tail_renderer,
                func_renderer,
                else_branch,
                new_context,
            )?;
            context.writeln(w)?;
            write![w, "}}"]?;
            Ok(())
        }
        Expr::LetMany(bindings, final_local) => {
            write![w, "let"]?;
            let new_context = context.add_indent();
            for (index, (binding_type, binding_expr, metadata)) in bindings.iter().enumerate() {
                write_metadata(w, new_context.indentation, metadata)?;
                new_context.writeln(w)?;
                write![w, "%{}: ", context.num_locals + index]?;
                write_type(w, type_renderer, binding_type)?;
                write![w, " = "]?;
                write_expr(
                    w,
                    type_renderer,
                    tail_renderer,
                    func_renderer,
                    binding_expr,
                    Context {
                        num_locals: context.num_locals + index,
                        indentation: new_context.indentation,
                    },
                )?;
            }
            context.writeln(w)?;
            write![w, "in %{}", final_local.0]?;
            Ok(())
        }
        Expr::Unreachable(_type) => write![w, "unreachable"],
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
        Expr::UnwrapVariant(_variants, variant_id, local_id) => {
            write![w, "unwrap variant {} %{}", variant_id.0, local_id.0]
        }
        Expr::WrapCustom(type_id, local_id) => {
            write![w, "wrap custom ~{} %{}", type_id.0, local_id.0]
        }
        Expr::UnwrapCustom(type_id, local_id) => {
            write![w, "unwrap custom ~{} %{}", type_id.0, local_id.0]
        }
        Expr::WrapBoxed(local_id, _type) => write![w, "wrap boxed %{}", local_id.0],
        Expr::UnwrapBoxed(local_id, _input_type, _type) => {
            write![w, "unwrap boxed %{}", local_id.0]
        }
        Expr::RcOp(_type, op, local_id) => match op {
            RcOp::Retain => write_single(w, "retain", local_id),
            RcOp::Release => write_single(w, "release", local_id),
        },
        Expr::CheckVariant(variant_id, local_id) => {
            write![w, "check variant {} %{}", variant_id.0, local_id.0]
        }

        Expr::Intrinsic(intr, local_id) => write![
            w,
            "{} %{}",
            intrinsic_to_name(*intr).debug_name(),
            local_id.0
        ],

        Expr::ArrayOp(_mode_scheme, array_op) => match array_op {
            ArrayOp::New => write![w, "new"],
            ArrayOp::Get(local_id1, local_id2) => write_double(w, "get", local_id1, local_id2),
            ArrayOp::Extract(local_id1, local_id2) => {
                write_double(w, "extract", local_id1, local_id2)
            }
            ArrayOp::Len(local_id) => write_single(w, "len", local_id),
            ArrayOp::Push(local_id1, local_id2) => write_double(w, "push", local_id1, local_id2),
            ArrayOp::Pop(local_id) => write_single(w, "pop", local_id),
            ArrayOp::Replace(local_id1, local_id2) => {
                write_double(w, "replace", local_id1, local_id2)
            }
            ArrayOp::Reserve(local_id1, local_id2) => {
                write_double(w, "reserve", local_id1, local_id2)
            }
        },

        Expr::IoOp(ioop) => match ioop {
            IoOp::Input => write![w, "input"],
            IoOp::Output(_, local_id) => write_single(w, "output", local_id),
        },

        Expr::Panic(_ret_type, _input_type, local_id) => write_single(w, "panic", local_id),

        Expr::BoolLit(val) => write![w, "{}", if *val { "True" } else { "False" }],
        Expr::ByteLit(val) => write![w, "{:?}", (*val as char)],
        Expr::IntLit(val) => write![w, "{}", val],
        Expr::FloatLit(val) => write![w, "{}", val],
    }
}

fn write_func(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    tail_renderer: &TailFuncRenderer<CustomFuncId>,
    func: &FuncDef,
    func_id: CustomFuncId,
) -> io::Result<()> {
    let func_renderer = FuncRenderer::from_symbols(&func.tail_func_symbols);

    write![w, "func {} (%0: ", tail_renderer.render(func_id)]?;
    write_type(w, type_renderer, &func.arg_type)?;
    write![w, "): "]?;
    write_type(w, type_renderer, &func.ret_type)?;
    write![w, " ="]?;

    let context = Context {
        indentation: 0,
        num_locals: 1,
    };
    let context = context.add_indent();

    context.writeln(w)?;
    write_expr(
        w,
        type_renderer,
        tail_renderer,
        &func_renderer,
        &func.body,
        context,
    )?;
    writeln![w]?;

    if func.tail_funcs.len() > 0 {
        write![w, "where"]?;
        for (tail_func_id, tail_func) in &func.tail_funcs {
            context.writeln(w)?;
            write![w, "tail func @{} (%0: ", func_renderer.render(tail_func_id)]?;
            write_type(w, type_renderer, &tail_func.arg_type)?;
            write![w, ") ="]?;
            let sub_context = context.add_indent();
            sub_context.writeln(w)?;
            write_expr(
                w,
                type_renderer,
                tail_renderer,
                &func_renderer,
                &tail_func.body,
                sub_context,
            )?;
        }
        writeln![w]?;
    }

    writeln![w]?;
    Ok(())
}

fn write_typedef(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    typedef: &Type,
    type_id: CustomTypeId,
) -> io::Result<()> {
    write![w, "custom type {} = ", type_renderer.render(type_id)]?;
    write_type(w, type_renderer, typedef)?;
    writeln![w]?;
    Ok(())
}

pub fn write_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    let type_renderer = CustomTypeRenderer::from_symbols(&program.custom_type_symbols);
    let func_renderer = TailFuncRenderer::from_symbols(&program.func_symbols);

    for (i, typedef) in &program.custom_types.types {
        write_typedef(w, &type_renderer, typedef, i)?;
    }
    writeln![w]?;
    for (i, func) in &program.funcs {
        write_func(w, &type_renderer, &func_renderer, func, i)?;
    }
    Ok(())
}
