use crate::data::first_order_ast::NumType;
use crate::data::low_ast::ArrayOp;
use crate::data::low_ast::Expr;
use crate::data::low_ast::FuncDef;
use crate::data::low_ast::IoOp;
use crate::data::low_ast::LocalId;
use crate::data::low_ast::Program;
use crate::data::low_ast::Type;
use crate::data::rc_specialized_ast2::RcOp;
use crate::intrinsic_config::intrinsic_to_name;
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

fn write_type(w: &mut dyn Write, type_: &Type) -> io::Result<()> {
    match type_ {
        Type::Bool => write![w, "Bool"],
        Type::Num(NumType::Byte) => write![w, "Byte"],
        Type::Num(NumType::Int) => write![w, "Int"],
        Type::Num(NumType::Float) => write![w, "Float"],
        Type::Array(item_type) => {
            write![w, " Array ("]?;
            write_type(w, item_type)?;
            write![w, ")"]
        }
        Type::HoleArray(item_type) => {
            write![w, " HoleArray ("]?;
            write_type(w, item_type)?;
            write![w, ")"]
        }
        Type::Tuple(types) => {
            if types.len() == 0 {
                write![w, "()"]?;
            } else if types.len() == 1 {
                write![w, "("]?;
                write_type(w, &types[0])?;
                write![w, ",)"]?
            } else {
                write![w, "("]?;
                for item_type in &types[..types.len() - 1] {
                    write_type(w, item_type)?;
                    write![w, ", "]?;
                }
                write_type(w, &types[types.len() - 1])?;
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
                write_type(w, &types[0])?;
                write![w, ",}}"]?
            } else {
                write![w, "{{"]?;
                for item_type in &types[..types.len() - 1] {
                    write_type(w, item_type)?;
                    write![w, ", "]?;
                }
                write_type(w, &types[types.len() - 1])?;
                write![w, "}}"]?;
            }
            Ok(())
        }
        Type::Boxed(box_type) => {
            write![w, " Box ("]?;
            write_type(w, box_type)?;
            write![w, ")"]
        }
        Type::Custom(type_id) => write![w, "~{}", type_id.0],
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

fn write_expr(w: &mut dyn Write, expr: &Expr, context: Context) -> io::Result<()> {
    match expr {
        Expr::Local(local_id) => write![w, "%{}", local_id.0],
        Expr::Call(func_id, local_id) => write![w, "call #{} (%{})", func_id.0, local_id.0],
        Expr::TailCall(tail_func_id, local_id) => {
            write![w, "tail call @{} (%{})", tail_func_id.0, local_id.0]
        }
        Expr::If(local_id, then_branch, else_branch) => {
            write![w, "if %{} {{", local_id.0]?;
            let new_context = context.add_indent();
            new_context.writeln(w)?;
            write_expr(w, then_branch, new_context)?;
            context.writeln(w)?;
            write![w, "}} else {{"]?;
            new_context.writeln(w)?;
            write_expr(w, else_branch, new_context)?;
            context.writeln(w)?;
            write![w, "}}"]?;
            Ok(())
        }
        Expr::LetMany(bindings, final_local) => {
            write![w, "let"]?;
            let new_context = context.add_indent();
            for (index, (binding_type, binding_expr)) in bindings.iter().enumerate() {
                new_context.writeln(w)?;
                write![w, "%{}: ", context.num_locals + index]?;
                write_type(w, binding_type)?;
                write![w, " = "]?;
                write_expr(
                    w,
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
        Expr::UnwrapBoxed(local_id, _type) => write![w, "unwrap boxed %{}", local_id.0],
        Expr::RcOp(op, _type, local_id) => match op {
            RcOp::Retain => write_single(w, "retain", local_id),
            RcOp::Release(_) => write_single(w, "release", local_id),
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

        Expr::ArrayOp(array_op) => {
            write![w, " "]?;
            match array_op {
                ArrayOp::New(_) => write![w, "new"],
                ArrayOp::Get(_, local_id1, local_id2) => {
                    write_double(w, "get", local_id1, local_id2)
                }
                ArrayOp::Extract(_, local_id1, local_id2) => {
                    write_double(w, "extract", local_id1, local_id2)
                }
                ArrayOp::Len(_, local_id) => write_single(w, "len", local_id),
                ArrayOp::Push(_, local_id1, local_id2) => {
                    write_double(w, "push", local_id1, local_id2)
                }
                ArrayOp::Pop(_, local_id) => write_single(w, "pop", local_id),
                ArrayOp::Replace(_, local_id1, local_id2) => {
                    write_double(w, "replace", local_id1, local_id2)
                }
                ArrayOp::Reserve(_, local_id1, local_id2) => {
                    write_double(w, "reserve", local_id1, local_id2)
                }
            }
        }

        Expr::IoOp(ioop) => {
            write![w, " "]?;
            match ioop {
                IoOp::Input => write![w, "input"],
                IoOp::Output(local_id) => write_single(w, "output", local_id),
            }
        }

        Expr::Panic(_ret_type, local_id) => {
            write![w, " "]?;
            write_single(w, "panic", local_id)
        }

        Expr::BoolLit(val) => write![w, "{}", if *val { "True" } else { "False" }],
        Expr::ByteLit(val) => write![w, "{:?}", (*val as char)],
        Expr::IntLit(val) => write![w, "{}", val],
        Expr::FloatLit(val) => write![w, "{}", val],
    }
}

fn write_func(w: &mut dyn Write, func: &FuncDef, func_id: usize) -> io::Result<()> {
    write![w, "func #{} (%0: ", func_id]?;
    write_type(w, &func.arg_type)?;
    write![w, "): "]?;
    write_type(w, &func.ret_type)?;
    write![w, " ="]?;

    let context = Context {
        indentation: 0,
        num_locals: 1,
    };
    let context = context.add_indent();

    context.writeln(w)?;
    write_expr(w, &func.body, context)?;
    writeln![w]?;

    if func.tail_funcs.len() > 0 {
        write![w, "where"]?;
        for (tail_func_id, tail_func) in &func.tail_funcs {
            context.writeln(w)?;
            write![w, "tail func @{} (%0: ", tail_func_id.0]?;
            write_type(w, &tail_func.arg_type)?;
            write![w, ") ="]?;
            let sub_context = context.add_indent();
            sub_context.writeln(w)?;
            write_expr(w, &tail_func.body, sub_context)?;
        }
        writeln![w]?;
    }

    writeln![w]?;
    Ok(())
}

fn write_custom_type(w: &mut dyn Write, type_: &Type, type_id: usize) -> io::Result<()> {
    write![w, "custom type ~{} = ", type_id]?;
    write_type(w, type_)?;
    writeln![w]?;
    Ok(())
}

pub fn write_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    for (i, type_) in program.custom_types.types.values().enumerate() {
        write_custom_type(w, type_, i)?;
    }
    writeln![w]?;
    for (i, func) in program.funcs.values().enumerate() {
        write_func(w, func, i)?;
    }
    Ok(())
}
