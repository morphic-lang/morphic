use crate::data::anon_sum_ast::Type;
use crate::data::first_order_ast::{CustomFuncId, CustomTypeId, NumType};
use crate::data::flat_ast::{
    ArrayOp, Condition, CustomTypeDef, Expr, FuncDef, IoOp, LocalId, Program,
};
use crate::intrinsic_config::intrinsic_to_name;
use crate::pretty_print::utils::{write_delimited, CustomTypeRenderer, FuncRenderer};
use core::str;
use std::io::{self, Write};

const TAB_SIZE: usize = 2;

#[derive(Clone, Debug, Copy)]
pub struct Context<'a> {
    pub type_renderer: &'a CustomTypeRenderer<CustomTypeId>,
    pub func_renderer: &'a FuncRenderer<CustomFuncId>,
    pub indentation: usize,
    pub num_locals: usize,
}

impl<'a> Context<'a> {
    fn add_indent(&self) -> Self {
        Self {
            indentation: self.indentation + TAB_SIZE,
            ..*self
        }
    }

    fn remove_indent(&self) -> Self {
        Self {
            indentation: self.indentation.saturating_sub(TAB_SIZE),
            ..*self
        }
    }

    fn writeln(&self, w: &mut dyn Write) -> io::Result<()> {
        writeln!(w)?;
        write!(w, "{}", " ".repeat(self.indentation))
    }
}

pub fn write_condition(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<CustomTypeId>>,
    condition: &Condition,
) -> io::Result<()> {
    match condition {
        Condition::Any => write!(w, "_",),
        Condition::Tuple(conditions) => {
            write_delimited(w, conditions, "(", ")", ", ", |w, cond| {
                write_condition(w, type_renderer, cond)
            })
        }
        Condition::Variant(variant_id, subcondition) => {
            write!(w, "variant {} (", variant_id.0)?;
            write_condition(w, type_renderer, subcondition)?;
            write!(w, ")")?;
            Ok(())
        }
        Condition::Boxed(subcondition, _content_type) => {
            write!(w, "boxed (")?;
            write_condition(w, type_renderer, subcondition)?;
            write!(w, ")")?;
            Ok(())
        }
        Condition::Custom(type_id, subcondition) => {
            if let Some(type_renderer) = type_renderer {
                write!(w, "custom {} (", type_renderer.render(type_id))?;
            } else {
                write!(w, "custom #{} (", type_id.0)?;
            }
            write_condition(w, type_renderer, subcondition)?;
            write!(w, ")")?;
            Ok(())
        }
        Condition::BoolConst(val) => write!(w, "{}", if *val { "True" } else { "False" }),
        Condition::ByteConst(val) => write!(w, "{:?}", *val as char),
        Condition::IntConst(val) => write!(w, "{}", val),
        Condition::FloatConst(val) => write!(w, "{}", val),
    }
}

pub fn write_type(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    type_: &Type,
) -> io::Result<()> {
    match type_ {
        Type::Bool => write!(w, "Bool"),
        Type::Num(NumType::Byte) => write!(w, "Byte"),
        Type::Num(NumType::Int) => write!(w, "Int"),
        Type::Num(NumType::Float) => write!(w, "Float"),
        Type::Tuple(types) => write_delimited(w, types, "(", ")", ", ", |w, type_| {
            write_type(w, type_renderer, type_)
        }),
        Type::Variants(types) => {
            write_delimited(w, types.as_slice(), "{", "}", ", ", |w, type_| {
                write_type(w, type_renderer, type_)
            })
        }
        Type::Custom(type_id) => write!(w, "{}", type_renderer.render(type_id)),
        Type::Array(item_type) => {
            write!(w, "Array (")?;
            write_type(w, type_renderer, item_type)?;
            write!(w, ")")
        }
        Type::HoleArray(item_type) => {
            write!(w, "HoleArray (")?;
            write_type(w, type_renderer, item_type)?;
            write!(w, ")")
        }
        Type::Boxed(item_type) => {
            write!(w, "Boxed (")?;
            write_type(w, type_renderer, item_type)?;
            write!(w, ")")
        }
    }
}

fn write_local(w: &mut dyn Write, local: LocalId) -> io::Result<()> {
    write!(w, "%{}", local.0)
}

fn write_single(w: &mut dyn Write, name: &str, local: LocalId) -> io::Result<()> {
    write!(w, "{name}(")?;
    write_local(w, local)?;
    write!(w, ")")
}

fn write_double(w: &mut dyn Write, name: &str, local1: LocalId, local2: LocalId) -> io::Result<()> {
    write!(w, "{name}(")?;
    write_local(w, local1)?;
    write!(w, ", ")?;
    write_local(w, local2)?;
    write!(w, ")")
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

pub fn write_expr(w: &mut dyn Write, expr: &Expr, context: Context) -> io::Result<()> {
    match expr {
        Expr::Local(local) => write_local(w, *local),
        Expr::Call(_purity, func_id, local) => {
            write!(w, "call {} (", context.func_renderer.render(func_id))?;
            write_local(w, *local)?;
            write!(w, ")")
        }
        Expr::Branch(local, conditions, _return_type) => {
            write!(w, "branch ")?;
            write_local(w, *local)?;
            write!(w, " {{")?;
            let new_context = context.add_indent();
            for (condition, sub_expr) in conditions {
                let newer_context = new_context.add_indent();
                new_context.writeln(w)?;
                write_condition(w, Some(context.type_renderer), condition)?;
                write!(w, " ->")?;
                newer_context.writeln(w)?;
                write_expr(w, sub_expr, newer_context)?;
            }
            context.writeln(w)?;
            write!(w, "}}")?;
            Ok(())
        }
        Expr::LetMany(bindings, final_local) => {
            write!(w, "let")?;
            let new_context = context.add_indent();
            let mut index = 0;
            while index < bindings.len() {
                if let Some(string) = match_string_bytes(&bindings[index..]) {
                    new_context.writeln(w)?;
                    write!(
                        w,
                        "%{}...%{}: Byte = {:?}",
                        context.num_locals + index,
                        context.num_locals + index + string.len() - 1,
                        string,
                    )?;
                    index += string.len();
                } else {
                    let (binding_type, binding_expr) = &bindings[index];
                    new_context.writeln(w)?;
                    write!(w, "%{}: ", context.num_locals + index)?;
                    write_type(w, context.type_renderer, binding_type)?;
                    write!(w, " = ")?;
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
            write!(w, "in ")?;
            write_local(w, *final_local)?;
            Ok(())
        }
        Expr::Tuple(elems) => {
            write_delimited(w, elems, "(", ")", ", ", |w, local| write_local(w, *local))
        }
        Expr::TupleField(local, index) => {
            write!(w, "tuple field {} ", index)?;
            write_local(w, *local)
        }
        Expr::WrapVariant(_variants, variant_id, local) => {
            write!(w, "wrap variant {} ", variant_id.0)?;
            write_local(w, *local)
        }
        Expr::UnwrapVariant(variant_id, local) => {
            write!(w, "unwrap variant {} ", variant_id.0)?;
            write_local(w, *local)
        }
        Expr::WrapBoxed(content, _content_type) => {
            write!(w, "wrap boxed ")?;
            write_local(w, *content)
        }
        Expr::UnwrapBoxed(content, _content_type) => {
            write!(w, "unwrap boxed ")?;
            write_local(w, *content)
        }
        Expr::WrapCustom(type_id, local) => {
            write!(w, "wrap custom {} ", context.type_renderer.render(*type_id))?;
            write_local(w, *local)
        }
        Expr::UnwrapCustom(type_id, local) => {
            write!(
                w,
                "unwrap custom {} ",
                context.type_renderer.render(*type_id)
            )?;
            write_local(w, *local)
        }
        Expr::Intrinsic(intr, local_id) => {
            write!(w, "{} ", intrinsic_to_name(*intr).debug_name())?;
            write_local(w, *local_id)
        }
        Expr::ArrayOp(array_op) => match array_op {
            ArrayOp::Get(_item_type, local1, local2) => write_double(w, "get", *local1, *local2),
            ArrayOp::Extract(_item_type, local1, local2) => {
                write_double(w, "extract", *local1, *local2)
            }
            ArrayOp::Len(_item_type, local) => write_single(w, "len", *local),
            ArrayOp::Push(_item_type, local1, local2) => write_double(w, "push", *local1, *local2),
            ArrayOp::Pop(_item_type, local) => write_single(w, "pop", *local),
            ArrayOp::Replace(_item_type, local1, local2) => {
                write_double(w, "replace", *local1, *local2)
            }
            ArrayOp::Reserve(_item_type, local1, local2) => {
                write_double(w, "reserve", *local1, *local2)
            }
        },
        Expr::IoOp(io_op) => match io_op {
            IoOp::Input => write!(w, "input"),
            IoOp::Output(local) => write_single(w, "output", *local),
        },
        Expr::Panic(_ret_type, local) => write_single(w, "panic", *local),
        Expr::ArrayLit(_type, elem_ids) => {
            let elems_are_contiguous = elem_ids.len() > 1
                && (0..elem_ids.len() - 1).all(|i| elem_ids[i].0 + 1 == elem_ids[i + 1].0);

            if elem_ids.len() == 0 {
                write!(w, "[]")?
            } else if elems_are_contiguous {
                write!(
                    w,
                    "[%{}...%{}]",
                    elem_ids.first().unwrap().0,
                    elem_ids.last().unwrap().0
                )?;
            } else {
                write!(w, "[")?;
                for elem_id in &elem_ids[..elem_ids.len() - 1] {
                    write!(w, "%{}, ", elem_id.0)?;
                }
                write!(w, "%{}]", elem_ids[elem_ids.len() - 1].0)?;
            }
            Ok(())
        }
        Expr::BoolLit(val) => write!(w, "{}", if *val { "True" } else { "False" }),
        Expr::ByteLit(val) => write!(w, "{:?}", (*val as char)),
        Expr::IntLit(val) => write!(w, "{}", val),
        Expr::FloatLit(val) => write!(w, "{}", val),
    }
}

pub fn write_func(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    func_renderer: &FuncRenderer<CustomFuncId>,
    func: &FuncDef,
    func_id: CustomFuncId,
) -> io::Result<()> {
    write!(w, "func {} (%0: ", func_renderer.render(func_id))?;
    write_type(w, type_renderer, &func.arg_type)?;
    write!(w, "): ")?;
    write_type(w, type_renderer, &func.ret_type)?;
    write!(w, " =\n")?;

    let context = Context {
        type_renderer,
        func_renderer,
        indentation: 0,
        num_locals: 1,
    };

    write_expr(w, &func.body, context)?;
    writeln!(w)?;
    Ok(())
}

pub fn write_typedef(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    typedef: &CustomTypeDef,
    type_id: CustomTypeId,
) -> io::Result<()> {
    write!(w, "custom type {} = ", type_renderer.render(type_id))?;
    write_type(w, type_renderer, &typedef.content)?;
    writeln!(w)?;
    Ok(())
}

pub fn write_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    let type_renderer = CustomTypeRenderer::from_symbols(&program.custom_type_symbols);
    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);

    for (i, typedef) in &program.custom_types.types {
        write_typedef(w, &type_renderer, typedef, i)?;
        writeln!(w)?;
    }
    for (i, func) in &program.funcs {
        write_func(w, &type_renderer, &func_renderer, func, i)?;
        writeln!(w)?;
    }
    Ok(())
}

pub struct DisplayCondition<'a> {
    type_renderer: Option<&'a CustomTypeRenderer<CustomTypeId>>,
    cond: &'a Condition,
}

impl<'a> std::fmt::Display for DisplayCondition<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut w = Vec::new();
        write_condition(&mut w, self.type_renderer, self.cond).unwrap();
        f.write_str(str::from_utf8(&w).unwrap())
    }
}

impl Condition {
    pub fn display(&self) -> DisplayCondition {
        DisplayCondition {
            type_renderer: None,
            cond: self,
        }
    }

    pub fn display_with<'a>(
        &'a self,
        type_renderer: &'a CustomTypeRenderer<CustomTypeId>,
    ) -> DisplayCondition<'a> {
        DisplayCondition {
            type_renderer: Some(type_renderer),
            cond: self,
        }
    }
}
