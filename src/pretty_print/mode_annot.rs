use crate::data::first_order_ast::{CustomFuncId, CustomTypeId};
use crate::data::mode_annot_ast2::{
    self as annot, ArrayOp, Condition, Constrs, CustomTypeDef, FuncDef, HeapModes, IoOp, Lt, Mode,
    ModeParam, ModeSolution, Program, Res, ResModes, Shape, ShapeInner,
};
use crate::data::num_type::NumType;
use crate::intrinsic_config::intrinsic_to_name;
use crate::pretty_print::borrow_common::*;
use crate::pretty_print::utils::{write_delimited, CustomTypeRenderer, FuncRenderer};
use crate::util::collection_ext::MapRef;
use std::io::{self, Write};

const TAB_SIZE: usize = 2;
const CONSTRS_PER_LINE: usize = 10;

type Type = annot::Type<ModeSolution, Lt>;
type Occur = annot::Occur<ModeSolution, Lt>;
type Expr = annot::Expr<ModeSolution, Lt>;

#[derive(Clone, Debug, Copy)]
struct Context<'a> {
    type_renderer: &'a CustomTypeRenderer<CustomTypeId>,
    func_renderer: &'a FuncRenderer<CustomFuncId>,
    indentation: usize,
    num_locals: usize,
}

impl<'a> Context<'a> {
    fn add_indent(&self) -> Self {
        Self {
            indentation: self.indentation + TAB_SIZE,
            ..*self
        }
    }

    fn writeln(&self, w: &mut dyn Write) -> io::Result<()> {
        writeln!(w)?;
        write!(w, "{}", " ".repeat(self.indentation))
    }
}

fn write_condition(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    condition: &Condition,
) -> io::Result<()> {
    match condition {
        Condition::Any => write!(w, "_",),
        Condition::Tuple(conditions) => write_delimited(w, conditions, "(", ")", ",", |w, cond| {
            write_condition(w, type_renderer, cond)
        }),
        Condition::Variant(variant_id, subcondition) => {
            write!(w, "variant {} (", variant_id.0)?;
            write_condition(w, type_renderer, subcondition)?;
            write!(w, ")")?;
            Ok(())
        }
        Condition::Boxed(subcondition) => {
            write!(w, "boxed (")?;
            write_condition(w, type_renderer, subcondition)?;
            write!(w, ")")?;
            Ok(())
        }
        Condition::Custom(subcondition) => {
            write!(w, "custom (")?;
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

pub fn write_mode_param(w: &mut dyn Write, m: &ModeParam) -> io::Result<()> {
    write!(w, "${}", m.0)
}

fn write_mode(w: &mut dyn Write, m: &ModeSolution) -> io::Result<()> {
    if m.lb.lb_const == Mode::Owned {
        write!(w, "●")?;
    } else if !m.lb.lb_vars.is_empty() {
        write!(w, "{{ ")?;
        for (i, param) in m.lb.lb_vars.iter().enumerate() {
            write_mode_param(w, param)?;
            if i < m.lb.lb_vars.len() - 1 {
                write!(w, " ⨆ ")?;
            }
        }
        write!(w, " }}")?;
    } else {
        write!(w, "&")?;
    }
    Ok(())
}

fn write_resource<M, L>(
    w: &mut dyn Write,
    write_mode: &impl Fn(&mut dyn Write, &M) -> io::Result<()>,
    write_lifetime: &impl Fn(&mut dyn Write, &L) -> io::Result<()>,
    res: &Res<M, L>,
) -> io::Result<()> {
    match &res.modes {
        ResModes::Stack(stack) => {
            write_mode(w, stack)?;
        }
        ResModes::Heap(HeapModes { access, storage }) => {
            write_mode(w, access)?;
            write!(w, "@")?;
            write_mode(w, storage)?
        }
    }
    write!(w, "<")?;
    write_lifetime(w, &res.lt)?;
    write!(w, ">")?;
    Ok(())
}

fn write_custom(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<CustomTypeId>>,
    type_id: CustomTypeId,
) -> io::Result<()> {
    if let Some(type_renderer) = type_renderer {
        write!(w, "{}", type_renderer.render(type_id))
    } else {
        write!(w, "Custom#{}", type_id.0)
    }
}

pub fn write_type_impl<M, L>(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<CustomTypeId>>,
    write_mode: &impl Fn(&mut dyn Write, &M) -> io::Result<()>,
    write_lifetime: &impl Fn(&mut dyn Write, &L) -> io::Result<()>,
    shape: &Shape,
    res: &[Res<M, L>],
) -> io::Result<()> {
    match &*shape.inner {
        ShapeInner::Bool => write!(w, "Bool"),
        ShapeInner::Num(NumType::Byte) => write!(w, "Byte"),
        ShapeInner::Num(NumType::Int) => write!(w, "Int"),
        ShapeInner::Num(NumType::Float) => write!(w, "Float"),
        ShapeInner::Tuple(shapes) => {
            let items = annot::iter_shapes(shapes, res);
            write_delimited(w, items, "(", ")", ", ", |w, (shape, res)| {
                write_type_impl(w, type_renderer, write_mode, write_lifetime, shape, res)
            })
        }
        ShapeInner::Variants(shapes) => {
            let items = annot::iter_shapes(shapes.as_slice(), res);
            write_delimited(w, items, "{", "}", ", ", |w, (shape, res)| {
                write_type_impl(w, type_renderer, write_mode, write_lifetime, shape, res)
            })
        }
        ShapeInner::Custom(type_id) => write_custom(w, type_renderer, *type_id),
        ShapeInner::SelfCustom(type_id) => write!(w, "Self#{}", type_id.0),
        ShapeInner::Array(shape) => {
            write_resource(w, write_mode, write_lifetime, &res[0])?;
            write!(w, " Array (")?;
            write_type_impl(
                w,
                type_renderer,
                write_mode,
                write_lifetime,
                shape,
                &res[1..],
            )?;
            write!(w, ")")
        }
        ShapeInner::HoleArray(shape) => {
            write_resource(w, write_mode, write_lifetime, &res[0])?;
            write!(w, " HoleArray (")?;
            write_type_impl(
                w,
                type_renderer,
                write_mode,
                write_lifetime,
                shape,
                &res[1..],
            )?;
            write!(w, ")")
        }
        ShapeInner::Boxed(shape) => {
            write_resource(w, write_mode, write_lifetime, &res[0])?;
            write!(w, " Boxed (")?;
            write_type_impl(
                w,
                type_renderer,
                write_mode,
                write_lifetime,
                shape,
                &res[1..],
            )?;
            write!(w, ")")
        }
    }
}

pub fn write_type<M, L>(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<CustomTypeId>>,
    write_mode: impl Fn(&mut dyn Write, &M) -> io::Result<()>,
    write_lifetime: impl Fn(&mut dyn Write, &L) -> io::Result<()>,
    type_: &annot::Type<M, L>,
) -> io::Result<()> {
    write_type_impl(
        w,
        type_renderer,
        &write_mode,
        &write_lifetime,
        &type_.shape,
        type_.res.as_slice(),
    )
}

pub fn write_shape<'a>(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<CustomTypeId>>,
    customs: impl MapRef<'a, CustomTypeId, CustomTypeDef>,
    shape: &Shape,
) -> io::Result<()> {
    write_type_impl(
        w,
        type_renderer,
        &|w, _| write!(w, "_"),
        &|w, _| write!(w, "_"),
        shape,
        shape.gen_resources(customs, || (), || ()).as_slice(),
    )
}

fn write_type_concrete(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    type_: &Type,
) -> io::Result<()> {
    write_type(w, Some(type_renderer), write_mode, write_lifetime, type_)
}

fn write_occur(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    occur: &Occur,
) -> io::Result<()> {
    write!(w, "%{} as ", occur.id.0)?;
    write_type_concrete(w, type_renderer, &occur.ty)
}

fn write_single(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    name: &str,
    occur: &Occur,
) -> io::Result<()> {
    write!(w, "{name}(")?;
    write_occur(w, type_renderer, occur)?;
    write!(w, ")")
}

fn write_double(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    name: &str,
    occur1: &Occur,
    occur2: &Occur,
) -> io::Result<()> {
    write!(w, "{name}(")?;
    write_occur(w, type_renderer, occur1)?;
    write!(w, ", ")?;
    write_occur(w, type_renderer, occur2)?;
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

fn write_expr(w: &mut dyn Write, expr: &Expr, context: Context) -> io::Result<()> {
    match expr {
        Expr::Local(occur) => write_occur(w, context.type_renderer, occur),
        Expr::Call(_purity, func_id, occur) => {
            write!(w, "call {} (", context.func_renderer.render(func_id))?;
            write_occur(w, context.type_renderer, occur)?;
            write!(w, ")")
        }
        Expr::Branch(occur, conditions, _return_type) => {
            write!(w, "branch ")?;
            write_occur(w, context.type_renderer, occur)?;
            write!(w, " {{")?;
            let new_context = context.add_indent();
            for (condition, sub_expr) in conditions {
                let newer_context = new_context.add_indent();
                new_context.writeln(w)?;
                write_condition(w, context.type_renderer, condition)?;
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
                    let last_index = index + string.len() - 1;
                    write!(
                        w,
                        "{}...{}: %{}...%{}: Byte = {:?}",
                        index,
                        last_index,
                        context.num_locals + index,
                        context.num_locals + last_index,
                        string,
                    )?;
                    index += string.len();
                } else {
                    let (binding_type, binding_expr) = &bindings[index];
                    new_context.writeln(w)?;
                    write!(w, "{}: %{}: ", index, context.num_locals + index)?;
                    write_type_concrete(w, context.type_renderer, binding_type)?;
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
            write_occur(w, context.type_renderer, final_local)?;
            Ok(())
        }
        Expr::Tuple(elems) => write_delimited(w, elems, "(", ")", ",", |w, occur| {
            write_occur(w, context.type_renderer, occur)
        }),
        Expr::TupleField(occur, index) => {
            write!(w, "tuple field {} ", index)?;
            write_occur(w, context.type_renderer, occur)
        }
        Expr::WrapVariant(_variants, variant_id, occur) => {
            write!(w, "wrap variant {} ", variant_id.0)?;
            write_occur(w, context.type_renderer, occur)
        }
        Expr::UnwrapVariant(variant_id, occur) => {
            write!(w, "unwrap variant {} ", variant_id.0)?;
            write_occur(w, context.type_renderer, occur)
        }
        Expr::WrapBoxed(content, _content_type) => {
            write!(w, "wrap boxed ")?;
            write_occur(w, context.type_renderer, content)
        }
        Expr::UnwrapBoxed(content, _content_type) => {
            write!(w, "unwrap boxed ")?;
            write_occur(w, context.type_renderer, content)
        }
        Expr::WrapCustom(type_id, occur) => {
            write!(w, "wrap custom {} ", context.type_renderer.render(*type_id))?;
            write_occur(w, context.type_renderer, occur)
        }
        Expr::UnwrapCustom(type_id, occur) => {
            write!(
                w,
                "unwrap custom {} ",
                context.type_renderer.render(*type_id)
            )?;
            write_occur(w, context.type_renderer, occur)
        }
        Expr::Intrinsic(intr, local_id) => {
            write!(w, "{} ", intrinsic_to_name(*intr).debug_name())?;
            write_occur(w, context.type_renderer, local_id)
        }
        Expr::ArrayOp(array_op) => match array_op {
            ArrayOp::Get(occur1, occur2, output_type) => {
                write_double(w, context.type_renderer, "get", occur1, occur2)?;
                write!(w, " as ")?;
                write_type_concrete(w, context.type_renderer, output_type)
            }
            ArrayOp::Extract(occur1, occur2) => {
                write_double(w, context.type_renderer, "extract", occur1, occur2)
            }
            ArrayOp::Len(occur) => write_single(w, context.type_renderer, "len", occur),
            ArrayOp::Push(occur1, occur2) => {
                write_double(w, context.type_renderer, "push", occur1, occur2)
            }
            ArrayOp::Pop(occur) => write_single(w, context.type_renderer, "pop", occur),
            ArrayOp::Replace(occur1, occur2) => {
                write_double(w, context.type_renderer, "replace", occur1, occur2)
            }
            ArrayOp::Reserve(occur1, occur2) => {
                write_double(w, context.type_renderer, "reserve", occur1, occur2)
            }
        },
        Expr::IoOp(io_op) => match io_op {
            IoOp::Input => write!(w, "input"),
            IoOp::Output(occur) => write_single(w, context.type_renderer, "output", occur),
        },
        Expr::Panic(_ret_type, occur) => write_single(w, context.type_renderer, "panic", occur),
        Expr::ArrayLit(_type, elem_occurs) => {
            let elem_ids = elem_occurs.iter().map(|occur| occur.id).collect::<Vec<_>>();

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

fn write_constrs(w: &mut dyn Write, constrs: &Constrs) -> io::Result<()> {
    let mut num_written = 0;
    write!(w, "{{ ")?;
    for (p, bound) in &constrs.sig {
        for lb in &bound.lb_vars {
            write_mode_param(w, lb)?;
            write!(w, " ≤ ")?;
            write_mode_param(w, &p)?;
            write!(w, ", ")?;
            num_written += 1;
        }
        if bound.lb_const == Mode::Owned {
            write!(w, "● ≤ ")?;
            write_mode_param(w, &p)?;
            write!(w, ", ")?;
            num_written += 1;
        }
        if num_written > 0 && num_written % CONSTRS_PER_LINE == 0 {
            writeln!(w)?;
            write!(w, "{}", " ".repeat(TAB_SIZE))?;
        }
    }
    write!(w, "}}")?;
    Ok(())
}

pub fn write_func(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<CustomTypeId>,
    func_renderer: &FuncRenderer<CustomFuncId>,
    func: &FuncDef,
    func_id: CustomFuncId,
) -> io::Result<()> {
    write!(w, "func {} (%0: ", func_renderer.render(func_id))?;
    write_type(
        w,
        Some(type_renderer),
        &write_mode_param,
        &write_lifetime,
        &func.arg_ty,
    )?;
    write!(w, "): ")?;
    write_type(
        w,
        Some(type_renderer),
        &write_mode_param,
        &write_lifetime_param,
        &func.ret_ty,
    )?;

    write!(w, "\n{}where ", " ".repeat(TAB_SIZE))?;
    write_constrs(w, &func.constrs)?;
    write!(w, "\n=\n")?;

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
    type_renderer: Option<&CustomTypeRenderer<CustomTypeId>>,
    customs: &annot::CustomTypes,
    typedef: &CustomTypeDef,
    type_id: CustomTypeId,
) -> io::Result<()> {
    write!(w, "custom type ")?;
    write_custom(w, type_renderer, type_id)?;
    write!(w, " = ")?;
    write_shape(w, type_renderer, &customs.types, &typedef.content)?;
    Ok(())
}

pub fn write_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    let type_renderer = CustomTypeRenderer::from_symbols(&program.custom_type_symbols);
    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);

    for (i, typedef) in &program.custom_types.types {
        write_typedef(w, Some(&type_renderer), &program.custom_types, typedef, i)?;
        writeln!(w)?;
    }
    for (i, func) in &program.funcs {
        write_func(w, &type_renderer, &func_renderer, func, i)?;
        writeln!(w)?;
    }
    Ok(())
}
