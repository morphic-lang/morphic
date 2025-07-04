use crate::data::first_order_ast::{CustomFuncId, CustomTypeId};
use crate::data::metadata::Metadata;
use crate::data::mode_annot_ast::{
    self as annot, ArrayOp, Constrs, CustomTypeDef, FuncDef, HeapModes, IoOp, Lt, LtParam, Mode,
    ModeParam, ModeSolution, ModeVar, Position, Program, Res, ResModes, Shape, ShapeInner,
};
use crate::data::num_type::NumType;
use crate::intrinsic_config::intrinsic_to_name;
use crate::pretty_print::utils::{
    write_delimited, write_metadata, CustomTypeRenderer, FuncRenderer,
};
use core::str;
use id_collections::Id;
use std::fmt;
use std::io::{self, Write};

pub use crate::pretty_print::borrow_common::*;

const TAB_SIZE: usize = 2;
const CONSTRS_PER_LINE: usize = 10;

type Type<I> = annot::Type<Res<ModeSolution, Lt>, I>;
type Occur = annot::Occur<Res<ModeSolution, Lt>, CustomTypeId>;
type Expr = annot::Expr<Res<ModeSolution, Lt>, CustomTypeId, CustomFuncId>;

#[derive(Clone, Debug, Copy)]
pub struct Context<'a, I, J> {
    pub type_renderer: &'a CustomTypeRenderer<I>,
    pub func_renderer: &'a FuncRenderer<J>,
    pub indentation: usize,
    pub num_locals: usize,
}

impl<'a, I, J> Context<'a, I, J> {
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

pub fn write_mode_param(w: &mut dyn Write, m: &ModeParam) -> io::Result<()> {
    write!(w, "${}", m.0)
}

pub fn write_mode_var(w: &mut dyn Write, m: &ModeVar) -> io::Result<()> {
    write!(w, "?{}", m.0)
}

pub fn write_mode_solution(w: &mut dyn Write, m: &ModeSolution) -> io::Result<()> {
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

pub fn write_resource_modes<M>(
    w: &mut dyn Write,
    write_mode: &impl Fn(&mut dyn Write, &M) -> io::Result<()>,
    modes: &ResModes<M>,
) -> io::Result<()> {
    match modes {
        ResModes::Stack(stack) => write_mode(w, stack),
        ResModes::Heap(HeapModes { access, storage }) => {
            write_mode(w, access)?;
            write!(w, "@")?;
            write_mode(w, storage)
        }
    }
}

pub fn write_resource<M, L>(
    w: &mut dyn Write,
    write_mode: &impl Fn(&mut dyn Write, &M) -> io::Result<()>,
    write_lifetime: &impl Fn(&mut dyn Write, &L) -> io::Result<()>,
    res: &Res<M, L>,
) -> io::Result<()> {
    write_resource_modes(w, write_mode, &res.modes)?;
    write!(w, "<")?;
    write_lifetime(w, &res.lt)?;
    write!(w, ">")?;
    Ok(())
}

pub fn write_custom<I: Id + 'static>(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<I>>,
    type_id: I,
) -> io::Result<()> {
    if let Some(type_renderer) = type_renderer {
        write!(w, "{}", type_renderer.render(type_id))
    } else {
        write!(w, "Custom#{}", type_id.to_index())
    }
}

pub fn write_type_raw<T, I: Id + 'static>(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<I>>,
    write_res: &impl Fn(&mut dyn Write, &T) -> io::Result<()>,
    shape: &Shape<I>,
    res: &[T],
) -> io::Result<()> {
    match &*shape.inner {
        ShapeInner::Bool => write!(w, "Bool"),
        ShapeInner::Num(NumType::Byte) => write!(w, "Byte"),
        ShapeInner::Num(NumType::Int) => write!(w, "Int"),
        ShapeInner::Num(NumType::Float) => write!(w, "Float"),
        ShapeInner::Tuple(shapes) => {
            let items = annot::iter_shapes(shapes, res);
            write_delimited(w, items, "(", ")", ", ", |w, (shape, res)| {
                write_type_raw(w, type_renderer, write_res, shape, res)
            })
        }
        ShapeInner::Variants(shapes) => {
            let items = annot::iter_shapes(shapes.as_slice(), res);
            write_delimited(w, items, "{", "}", ", ", |w, (shape, res)| {
                write_type_raw(w, type_renderer, write_res, shape, res)
            })
        }
        ShapeInner::Custom(type_id) => {
            write_custom(w, type_renderer, *type_id)?;
            write_delimited(w, res, "<", ">", ", ", |w, res| write_res(w, res))
        }
        ShapeInner::SelfCustom(type_id) => write!(w, "Self#{}", type_id.to_index()),
        ShapeInner::Array(shape) => {
            write_res(w, &res[0])?;
            write!(w, " Array (")?;
            write_type_raw(w, type_renderer, write_res, shape, &res[1..])?;
            write!(w, ")")
        }
        ShapeInner::HoleArray(shape) => {
            write_res(w, &res[0])?;
            write!(w, " HoleArray (")?;
            write_type_raw(w, type_renderer, write_res, shape, &res[1..])?;
            write!(w, ")")
        }
        ShapeInner::Boxed(shape) => {
            write_res(w, &res[0])?;
            write!(w, " Boxed (")?;
            write_type_raw(w, type_renderer, write_res, shape, &res[1..])?;
            write!(w, ")")
        }
    }
}

pub fn write_type<M, L, I: Id + 'static>(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<I>>,
    write_mode: impl Fn(&mut dyn Write, &M) -> io::Result<()>,
    write_lifetime: impl Fn(&mut dyn Write, &L) -> io::Result<()>,
    type_: &annot::Type<Res<M, L>, I>,
) -> io::Result<()> {
    write_type_raw(
        w,
        type_renderer,
        &|w, res| write_resource(w, &write_mode, &write_lifetime, res),
        &type_.shape(),
        type_.res().as_slice(),
    )
}

fn write_shape_impl<I: Id + 'static>(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<I>>,
    pos: Position,
    shape: &Shape<I>,
) -> io::Result<()> {
    let write_res = |w: &mut dyn Write| {
        let dummy = Res {
            modes: match pos {
                Position::Stack => ResModes::Stack(()),
                Position::Heap => ResModes::Heap(HeapModes {
                    access: (),
                    storage: (),
                }),
            },
            lt: (),
        };
        write_resource(w, &|w, _| write!(w, "_"), &|w, _| write!(w, "_"), &dummy)
    };
    match &*shape.inner {
        ShapeInner::Bool => write!(w, "Bool"),
        ShapeInner::Num(NumType::Byte) => write!(w, "Byte"),
        ShapeInner::Num(NumType::Int) => write!(w, "Int"),
        ShapeInner::Num(NumType::Float) => write!(w, "Float"),
        ShapeInner::Tuple(shapes) => write_delimited(w, shapes, "(", ")", ", ", |w, shape| {
            write_shape_impl(w, type_renderer, pos, shape)
        }),
        ShapeInner::Variants(shapes) => {
            write_delimited(w, shapes.values(), "{", "}", ", ", |w, shape| {
                write_shape_impl(w, type_renderer, pos, shape)
            })
        }
        ShapeInner::Custom(type_id) => {
            write_custom(w, type_renderer, *type_id)?;
            write!(w, "<...>")
        }
        ShapeInner::SelfCustom(type_id) => write!(w, "Self#{}", type_id.to_index()),
        ShapeInner::Array(shape) => {
            write_res(w)?;
            write!(w, " Array (")?;
            write_shape_impl(w, type_renderer, Position::Heap, shape)?;
            write!(w, ")")
        }
        ShapeInner::HoleArray(shape) => {
            write_res(w)?;
            write!(w, " HoleArray (")?;
            write_shape_impl(w, type_renderer, Position::Heap, shape)?;
            write!(w, ")")
        }
        ShapeInner::Boxed(shape) => {
            write_res(w)?;
            write!(w, " Boxed (")?;
            write_shape_impl(w, type_renderer, Position::Heap, shape)?;
            write!(w, ")")
        }
    }
}

pub fn write_shape<I: Id + 'static>(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<I>>,
    shape: &Shape<I>,
) -> io::Result<()> {
    write_shape_impl(w, type_renderer, Position::Stack, shape)
}

pub fn write_solved_type<I: Id + 'static>(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<I>,
    type_: &Type<I>,
) -> io::Result<()> {
    write_type(
        w,
        Some(type_renderer),
        write_mode_solution,
        write_lifetime,
        type_,
    )
}

pub fn write_occur<R, I: Id + 'static>(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<I>,
    write_res: &impl Fn(&mut dyn Write, &R) -> io::Result<()>,
    occur: &annot::Occur<R, I>,
) -> io::Result<()> {
    write!(w, "%{} as ", occur.id.0)?;
    write_type_raw(
        w,
        Some(type_renderer),
        write_res,
        occur.ty.shape(),
        occur.ty.res().as_slice(),
    )
}

fn write_single<R, I: Id + 'static>(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<I>,
    write_res: &impl Fn(&mut dyn Write, &R) -> io::Result<()>,
    name: &str,
    occur: &annot::Occur<R, I>,
) -> io::Result<()> {
    write!(w, "{name}(")?;
    write_occur(w, type_renderer, write_res, occur)?;
    write!(w, ")")
}

fn write_double<R, I: Id + 'static>(
    w: &mut dyn Write,
    type_renderer: &CustomTypeRenderer<I>,
    write_res: &impl Fn(&mut dyn Write, &R) -> io::Result<()>,
    name: &str,
    occur1: &annot::Occur<R, I>,
    occur2: &annot::Occur<R, I>,
) -> io::Result<()> {
    write!(w, "{name}(")?;
    write_occur(w, type_renderer, write_res, occur1)?;
    write!(w, ", ")?;
    write_occur(w, type_renderer, write_res, occur2)?;
    write!(w, ")")
}

fn match_string_bytes<R, I: Id + 'static, J: Id + 'static>(
    bindings: &[(annot::Type<R, I>, annot::Expr<R, I, J>, Metadata)],
) -> Option<String> {
    let mut result_bytes = Vec::new();
    for binding in bindings {
        if let (_, annot::Expr::ByteLit(byte), _) = binding {
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

pub fn write_expr<R, I: Id + 'static, J: Id + 'static>(
    w: &mut dyn Write,
    write_res: &impl Fn(&mut dyn Write, &R) -> io::Result<()>,
    expr: &annot::Expr<R, I, J>,
    context: Context<I, J>,
) -> io::Result<()> {
    match expr {
        annot::Expr::Local(occur) => write_occur(w, context.type_renderer, write_res, occur),
        annot::Expr::Call(_purity, func_id, occur) => {
            write!(w, "call {} (", context.func_renderer.render(func_id))?;
            write_occur(w, context.type_renderer, write_res, occur)?;
            write!(w, ")")
        }
        annot::Expr::LetMany(bindings, final_local) => {
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
                    let (binding_type, binding_expr, metadata) = &bindings[index];
                    write_metadata(w, new_context.indentation, metadata)?;
                    new_context.writeln(w)?;
                    write!(w, "{}: %{}: ", index, context.num_locals + index)?;
                    write_type_raw(
                        w,
                        Some(context.type_renderer),
                        write_res,
                        binding_type.shape(),
                        binding_type.res().as_slice(),
                    )?;
                    new_context.writeln(w)?;
                    write!(w, " = ")?;
                    write_expr(
                        w,
                        write_res,
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
            write_occur(w, context.type_renderer, write_res, final_local)?;
            Ok(())
        }
        annot::Expr::If(occur, then_branch, else_branch) => {
            write!(w, "if ")?;
            write_occur(w, context.type_renderer, write_res, occur)?;
            write!(w, " {{")?;

            let new_context = context.add_indent();
            new_context.writeln(w)?;
            write_expr(w, write_res, then_branch, new_context)?;
            context.writeln(w)?;

            write!(w, "}} else {{")?;
            new_context.writeln(w)?;
            write_expr(w, write_res, else_branch, new_context)?;
            context.writeln(w)?;

            write!(w, "}}")?;
            Ok(())
        }
        annot::Expr::CheckVariant(variant_id, occur) => {
            write!(w, "check variant {} ", variant_id.0)?;
            write_occur(w, context.type_renderer, write_res, occur)
        }
        annot::Expr::Unreachable(_type) => write!(w, "unreachable"),
        annot::Expr::Tuple(elems) => write_delimited(w, elems, "(", ")", ", ", |w, occur| {
            write_occur(w, context.type_renderer, write_res, occur)
        }),
        annot::Expr::TupleField(occur, index) => {
            write!(w, "tuple field {} ", index)?;
            write_occur(w, context.type_renderer, write_res, occur)
        }
        annot::Expr::WrapVariant(_variants, variant_id, occur) => {
            write!(w, "wrap variant {} ", variant_id.0)?;
            write_occur(w, context.type_renderer, write_res, occur)
        }
        annot::Expr::UnwrapVariant(variant_id, occur) => {
            write!(w, "unwrap variant {} ", variant_id.0)?;
            write_occur(w, context.type_renderer, write_res, occur)
        }
        annot::Expr::WrapBoxed(content, _) => {
            write!(w, "wrap boxed ")?;
            write_occur(w, context.type_renderer, write_res, content)
        }
        annot::Expr::UnwrapBoxed(content, _) => {
            write!(w, "unwrap boxed ")?;
            write_occur(w, context.type_renderer, write_res, content)
        }
        annot::Expr::WrapCustom(type_id, _recipe, occur) => {
            write!(w, "wrap custom {} ", context.type_renderer.render(*type_id))?;
            write_occur(w, context.type_renderer, write_res, occur)
        }
        annot::Expr::UnwrapCustom(type_id, _recipe, occur) => {
            write!(
                w,
                "unwrap custom {} ",
                context.type_renderer.render(*type_id)
            )?;
            write_occur(w, context.type_renderer, write_res, occur)
        }
        annot::Expr::Intrinsic(intr, local_id) => {
            write!(w, "{} ", intrinsic_to_name(*intr).debug_name())?;
            write_occur(w, context.type_renderer, write_res, local_id)
        }
        annot::Expr::ArrayOp(array_op) => match array_op {
            ArrayOp::Get(occur1, occur2, output_type) => {
                write_double(w, context.type_renderer, write_res, "get", occur1, occur2)?;
                write!(w, " as ")?;
                write_type_raw(
                    w,
                    Some(context.type_renderer),
                    write_res,
                    output_type.shape(),
                    output_type.res().as_slice(),
                )
            }
            ArrayOp::Extract(occur1, occur2) => write_double(
                w,
                context.type_renderer,
                write_res,
                "extract",
                occur1,
                occur2,
            ),
            ArrayOp::Len(occur) => write_single(w, context.type_renderer, write_res, "len", occur),
            ArrayOp::Push(occur1, occur2) => {
                write_double(w, context.type_renderer, write_res, "push", occur1, occur2)
            }
            ArrayOp::Pop(occur) => write_single(w, context.type_renderer, write_res, "pop", occur),
            ArrayOp::Replace(occur1, occur2) => write_double(
                w,
                context.type_renderer,
                write_res,
                "replace",
                occur1,
                occur2,
            ),
            ArrayOp::Reserve(occur1, occur2) => write_double(
                w,
                context.type_renderer,
                write_res,
                "reserve",
                occur1,
                occur2,
            ),
        },
        annot::Expr::IoOp(io_op) => match io_op {
            IoOp::Input => write!(w, "input"),
            IoOp::Output(occur) => {
                write_single(w, context.type_renderer, write_res, "output", occur)
            }
        },
        annot::Expr::Panic(_ret_type, occur) => {
            write_single(w, context.type_renderer, write_res, "panic", occur)
        }
        annot::Expr::ArrayLit(_type, elem_occurs) => {
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
        annot::Expr::BoolLit(val) => write!(w, "{}", if *val { "True" } else { "False" }),
        annot::Expr::ByteLit(val) => write!(w, "{:?}", (*val as char)),
        annot::Expr::IntLit(val) => write!(w, "{}", val),
        annot::Expr::FloatLit(val) => write!(w, "{}", val),
    }
}

pub fn write_constrs(w: &mut dyn Write, constrs: &Constrs) -> io::Result<()> {
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
        write_mode_param,
        write_lifetime,
        &func.arg_ty,
    )?;
    write!(w, "): ")?;
    write_type(
        w,
        Some(type_renderer),
        write_mode_param,
        write_lifetime_param,
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

    write_expr(
        w,
        &|w, res| write_resource(w, &write_mode_solution, &write_lifetime, res),
        &func.body,
        context,
    )?;
    writeln!(w)?;
    Ok(())
}

pub fn write_typedef<I: Id + 'static, J: Id + 'static>(
    w: &mut dyn Write,
    type_renderer: Option<&CustomTypeRenderer<I>>,
    typedef: &CustomTypeDef<I, J>,
    type_id: I,
) -> io::Result<()> {
    write!(w, "custom type ")?;
    write_custom(w, type_renderer, type_id)?;
    write!(w, " = ")?;
    write_shape(w, type_renderer, &typedef.content)?;
    Ok(())
}

pub fn write_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    let type_renderer = CustomTypeRenderer::from_symbols(&program.custom_type_symbols);
    let func_renderer = FuncRenderer::from_symbols(&program.func_symbols);

    for (i, typedef) in &program.custom_types.types {
        write_typedef(w, Some(&type_renderer), typedef, i)?;
        writeln!(w)?;
    }
    writeln!(w)?;
    for (i, func) in &program.funcs {
        write_func(w, &type_renderer, &func_renderer, func, i)?;
        writeln!(w)?;
    }
    Ok(())
}

// Convenience wrappers for debugging which implement `Display`

pub struct DisplayShape<'a, I> {
    type_renderer: Option<&'a CustomTypeRenderer<I>>,
    shape: &'a Shape<I>,
}

impl<I: Id + 'static> fmt::Display for DisplayShape<'_, I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut w = Vec::<u8>::new();
        write_shape(&mut w, self.type_renderer, self.shape).unwrap();
        f.write_str(str::from_utf8(&w).unwrap())
    }
}

impl<I: Id + 'static> Shape<I> {
    pub fn display<'a>(&'a self) -> DisplayShape<'a, I> {
        DisplayShape {
            type_renderer: None,
            shape: self,
        }
    }

    pub fn display_with<'a>(
        &'a self,
        type_renderer: &'a CustomTypeRenderer<I>,
    ) -> DisplayShape<'a, I> {
        DisplayShape {
            type_renderer: Some(type_renderer),
            shape: self,
        }
    }
}

pub struct DisplaySolverType<'a, L, I> {
    type_renderer: Option<&'a CustomTypeRenderer<I>>,
    type_: &'a annot::Type<Res<ModeVar, L>, I>,
}

impl<I: Id + 'static> fmt::Display for DisplaySolverType<'_, Lt, I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut w = Vec::new();
        write_type(
            &mut w,
            self.type_renderer,
            write_mode_var,
            write_lifetime,
            self.type_,
        )
        .unwrap();
        f.write_str(str::from_utf8(&w).unwrap())
    }
}

impl<I: Id + 'static> fmt::Display for DisplaySolverType<'_, LtParam, I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut w = Vec::new();
        write_type(
            &mut w,
            self.type_renderer,
            write_mode_var,
            write_lifetime_param,
            self.type_,
        )
        .unwrap();
        f.write_str(str::from_utf8(&w).unwrap())
    }
}

impl<L, I: Id + 'static> annot::Type<Res<ModeVar, L>, I> {
    pub fn display<'a>(&'a self) -> DisplaySolverType<'a, L, I> {
        DisplaySolverType {
            type_renderer: None,
            type_: self,
        }
    }

    pub fn display_with<'a>(
        &'a self,
        type_renderer: &'a CustomTypeRenderer<I>,
    ) -> DisplaySolverType<'a, L, I> {
        DisplaySolverType {
            type_renderer: Some(type_renderer),
            type_: self,
        }
    }
}

pub struct DisplaySolvedType<'a, L, I> {
    type_renderer: Option<&'a CustomTypeRenderer<I>>,
    type_: &'a annot::Type<Res<ModeSolution, L>, I>,
}

impl<I: Id + 'static> fmt::Display for DisplaySolvedType<'_, Lt, I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut w = Vec::new();
        write_type(
            &mut w,
            self.type_renderer,
            write_mode_solution,
            write_lifetime,
            self.type_,
        )
        .unwrap();
        f.write_str(str::from_utf8(&w).unwrap())
    }
}

impl<I: Id + 'static> fmt::Display for DisplaySolvedType<'_, LtParam, I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut w = Vec::new();
        write_type(
            &mut w,
            self.type_renderer,
            write_mode_solution,
            write_lifetime_param,
            self.type_,
        )
        .unwrap();
        f.write_str(str::from_utf8(&w).unwrap())
    }
}

impl<L, I: Id + 'static> annot::Type<Res<ModeSolution, L>, I> {
    pub fn display<'a>(&'a self) -> DisplaySolvedType<'a, L, I> {
        DisplaySolvedType {
            type_renderer: None,
            type_: self,
        }
    }

    pub fn display_with<'a>(
        &'a self,
        type_renderer: &'a CustomTypeRenderer<I>,
    ) -> DisplaySolvedType<'a, L, I> {
        DisplaySolvedType {
            type_renderer: Some(type_renderer),
            type_: self,
        }
    }
}
