use crate::data::first_order_ast::*;
use crate::data::mono_ast::ValSymbols;
use crate::data::num_type::NumType;
use crate::data::profile::ProfilePointId;
use crate::data::purity::Purity;
use crate::data::resolved_ast;
use crate::util::graph::{self, Graph};

use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::io::Write;

const TAB_SIZE: usize = 2;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Variant {
    OCAML,
    SML,
    MORPHIC,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Precedence {
    Top,
    Fun,
    App,
    Var,
}

struct Context<'a, 'b> {
    variant: Variant,
    writer: &'b mut dyn Write,
    indentation: usize,
    num_locals: usize,
    prog: &'a Program,
}

impl<'a, 'b> Context<'a, 'b> {
    fn add_indent(&mut self) {
        self.indentation += TAB_SIZE;
    }

    fn remove_indent(&mut self) {
        self.indentation -= TAB_SIZE;
    }

    fn add_locals(&mut self, n: usize) {
        self.num_locals += n;
    }

    fn remove_locals(&mut self, n: usize) {
        self.num_locals -= n;
    }

    fn write(&mut self, e: impl std::fmt::Display + Copy) -> io::Result<()> {
        write![self.writer, "{}", e]
    }

    fn writeln(&mut self) -> io::Result<()> {
        writeln![self.writer]?;
        write![self.writer, "{}", " ".repeat(self.indentation)]
    }

    fn write_type(&mut self, type_: &Type, precedence: Precedence) -> io::Result<()> {
        fn get_precedence(t: &Type) -> Precedence {
            match t {
                Type::Bool => Precedence::Var,
                Type::Num(_) => Precedence::Var,
                Type::Array(_) => Precedence::App,
                Type::HoleArray(_) => Precedence::Fun,
                Type::Tuple(types) => {
                    if types.len() == 0 {
                        Precedence::Var
                    } else if types.len() == 1 {
                        get_precedence(&types[0])
                    } else {
                        Precedence::Fun
                    }
                }
                Type::Custom(_) => Precedence::Var,
            }
        }
        let my_precedence = get_precedence(type_);
        if precedence > my_precedence {
            self.write("(")?;
        }

        match type_ {
            Type::Bool => match self.variant {
                Variant::OCAML | Variant::SML => {
                    self.write("bool")?;
                }
                Variant::MORPHIC => {
                    self.write("Bool")?;
                }
            },
            Type::Num(num_type) => match num_type {
                NumType::Byte => match self.variant {
                    Variant::OCAML | Variant::SML => {
                        self.write("char")?;
                    }
                    Variant::MORPHIC => {
                        self.write("Byte")?;
                    }
                },
                NumType::Int => match self.variant {
                    Variant::OCAML => {
                        self.write("int64")?;
                    }
                    Variant::SML => {
                        self.write("int")?;
                    }
                    Variant::MORPHIC => {
                        self.write("Int")?;
                    }
                },
                NumType::Float => match self.variant {
                    Variant::OCAML => self.write("float")?,
                    Variant::SML => self.write("real")?,
                    Variant::MORPHIC => self.write("Float")?,
                },
            },
            Type::Array(elem_type) => match self.variant {
                Variant::MORPHIC => {
                    self.write("Array ")?;
                    self.write_type(elem_type, Precedence::Var)?;
                }
                Variant::SML | Variant::OCAML => {
                    self.write_type(elem_type, Precedence::Var)?;
                    self.write(" PersistentArray.array")?;
                }
            },
            Type::HoleArray(elem_type) => match self.variant {
                Variant::MORPHIC => {
                    self.write_type(elem_type, Precedence::App)?;
                    self.write(" -> Array ")?;
                    self.write_type(elem_type, Precedence::Var)?;
                }
                Variant::SML | Variant::OCAML => {
                    self.write_type(elem_type, Precedence::App)?;
                    self.write(" -> ")?;
                    self.write_type(elem_type, Precedence::Var)?;
                    self.write(" PersistentArray.array")?;
                }
            },
            Type::Tuple(types) => {
                if types.len() == 0 {
                    match self.variant {
                        Variant::OCAML | Variant::SML => {
                            self.write("unit")?;
                        }
                        Variant::MORPHIC => {
                            self.write("()")?;
                        }
                    }
                } else if types.len() == 1 {
                    self.write_type(&types[0], precedence)?;
                } else {
                    match self.variant {
                        Variant::MORPHIC => {
                            self.write("(")?;
                            for (i, type_) in types.iter().enumerate() {
                                self.write_type(type_, Precedence::Top)?;
                                if i != types.len() - 1 {
                                    self.write(", ")?;
                                }
                            }
                            self.write(")")?;
                        }
                        Variant::SML | Variant::OCAML => {
                            for (i, type_) in types.iter().enumerate() {
                                self.write_type(type_, Precedence::App)?;
                                if i != types.len() - 1 {
                                    self.write(" * ")?;
                                }
                            }
                        }
                    }
                }
            }
            Type::Custom(custom_type_id) => {
                self.write_custom_type_id(*custom_type_id)?;
            }
        }

        if precedence > my_precedence {
            self.write(")")?;
        }

        Ok(())
    }

    fn write_custom_type_id(&mut self, type_id: CustomTypeId) -> io::Result<()> {
        match &self.prog.custom_type_symbols[type_id] {
            CustomTypeSymbols::CustomType(type_name) => match self.variant {
                Variant::OCAML | Variant::SML => {
                    self.write(&type_name.type_name.0.to_lowercase())?;
                    self.write("_")?;
                    self.write(type_id.0)?;
                }
                Variant::MORPHIC => {
                    self.write(&type_name.type_name.0)?;
                    self.write(type_id.0)?;
                }
            },
            CustomTypeSymbols::ClosureType => match self.variant {
                Variant::OCAML | Variant::SML => {
                    self.write("closure_")?;
                    self.write(type_id.0)?;
                }
                Variant::MORPHIC => {
                    self.write("Closure")?;
                    self.write(type_id.0)?;
                }
            },
        }
        Ok(())
    }

    fn write_variant(&mut self, type_id: CustomTypeId, variant_id: VariantId) -> io::Result<()> {
        match &self.prog.custom_type_symbols[type_id] {
            CustomTypeSymbols::CustomType(type_symbols) => {
                self.write(
                    &(type_symbols.variant_symbols[resolved_ast::VariantId(variant_id.0)]
                        .variant_name
                        .0),
                )?;
                self.write(type_id.0)?;
                self.write("_")?;
                self.write(variant_id.0)?;
            }
            CustomTypeSymbols::ClosureType => {
                self.write("Variant")?;
                self.write(type_id.0)?;
                self.write("_")?;
                self.write(variant_id.0)?;
            }
        }
        Ok(())
    }

    fn write_pattern(&mut self, p: &Pattern) -> io::Result<usize> {
        self.write_pattern_rec(p, true)
    }

    fn write_pattern_rec(&mut self, p: &Pattern, write_type: bool) -> io::Result<usize> {
        match p {
            Pattern::Any(_) => {
                self.write("_")?;
                Ok(0)
            }

            Pattern::Var(var_type) => {
                match self.variant {
                    Variant::OCAML => {
                        self.write("(")?;
                        self.write("l")?;
                        self.write(self.num_locals)?;
                        if write_type {
                            self.write(" : ")?;
                            self.write_type(var_type, Precedence::Top)?;
                        }
                        self.write(")")?;
                    }
                    Variant::SML => {
                        self.write("l")?;
                        self.write(self.num_locals)?;
                        self.write(" : ")?;
                        self.write_type(var_type, Precedence::Top)?;
                    }
                    Variant::MORPHIC => {
                        self.write("l")?;
                        self.write(self.num_locals)?;
                    }
                }
                Ok(1)
            }
            Pattern::Tuple(pats) => {
                if pats.len() == 1 {
                    self.write_pattern_rec(&pats[0], write_type)
                } else {
                    if let Variant::OCAML = self.variant {
                        if write_type {
                            self.write("(")?;
                        }
                    }

                    self.write("(")?;
                    let mut total_locals = 0;
                    for (i, pat) in pats.iter().enumerate() {
                        let num_locals = self.write_pattern_rec(pat, false)?;
                        total_locals += num_locals;
                        self.add_locals(num_locals);
                        if i != pats.len() - 1 {
                            self.write(", ")?;
                        }
                    }
                    self.remove_locals(total_locals);
                    self.write(")")?;

                    if let Variant::OCAML = self.variant {
                        if write_type {
                            self.write(" : ")?;
                            fn pat_to_type(p: &Pattern) -> Type {
                                match p {
                                    Pattern::Any(t) => t.clone(),
                                    Pattern::Var(t) => t.clone(),
                                    Pattern::Tuple(pats) => {
                                        Type::Tuple(pats.iter().map(|x| pat_to_type(x)).collect())
                                    }
                                    Pattern::Ctor(type_id, _, _) => Type::Custom(*type_id),
                                    Pattern::BoolConst(_) => Type::Bool,
                                    Pattern::ByteConst(_) => Type::Num(NumType::Byte),
                                    Pattern::IntConst(_) => Type::Num(NumType::Int),
                                    Pattern::FloatConst(_) => Type::Num(NumType::Float),
                                }
                            }

                            if pats.len() == 0 {
                                self.write("unit")?;
                            } else {
                                match self.variant {
                                    Variant::OCAML | Variant::SML => {
                                        for (i, pat) in pats.iter().enumerate() {
                                            self.write_type(&pat_to_type(pat), Precedence::App)?;
                                            if i != pats.len() - 1 {
                                                self.write(" * ")?;
                                            }
                                        }
                                    }
                                    Variant::MORPHIC => {
                                        self.write("(")?;
                                        for (i, pat) in pats.iter().enumerate() {
                                            self.write_type(&pat_to_type(pat), Precedence::Top)?;
                                            if i != pats.len() - 1 {
                                                self.write(", ")?;
                                            }
                                        }
                                        self.write(")")?;
                                    }
                                }
                            }
                            self.write(")")?;
                        }
                    }
                    Ok(total_locals)
                }
            }
            Pattern::Ctor(type_id, variant_id, maybe_pattern) => {
                self.write_variant(*type_id, *variant_id)?;
                let new_locals = match maybe_pattern {
                    Some(p) => {
                        self.write(" (")?;
                        let n = self.write_pattern_rec(p, write_type)?;
                        self.write(")")?;
                        n
                    }
                    None => 0,
                };
                Ok(new_locals)
            }
            Pattern::BoolConst(b) => {
                match self.variant {
                    Variant::MORPHIC => {
                        if *b {
                            self.write("True")?;
                        } else {
                            self.write("False")?;
                        }
                    }
                    Variant::OCAML | Variant::SML => {
                        if *b {
                            self.write("true")?;
                        } else {
                            self.write("false")?;
                        }
                    }
                }
                Ok(0)
            }
            Pattern::ByteConst(byte) => {
                self.write_byte_const(byte)?;
                Ok(0)
            }
            Pattern::IntConst(int) => {
                self.write_int_const(*int)?;
                Ok(0)
            }
            Pattern::FloatConst(_) => todo!(),
        }
    }

    fn write_expr(&mut self, expr: &Expr, precedence: Precedence) -> io::Result<()> {
        let my_precedence = match expr {
            Expr::Intrinsic(_, _) => Precedence::App,
            Expr::ArrayOp(_) => Precedence::App,
            Expr::IoOp(_) => Precedence::App,
            Expr::Panic(_, _) => Precedence::App,
            Expr::Ctor(_, _, _) => Precedence::App,
            Expr::Local(_) => Precedence::Var,
            Expr::Tuple(_) => Precedence::Var,
            Expr::Call(_, _, _) => Precedence::App,
            Expr::Match(_, _, _) => Precedence::Top,
            Expr::LetMany(_, _) => Precedence::Top,
            Expr::ArrayLit(_, _) => Precedence::App,
            Expr::BoolLit(_) => Precedence::Var,
            Expr::ByteLit(_) => Precedence::Var,
            Expr::IntLit(_) => Precedence::Var,
            Expr::FloatLit(_) => Precedence::Var,
        };

        if precedence > my_precedence {
            self.write("(")?;
        }

        match expr {
            Expr::Intrinsic(intrinsic, expr) => match self.variant {
                Variant::MORPHIC => {
                    self.write(&format!("intrinsic_{:?}(", intrinsic))?;
                    self.write_expr(expr, Precedence::Top)?;
                    self.write(")")?;
                }
                Variant::OCAML | Variant::SML => {
                    self.write(&format!("intrinsic_{:?} ", intrinsic))?;
                    self.write_expr(expr, Precedence::Var)?;
                }
            },
            Expr::ArrayOp(array_op) => match array_op {
                ArrayOp::Get(_type, a, b) => match self.variant {
                    Variant::MORPHIC => {
                        self.write("get(")?;
                        self.write_expr(
                            &Expr::Tuple(vec![*a.clone(), *b.clone()]),
                            Precedence::Top,
                        )?;
                        self.write(")")?;
                    }
                    Variant::OCAML | Variant::SML => {
                        self.write("intrinsic_get ")?;
                        self.write_expr(
                            &Expr::Tuple(vec![*a.clone(), *b.clone()]),
                            Precedence::Top,
                        )?;
                    }
                },
                ArrayOp::Extract(_type, a, b) => match self.variant {
                    Variant::MORPHIC => {
                        self.write("extract(")?;
                        self.write_expr(
                            &Expr::Tuple(vec![*a.clone(), *b.clone()]),
                            Precedence::Top,
                        )?;
                        self.write(")")?;
                    }
                    Variant::OCAML | Variant::SML => {
                        self.write("intrinsic_extract ")?;
                        self.write_expr(
                            &Expr::Tuple(vec![*a.clone(), *b.clone()]),
                            Precedence::Top,
                        )?;
                    }
                },
                ArrayOp::Len(_type, a) => match self.variant {
                    Variant::MORPHIC => {
                        self.write("len(")?;
                        self.write_expr(a, Precedence::Top)?;
                        self.write(")")?;
                    }
                    Variant::OCAML | Variant::SML => {
                        self.write("intrinsic_len ")?;
                        self.write_expr(a, Precedence::Var)?;
                    }
                },
                ArrayOp::Push(_type, a, b) => match self.variant {
                    Variant::MORPHIC => {
                        self.write("push(")?;
                        self.write_expr(
                            &Expr::Tuple(vec![*a.clone(), *b.clone()]),
                            Precedence::Top,
                        )?;
                        self.write(")")?;
                    }
                    Variant::OCAML | Variant::SML => {
                        self.write("intrinsic_push ")?;
                        self.write_expr(
                            &Expr::Tuple(vec![*a.clone(), *b.clone()]),
                            Precedence::Top,
                        )?;
                    }
                },
                ArrayOp::Pop(_type, a) => match self.variant {
                    Variant::MORPHIC => {
                        self.write("pop(")?;
                        self.write_expr(a, Precedence::Top)?;
                        self.write(")")?;
                    }
                    Variant::OCAML | Variant::SML => {
                        self.write("intrinsic_pop ")?;
                        self.write_expr(a, Precedence::Var)?;
                    }
                },
                ArrayOp::Replace(_type, a, b) => match self.variant {
                    Variant::MORPHIC => {
                        self.write_expr(a, Precedence::Var)?;
                        self.write("(")?;
                        self.write_expr(b, Precedence::Top)?;
                        self.write(")")?;
                    }
                    Variant::OCAML | Variant::SML => {
                        self.write("intrinsic_replace ")?;
                        self.write_expr(
                            &Expr::Tuple(vec![*a.clone(), *b.clone()]),
                            Precedence::Top,
                        )?;
                    }
                },
                ArrayOp::Reserve(_type, a, b) => match self.variant {
                    Variant::MORPHIC => {
                        self.write("reserve(")?;
                        self.write_expr(
                            &Expr::Tuple(vec![*a.clone(), *b.clone()]),
                            Precedence::Top,
                        )?;
                        self.write(")")?;
                    }
                    Variant::OCAML | Variant::SML => {
                        self.write("intrinsic_reserve ")?;
                        self.write_expr(
                            &Expr::Tuple(vec![*a.clone(), *b.clone()]),
                            Precedence::Top,
                        )?;
                    }
                },
            },
            Expr::IoOp(io_op) => match io_op {
                IoOp::Input => match self.variant {
                    Variant::MORPHIC => {
                        self.write("do input ()")?;
                    }
                    Variant::OCAML | Variant::SML => {
                        self.write("input ()")?;
                    }
                },
                IoOp::Output(a) => match self.variant {
                    Variant::MORPHIC => {
                        self.write("do output (")?;
                        self.write_expr(a, Precedence::Top)?;
                        self.write(")")?;
                    }
                    Variant::OCAML | Variant::SML => {
                        self.write("output ")?;
                        self.write_expr(a, Precedence::Var)?;
                    }
                },
            },
            Expr::Panic(_type, a) => match self.variant {
                Variant::MORPHIC => {
                    self.write("panic (")?;
                    self.write_expr(a, Precedence::Top)?;
                    self.write(")")?;
                }
                Variant::OCAML | Variant::SML => {
                    self.write("panic ")?;
                    self.write_expr(a, Precedence::Var)?;
                }
            },
            Expr::Ctor(type_id, variant_id, maybe_expr) => match self.variant {
                Variant::MORPHIC => {
                    self.write_variant(*type_id, *variant_id)?;
                    match maybe_expr {
                        Some(expr) => {
                            self.write(" (")?;
                            self.write_expr(expr, Precedence::Top)?;
                            self.write(")")?;
                        }
                        None => {}
                    }
                }
                Variant::OCAML | Variant::SML => {
                    self.write_variant(*type_id, *variant_id)?;
                    match maybe_expr {
                        Some(expr) => {
                            self.write(" ")?;
                            self.write_expr(expr, Precedence::Var)?;
                        }
                        None => {}
                    }
                }
            },
            Expr::Local(local_id) => {
                self.write("l")?;
                self.write(local_id.0)?;
            }
            Expr::Tuple(exprs) => {
                if exprs.len() == 1 {
                    self.write_expr(&exprs[0], Precedence::Top)?;
                } else {
                    self.write("(")?;
                    for (i, expr) in exprs.iter().enumerate() {
                        self.write_expr(expr, Precedence::App)?;
                        if i != exprs.len() - 1 {
                            self.write(", ")?;
                        }
                    }
                    self.write(")")?;
                }
            }
            Expr::Call(purity, func_id, arg) => match self.variant {
                Variant::MORPHIC => {
                    if *purity == Purity::Impure {
                        self.write("do ")?;
                    }
                    self.write_custom_func_id(*func_id)?;
                    self.write(" (")?;
                    self.write_expr(arg, Precedence::Top)?;
                    self.write(")")?;
                }
                Variant::OCAML | Variant::SML => {
                    self.write_custom_func_id(*func_id)?;
                    self.write(" ")?;
                    self.write_expr(arg, Precedence::Var)?;
                }
            },
            Expr::Match(expr, patterns, _type) => {
                match self.variant {
                    Variant::OCAML => {
                        self.write("match ")?;
                        self.write_expr(expr, Precedence::App)?;
                        self.write(" with")?;
                    }
                    Variant::SML => {
                        self.write("case ")?;
                        self.write_expr(expr, Precedence::App)?;
                        self.write(" of")?;
                    }
                    Variant::MORPHIC => {
                        self.write("match ")?;
                        self.write_expr(expr, Precedence::App)?;
                        self.write(" {")?;
                    }
                }
                for (i, (pattern, expr)) in patterns.iter().enumerate() {
                    self.writeln()?;
                    match self.variant {
                        Variant::OCAML | Variant::SML => {
                            if i == 0 {
                                self.write("  ")?;
                            } else {
                                self.write("| ")?;
                            }
                        }
                        Variant::MORPHIC => {}
                    }

                    self.write("(")?;
                    let num_locals = match self.variant {
                        Variant::MORPHIC => self.write_pattern_rec(pattern, false)?,
                        _ => self.write_pattern(pattern)?,
                    };
                    self.write(")")?;

                    self.add_indent();
                    self.add_locals(num_locals);
                    match self.variant {
                        Variant::OCAML => {
                            self.write(" -> ")?;
                        }
                        Variant::SML => {
                            self.write(" => ")?;
                        }
                        Variant::MORPHIC => {
                            self.write(" -> ")?;
                        }
                    }
                    self.write_expr(expr, Precedence::App)?;
                    self.remove_indent();
                    self.remove_locals(num_locals);

                    match self.variant {
                        Variant::MORPHIC => {
                            self.write(",")?;
                        }
                        Variant::SML | Variant::OCAML => {}
                    }
                }
                match self.variant {
                    Variant::MORPHIC => {
                        self.write("}")?;
                    }
                    Variant::SML | Variant::OCAML => {}
                }
            }
            Expr::LetMany(bindings, expr) => {
                let mut total_locals = 0;
                self.write("let")?;
                self.add_indent();

                for (i, binding) in bindings.iter().enumerate() {
                    self.writeln()?;
                    match self.variant {
                        Variant::OCAML => {
                            if i != 0 {
                                self.write("in let ")?;
                            }
                        }
                        Variant::SML => {
                            self.write("val ")?;
                        }
                        Variant::MORPHIC => {
                            if i != 0 {
                                self.write("in let ")?;
                            }
                        }
                    }
                    let num_locals = match self.variant {
                        Variant::MORPHIC => self.write_pattern_rec(&binding.0, false)?,
                        _ => self.write_pattern(&binding.0)?,
                    };
                    total_locals = total_locals + num_locals;
                    self.write(" = ")?;
                    self.write_expr(&binding.1, Precedence::Fun)?;
                    self.add_locals(num_locals);
                }
                self.remove_indent();
                self.writeln()?;
                self.write("in")?;
                self.add_indent();

                self.writeln()?;
                self.write_expr(expr, Precedence::Fun)?;

                self.remove_indent();
                self.remove_locals(total_locals);

                if let Variant::SML = self.variant {
                    self.writeln()?;
                    self.write("end")?;
                }
            }
            Expr::ArrayLit(_type, elems) => {
                match self.variant {
                    Variant::OCAML | Variant::SML => {
                        self.write("PersistentArray.fromList ")?;
                    }
                    Variant::MORPHIC => {}
                }
                match self.variant {
                    Variant::OCAML => {
                        self.write("[|")?;
                    }
                    Variant::SML => {
                        self.write("[")?;
                    }
                    Variant::MORPHIC => {
                        self.write("[")?;
                    }
                }
                for (i, elem) in elems.iter().enumerate() {
                    self.write_expr(elem, Precedence::Top)?;
                    if i != elems.len() - 1 {
                        match self.variant {
                            Variant::OCAML => {
                                self.write("; ")?;
                            }
                            Variant::SML => {
                                self.write(", ")?;
                            }
                            Variant::MORPHIC => {
                                self.write(", ")?;
                            }
                        }
                    }
                }
                match self.variant {
                    Variant::OCAML => {
                        self.write("|]")?;
                    }
                    Variant::SML => {
                        self.write("]")?;
                    }
                    Variant::MORPHIC => {
                        self.write("]")?;
                    }
                }
            }
            Expr::BoolLit(b) => match self.variant {
                Variant::MORPHIC => {
                    if *b {
                        self.write("True")?;
                    } else {
                        self.write("False")?;
                    }
                }
                Variant::OCAML | Variant::SML => {
                    if *b {
                        self.write("true")?;
                    } else {
                        self.write("false")?;
                    }
                }
            },
            Expr::ByteLit(byte) => {
                self.write_byte_const(byte)?;
            }
            Expr::IntLit(int) => {
                self.write_int_const(*int)?;
            }
            Expr::FloatLit(float) => {
                self.write_float_const(*float)?;
            }
        };

        if precedence > my_precedence {
            self.write(")")?;
        }
        Ok(())
    }

    fn write_byte_const(&mut self, byte: &u8) -> Result<(), io::Error> {
        match self.variant {
            Variant::OCAML => {
                self.write("'")?;
                if *byte == '\'' as u8 {
                    self.write("\\\'")?;
                } else if *byte == '\\' as u8 {
                    self.write("\\\\")?;
                } else if !byte.is_ascii_control() {
                    self.write(*byte as char)?;
                } else {
                    self.write(&format!("\\{:03}", byte))?;
                }
                self.write("\'")?;
            }
            Variant::SML => {
                self.write("#\"")?;
                if *byte == '\"' as u8 {
                    self.write("\\\"")?;
                } else if *byte == '\\' as u8 {
                    self.write("\\\\")?;
                } else if !byte.is_ascii_control() {
                    self.write(*byte as char)?;
                } else {
                    self.write(&format!("\\{:03}", byte))?;
                }
                self.write("\"")?;
            }
            Variant::MORPHIC => {
                self.write(byte)?;
                self.write("b")?;
            }
        }
        Ok(())
    }

    fn write_int_const(&mut self, int: i64) -> Result<(), io::Error> {
        self.write(int)?;
        if let Variant::OCAML = self.variant {
            self.write("L")?;
        }
        Ok(())
    }

    fn write_float_const(&mut self, float: f64) -> Result<(), io::Error> {
        self.write(float)?;
        if float.fract() == 0.0 {
            self.write(".0")?;
        }
        Ok(())
    }

    fn write_custom_type(
        &mut self,
        type_id: CustomTypeId,
        def: &TypeDef,
        is_first: bool,
    ) -> io::Result<bool> {
        if def.variants.len() == 0 {
            return Ok(false);
        }

        match self.variant {
            Variant::MORPHIC => {
                self.write("type ")?;
            }
            Variant::OCAML => {
                if is_first {
                    self.write("type ")?;
                } else {
                    self.write("and ")?;
                }
            }
            Variant::SML => {
                if is_first {
                    self.write("datatype ")?;
                } else {
                    self.write("and ")?;
                }
            }
        }
        self.write_custom_type_id(type_id)?;
        match self.variant {
            Variant::MORPHIC => {
                self.write(" { ")?;
                self.add_indent();
            }
            _ => self.write(" = ")?,
        }
        self.writeln()?;
        for (i, (variant_id, variant)) in def.variants.iter().enumerate() {
            match self.variant {
                Variant::MORPHIC => {}
                Variant::OCAML | Variant::SML => {
                    if i == 0 {
                        self.write("  ")?;
                    } else {
                        self.write("| ")?;
                    }
                }
            }

            match variant {
                Some(type_arg) => {
                    self.write_variant(type_id, variant_id)?;
                    match self.variant {
                        Variant::MORPHIC => {
                            self.write(" (")?;
                            self.write_type(type_arg, Precedence::Top)?;
                            self.write(")")?;
                        }
                        Variant::OCAML | Variant::SML => {
                            self.write(" of ")?;
                            self.write_type(type_arg, Precedence::App)?;
                        }
                    }
                }
                None => self.write_variant(type_id, variant_id)?,
            }
            if let Variant::MORPHIC = self.variant {
                self.write(",")?;
            }

            self.writeln()?;
        }
        if let Variant::MORPHIC = self.variant {
            self.remove_indent();
            self.write("}")?;
        }

        Ok(true)
    }

    fn write_custom_func_id(&mut self, func_id: CustomFuncId) -> io::Result<()> {
        match &self.prog.func_symbols[func_id] {
            FuncSymbols::Global(val_symbols) => match val_symbols {
                ValSymbols::Wrapper(val_name) => {
                    self.write("wrapped_")?;
                    self.write(&val_name.val_name.0)?;
                    self.write("_")?;
                    self.write(func_id.0)?;
                }
                ValSymbols::Normal(val_name) => {
                    self.write(&val_name.val_name.0)?;
                    self.write("_")?;
                    self.write(func_id.0)?;
                }
            },
            FuncSymbols::Lam(lam_symbols) => {
                self.write("lam_")?;
                match &lam_symbols.lifted_from {
                    ValSymbols::Wrapper(val_name) => {
                        self.write("wrapped_")?;
                        self.write(&val_name.val_name.0)?;
                        self.write("_")?;
                        self.write(func_id.0)?;
                    }
                    ValSymbols::Normal(val_name) => {
                        self.write(&val_name.val_name.0)?;
                        self.write("_")?;
                        self.write(func_id.0)?;
                    }
                }
            }
            FuncSymbols::MainWrapper => {
                self.write("main_wrapper_")?;
                self.write(func_id.0)?;
            }
            FuncSymbols::Dispatch => {
                self.write("dispatch_")?;
                self.write(func_id.0)?;
            }
        }
        Ok(())
    }

    fn write_program(&mut self, prog: &Program) -> io::Result<()> {
        match self.variant {
            Variant::OCAML | Variant::SML => {
                self.write(
                    "(* Lines 1-150ish are prelude, included in every generated program. *)\n",
                )?;
                self.write("(* The generated program begins around line 150. *)")?;
            }
            Variant::MORPHIC => {}
        }
        self.writeln()?;
        match self.variant {
            Variant::OCAML => {
                self.write(PRELUDE_PERSISTENT_OCAML)?;
                self.writeln()?;
                self.write(PRELUDE_OCAML)?;
            }
            Variant::SML => {
                self.write(PRELUDE_PERSISTENT_SML)?;
                self.writeln()?;
                self.write(PRELUDE_SML)?;
            }
            Variant::MORPHIC => {
                self.write(PRELUDE_MOR)?;
            }
        }
        self.writeln()?;

        let type_sccs = graph::strongly_connected(&Graph {
            edges_out: prog.custom_types.map_refs(|_, type_def| {
                let mut deps = BTreeSet::new();
                for variant in &type_def.variants {
                    match variant.1 {
                        Some(type_) => {
                            add_type_deps(&mut deps, &type_);
                        }
                        None => {}
                    }
                }
                deps.into_iter().collect()
            }),
        });

        for scc in type_sccs {
            for (i, id) in scc.iter().enumerate() {
                let type_def = &prog.custom_types[id];
                let written = if i == 0 {
                    self.write_custom_type(*id, type_def, true)?
                } else {
                    self.write_custom_type(*id, type_def, false)?
                };
                if written {
                    self.writeln()?;
                }
            }
        }

        let func_graph = Graph {
            edges_out: prog.funcs.map_refs(|_, func_def| {
                let mut deps = BTreeSet::new();
                add_func_deps(&mut deps, &func_def.body);
                deps.into_iter().collect()
            }),
        };

        let mut reachable: BTreeSet<CustomFuncId> = BTreeSet::new();

        fn set_reachable(
            graph: &Graph<CustomFuncId>,
            reachable: &mut BTreeSet<CustomFuncId>,
            id: CustomFuncId,
        ) {
            reachable.insert(id);

            for reachable_id in &graph.edges_out[id] {
                if !reachable.contains(&reachable_id) {
                    set_reachable(graph, reachable, *reachable_id);
                }
            }
        }

        set_reachable(&func_graph, &mut reachable, prog.main);

        let func_sccs = graph::strongly_connected(&func_graph);

        let mut profile_points: BTreeMap<ProfilePointId, CustomFuncId> = BTreeMap::new();

        for scc in func_sccs {
            for id in &scc {
                if !reachable.contains(id) {
                    continue;
                }
            }

            for (i, id) in scc.iter().enumerate() {
                let func = &prog.funcs[id];

                if let Some(prof_id) = func.profile_point {
                    profile_points.insert(prof_id, *id);
                    match self.variant {
                        Variant::OCAML => {
                            self.write("let total_calls_")?;
                            self.write(id.0)?;
                            self.write(" = ref 0")?;
                            self.writeln()?;
                            self.write("let total_clock_nanos_")?;
                            self.write(id.0)?;
                            self.write(" = ref 0")?;
                            self.writeln()?;
                        }
                        Variant::SML => {
                            self.write("val total_calls_")?;
                            self.write(id.0)?;
                            self.write(" = ref 0")?;
                            self.writeln()?;
                            self.write("val total_clock_nanos_")?;
                            self.write(id.0)?;
                            self.write(" = ref 0")?;
                            self.writeln()?;
                        }
                        Variant::MORPHIC => {}
                    }
                }

                match self.variant {
                    Variant::MORPHIC => {
                        if func.purity == Purity::Impure {
                            self.write("proc ")?;
                        }
                    }
                    _ => {
                        if i == 0 {
                            match self.variant {
                                Variant::OCAML => {
                                    self.write("let rec ")?;
                                }
                                Variant::SML => {
                                    self.write("fun ")?;
                                }
                                Variant::MORPHIC => {}
                            }
                        } else {
                            self.write("and ")?;
                        }
                    }
                }

                self.write_custom_func_id(*id)?;

                let num_locals = match self.variant {
                    Variant::OCAML | Variant::SML => {
                        self.write(" (")?;
                        let num_locals = self.write_pattern(&func.arg)?;
                        self.write("): ")?;
                        self.write_type(&func.ret_type, Precedence::Top)?;
                        num_locals
                    }
                    Variant::MORPHIC => {
                        fn pattern_to_type(x: &Pattern) -> Type {
                            match x {
                                Pattern::Any(t) => t.clone(),
                                Pattern::Var(t) => t.clone(),
                                Pattern::Tuple(pats) => {
                                    Type::Tuple(pats.iter().map(|p| pattern_to_type(&p)).collect())
                                }
                                Pattern::Ctor(custom_type_id, _, _) => {
                                    Type::Custom(*custom_type_id)
                                }
                                Pattern::BoolConst(_) => Type::Bool,
                                Pattern::ByteConst(_) => Type::Num(NumType::Byte),
                                Pattern::IntConst(_) => Type::Num(NumType::Int),
                                Pattern::FloatConst(_) => Type::Num(NumType::Float),
                            }
                        }

                        self.write("(arg: ")?;
                        self.write_type(&pattern_to_type(&func.arg), Precedence::Top)?;
                        self.write("):")?;
                        self.write_type(&func.ret_type, Precedence::Top)?;
                        self.write("= let ")?;
                        let new_vars = self.write_pattern_rec(&func.arg, false)?;
                        self.write(" = arg in ")?;

                        new_vars
                    }
                };

                if let Some(_) = func.profile_point {
                    match self.variant {
                        Variant::OCAML => {
                            self.write(" = let start = Unix.gettimeofday () in let res =")?;
                        }
                        Variant::SML => {
                            self.write(" = let val start = Time.now () val res =")?;
                        }
                        Variant::MORPHIC => {}
                    }
                } else {
                    match self.variant {
                        Variant::MORPHIC => {}
                        _ => self.write(" =")?,
                    }
                }
                self.add_indent();
                self.add_locals(num_locals);

                self.writeln()?;
                self.write_expr(&func.body, Precedence::Top)?;

                self.remove_indent();
                self.remove_locals(num_locals);

                if let Some(_) = func.profile_point {
                    match self.variant {
                        Variant::OCAML => {
                            self.write(
                                " in let stop = Unix.gettimeofday () in let _ = incr total_calls_",
                            )?;
                            self.write(id.0)?;
                            self.write(" in let _ = total_clock_nanos_")?;
                            self.write(id.0)?;
                            self.write(" := int_of_float ((stop -. start) *. 1000000000.0) + !total_clock_nanos_")?;
                            self.write(id.0)?;
                            self.write(" in res")?;
                        }
                        Variant::SML => {
                            self.write(" val stop = Time.now () val _ = total_calls_")?;
                            self.write(id.0)?;
                            self.write(" := !total_calls_")?;
                            self.write(id.0)?;
                            self.write("+ 1 val _ = total_clock_nanos_")?;
                            self.write(id.0)?;
                            self.write(
                                    " := Time.toNanoseconds (Time.- (stop, start)) + !total_clock_nanos_",
                                )?;
                            self.write(id.0)?;
                            self.write(" in res end")?;
                        }
                        Variant::MORPHIC => {}
                    }
                }
                self.writeln()?;
                self.writeln()?;
            }
        }

        self.writeln()?;
        match self.variant {
            Variant::OCAML => {
                self.write("let _ = main_wrapper_")?;
            }
            Variant::SML => {
                self.write("val _ = main_wrapper_")?;
            }
            Variant::MORPHIC => {
                self.write("proc main(): () = do main_wrapper_")?;
            }
        }
        self.write(prog.main.0)?;
        match self.variant {
            Variant::OCAML | Variant::SML => self.write(" ();")?,
            Variant::MORPHIC => self.write("()")?,
        }
        self.writeln()?;

        if !profile_points.is_empty() {
            match self.variant {
                Variant::OCAML => {
                    self.write("let profile_path = Sys.getenv_opt(\"MORPHIC_PROFILE_PATH\");")?;
                    self.writeln()?;
                    self.write("in match profile_path with")?;
                    self.writeln()?;
                    self.write("  Some (profile_path) ->")?;
                    self.writeln()?;
                    self.write("    let profile_file = open_out profile_path;")?;
                    self.writeln()?;
                    self.write("    in Out_channel.output_string profile_file \"[\";")?;
                    self.writeln()?;
                    for profile_point in profile_points {
                        self.write("Printf.fprintf profile_file ")?;
                        let func_id = profile_point.1 .0;
                        let json_object = format!(
                            r#""{{\"func_id\": {func_id}, \"total_calls\": %d, \"total_clock_nanos\": %d}}""#
                        );
                        self.write(&json_object)?;
                        self.write(&format!(
                            " !total_calls_{func_id} !total_clock_nanos_{func_id};"
                        ))?;
                        self.writeln()?;
                    }
                    self.write("    Out_channel.output_string profile_file \"]\";")?;
                    self.writeln()?;
                    self.write(
                        "  | None -> Printf.eprintf \"Warning: no MORPHIC_PROFILE_PATH provided\"",
                    )?;
                    self.writeln()?;
                }
                Variant::SML => {
                    self.write("val profile_path = OS.Process.getEnv(\"MORPHIC_PROFILE_PATH\");")?;
                    self.writeln()?;
                    self.write("val _ = case profile_path of")?;
                    self.writeln()?;
                    self.write("  SOME (profile_path) =>")?;
                    self.writeln()?;
                    self.write("    let val profile_file = TextIO.openOut profile_path;")?;
                    self.writeln()?;
                    self.write("    in TextIO.output (profile_file, \"[\");")?;
                    self.writeln()?;
                    for profile_point in profile_points {
                        let func_id = profile_point.1 .0;
                        self.write(r#"    TextIO.output (profile_file, "{\"func_id\": "#)?;
                        self.write(func_id)?;
                        self.write(r#", \"total_calls\": ");"#)?;
                        self.writeln()?;
                        self.write(&format!(
                            "    TextIO.output (profile_file, (Int.toString (!total_calls_{func_id})));"
                        ))?;
                        self.writeln()?;
                        self.write(
                            r#"    TextIO.output (profile_file, ", \"total_clock_nanos\": ");"#,
                        )?;
                        self.writeln()?;
                        self.write(&format!(
                            "    TextIO.output (profile_file, (LargeInt.toString (!total_clock_nanos_{func_id})));"
                        ))?;
                        self.writeln()?;
                        self.write("    TextIO.output (profile_file, \"}\");")?;
                        self.writeln()?;
                    }
                    self.write("    TextIO.output (profile_file, \"]\")")?;
                    self.writeln()?;
                    self.write("    end")?;
                    self.writeln()?;
                    self.write(
                        "  | NONE => TextIO.output (TextIO.stdErr, \"Warning: no MORPHIC_PROFILE_PATH provided\")",
                    )?;
                    self.writeln()?;
                }
                Variant::MORPHIC => {}
            }
        }

        Ok(())
    }
}

const PRELUDE_SML: &str = include_str!("prelude.sml");
const PRELUDE_OCAML: &str = include_str!("prelude.ml");
const PRELUDE_MOR: &str = include_str!("prelude.mor");

// TODO: Add a flag to control whether we use immutable/mutable arrays in the generated SML code.
// We hard-code mutable for now because it's sufficient for the benchmarks we're interested in.
const PRELUDE_PERSISTENT_SML: &str = include_str!("persistent.sml");
const PRELUDE_PERSISTENT_OCAML: &str = include_str!("persistent.ml");

fn add_type_deps(deps: &mut BTreeSet<CustomTypeId>, type_: &Type) {
    match type_ {
        Type::Bool => {}
        Type::Num(_) => {}
        Type::Array(elem_type) => {
            add_type_deps(deps, elem_type);
        }
        Type::HoleArray(elem_type) => {
            add_type_deps(deps, elem_type);
        }
        Type::Tuple(elem_types) => {
            for elem_type in elem_types {
                add_type_deps(deps, elem_type);
            }
        }
        Type::Custom(custom_type_id) => {
            deps.insert(*custom_type_id);
        }
    }
}

fn add_func_deps(deps: &mut BTreeSet<CustomFuncId>, expr: &Expr) {
    match expr {
        Expr::Intrinsic(_, arg) => {
            add_func_deps(deps, arg);
        }
        Expr::ArrayOp(array_op) => match array_op {
            ArrayOp::Get(_, a, b) => {
                add_func_deps(deps, a);
                add_func_deps(deps, b);
            }
            ArrayOp::Extract(_, a, b) => {
                add_func_deps(deps, a);
                add_func_deps(deps, b);
            }
            ArrayOp::Len(_, a) => {
                add_func_deps(deps, a);
            }
            ArrayOp::Push(_, a, b) => {
                add_func_deps(deps, a);
                add_func_deps(deps, b);
            }
            ArrayOp::Pop(_, a) => {
                add_func_deps(deps, a);
            }
            ArrayOp::Replace(_, a, b) => {
                add_func_deps(deps, a);
                add_func_deps(deps, b);
            }
            ArrayOp::Reserve(_, a, b) => {
                add_func_deps(deps, a);
                add_func_deps(deps, b);
            }
        },
        Expr::IoOp(op) => match op {
            IoOp::Input => {}
            IoOp::Output(a) => add_func_deps(deps, a),
        },
        Expr::Panic(_, a) => add_func_deps(deps, a),
        Expr::Ctor(_, _, a) => match a {
            Some(b) => add_func_deps(deps, b),
            None => {}
        },
        Expr::Local(_) => {}
        Expr::Tuple(elems) => {
            for elem in elems {
                add_func_deps(deps, elem);
            }
        }
        Expr::Call(_, func, arg) => {
            deps.insert(*func);
            add_func_deps(deps, arg)
        }
        Expr::Match(expr, arms, _) => {
            add_func_deps(deps, expr);
            for (_, arm) in arms {
                add_func_deps(deps, arm);
            }
        }
        Expr::LetMany(lets, body) => {
            for (_, let_) in lets {
                add_func_deps(deps, let_);
            }
            add_func_deps(deps, body);
        }
        Expr::ArrayLit(_, elems) => {
            for elem in elems {
                add_func_deps(deps, elem);
            }
        }
        Expr::BoolLit(_) => {}
        Expr::ByteLit(_) => {}
        Expr::IntLit(_) => {}
        Expr::FloatLit(_) => {}
    }
}

pub fn write_sml_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    let mut context = Context {
        variant: Variant::SML,
        writer: w,
        indentation: 0,
        num_locals: 0,
        prog: program,
    };
    context.write_program(program)?;
    Ok(())
}

pub fn write_ocaml_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    let mut context = Context {
        variant: Variant::OCAML,
        writer: w,
        indentation: 0,
        num_locals: 0,
        prog: program,
    };
    context.write_program(program)?;
    Ok(())
}

pub fn write_morphic_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    let mut context = Context {
        variant: Variant::MORPHIC,
        writer: w,
        indentation: 0,
        num_locals: 0,
        prog: program,
    };
    context.write_program(program)?;
    Ok(())
}
