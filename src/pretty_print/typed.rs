use crate::data::resolved_ast::{
    ArrayOp, CustomGlobalId, CustomTypeId, GlobalId, IoOp, Type, TypeDef, TypeId, TypeParamId,
    VariantId,
};
use crate::data::typed_ast::*;
use crate::util::graph::{self, Graph};

use std::collections::BTreeSet;
use std::io;
use std::io::Write;

const TAB_SIZE: usize = 2;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Precedence {
    Top,
    Fun,
    App,
    Var,
}

struct Context<'a, 'b> {
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

    fn write_type_var(&mut self, type_var: &TypeParamId) -> io::Result<()> {
        self.write("'")?;
        self.write(type_var.0)?;
        Ok(())
    }

    fn write_type_id(&mut self, type_id: &TypeId) -> io::Result<()> {
        match type_id {
            TypeId::Bool => self.write("bool")?,
            TypeId::Byte => self.write("char")?,
            TypeId::Int => self.write("LargeInt.int")?,
            TypeId::Float => self.write("real")?,
            TypeId::Array => self.write("PersistentArray.array")?,
            TypeId::Custom(type_id) => {
                self.write(&self.prog.custom_type_symbols[type_id].type_name.0)?
            }
        }
        Ok(())
    }

    fn write_type(&mut self, type_: &Type, precedence: Precedence) -> io::Result<()> {
        let my_precedence = match type_ {
            Type::Var(_) => Precedence::Var,
            Type::App(_, args) => {
                if args.len() == 0 {
                    Precedence::Var
                } else {
                    Precedence::App
                }
            }
            Type::Tuple(_) => Precedence::App,
            Type::Func(_, _, _) => Precedence::Fun,
        };
        if precedence > my_precedence {
            self.write("(")?;
        }

        match type_ {
            Type::Var(type_var) => self.write_type_var(type_var)?,
            Type::App(type_id, args) => {
                if args.len() == 1 {
                    self.write_type(&args[0], Precedence::Var)?;
                    self.write(" ")?;
                } else if args.len() > 1 {
                    self.write("(")?;
                    for (i, arg) in args.iter().enumerate() {
                        self.write_type(arg, Precedence::Var)?;
                        if i != args.len() - 1 {
                            self.write(", ")?;
                        }
                    }
                    self.write(") ")?;
                }
                self.write_type_id(type_id)?;
            }
            Type::Tuple(types) => {
                if types.len() == 0 {
                    self.write("unit")?;
                } else {
                    for (i, type_) in types.iter().enumerate() {
                        self.write_type(type_, Precedence::App)?;
                        if i != types.len() - 1 {
                            self.write(" * ")?;
                        }
                    }
                }
            }
            Type::Func(_purity, arg_type, ret_type) => {
                self.write_type(arg_type, Precedence::App)?;
                self.write(" -> ")?;
                self.write_type(ret_type, Precedence::Top)?;
            }
        }

        if precedence > my_precedence {
            self.write(")")?;
        }

        Ok(())
    }

    fn write_variant(&mut self, type_id: CustomTypeId, variant_id: VariantId) -> io::Result<()> {
        self.write(
            &self.prog.custom_type_symbols[type_id].variant_symbols[variant_id]
                .variant_name
                .0,
        )?;
        Ok(())
    }

    fn write_pattern(&mut self, p: &Pattern) -> io::Result<usize> {
        match p {
            Pattern::Any(_) => {
                self.write("_")?;
                Ok(0)
            }

            Pattern::Var(var_type) => {
                self.write("l")?;
                self.write(self.num_locals)?;
                self.write(" : ")?;
                self.write_type(var_type, Precedence::Top)?;
                Ok(1)
            }
            Pattern::Tuple(pats) => {
                if pats.len() == 1 {
                    panic!("length 1 tuple");
                }
                self.write("(")?;
                let mut total_locals = 0;
                for (i, pat) in pats.iter().enumerate() {
                    let num_locals = self.write_pattern(pat)?;
                    total_locals += num_locals;
                    self.add_locals(num_locals);
                    if i != pats.len() - 1 {
                        self.write(", ")?;
                    }
                }
                self.remove_locals(total_locals);
                self.write(")")?;
                Ok(total_locals)
            }
            Pattern::Ctor(type_id, _type_args, variant_id, maybe_pattern) => {
                match type_id {
                    TypeId::Bool => match variant_id.0 {
                        0 => self.write("false")?,
                        1 => self.write("true")?,
                        _ => unreachable!(),
                    },
                    TypeId::Byte => todo!(),
                    TypeId::Int => todo!(),
                    TypeId::Float => todo!(),
                    TypeId::Array => todo!(),
                    TypeId::Custom(type_id) => {
                        self.write_variant(*type_id, *variant_id)?;
                    }
                }
                let new_locals = match maybe_pattern {
                    Some(p) => {
                        self.write(" (")?;
                        let n = self.write_pattern(p)?;
                        self.write(")")?;
                        n
                    }
                    None => 0,
                };
                Ok(new_locals)
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
            Pattern::Span(_hi, _lo, pattern) => self.write_pattern(pattern),
        }
    }

    fn write_global_id(&mut self, global_id: &GlobalId) -> io::Result<()> {
        match global_id {
            GlobalId::Intrinsic(intrinsic) => {
                self.write("intrinsic_")?;
                self.write(&format!("{:?}", intrinsic))?;
            }
            GlobalId::ArrayOp(array_op) => match array_op {
                ArrayOp::Get => self.write("intrinsic_get")?,
                ArrayOp::Extract => self.write("intrinsic_extract")?,
                ArrayOp::Len => self.write("intrinsic_len")?,
                ArrayOp::Push => self.write("intrinsic_push")?,
                ArrayOp::Pop => self.write("intrinsic_pop")?,
                ArrayOp::Reserve => self.write("intrinsic_reserve")?,
            },
            GlobalId::IoOp(io_op) => match io_op {
                IoOp::Input => self.write("input")?,
                IoOp::Output => self.write("output")?,
            },
            GlobalId::Panic => self.write("panic")?,
            GlobalId::Ctor(type_id, variant_id) => match type_id {
                TypeId::Bool => {
                    let bool_name = match variant_id.0 {
                        0 => "false",
                        1 => "true",
                        _ => unreachable!(),
                    };
                    self.write(bool_name)?;
                }
                TypeId::Byte => todo!(),
                TypeId::Int => todo!(),
                TypeId::Float => todo!(),
                TypeId::Array => todo!(),
                TypeId::Custom(custom_type_id) => {
                    self.write_variant(*custom_type_id, *variant_id)?;
                }
            },
            GlobalId::Custom(custom_global_id) => {
                if let Expr::Lam(_, _, _, _, _, _) = self.prog.vals[custom_global_id].body {
                    self.write_identifier(*custom_global_id)?;
                } else {
                    self.write_identifier(*custom_global_id)?;
                    self.write(" ()")?;
                }
            }
        };

        Ok(())
    }

    fn write_expr(&mut self, expr: &Expr, precedence: Precedence) -> io::Result<()> {
        let my_precedence = match expr {
            Expr::Global(global, _) => match global {
                GlobalId::Custom(custom_global_id) => {
                    if let Expr::Lam(_, _, _, _, _, _) = self.prog.vals[custom_global_id].body {
                        Precedence::Var
                    } else {
                        Precedence::App
                    }
                }
                _ => Precedence::Var,
            },
            Expr::Local(_) => Precedence::Var,
            Expr::Tuple(_) => Precedence::Var,
            Expr::Lam(_, _, _, _, _, _) => Precedence::App,
            Expr::App(_, _, _) => Precedence::App,
            Expr::Match(_, _, _) => Precedence::Fun,
            Expr::LetMany(_, _) => Precedence::App,
            Expr::ArrayLit(_, _) => Precedence::App,
            Expr::ByteLit(_) => Precedence::Var,
            Expr::IntLit(_) => Precedence::Var,
            Expr::FloatLit(_) => Precedence::Var,
            Expr::Span(_, _, _) => Precedence::Var,
        };

        if precedence > my_precedence {
            self.write("(")?;
        }

        match expr {
            Expr::Global(global_id, _type_args) => {
                self.write_global_id(global_id)?;
            }
            Expr::Local(local_id) => {
                self.write("l")?;
                self.write(local_id.0)?;
            }
            Expr::Tuple(exprs) => {
                self.write("(")?;
                for (i, expr) in exprs.iter().enumerate() {
                    self.write_expr(expr, Precedence::Top)?;
                    if i != exprs.len() - 1 {
                        self.write(", ")?;
                    }
                }
                self.write(")")?;
            }
            Expr::Lam(_purity, _arg_type, _ret_type, pattern, body, _prof) => {
                self.write("fn (")?;
                let num_locals = self.write_pattern(pattern)?;
                self.add_indent();
                self.add_locals(num_locals);
                self.write(") ")?;
                self.write("=> ")?;
                self.write_expr(body, Precedence::Top)?;
                self.remove_indent();
                self.remove_locals(num_locals);
            }
            Expr::App(_purity, func, arg) => {
                self.write_expr(func, Precedence::Var)?;
                self.write(" ")?;
                self.write_expr(arg, Precedence::Var)?;
            }
            Expr::Match(expr, patterns, _type) => {
                self.write("case ")?;
                self.write_expr(expr, Precedence::App)?;
                self.write(" of ")?;
                for (i, (pattern, expr)) in patterns.iter().enumerate() {
                    self.writeln()?;
                    if i == 0 {
                        self.write("  ")?;
                    } else {
                        self.write("| ")?;
                    }

                    let num_locals = self.write_pattern(pattern)?;

                    self.add_indent();
                    self.add_locals(num_locals);
                    self.write(" => ")?;
                    self.write_expr(expr, Precedence::App)?;
                    self.remove_indent();
                    self.remove_locals(num_locals);
                }
            }
            Expr::LetMany(bindings, expr) => {
                let mut total_locals = 0;
                self.write("let")?;
                self.add_indent();

                for binding in bindings {
                    self.writeln()?;
                    self.write("val ")?;
                    let num_locals = self.write_pattern(&binding.0)?;
                    total_locals = total_locals + num_locals;
                    self.write(" = ")?;
                    self.write_expr(&binding.1, Precedence::Top)?;
                    self.add_locals(num_locals);
                }
                self.remove_indent();
                self.writeln()?;
                self.write("in")?;
                self.add_indent();

                self.writeln()?;
                self.write_expr(expr, Precedence::Top)?;

                self.remove_indent();
                self.remove_locals(total_locals);

                self.writeln()?;
                self.write("end")?;
            }
            Expr::ArrayLit(_type, elems) => {
                self.write("PersistentArray.fromList ")?;
                self.write("[")?;
                for (i, elem) in elems.iter().enumerate() {
                    self.write_expr(elem, Precedence::Top)?;
                    if i != elems.len() - 1 {
                        self.write(", ")?;
                    }
                }
                self.write("]")?;
            }
            Expr::ByteLit(byte) => {
                self.write_byte_const(byte)?;
            }
            Expr::IntLit(int) => {
                self.write_int_const(*int)?;
            }
            Expr::FloatLit(float) => {
                self.write_float_const(*float)?;
            }
            Expr::Span(_lo, _hi, expr) => {
                self.write_expr(expr, precedence)?;
            }
        };

        if precedence > my_precedence {
            self.write(")")?;
        }
        Ok(())
    }

    fn write_byte_const(&mut self, byte: &u8) -> Result<(), io::Error> {
        self.write("#\"")?;
        if *byte == '\"' as u8 {
            self.write("\\\"")?;
        } else if !byte.is_ascii_control() {
            self.write(*byte as char)?;
        } else {
            self.write(&format!("\\{:03}", byte))?;
        }
        self.write("\"")?;
        Ok(())
    }

    fn write_int_const(&mut self, int: i64) -> Result<(), io::Error> {
        self.write(int)?;
        Ok(())
    }

    fn write_float_const(&mut self, float: f64) -> Result<(), io::Error> {
        self.write(float)?;
        if float.fract() == 0.0 {
            self.write(".0")?;
        }
        Ok(())
    }

    fn write_custom_type(&mut self, type_id: CustomTypeId, def: &TypeDef) -> io::Result<()> {
        self.write("datatype ")?;
        if def.num_params == 1 {
            self.write("'0 ")?;
        } else if def.num_params > 1 {
            self.write("(")?;
            for type_arg in 0..def.num_params {
                self.write_type_var(&TypeParamId(type_arg))?;
                if type_arg != def.num_params - 1 {
                    self.write(", ")?;
                }
            }
            self.write(") ")?;
        }
        self.write(&self.prog.custom_type_symbols[type_id].type_name.0)?;
        self.write(" = ")?;
        self.writeln()?;
        for (i, (variant_id, variant)) in def.variants.iter().enumerate() {
            if i == 0 {
                self.write("  ")?;
            } else {
                self.write("| ")?;
            }

            match variant {
                Some(type_arg) => {
                    self.write_variant(type_id, variant_id)?;
                    self.write(" of ")?;
                    self.write_type(type_arg, Precedence::Top)?;
                }
                None => self.write_variant(type_id, variant_id)?,
            }
            self.writeln()?;
        }

        Ok(())
    }
    fn write_identifier(&mut self, custom_global_id: CustomGlobalId) -> io::Result<()> {
        self.write(&self.prog.val_symbols[custom_global_id].val_name.0)?;
        self.write("_")?;
        self.write(custom_global_id.0)?;
        Ok(())
    }

    fn write_program(&mut self, prog: &Program) -> io::Result<()> {
        self.write("(* Lines 1-1958 are prelude, included in every generated SML program. *)")?;
        self.write("(* The generated program begins on line 1959. *)")?;
        self.writeln()?;
        self.write(PRELUDE_PERSISTENT)?;
        self.writeln()?;
        self.write(PRELUDE)?;
        self.writeln()?;

        for (id, type_def) in prog.custom_types.iter() {
            self.write_custom_type(id, type_def)?;
            self.writeln()?;
        }

        let graph_sccs = graph::strongly_connected(&Graph {
            edges_out: prog.vals.map(|_, val_def| {
                let mut deps = BTreeSet::new();
                add_func_deps(&mut deps, &val_def.body);
                deps.into_iter().collect()
            }),
        });

        for scc in graph_sccs {
            for (i, id) in scc.iter().enumerate() {
                let val = &prog.vals[id];
                if let Expr::Lam(_purity, _arg_type, ret_type, pattern, body, _prof) = &val.body {
                    if i == 0 {
                        self.write("fun ")?;
                    } else {
                        self.write("and ")?;
                    }
                    self.write_identifier(*id)?;
                    self.write(" (")?;
                    let num_locals = self.write_pattern(&pattern)?;
                    self.write("): ")?;
                    self.write_type(&ret_type, Precedence::Top)?;
                    self.write(" =")?;
                    self.add_indent();
                    self.add_locals(num_locals);

                    self.writeln()?;
                    self.write_expr(&body, Precedence::Top)?;

                    self.remove_indent();
                    self.remove_locals(num_locals);
                } else {
                    self.write("fun ")?;
                    self.write_identifier(*id)?;
                    self.write(" (): ")?;
                    self.write_type(&val.scheme.body, Precedence::Top)?;
                    self.write(" =")?;
                    self.add_indent();
                    self.writeln()?;

                    self.write_expr(&val.body, Precedence::Top)?;
                    self.remove_indent();
                }
            }
            self.writeln()?;
            self.writeln()?;
        }
        self.writeln()?;
        self.write("val _ = main_")?;
        self.write(prog.main.0)?;
        self.write(" ();")?;
        self.writeln()?;
        Ok(())
    }
}

const PRELUDE : &str = "
fun intrinsic_AddByte(x : char, y : char): char = chr (Word8.toInt (Word8.fromInt (ord x) + Word8.fromInt (ord y)))
fun intrinsic_SubByte(x : char, y : char): char = chr (Word8.toInt (Word8.fromInt (ord x) - Word8.fromInt (ord y)))
fun intrinsic_MulByte(x : char, y : char): char = chr (Word8.toInt (Word8.fromInt (ord x) * Word8.fromInt (ord y)))
fun intrinsic_DivByte(x : char, y : char): char = chr (Word8.toInt (Word8.fromInt (ord x) div Word8.fromInt (ord y)))
fun intrinsic_NegByte(x : char): char = chr (Word8.toInt (~ (Word8.fromInt (ord x))))
fun intrinsic_EqByte(x : char, y : char): bool = x = y
fun intrinsic_LtByte(x : char, y : char): bool = x < y
fun intrinsic_LteByte(x : char, y : char): bool = x <= y
fun intrinsic_GtByte(x : char, y : char): bool = x > y
fun intrinsic_GteByte(x : char, y : char): bool = x >= y
fun intrinsic_AddInt(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.fromLargeInt x + Word64.fromLargeInt y)
fun intrinsic_SubInt(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.fromLargeInt x - Word64.fromLargeInt y)
fun intrinsic_MulInt(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.fromLargeInt x * Word64.fromLargeInt y)
fun intrinsic_DivInt(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.fromLargeInt x div Word64.fromLargeInt y)
fun intrinsic_NegInt(x : LargeInt.int): LargeInt.int = Word64.toLargeIntX (~ (Word64.fromLargeInt x))
fun intrinsic_EqInt(x : LargeInt.int, y : LargeInt.int): bool = x = y
fun intrinsic_LtInt(x : LargeInt.int, y : LargeInt.int): bool = x < y
fun intrinsic_LteInt(x : LargeInt.int, y : LargeInt.int): bool = x <= y
fun intrinsic_GtInt(x : LargeInt.int, y : LargeInt.int): bool = x > y
fun intrinsic_GteInt(x : LargeInt.int, y : LargeInt.int): bool = x >= y
fun intrinsic_AddFloat(x : real, y : real): real = x + y
fun intrinsic_SubFloat(x : real, y : real): real = x - y
fun intrinsic_MulFloat(x : real, y : real): real = x * y
fun intrinsic_DivFloat(x : real, y : real): real = x / y
fun intrinsic_NegFloat(x : real): real = ~ x
fun intrinsic_EqFloat(x : real, y : real): bool = Real.== (x, y)
fun intrinsic_LtFloat(x : real, y : real): bool = x < y
fun intrinsic_LteFloat(x : real, y : real): bool = x <= y
fun intrinsic_GtFloat(x : real, y : real): bool = x > y
fun intrinsic_GteFloat(x : real, y : real): bool = x >= y
fun intrinsic_Not(x : bool): bool = not x
fun intrinsic_ByteToInt(x : char): LargeInt.int = Int.toLarge (ord x)
fun intrinsic_ByteToIntSigned(x : char): LargeInt.int = Word8.toLargeIntX (Word8.fromInt (ord x))
fun intrinsic_IntToByte(x : LargeInt.int): char = chr (Word8.toInt (Word8.fromLargeInt x))
fun intrinsic_IntShiftLeft(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.<< (Word64.fromLargeInt x, Word.fromLargeInt (y mod 64)))
fun intrinsic_IntShiftRight(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.>> (Word64.fromLargeInt x, Word.fromLargeInt (y mod 64)))
fun intrinsic_IntBitAnd(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.andb (Word64.fromLargeInt x, Word64.fromLargeInt y))
fun intrinsic_IntBitOr(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.orb (Word64.fromLargeInt x, Word64.fromLargeInt y))
fun intrinsic_IntBitXor(x : LargeInt.int, y : LargeInt.int): LargeInt.int = Word64.toLargeIntX (Word64.xorb (Word64.fromLargeInt x, Word64.fromLargeInt y))

fun intrinsic_get(l : 'a PersistentArray.array, i : LargeInt.int): 'a = PersistentArray.sub (l, (Int.fromLarge i))
fun intrinsic_extract(l : 'a PersistentArray.array, i : LargeInt.int): 'a * ('a -> 'a PersistentArray.array) = (PersistentArray.sub (l, (Int.fromLarge i)), fn new => PersistentArray.update (l, Int.fromLarge i, new))
fun intrinsic_len(l : 'a PersistentArray.array): LargeInt.int = Int.toLarge (PersistentArray.length l)
fun intrinsic_push(l : 'a PersistentArray.array, x : 'a): 'a PersistentArray.array = PersistentArray.append (l, x)
fun intrinsic_pop(l : 'a PersistentArray.array): 'a PersistentArray.array * 'a = PersistentArray.popEnd(l)
fun intrinsic_reserve(l : 'a PersistentArray.array, i : LargeInt.int): 'a PersistentArray.array = l

fun input(()) : char PersistentArray.array = #1 (intrinsic_pop (PersistentArray.fromList (explode (Option.getOpt ((TextIO.inputLine TextIO.stdIn), \"\\n\")))))
fun output(l : char PersistentArray.array) = print (implode (PersistentArray.toList l));
fun panic(l : char PersistentArray.array) = raise Fail (implode (PersistentArray.toList l))
";

const PRELUDE_PERSISTENT: &str = include_str!("persistent.sml");

fn add_func_deps(deps: &mut BTreeSet<CustomGlobalId>, expr: &Expr) {
    match expr {
        Expr::Global(global_id, _) => match global_id {
            GlobalId::Intrinsic(_) => {}
            GlobalId::ArrayOp(_) => {}
            GlobalId::IoOp(_) => {}
            GlobalId::Panic => {}
            GlobalId::Ctor(_, _) => {}
            GlobalId::Custom(custom_id) => {
                deps.insert(*custom_id);
            }
        },
        Expr::Local(_) => {}
        Expr::Tuple(elems) => {
            for elem in elems {
                add_func_deps(deps, elem);
            }
        }
        Expr::Lam(_, _, _, _, body, _) => add_func_deps(deps, body),
        Expr::App(_, func, arg) => {
            add_func_deps(deps, func);
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
        Expr::ByteLit(_) => {}
        Expr::IntLit(_) => {}
        Expr::FloatLit(_) => {}
        Expr::Span(_, _, expr) => {
            add_func_deps(deps, expr);
        }
    }
}

pub fn write_program(w: &mut dyn Write, program: &Program) -> io::Result<()> {
    let mut context = Context {
        writer: w,
        indentation: 0,
        num_locals: 0,
        prog: program,
    };
    context.write_program(program)?;
    Ok(())
}
